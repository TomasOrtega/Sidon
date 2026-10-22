#!/usr/bin/env python3
"""Report local Codex team token counters without exporting transcript content."""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path


FIELDS = (
    "input_tokens", "cached_input_tokens", "cache_write_input_tokens",
    "output_tokens", "reasoning_output_tokens", "total_tokens",
)
CONTEXT_THRESHOLD = 272000
PRICING_URL = "https://developers.openai.com/api/docs/pricing"
RATES = {
    "short": {"standard": (2.0, 0.10, 10.0), "fast": (4.0, 0.20, 20.0)},
    "long": {"standard": (4.0, 0.20, 15.0), "fast": (8.0, 0.40, 30.0)},
}


def zero_usage():
    return dict.fromkeys(FIELDS, 0)


def normalized_usage(raw):
    result = {key: int(raw.get(key, 0)) for key in FIELDS}
    if "total_tokens" not in raw:
        result["total_tokens"] = result["input_tokens"] + result["output_tokens"]
    if any(value < 0 for value in result.values()):
        raise ValueError("Negative token usage counter")
    return result


def add_usage(target, source):
    for key in FIELDS:
        target[key] += source[key]


def events(path):
    with path.open(encoding="utf-8") as handle:
        for number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            try:
                yield number, json.loads(line)
            except json.JSONDecodeError:
                if not line.endswith("\n"):
                    return
                raise ValueError(f"Malformed JSON in {path.name}, line {number}") from None


def parse_timestamp(value):
    return datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(timezone.utc)


def owner_metadata(path):
    first = next(events(path), (None, {}))[1]
    if first.get("type") != "session_meta":
        return None
    payload = first.get("payload", {})
    if not payload.get("id") or not payload.get("timestamp"):
        return None
    source = payload.get("source", {})
    spawn = source.get("subagent", {}).get("thread_spawn", {}) if isinstance(source, dict) else {}
    return {
        "thread_id": payload["id"],
        "parent_thread_id": payload.get("forked_from_id") or spawn.get("parent_thread_id"),
        "created_at": payload["timestamp"],
        "agent_path": spawn.get("agent_path"),
        "path": path,
    }


def read_session(metadata, snapshot_at):
    created_second = int(parse_timestamp(metadata["created_at"]).timestamp())
    previous = zero_usage()
    baseline = zero_usage()
    total = zero_usage()
    bands = {band: zero_usage() for band in (*RATES, "unknown")}
    requests = []
    issues = []
    active = False
    started_at = None
    model = None
    service_tiers = set()
    last_count_timestamp = None

    for number, item in events(metadata["path"]):
        if item.get("timestamp") and parse_timestamp(item["timestamp"]) > snapshot_at:
            continue
        payload = item.get("payload", {})
        kind = payload.get("type")
        if item.get("type") == "turn_context":
            model = payload.get("model", model)
            if active and payload.get("service_tier"):
                service_tiers.add(payload["service_tier"])
        if item.get("type") != "event_msg":
            continue
        if kind == "task_started" and not active:
            start = payload.get("started_at")
            if isinstance(start, (int, float)) and start >= created_second:
                active = True
                started_at = start
                baseline = previous.copy()
        if kind != "token_count":
            continue
        info = payload.get("info") or {}
        if not info.get("total_token_usage"):
            continue
        current = normalized_usage(info["total_token_usage"])
        if not active:
            previous = current
            continue
        if current == previous:
            continue
        delta = {key: current[key] - previous[key] for key in FIELDS}
        if any(value < 0 for value in delta.values()):
            raise ValueError(f"Token counter decreased in {metadata['path'].name}, line {number}")
        previous = current
        add_usage(total, delta)
        last = normalized_usage(info.get("last_token_usage") or {})
        if all(delta[key] == last[key] for key in FIELDS):
            band = "short" if last["input_tokens"] <= CONTEXT_THRESHOLD else "long"
        elif delta["input_tokens"] <= CONTEXT_THRESHOLD:
            band = "short"
            issues.append(f"Line {number}: grouped usage; all input fits the short-context band")
        else:
            band = "unknown"
            issues.append(f"Line {number}: request context band cannot be established")
        if delta["cached_input_tokens"] > delta["input_tokens"]:
            raise ValueError(f"Cached input exceeds input in {metadata['path'].name}, line {number}")
        add_usage(bands[band], delta)
        requests.append({"model": model, "context_band": band, "usage": delta})
        last_count_timestamp = item.get("timestamp", last_count_timestamp)

    if not active:
        issues.append("No owner task_started boundary found; no usage attributed")
    return {
        "thread_id": metadata["thread_id"],
        "parent_thread_id": metadata["parent_thread_id"],
        "agent_path": metadata["agent_path"],
        "source_file": metadata["path"].name,
        "created_at": metadata["created_at"],
        "started_at": started_at,
        "last_token_count_at": last_count_timestamp,
        "inherited_baseline": baseline,
        "totals": total,
        "context_bands": bands,
        "requests": requests,
        "observed_service_tiers": sorted(service_tiers),
        "issues": issues,
    }


def collect_report(root_thread, sessions_dir, snapshot_at=None):
    snapshot_at = snapshot_at or datetime.now(timezone.utc)
    metadata = {}
    for path in sorted(Path(sessions_dir).rglob("*.jsonl")):
        row = owner_metadata(path)
        if row and parse_timestamp(row["created_at"]) <= snapshot_at:
            if row["thread_id"] in metadata:
                raise ValueError(f"Multiple log files for thread {row['thread_id']}")
            metadata[row["thread_id"]] = row
    if root_thread not in metadata:
        raise ValueError("Requested root thread not found in the sessions directory")
    selected = {root_thread}
    while True:
        descendants = {
            thread for thread, row in metadata.items()
            if row["parent_thread_id"] in selected
        }
        expanded = selected | descendants
        if expanded == selected:
            break
        selected = expanded

    sessions = [read_session(metadata[thread], snapshot_at) for thread in sorted(selected)]
    root = next(row for row in sessions if row["thread_id"] == root_thread)
    totals = zero_usage()
    bands = {band: zero_usage() for band in (*RATES, "unknown")}
    estimates = {"standard": 0.0, "fast": 0.0}
    price_complete = True
    request_count = 0
    models = set()
    for session in sessions:
        add_usage(totals, session["totals"])
        for band in bands:
            add_usage(bands[band], session["context_bands"][band])
        request_count += len(session["requests"])
        for request in session["requests"]:
            model, band, usage = request["model"], request["context_band"], request["usage"]
            models.add(model or "unknown")
            if model != "gpt-6.1-sol" or band not in RATES:
                price_complete = False
                continue
            for mode, (input_rate, cached_rate, output_rate) in RATES[band].items():
                estimates[mode] += (
                    (usage["input_tokens"] - usage["cached_input_tokens"]) * input_rate
                    + usage["cached_input_tokens"] * cached_rate
                    + usage["output_tokens"] * output_rate
                ) / 1000000
        if session["started_at"] is None:
            price_complete = False
        del session["requests"]

    return {
        "schema_version": 1,
        "root_thread": root_thread,
        "snapshot_at": snapshot_at.isoformat(),
        "started_at": datetime.fromtimestamp(root["started_at"], timezone.utc).isoformat()
        if root["started_at"] is not None else None,
        "elapsed_seconds": round(snapshot_at.timestamp() - root["started_at"], 3)
        if root["started_at"] is not None else None,
        "totals": totals,
        "context_bands": bands,
        "request_count": request_count,
        "models": sorted(models),
        "api_equivalent_usd": {mode: round(value, 9) for mode, value in estimates.items()},
        "api_estimate_covers_all_attributed_usage": price_complete,
        "pricing_source": PRICING_URL,
        "actual_billed_cost_usd": None,
        "sessions": sessions,
        "limitations": [
            "Snapshot of locally recorded root and fork/spawn descendant usage; later requests are excluded.",
            "Inherited child counter prefixes are subtracted and repeated cumulative counters ignored.",
            "Reasoning output is reported separately but is already included in output tokens.",
            "Standard and Fast API equivalents are estimates; actual service tier and subscription billing are unknown.",
            "Cache-write charges, tool fees, residency uplifts and taxes are excluded.",
            "Unrecorded server requests and harness-only review sessions are outside the measured collaboration graph.",
        ],
    }


def render_markdown(report):
    totals = report["totals"]
    elapsed = report["elapsed_seconds"]
    duration = f"{elapsed / 60:.2f} minutes ({elapsed:,.3f} seconds)" if elapsed is not None else "unavailable"
    coverage = "all attributed usage" if report["api_estimate_covers_all_attributed_usage"] else "only the priced subset"
    lines = [
        "# Usage snapshot", "",
        f"Measured at {report['snapshot_at']} from root `{report['root_thread']}` and its recorded descendants.",
        f"Elapsed time since the root task began: {duration}.", "",
        f"{totals['total_tokens']:,} tokens: {totals['input_tokens']:,} input "
        f"({totals['cached_input_tokens']:,} cached), {totals['output_tokens']:,} output. "
        f"The output includes {totals['reasoning_output_tokens']:,} reasoning tokens; these are not counted twice.", "",
        f"Recorded inference increments: {report['request_count']:,}; sessions: {len(report['sessions'])}.", "",
        "| Session | Input | Cached input | Output | Total |", "| --- | ---: | ---: | ---: | ---: |",
    ]
    for session in report["sessions"]:
        usage = session["totals"]
        label = session["agent_path"] or ("/root" if session["thread_id"] == report["root_thread"] else session["thread_id"])
        lines.append(f"| `{label}` | {usage['input_tokens']:,} | {usage['cached_input_tokens']:,} | "
                     f"{usage['output_tokens']:,} | {usage['total_tokens']:,} |")
    prices = report["api_equivalent_usd"]
    lines.extend([
        "", f"Token-only API-equivalent estimates covering {coverage}: "
        f"**${prices['standard']:.6f} Standard** or **${prices['fast']:.6f} Fast**. "
        "Actual billed cost is unavailable. Context bands are applied per inference increment.", "",
        "[Official pricing](https://developers.openai.com/api/docs/pricing); "
        "[rates and accounting assumptions](pricing.md).", "",
        "Refresh this snapshot:", "", "```bash",
        f"python3 scripts/usage_report.py --root-thread {report['root_thread']}", "```", "",
    ])
    lines.extend(f"- {item}" for item in report["limitations"])
    for session in report["sessions"]:
        lines.extend(f"- `{session['thread_id']}`: {issue}" for issue in session["issues"])
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-thread", required=True)
    parser.add_argument("--sessions-dir", type=Path, default=Path.home() / ".codex" / "sessions")
    parser.add_argument("--output-json", type=Path, default=Path("docs/usage.json"))
    parser.add_argument("--output-markdown", type=Path, default=Path("docs/usage.md"))
    args = parser.parse_args()
    try:
        report = collect_report(args.root_thread, args.sessions_dir)
    except (OSError, ValueError) as error:
        parser.exit(1, f"Unable to measure usage: {error}\n")
    for path in (args.output_json, args.output_markdown):
        path.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    args.output_markdown.write_text(render_markdown(report), encoding="utf-8")
    print(f"Recorded {report['totals']['total_tokens']:,} tokens from {len(report['sessions'])} sessions.")


if __name__ == "__main__":
    main()
