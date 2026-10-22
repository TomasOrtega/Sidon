import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "usage_report.py"
SPEC = importlib.util.spec_from_file_location("usage_report", SCRIPT)
usage_report = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = usage_report
SPEC.loader.exec_module(usage_report)


def event(kind, **payload):
    return {"type": kind, "payload": payload}


def usage(input_tokens, cached_input_tokens, output_tokens, reasoning=0):
    return {
        "input_tokens": input_tokens,
        "cached_input_tokens": cached_input_tokens,
        "output_tokens": output_tokens,
        "reasoning_output_tokens": reasoning,
        "cache_write_input_tokens": 0,
        "total_tokens": input_tokens + output_tokens,
    }


def count(total, last):
    return event("event_msg", type="token_count", info={
        "total_token_usage": total, "last_token_usage": last,
    })


def metadata(thread, timestamp, parent=None):
    payload = {"id": thread, "timestamp": timestamp}
    if parent:
        payload["forked_from_id"] = parent
        payload["source"] = {"subagent": {"thread_spawn": {
            "parent_thread_id": parent, "agent_path": f"/root/{thread}",
        }}}
    return event("session_meta", **payload)


class UsageReportTest(unittest.TestCase):
    def write_log(self, directory, name, events):
        path = directory / f"{name}.jsonl"
        path.write_text("\n".join(json.dumps(row) for row in events) + "\n")
        return path

    def test_inherited_prefix_is_subtracted_and_duplicate_counters_ignored(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            root_prefix = [
                metadata("root", "2026-10-22T10:00:00Z"),
                event("event_msg", type="task_started", started_at=1792663200),
                event("turn_context", model="gpt-6.1-sol"),
                count(usage(1000, 200, 50, 10), usage(1000, 200, 50, 10)),
            ]
            self.write_log(directory, "root", root_prefix + [root_prefix[-1]])
            child_count = count(usage(1300, 300, 70, 15), usage(300, 100, 20, 5))
            self.write_log(directory, "child", [
                metadata("child", "2026-10-22T10:01:00.900Z", "root"),
                *root_prefix,
                event("event_msg", type="task_started", started_at=1792663260),
                event("turn_context", model="gpt-6.1-sol"),
                child_count, child_count,
                event("response_item", text="PRIVATE_TRANSCRIPT_SENTINEL"),
            ])
            self.write_log(directory, "other", [
                metadata("other", "2026-10-22T10:00:00Z"),
                event("event_msg", type="task_started", started_at=1792663200),
                count(usage(99999, 0, 99999), usage(99999, 0, 99999)),
            ])
            report = usage_report.collect_report(
                "root", directory,
                snapshot_at=datetime(2026, 10, 22, 10, 2, tzinfo=timezone.utc),
            )
            self.assertEqual(report["totals"], usage(1300, 300, 70, 15))
            self.assertEqual(report["uncached_input_tokens"], 1000)
            self.assertEqual(report["uncached_input_plus_output_tokens"], 1070)
            self.assertIn("1,070 uncached-input-plus-output tokens", usage_report.render_markdown(report))
            self.assertEqual(report["elapsed_seconds"], 120)
            self.assertEqual(len(report["sessions"]), 2)
            self.assertEqual(report["request_count"], 2)
            child = next(row for row in report["sessions"] if row["thread_id"] == "child")
            self.assertEqual(child["inherited_baseline"], usage(1000, 200, 50, 10))
            self.assertEqual(child["totals"], usage(300, 100, 20, 5))
            self.assertNotIn("PRIVATE_TRANSCRIPT_SENTINEL", json.dumps(report))
            self.assertAlmostEqual(report["api_equivalent_usd"]["standard"], 0.00273)

    def test_context_threshold_applies_per_request_and_reasoning_is_not_added_twice(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            first = usage(272000, 100000, 100, 40)
            second = usage(272001, 100000, 200, 90)
            total = {key: first[key] + second[key] for key in first}
            self.write_log(directory, "root", [
                metadata("root", "2026-10-22T10:00:00Z"),
                event("event_msg", type="task_started", started_at=1792663200),
                event("turn_context", model="gpt-6.1-sol"),
                count(first, first), count(total, second),
            ])
            report = usage_report.collect_report(
                "root", directory,
                snapshot_at=datetime(2026, 10, 22, 10, 2, tzinfo=timezone.utc),
            )
            self.assertEqual(report["context_bands"]["short"]["input_tokens"], 272000)
            self.assertEqual(report["context_bands"]["long"]["input_tokens"], 272001)
            self.assertEqual(report["totals"]["total_tokens"], 544301)
            self.assertEqual(report["totals"]["reasoning_output_tokens"], 130)
            self.assertAlmostEqual(report["api_equivalent_usd"]["standard"], 1.066004)
            self.assertAlmostEqual(report["api_equivalent_usd"]["fast"], 2.132008)

    def test_snapshot_does_not_include_usage_appended_after_its_cutoff(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            first = count(usage(1000, 0, 50), usage(1000, 0, 50))
            first["timestamp"] = "2026-10-22T10:01:00Z"
            future = count(usage(2000, 0, 100), usage(1000, 0, 50))
            future["timestamp"] = "2026-10-22T10:03:00Z"
            self.write_log(directory, "root", [
                metadata("root", "2026-10-22T10:00:00Z"),
                event("event_msg", type="task_started", started_at=1792663200),
                event("turn_context", model="gpt-6.1-sol"), first, future,
            ])
            report = usage_report.collect_report(
                "root", directory,
                snapshot_at=datetime(2026, 10, 22, 10, 2, tzinfo=timezone.utc),
            )
            self.assertEqual(report["totals"], usage(1000, 0, 50))


if __name__ == "__main__":
    unittest.main()
