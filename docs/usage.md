# Usage snapshot

Measured at 2026-10-22T13:59:48.521142+00:00 from root `01a1636c-beb7-7282-9390-a9ced5631a74` and its recorded descendants.
Elapsed time since the root task began: 133.94 minutes (8,036.521 seconds).

382,746,253 tokens: 381,603,847 input (377,360,640 cached), 1,142,406 output. The output includes 405,992 reasoning tokens; these are not counted twice.

5,385,613 uncached-input-plus-output tokens (4,243,207 uncached input + 1,142,406 output). This excludes cached input reprocessed across requests and matches the goal counter definition; the larger total above includes those cached tokens for API pricing.

Recorded inference increments: 2,096; sessions: 4.

| Session | Input | Cached input | Output | Total |
| --- | ---: | ---: | ---: | ---: |
| `/root` | 81,127,547 | 80,210,432 | 246,222 | 81,373,769 |
| `/root/scout` | 102,509,031 | 101,371,776 | 302,403 | 102,811,434 |
| `/root/proof_core` | 92,965,331 | 91,714,944 | 299,702 | 93,265,033 |
| `/root/proof_applications` | 105,001,938 | 104,063,488 | 294,079 | 105,296,017 |

Token-only API-equivalent estimates covering all attributed usage: **$72.499789 Standard** or **$144.999578 Fast**. Actual billed cost is unavailable. Context bands are applied per inference increment.

[Official pricing](https://developers.openai.com/api/docs/pricing); [rates and accounting assumptions](pricing.md).

Refresh this snapshot:

```bash
python3 scripts/usage_report.py --root-thread 01a1636c-beb7-7282-9390-a9ced5631a74
```

- Snapshot of locally recorded root and fork/spawn descendant usage; later requests are excluded.
- Inherited child counter prefixes are subtracted and repeated cumulative counters ignored.
- Reasoning output is reported separately but is already included in output tokens.
- Standard and Fast API equivalents are estimates; actual service tier and subscription billing are unknown.
- Cache-write charges, tool fees, residency uplifts and taxes are excluded.
- Unrecorded server requests and harness-only review sessions are outside the measured collaboration graph.
