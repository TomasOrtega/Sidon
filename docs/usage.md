# Usage snapshot

Measured at 2026-10-22T15:03:42.121272+00:00 from root `01a1636c-beb7-7282-9390-a9ced5631a74` and its recorded descendants.
Elapsed time since the root task began: 197.84 minutes (11,870.121 seconds).

543,383,238 tokens: 541,747,108 input (535,830,912 cached), 1,636,130 output. The output includes 592,448 reasoning tokens; these are not counted twice.

7,552,326 uncached-input-plus-output tokens (5,916,196 uncached input + 1,636,130 output). This excludes cached input reprocessed across requests and matches the goal counter definition; the larger total above includes those cached tokens for API pricing.

Recorded inference increments: 2,998; sessions: 4.

| Session | Input | Cached input | Output | Total |
| --- | ---: | ---: | ---: | ---: |
| `/root` | 119,734,909 | 118,523,904 | 353,968 | 120,088,877 |
| `/root/scout` | 142,916,531 | 141,364,608 | 426,569 | 143,343,100 |
| `/root/proof_core` | 133,490,169 | 131,592,576 | 433,413 | 133,923,582 |
| `/root/proof_applications` | 145,605,499 | 144,349,824 | 422,180 | 146,027,679 |

Token-only API-equivalent estimates covering all attributed usage: **$101.565000 Standard** or **$203.130000 Fast**. Actual billed cost is unavailable. Context bands are applied per inference increment.

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
