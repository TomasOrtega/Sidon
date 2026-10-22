# Usage snapshot

Measured at 2026-10-22T12:15:48.188860+00:00 from root `01a1636c-beb7-7282-9390-a9ced5631a74` and its recorded descendants.
Elapsed time since the root task began: 29.94 minutes (1,796.189 seconds).

72,484,075 tokens: 72,192,580 input (71,207,424 cached), 291,495 output. The output includes 103,292 reasoning tokens; these are not counted twice.

Recorded inference increments: 406; sessions: 4.

| Session | Input | Cached input | Output | Total |
| --- | ---: | ---: | ---: | ---: |
| `/root` | 17,790,282 | 17,532,416 | 62,040 | 17,852,322 |
| `/root/scout` | 27,335,475 | 27,014,144 | 76,026 | 27,411,501 |
| `/root/proof_core` | 15,014,308 | 14,815,360 | 74,612 | 15,088,920 |
| `/root/proof_applications` | 12,052,515 | 11,845,504 | 78,817 | 12,131,332 |

Token-only API-equivalent estimates covering all attributed usage: **$13.631318 Standard** or **$27.262636 Fast**. Actual billed cost is unavailable. Context bands are applied per inference increment.

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
