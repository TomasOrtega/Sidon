# Usage snapshot

Measured at 2026-10-22T13:03:01.130903+00:00 from root `01a1636c-beb7-7282-9390-a9ced5631a74` and its recorded descendants.
Elapsed time since the root task began: 77.15 minutes (4,629.131 seconds).

202,537,646 tokens: 201,820,990 input (199,556,096 cached), 716,656 output. The output includes 251,188 reasoning tokens; these are not counted twice.

Recorded inference increments: 1,144; sessions: 4.

| Session | Input | Cached input | Output | Total |
| --- | ---: | ---: | ---: | ---: |
| `/root` | 47,808,881 | 47,220,864 | 162,998 | 47,971,879 |
| `/root/scout` | 60,840,086 | 60,186,752 | 183,797 | 61,023,883 |
| `/root/proof_core` | 46,497,879 | 45,961,472 | 183,858 | 46,681,737 |
| `/root/proof_applications` | 46,674,144 | 46,187,008 | 186,003 | 46,860,147 |

Token-only API-equivalent estimates covering all attributed usage: **$37.878712 Standard** or **$75.757424 Fast**. Actual billed cost is unavailable. Context bands are applied per inference increment.

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
