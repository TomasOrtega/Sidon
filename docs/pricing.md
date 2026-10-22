# Pricing and accounting basis

Checked on 2026-10-22 using OpenAI Docs: searched for the exact model
`GPT-6.1` / `gpt-6.1-sol`, then fetched the official pricing page.

The published API model is `gpt-6.1-sol`. No separate price for an identifier
spelled only `GPT-6.1` was established. The following are public API rates,
in US dollars per million tokens, not a statement of the user's Codex bill.
[Official OpenAI API pricing](https://developers.openai.com/api/docs/pricing)

| Mode | Context | Input | Cached input | Output | 30-minute cache write | 12-hour cache write |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Standard | At most 272,000 input tokens | 2.00 | 0.10 | 10.00 | 2.50 | 5.00 |
| Standard | Above 272,000 input tokens | 4.00 | 0.20 | 15.00 | 5.00 | 10.00 |
| Fast | At most 272,000 input tokens | 4.00 | 0.20 | 20.00 | 5.00 | 10.00 |
| Fast | Above 272,000 input tokens | 8.00 | 0.40 | 30.00 | 10.00 | 20.00 |

The official page says Priority processing was renamed Fast mode on
2026-07-30. The runtime's model metadata offers a `priority` service tier;
equating that internal setting with a particular billed API mode is an
accounting assumption, not billing evidence. Report Standard and Fast
equivalent estimates separately when that mapping is unavailable.
[Official OpenAI API pricing](https://developers.openai.com/api/docs/pricing)

For each request, let `I` be total input tokens, `C` the cached subset of
input tokens, and `O` output tokens. With the relevant row's rates,

```text
API-equivalent estimate = ((I - C) * input_rate
                         + C * cached_input_rate
                         + O * output_rate) / 1,000,000
```

Sum this over requests and agents; context bands apply per request. Add
cache-write charges only if actual write counts and their billing semantics
are known. Reasoning-output tokens must not be added a second time if the
usage record already includes them in `O`. Tool fees, residency surcharges,
tax, and subscription charges are outside this token-only estimate.

An aggregate total without the input/output/cache split does not determine
a price. A root-agent counter also does not establish total team usage:
subagent requests may have separate counters, repeated shared input, and
their own context bands. Never call a partial count the complete goal cost.

Codex plan allowances and purchased-credit usage depend on model, context,
reasoning, tools, retrieval, caching, and speed mode. An API-equivalent
estimate therefore cannot establish actual subscription or credit charges.
[Official OpenAI ChatGPT Work pricing](https://learn.chatgpt.com/docs/pricing#what-are-the-usage-limits-for-my-plan)

Record unavailable measurements as unavailable. Use observed timestamps for
elapsed wall time, explain counter scope, and preserve the raw usage records
or their source paths when available. An estimate of final generated text
length is not a substitute for inference token usage.
