# AI-development correspondence and provenance

This folder accompanies the "Background and use of generative artificial
intelligence" section of `paper/prop51.tex`. It records, as transparently as is
practical, how generative-AI systems were used to produce the proof and its
formalization.

## Provenance

| role | provider / model | interface | dates (2026) |
|---|---|---|---|
| Central investigation & drafting | OpenAI / ChatGPT 5.5 Pro | ChatGPT web | 10 Jun – mid Jun |
| Adversarial mathematical audits | OpenAI / ChatGPT 5.5 Pro | ChatGPT web | 11–15 Jun |
| Strategic guidance | Anthropic / Claude Fable 5 | Claude web | 10–12 Jun |
| First formalization push | Anthropic / Claude Fable 5 | Claude Code | 11–12 Jun |
| Long-horizon completion drive | OpenAI / Codex CLI | Codex CLI | 15–20 Jun |
| "Is the worker stuck?" / correction reviews | OpenAI / ChatGPT 5.5 Pro; Anthropic / Claude Opus 4.8 | ChatGPT web; Claude Code | 19–20 Jun |

The human role was orchestration, not mathematics: choosing the problem,
designing and relaying prompts, maintaining the harness, and deciding from
high-level signals when to seek an outside review. See the interaction cards in
the paper for the per-step prompts and the public conversation links.

Stable API model identifiers were not all exposed by the interfaces used; the
public model names above are the designations under which the systems were
accessed. The full commit-level history of the development is preserved in this
repository's Git log.

## What is archived here

- `answer_by_gptpro.md`, `questions_for_gptpro.md` — the relayed-question
  exchange that diagnosed the false split-product target and prescribed the
  direct-saddle fix (paper Cards 6–7).

## What is deliberately not included

The raw command-line-agent transcripts (Claude Code and Codex CLI) are **not**
archived verbatim. They run to hundreds of megabytes, are dominated by build
logs and encrypted reasoning blobs, and contain incidental references to
unrelated projects on the author's machine. The publishable, on-topic content —
the human prompts and the substantive model conclusions — is captured by the
interaction cards and the public conversation links in the paper. No credential
files were ever part of this record.
