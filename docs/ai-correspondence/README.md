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

- `claude-code-sessions.md` — curated, redacted excerpt of the two Claude Code
  CLI sessions: the first formalization push (Claude Fable 5, layers A–B and the
  start of C) and the "is the worker stuck?" review and paper work (Claude Opus
  4.8). Human prompts verbatim; AI responses summarized.
- `codex-sessions.md` — curated, redacted excerpt of the OpenAI Codex CLI
  completion drive (the analytic tail, sign lock, positive part, the stuck point
  and its repair, and the publication pass), including the verbatim persistent
  `/goal` prompt. Human prompts verbatim; AI work summarized.
- `answer_by_gptpro.md`, `questions_for_gptpro.md` — the relayed-question
  exchange that diagnosed the false split-product target and prescribed the
  direct-saddle fix (paper Cards 6–7).

The two `*-sessions.md` files are the curated raw outputs recommended for
Level-A/C work: every genuine human turn is reproduced, with the AI side
summarized. Redaction was limited to local file paths, the author's email, and a
few incidental references to unrelated projects; the public conversation links
are retained.

## What is deliberately not included

The *full, verbatim* command-line-agent transcripts are not archived. They run to
roughly 185 MB, dominated by build logs and encrypted model-reasoning blobs, and
the raw streams contain incidental references to unrelated projects on the
author's machine. The curated `*-sessions.md` files above capture the
publishable, on-topic content. No credential files were ever part of this
record.
