# AI-development correspondence and provenance

This folder accompanies the "Background and use of generative artificial
intelligence" section of `paper/prop51.tex`. It records, as transparently as is
practical, how generative-AI systems were used to produce the proofs (Chen–Larson
Proposition 5.1 and the corrected Proposition 5.2) and their formalizations.

## Provenance

| role | provider / model | interface | dates (2026) |
|---|---|---|---|
| Central investigation & drafting | OpenAI / ChatGPT 5.5 Pro | ChatGPT web | 10 Jun – mid Jun |
| Adversarial mathematical audits | OpenAI / ChatGPT 5.5 Pro | ChatGPT web | 11–15 Jun |
| Strategic guidance | Anthropic / Claude Fable 5 | Claude web | 10–12 Jun |
| First formalization push | Anthropic / Claude Fable 5 | Claude Code | 11–12 Jun |
| Long-horizon completion drive | OpenAI / Codex CLI | Codex CLI | 15–20 Jun |
| "Is the worker stuck?" / correction reviews | OpenAI / ChatGPT 5.5 Pro; Anthropic / Claude Opus 4.8 | ChatGPT web; Claude Code | 19–20 Jun |
| Corrected Prop 5.2: derivation, audit of the published paper, formalization plan | OpenAI / ChatGPT 5.5 Pro | ChatGPT web | 23 Jun |
| Corrected Prop 5.2: autonomous formalization | OpenAI / Codex CLI | Codex CLI | 23–24 Jun |
| Prop 5.2 vetting and repository integration | Anthropic / Claude Opus 4.8 | Claude Code | 24 Jun |

The human role was orchestration, not mathematics: choosing the problem,
designing and relaying prompts, maintaining the harness, and deciding from
high-level signals when to seek an outside review. See the interaction cards in
the paper for the per-step prompts and the public conversation links.

Stable API model identifiers were not all exposed by the interfaces used; the
public model names above are the designations under which the systems were
accessed. The full commit-level history of the development is preserved in this
repository's Git log.

## What is archived here

- `claude-code-sessions.md` — curated, redacted session record of the two Claude
  Code CLI sessions: the first formalization push (Claude Fable 5, layers A–B and
  the start of C) and the "is the worker stuck?" review and paper work (Claude
  Opus 4.8). Human instructions verbatim; AI responses summarized.
- `codex-sessions.md` — curated, redacted session records of the OpenAI Codex CLI
  drives: the Proposition 5.1 completion drive (the analytic tail, sign lock,
  positive part, the stuck point and its repair, and the publication pass,
  including the verbatim persistent `/goal` prompt), and the separate, fully
  autonomous corrected-Proposition-5.2 completion drive (handed a research note
  and Lean plan, finished with no further human turns). Human instructions
  verbatim; AI work summarized.
- `answer_by_gptpro.md`, `questions_for_gptpro.md` — the relayed-question
  exchange that diagnosed the false split-product target and prescribed the
  direct-saddle fix (paper Cards 6–7). This is one of the decisive AI outputs,
  retained verbatim.

The two `*-sessions.md` files are curated, redacted session records: every
on-topic human instruction from the selected sessions is reproduced, with the AI
side summarized rather than quoted (so they are records, not raw outputs).
Redaction was limited to local file paths, the author's email, and a few
incidental references to unrelated projects; the public conversation links are
retained.

## What is deliberately not included

The *full, verbatim* command-line-agent transcripts are not archived. They run to
roughly 185 MB, dominated by opaque internal trace payloads and extensive
tool/build logs, and the raw streams contain incidental references to unrelated
projects on the author's machine. The curated session records above capture the
publishable, on-topic content. No credential files were ever part of this
record.

## Session metadata

| field | record |
|---|---|
| interfaces | Claude web, ChatGPT web, Claude Code (CLI), OpenAI Codex CLI |
| displayed model names | ChatGPT 5.5 Pro, Claude Fable 5, Claude Opus 4.8 |
| stable API model identifiers | not exposed by the interfaces used |
| CLI client versions | not separately recorded |
| permissions granted to CLI agents | shell, file read/write, network; Codex ran with `workspace-write` |
| context supplied per session | the repository tree and the LaTeX note (plus, later, the relayed external reviews) |
| tokens / monetary cost | not retained |
| toolchain | Lean 4.27.0; Mathlib pinned in `lake-manifest.json` |
| principal artifacts | the Lean formalization, the LaTeX paper, and the certificates in this repository |

`decisive-outputs.md` additionally collects a few verbatim AI responses from the
moments that changed the proof's direction.
