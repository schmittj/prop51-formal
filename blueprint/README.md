# Blueprint (planned)

This directory is a placeholder for a future
[leanblueprint](https://github.com/PatrickMassot/leanblueprint): a
dependency-graphed, web-rendered version of `paper/prop51.tex` with
`\lean{}`/`\leanok` annotations tying every lemma to its Lean counterpart.

The proof is **complete** (the formalization is finished and `sorry`-free); the
blueprint web build has simply not been produced yet. Until it is, the
authoritative paper-to-Lean correspondence is:

- the "Paper-to-Lean correspondence" appendix of `paper/prop51.tex`, and
- [`docs/FORMALIZATION.md`](../docs/FORMALIZATION.md), the layer-by-layer guide.

To bootstrap the web blueprint later: `pip install leanblueprint && leanblueprint new`.
