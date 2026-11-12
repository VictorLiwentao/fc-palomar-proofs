# Gowers–Long: F(n) ≥ n^{3/2} when n is a perfect square

Let F(n) be the maximal length of a 2-increasing sequence of triples in {1..n}^3, where a triple is 2-less than another if it is smaller in at least two coordinates. Gowers and Long show that F(n) ≥ n^{3/2} when n is a perfect square (arXiv:1609.08688, Proposition 1.4). The package proves (√n)^3 ≤ F(n) for every perfect square n.

- Formal Conjectures statement: `Arxiv.«1609.08688».maximalLength_ge_of_isSquare` in [`FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: W. T. Gowers and J. Long, arXiv:1609.08688, Proposition 1.4; the bound F(n) <= n^2 uses the Formal Conjectures pigeonhole lemma (DeepMind PR 4207, ChakshuGupta13); an earlier Lean proof is in weiyangzen/awesome_theorems.
- Lean proof: Wentao Li, with AI assistance (OpenAI Codex, GPT-6.1 Sol; ported to Lean 4.35 with Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
