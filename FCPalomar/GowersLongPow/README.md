# Gowers–Long: F(n) = n^α implies F(m) >= m^β eventually for β < α

Let F(n) be the maximal length of a 2-increasing sequence of triples in {1..n}^3. If F(n) = n^α for some n > 1, then F(m) >= m^β for every β < α and all large m (Gowers–Long, remark after Lemma 1.7).

- Formal Conjectures statement: `Arxiv.«1609.08688».maximalLength_pow_eventually` in [`FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: W. T. Gowers and J. Long, The length of an s-increasing sequence of r-tuples, Combin. Probab. Comput. 30 (2021), 686–721 (arXiv:1609.08688).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
