# Erdős Problem 934: h_1(d) = d + 1 for d ≠ 2

For every d ≠ 2, the least m such that every graph with at least m edges and maximum degree at most d has two vertex-disjoint edges is d + 1. The value is folklore; Cambie et al. (2022) call it easy.

- Formal Conjectures statement: `Erdos934.erdos_934.variants.h_one` in [`FormalConjectures/ErdosProblems/934.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/934.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: folklore, stated as easy on erdosproblems.com/934 and in Cambie, Cames van Batenburg, de Joannis de Verclos and Kang, SIAM J. Discrete Math. 36 (2022) (arXiv:2103.11898).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
