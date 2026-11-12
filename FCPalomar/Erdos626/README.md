# Erdős Problem 626: Erdős's upper bound g_k(n) <= 2 log n / log(k−2) + 1

For k >= 4, g_k(n) <= 2 log n / log(k−2) + 1 for every n, where g_k(n) is the largest m such that some k-chromatic graph on n vertices has no cycle of length <= m. This is Theorem 1 of Erdős (1962).

- Formal Conjectures statement: `Erdos626.erdos_626.variants.erdos_upper` in [`FormalConjectures/ErdosProblems/626.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/626.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: P. Erdős, On circuits and subgraphs of chromatic graphs, Mathematika 9 (1962), 170–175, Theorem 1. (The upstream docstring and erdosproblems.com cite Erdős 1959, which has only the existence direction.)
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
