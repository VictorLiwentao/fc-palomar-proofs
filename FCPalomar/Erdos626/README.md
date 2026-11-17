# Erdős Problem 626: Erdős's upper bound g_k(n) <= 2 log n / log(k−2) + 1

For k >= 4 and all sufficiently large n, g_k(n) <= 2 log n / log(k−2) + 1, where g_k(n) is the largest m such that some graph on n vertices with chromatic number k has no cycle of length <= m. This is Erdős's upper bound (Mathematika 1962, Theorem 1) in the form his printed proof gives. Erdős's g_k(n) is the largest girth, one more than the g_k(n) used here, so the formal bound is one weaker than Theorem 1 as printed. With Erdős's lower bound of order log n, it shows that g_k(n) has order log n. Whether g_k(n)/log n converges is the open Erdős Problem 626.

- Formal Conjectures statement: `Erdos626.erdos_626.variants.erdos_upper` in [`FormalConjectures/ErdosProblems/626.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/626.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: P. Erdős, On circuits and subgraphs of chromatic graphs, Mathematika 9 (1962), 170–175, Theorem 1. (The upstream docstring and erdosproblems.com cite Erdős 1959, which has only the existence direction.)
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
