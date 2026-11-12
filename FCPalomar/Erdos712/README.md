# Erdős Problem 712, graph case: Turán's density limit

For k >= 2, ex_2(n, K_k)/C(n,2) -> 1 − 1/(k−1) and ex_2(n, K_k)/n^2 -> (1 − 1/(k−1))/2, for the Formal Conjectures hypergraph extremal number (Turán 1941).

- Formal Conjectures statement: `Erdos712.erdos_712.variants.graph_case`, `Erdos712.erdos_712.variants.graph_case_div_sq` in [`FormalConjectures/ErdosProblems/712.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/712.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: P. Turán, On an extremal problem in graph theory, Mat. Fiz. Lapok 48 (1941), 436–452, via Mathlib's Turán theorem.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
