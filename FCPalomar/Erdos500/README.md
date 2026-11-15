# Erdős Problem 500: Turán's lower bound ex₃(n, K₄³) >= (5/9 − o(1)) C(n,3)

For every ε > 0 and all large n, (5/9 − ε) C(n,3) <= ex₃(n, K₄³), the largest number of triples on n vertices with no 4-set covering all four of its triples. This is Turán's 1941 construction, as stated on erdosproblems.com/500.

- Formal Conjectures statement: `Erdos500.erdos_500.variants.lower_bound` in [`FormalConjectures/ErdosProblems/500.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/500.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: P. Turán's construction (1941), as recorded on erdosproblems.com/500 and in Erdős's problem papers.
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
