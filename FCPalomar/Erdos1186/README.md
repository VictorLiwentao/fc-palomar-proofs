# Erdős Problem 1186: bounds on the density of monochromatic progressions

For every k >= 2 the constant δ_k of Erdős Problem 1186 is positive (via van der Waerden's theorem) and at most 1/((k−1)2^k) (by the probabilistic method), as stated by Erdős (1980, p. 93).

- Formal Conjectures statement: `Erdos1186.erdos_1186.variants.van_der_waerden`, `Erdos1186.erdos_1186.variants.probabilistic` in [`FormalConjectures/ErdosProblems/1186.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/1186.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: P. Erdős, A survey of problems in combinatorial number theory, Ann. Discrete Math. 6 (1980), 89–115, p. 93: the lower bound from van der Waerden's theorem and the upper bound (7) from the probability method.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
