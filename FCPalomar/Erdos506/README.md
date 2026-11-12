# Erdős Problem 506: Segre's eight points determining fewer than C(7,2) circles

There are 8 points in the plane, not all on a line or a circle, that determine fewer than C(7,2) = 21 circles. The witness is two concentric aligned squares, which determine 18 circles (Segre's remark, after Elliott 1967).

- Formal Conjectures statement: `Erdos506.erdos_506.variants.segre_n_eq_eight` in [`FormalConjectures/ErdosProblems/506.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/506.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: Segre's remark, as reported on erdosproblems.com/506 after P. D. T. A. Elliott, On the number of circles determined by n points, Acta Math. Acad. Sci. Hungar. 18 (1967), 181–188.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
