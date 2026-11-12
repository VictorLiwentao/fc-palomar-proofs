# The burning number of a path

For n >= 1 the burning number of the path on n vertices is exactly ceil(sqrt n), so the bound in the burning number conjecture cannot be improved (Bonato–Janssen–Roshanbin 2016, Theorem 10).

- Formal Conjectures statement: `BurningNumberConjecture.burning_number_conjecture.variants.path` in [`FormalConjectures/Paper/BurningNumberConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Paper/BurningNumberConjecture.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: A. Bonato, J. Janssen and E. Roshanbin, How to burn a graph, Internet Math. 12 (2016), 85–100, Theorem 10 (arXiv:1507.06524).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
