# OEIS A053175: Hankel determinants of the Catalan–Larcombe–French numbers

For every n, 2^(n(n+3)) divides the (n+1)×(n+1) Hankel determinant det[a(i+j)] of the Catalan–Larcombe–French numbers a, and the quotient is a positive odd integer. This is Zhi-Wei Sun's conjecture (2013), proved by Zhu and Sun (2018).

- Formal Conjectures statement: `OeisA53175.conjecture` in [`FormalConjectures/OEIS/53175.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/OEIS/53175.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: conjecture by Zhi-Wei Sun (OEIS A053175, Aug 14 2013); proved by B.-X. Zhu and Z.-W. Sun, Int. J. Number Theory 14 (2018), Theorem 1.2 (arXiv:1609.06810).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
