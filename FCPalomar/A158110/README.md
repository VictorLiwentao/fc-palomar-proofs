# OEIS A158110: exp(Σ q^(n^m) x^n/n) has integer coefficients (Hanna's conjecture, Fried 2025)

For all natural numbers q and m, exp(Σ_{n>=1} q^(n^m) x^n/n) is a power series with integer coefficients. Conjectured by Paul D. Hanna (2009) and proved by Sela Fried (2025).

- Statement: `OeisA158110.conjecture`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/158110.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Paul D. Hanna (OEIS A158110, 2009); proved by Sela Fried, Proof of a conjecture stated in A158110 (2025), https://oeis.org/A158110/a158110.pdf, and arXiv:2607.24832.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
