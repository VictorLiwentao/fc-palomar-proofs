# OEIS A113052 and A113047: Fuss–Catalan numbers modulo p (Barry's conjecture, Israel 2018)

For every prime p, C(pn, n)/((p−1)n+1) modulo p is 1 when n = (p^k−1)/(p−1) and 0 otherwise. Conjectured by Paul Barry (2005); proved by Robert Israel (2018), with Kevin Ryde's proof of the p = 3 case (A113047).

- Statement: `OeisA113052.conjecture`, `OeisA113052.a113047`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/113052.lean`, which does not exist upstream yet.
- Mathematics: conjectures by Paul Barry (OEIS A113052, Oct 12 2005; A113047, Oct 11 2005); proved by Robert Israel (2018, https://oeis.org/A113052/a113052.pdf) and, for p = 3, Kevin Ryde (2021).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
