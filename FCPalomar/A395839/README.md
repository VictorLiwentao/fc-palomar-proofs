# OEIS A395839: parity and residues mod 3 of 10C(x)^2 − C(x) (Hanna's conjectures)

For the g.f. 10C(x)^2 − C(x) with C the Catalan g.f., a(n) is odd iff n = 2^k − 1, and a(3n+1) ≡ C_n, a(3n) ≡ a(3n+2) ≡ 0 (mod 3). Conjectured by Paul D. Hanna (2026).

- Statement: `OeisA395839.odd_iff`, `OeisA395839.mod_three`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/395839.lean`, which does not exist upstream yet.
- Mathematics: conjectures by Paul D. Hanna (OEIS A395839, May 17 2026). The parity clause follows from Deutsch–Sagan (2006), Theorem 2.1 (v_2(C_n) = s_2(n+1) − 1).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
