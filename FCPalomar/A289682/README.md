# OEIS A289682: Catalan numbers at 2^n − 1 and 2^n modulo 16 (Israel's conjecture)

For n >= 3, C(2^n − 1) ≡ 13 and C(2^n) ≡ 6 (mod 16). Conjectured by Robert Israel (2017); consistent with Liu–Yeh's classification of Catalan numbers modulo 2^k.

- Statement: `OeisA289682.catalan_two_pow_mod_sixteen`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/289682.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Robert Israel (OEIS A289682, Jul 09 2017); S.-C. Liu and J. C.-C. Yeh, Catalan numbers modulo 2^k, J. Integer Seq. 13 (2010), Article 10.5.4, classify C_n mod 16 and mod 64.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
