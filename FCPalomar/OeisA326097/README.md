# OEIS A326097: the parity of a(k) (Hanna's conjecture)

The e.g.f. A(x) of OEIS A326097 satisfies 1 = Σ_{n≥0} ((1+x)^n − A(x))^n/n!. The package proves that this equation has exactly one solution in ℚ[[x]], that every a(k) = k! [x^k] A(x) is an integer, and that a(k) is odd if and only if k ∈ {0, 1, 3} or k ≡ 2 (mod 4). This settles Paul D. Hanna's 2019 parity conjecture in a slightly stronger form. The same holds for OEIS A385907, where (1+x)^n is replaced by 1/(1−x)^n.

- Statement: `OeisA326097.a326097_existsUnique`, `OeisA326097.a326097_parity`, `OeisA326097.a385907_existsUnique`, `OeisA326097.a385907_parity`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/326097.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Paul D. Hanna (OEIS A326097, June 6 2019); proof by Wentao Li, developed with AI assistance (Claude Code).
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
