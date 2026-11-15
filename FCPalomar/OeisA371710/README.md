# OEIS A371710: Hanna's mod-3 pattern

The e.g.f. A(x) = Σ a(n)xⁿ/n! of OEIS A371710 satisfies Σ_{n≥0} (A(x)^n − x)^n/n! = 1. The package proves that exactly one A ∈ ℚ[[x]] does, that A(0) = 0 and every a(n) is an integer, and Paul D. Hanna's 2024 conjecture that a(6n + k) ≡ [2, 0, 2, 1, 2, 2](k) (mod 3) for n > 0 and k = 0, …, 5. It also proves the stronger pattern a(m) ≡ 2 for even m ≥ 2 and a(m) ≡ 1 − m for odd m ≥ 3, modulo 3.

- Statement: `OeisA371710.a371710_existsUnique`, `OeisA371710.a371710_constantCoeff`, `OeisA371710.a371710_integral`, `OeisA371710.a371710_mod_three`, `OeisA371710.a371710_mod_three_strong`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/371710.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Paul D. Hanna (OEIS A371710, April 2024); proof by Wentao Li, developed with AI assistance (Claude Code).
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
