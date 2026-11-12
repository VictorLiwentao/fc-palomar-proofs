# OEIS A389535: Hanna's formula (7), A(x)^5 ≡ A(x^5) (mod 5)

For the unique power series A with A(0) = 0, a(1) = 1 and A(x A(x)^4 + x A(x)^5) = A(x)^5, the coefficients are integers and A(x)^5 ≡ A(x^5) (mod 5). Formula (7) in OEIS A389535 is stated there as a conjecture by Paul D. Hanna.

- Statement: `OeisA389535.exists_unique_solution`, `OeisA389535.conjecture_seven`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/389535.lean`, which does not exist upstream yet.
- Mathematics: conjecture (7) by Paul D. Hanna, OEIS A389535 (2025). The congruence step is the Frobenius/Fermat identity B(x)^5 ≡ B(x^5) (mod 5) for integer series; the work is integrality, existence and uniqueness.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
