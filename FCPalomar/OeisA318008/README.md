# OEIS A318008: the parity of the compositional square root (Hanna's conjecture)

The o.g.f. A(x) of OEIS A318008 satisfies A(A(x − x²)) = x + x². The package proves that exactly one A ∈ ℚ[[x]] with A(0) = 0 does, that every coefficient a(n) is an integer, and that a(n) is odd if and only if n = 2^k − 1 or n = 2^(k+1) − 2 for some k ≥ 1, as conjectured by Paul D. Hanna (2018). It also proves the companion facts for OEIS A277292: its series is unique and odd, its coefficients are the odd-indexed a(n), and they are odd exactly at the powers of 2.

- Statement: `OeisA318008.exists_unique_solution`, `OeisA318008.parity_conjecture`, `OeisA318008.a277292_existsUnique`, `OeisA318008.a277292_odd`, `OeisA318008.a318008_odd_bisection`, `OeisA318008.a277292_parity`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/318008.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Paul D. Hanna (OEIS A318008, September 2018); an earlier proof by the same route by hilbert-clavius (OpenWitness, October 25, 2026); the proof here, by Wentao Li, was developed independently with AI assistance (Claude Code).
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
