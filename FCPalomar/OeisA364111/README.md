# OEIS A364111: Bala's p^(3r) supercongruences

For integers A ≥ 2 and B, C ≥ 1 let u(N) = Σ_{k=0}^{N} C(N+k−1, k)^A C(2N−2k, N−k)^B C(2k, k)^C. The package proves that u(np^r) ≡ u(np^{r−1}) (mod p^{3r}) for every prime p ≥ 5 and all n, r ≥ 1, as conjectured by Peter Bala (OEIS A364111, 2023), and the case (A, B, C) = (2, 1, 1), which is A364111 itself. The proof uses Coster's method, as Osburn and Sahu did for the generalized Domb numbers.

- Statement: `OeisA364111.u_supercongruence`, `OeisA364111.a_supercongruence`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/364111.lean`, which does not exist upstream yet.
- Mathematics: conjectures by Peter Bala (OEIS A364111, July 7 2023); proof by Wentao Li, developed with AI assistance (Claude Code), by Coster's method as used by Osburn and Sahu.
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
