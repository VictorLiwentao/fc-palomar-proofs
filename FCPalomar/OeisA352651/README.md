# OEIS A352651, N ≤ −1: integrality of Bala's u_N

For an integer N ≠ 0, 1, Peter Bala (OEIS A352651, 2022) defines u_N(n) = C(Nn,2n) C(Nn/2,2n) C(2n,n)² / C(Nn/2,n)² and conjectures that u_N is integral. The package proves the cases N ≤ −1, which R. Blanco Gómez lists as open: for every N ≤ −1 and n ≥ 0, u_N(n) is an integer, and the denominator C(Nn/2,n) is never zero. The binomials, whose top argument is a negative integer or half-integer here, are read as falling factorials over k!, as Bala's formulas A275652 = (5/3)u₋₁ and A275654 = (7/5)u₋₃ require. With N = −M and a = Mn the quantity is ∏_{j<n}(a+1+2j)·∏_{j<n}(a+2n+2j)/n!², that is 4ⁿ·C((a+1)/2+n−1, n)·C(a/2+2n−1, n), and integrality follows from an elementary divisibility. Bala's supercongruences for these N are not treated here.

- Statement: `OeisA352651.denominator_ne_zero`, `OeisA352651.u_integral`, written for this package from the source.
- Mathematics: conjecture by Peter Bala (OEIS A352651, 2022); proof by Wentao Li, developed with AI assistance (Claude Code).
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
