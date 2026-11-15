# OEIS A333472: Bala's p^(2k) supercongruences for a(r,s;n), every r ≥ 1 and s ∈ ℤ

Let c(x) be the Catalan series and F(x) = c(x/(1+x)). For r ≥ 1 and s ∈ ℤ let a(r,s;n) = [x^(rn)] F(x)^(sn), with F^m for m < 0 the power of the inverse series. The package proves a(r,s;np^k) ≡ a(r,s;np^(k−1)) (mod p^(2k)) for every prime p ≥ 5, every r ≥ 1, every integer s and all n, k ≥ 1, as conjectured by Peter Bala (OEIS A333472, 2020), and the case A333472(n) = [x^n] F(x)^n itself. The line s = −r contains Bala's 2022 conjecture on A246437. For primes p with v_p(r) ≤ v_p(s), including A333472 itself, the result also follows from a theorem of Pan and Sun through an order-two transfer theorem; the package proves all cases directly.

- Statement: `OeisA333472.a_tower`, `OeisA333472.a333472_tower`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/333472.lean`, which does not exist upstream yet.
- Mathematics: conjectures by Peter Bala (OEIS A333472, March 2020); proof by Wentao Li, developed with AI assistance (Claude Code), by Lagrange inversion and the exp/log Frobenius method. The line s = −r is Pan and Sun's theorem; for v_p(r) ≤ v_p(s) the family also follows from it by Blanco Gómez's transfer theorem.
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
