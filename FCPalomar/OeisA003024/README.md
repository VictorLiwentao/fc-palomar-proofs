# OEIS A003024 and A188457: Bala's exp-integrality conjectures, with Gauss congruences for every q

For an integer q let a_q(0) = 1 and a_q(n) = Σ_{k=1}^n (−1)^(k+1) C(n,k) q^(k(n−k)) a_q(n−k). Then a_2 is OEIS A003024 (labeled acyclic digraphs) and a_3 is OEIS A188457 (acyclic 2-multidigraphs). The package proves the Gauss congruences a_q(np^r) ≡ a_q(np^(r−1)) (mod p^r) for every integer q, every prime p and all n, r ≥ 1. Hence exp(Σ_{n≥1} a_q(n) xⁿ/n) has integer coefficients for every q. The cases q = 2 and q = 3 are Peter Bala's 2016 conjectures in A003024 and A188457; the first also shows that every term of A188490 is an integer.

- Statement: `OeisA003024.gauss_congruence`, `OeisA003024.exp_integral`, `OeisA003024.a003024_exp_integral`, `OeisA003024.a188457_exp_integral`, written for this package from the source.
- Mathematics: conjectures by Peter Bala (OEIS A003024 and A188457, January 14 2016); proof by Wentao Li, developed with AI assistance (Claude Code), with Robinson's recurrence and Dold's integrality criterion.
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
