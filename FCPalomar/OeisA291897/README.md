# OEIS A291897 and A292911: Shevelev's divisibility conjectures for Euler polynomials

Let E_m(x) be the Euler polynomials, Σ E_m(x)t^m/m! = 2e^(xt)/(e^t + 1), and E_k the Euler numbers, sech t = Σ E_k t^k/k!. OEIS A291897 is the numerator of E_(2n−1)(n), and A292911 is the set of n ≥ 1 with (2n − 1)³ dividing it. The package proves Vladimir Shevelev's 2017 conjectures: (2n − 1)² divides A291897(n) for every n ≥ 1, and every prime p ≡ 1 (mod 4) has the form 2a − 1 with a in A292911. It also proves the sharp forms: (2n − 1)³ divides A291897(n) iff 2n − 1 divides E_(2n−2), and for an odd prime p, (p + 1)/2 lies in A292911 iff p ≡ 1 (mod 4). Both definitions are checked against their e.g.f.s.

- Statement: `OeisA291897.eulerPoly_egf`, `OeisA291897.eulerNum_egf`, `OeisA291897.a291897_conjecture`, `OeisA291897.a291897_cube_dvd_iff`, `OeisA291897.a292911_conjecture`, `OeisA291897.prime_cube_dvd_num_iff`, `OeisA291897.prime_mem_a292911_iff`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/291897.lean`, which does not exist upstream yet.
- Mathematics: conjectures by Vladimir Shevelev (OEIS A291897, A292911, September 2017); proof by Wentao Li, developed with AI assistance (Claude Code), from DLMF 24.2.10 and Ely's congruence (1882).
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
