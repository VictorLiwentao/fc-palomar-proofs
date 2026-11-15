# OEIS A376465: Bala's p^(3r) tower holds and the shifted tower fails

Let T(m, k) = Σ_i C(m,i)² C(m+k−i, k−i) (OEIS A108625) and a(n) = Σ_k C(n,k)² C(n+k,k)² T(n−1, k) (OEIS A376465). Peter Bala conjectured in 2024 that a(n) satisfies both Apéry-number supercongruences: a(np^r) ≡ a(np^{r−1}) and a(np^r − 1) ≡ a(np^{r−1} − 1) (mod p^{3r}) for all primes p ≥ 5 and n, r ≥ 1. The package proves the first for every such p, n and r, and refutes the second: it fails at p = 5, n = 2, r = 1. Both results also appear, with a different proof, in a November 2026 preprint of L.-H. Su.

- Statement: `OeisA376465.tower`, `OeisA376465.not_shifted_tower`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/376465.lean`, which does not exist upstream yet.
- Mathematics: conjectures by Peter Bala (OEIS A376465, September 2024); proof of the first and counterexample to the second by Wentao Li, developed with AI assistance (Claude Code), by the methods of Gessel, Beukers, Straub and Kheyri–Hadweni. L.-H. Su posted a different proof of the first and the same counterexample to the second on November 5, 2026 (Zenodo 23980342).
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
