# McCarthy–Osburn–Straub Conjecture 1.3 for σ₈, with a shifted companion

Let A(n) be the sum, over k ∈ [0, n]^4 with k₁ + k₂ = k₃ + k₄, of the products Π C(n, k_i) C(n + k_i, k_i). The package proves A(mp^r) ≡ A(mp^{r−1}) (mod p^{3r}) and A(mp^r − 1) ≡ A(mp^{r−1} − 1) (mod p^{3r}) for every prime p ≥ 5 and all m, r ≥ 1. By McCarthy, Osburn and Straub's Proposition 3.1, A(n) is the leading coefficient of Brown's cellular integral for σ₈ = (8, 3, 6, 1, 4, 7, 2, 5), so the first congruence is their Conjecture 1.3 for σ₈. That link is not formalized. The second congruence is a companion that no source states. σ₈ is the self-dual configuration that MOS single out: their Theorem 1.2 relates A_σ₈((p − 1)/2) to the weight-6 newform η¹²(2z) modulo p².

- Statement: `MosN8.tower`, `MosN8.shifted_tower`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/Arxiv/1705.05586/CellularIntegrals.lean`, which does not exist upstream yet.
- Mathematics: conjecture by D. McCarthy, R. Osburn and A. Straub (Conjecture 1.3, arXiv:1705.05586); proof by Wentao Li, developed with AI assistance (Claude Code).
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
