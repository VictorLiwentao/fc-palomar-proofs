# Erdős Problem 494: Selfridge–Straus, A is determined by its k-sums when |A| has a prime factor p > k, and when k = 4, |A| > 12

For a finite set A of complex numbers, the multiset of k-element subset sums together with |A| determines A when |A| is divisible by a prime p > k, and when k = 4 and |A| > 12 (Selfridge–Straus 1958).

- Formal Conjectures statement: `Erdos494.erdos_494.variants.card_divisible_by_prime_gt_k`, `Erdos494.erdos_494.variants.k_eq_4_card_gt_12` in [`FormalConjectures/ErdosProblems/494.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/494.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: J. L. Selfridge and E. G. Straus, On the determination of numbers by their sums of a fixed order, Pacific J. Math. 8 (1958), 847–856 (Corollary to Theorem 4; Theorems 4 and 6).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
