# OEIS A368630: three congruences (Hanna's conjectures)

The exponential generating function A(x) of OEIS A368630 satisfies A(0) = 1 and A(x/A(x)^2) = exp(x A(x)). The package proves that this equation determines a unique integer coefficient sequence, and that a(n) ≡ 1 (mod 3) for every n, a(2n) is odd for every n, and a(2n+1) is even for n ≥ 1, as conjectured by Paul D. Hanna (OEIS A368630, 2024).

- Statement: `OeisA368630.exists_unique_sequence`, `OeisA368630.conjecture_mod_three`, `OeisA368630.conjecture_even`, `OeisA368630.conjecture_odd`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/368630.lean`, which does not exist upstream yet (proposed in google-deepmind/formal-conjectures PR #7674).
- Mathematics: conjectures by Paul D. Hanna (OEIS A368630, January 2 2024); proof by Wentao Li.
- Lean proof: Wentao Li, with AI assistance (OpenAI Codex, GPT-6.1 Sol; ported to Lean 4.35 with Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
