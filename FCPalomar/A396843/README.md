# OEIS A396843: integral construction and oddness (Hanna's conjecture)

The ordinary generating function A(x) of OEIS A396843, with A(0) = 0 and A'(0) = 1, satisfies A(x A(x) − 3x A(x)^2) = x^2. The package proves that this equation has exactly one integer power-series solution and that every term a(n) with n ≥ 1 is odd, as conjectured by Paul D. Hanna (OEIS A396843, 2026). An earlier Lean proof of the oddness is in the-omega-institute/trureturing PR #6773.

- Statement: `OeisA396843.source_existence`, `OeisA396843.conjecture`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/396843.lean`, which does not exist upstream yet (proposed in google-deepmind/formal-conjectures PR #7673).
- Mathematics: conjecture by Paul D. Hanna (OEIS A396843, July 1 2026); earlier Lean oddness proof by ElonSG (trureturing PR #6773).
- Lean proof: Wentao Li, with AI assistance (OpenAI Codex, GPT-6.1 Sol; ported to Lean 4.35 with Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
