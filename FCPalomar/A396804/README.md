# OEIS A396804: a(n) mod 5 is never 3 (Hanna's conjecture)

For A(x) = Σ a(n) x^n/n! with A(x) = x exp(A∘A∘A∘A(x)), every a(n) (n >= 1) is an integer not congruent to 3 mod 5. Conjectured by Paul D. Hanna; an informal proof is in Vladimir Reshetnikov's ProveIt report (2026). The Lean proof is different.

- Statement: `OeisA396804.exists_unique_solution`, `OeisA396804.conjecture_mod_five`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/396804.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Paul D. Hanna (OEIS A396804); informal proof in V. Reshetnikov, Prime-power congruences for compositional tree series, ProveIt research report (September 2026).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
