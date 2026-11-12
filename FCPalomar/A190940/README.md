# OEIS A190940: lcm of partial sums of compositions (Oudra's conjecture, Alekseyev 2024)

For n >= 1, the number of distinct values of lcm(a, a+b, a+b+c, ..., n) over the compositions of n equals the number of divisors of lcm(1..n)/n. Conjectured by Ridouane Oudra (2019), proved by Max Alekseyev (2024).

- Statement: `OeisA190940.card_lcmPartialSums`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/190940.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Ridouane Oudra (OEIS A190940, Aug 24 2019); proof by Max Alekseyev in the entry (Nov 22 2024).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
