# OEIS A000350: Fibonacci numbers whose binary expansion ends with their index (Stephan's conjecture, Alekseyev 2009)

The binary expansion of F(m) ends with that of m only for m = 0, 1, 5. Conjectured by Ralf Stephan (2006), proved by Max Alekseyev (2009).

- Statement: `OeisA350.digits_prefix_fib_iff`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/350.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Ralf Stephan (OEIS A000350, Aug 21 2006); proof by Max Alekseyev (Jul 03 2009) in the entry.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
