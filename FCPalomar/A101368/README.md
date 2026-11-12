# OEIS A101368: pairs with i | 1+j+j^2 and j | 1+i+i^2 (Stephan's g.f., Alekseyev 2006)

The positive solutions of i | 1 + j + j^2, j | 1 + i + i^2 are exactly the pairs (c(n), c(n+1)), n >= 1, in either order, where c(n) are the coefficients of x(1 − 5x + 3x^2)/((1 − x)(1 − 5x + x^2)). Stephan's g.f. conjecture (2005), proved by Max Alekseyev (2006); the problem is W. W. Chao's Crux problem 2981.

- Statement: `OeisA101368.solutions_iff`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/101368.lean`, which does not exist upstream yet.
- Mathematics: g.f. conjectured by Ralf Stephan (OEIS A101368, Jan 14 2005), proved by Max Alekseyev (Aug 03 2006); W. W. Chao, Crux Math. Problem 2981 (2004); see also Alekseyev–Khomovsky, arXiv:2610.00808, Example 7.1.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
