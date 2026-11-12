# OEIS A265100: Catalan numbers divisible by 3 and block numbers (Jeffery's Conjectures 5, 1, 2, 3)

3 | C(n) iff the base-3 expansions of n and n+1 both contain a 2 (Conjecture 5; Deutsch–Sagan 2006, Thm 5.2; Israel 2015); every block number is a term 9·A005836(i)+5 (Conjecture 1), and Conjectures 2 and 3 follow.

- Statement: `OeisA265100.conjecture5`, `OeisA265100.conjecture1`, `OeisA265100.conjecture2`, `OeisA265100.conjecture3`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/265100.lean`, which does not exist upstream yet.
- Mathematics: conjectures by L. Edson Jeffery (OEIS A265100, 2015); Conjecture 5 is Deutsch–Sagan (2006), Theorem 5.2 (C_n mod 3), proved again by Robert Israel (Sequence Fans, 2015).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
