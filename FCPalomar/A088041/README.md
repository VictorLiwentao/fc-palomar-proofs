# OEIS A088041: the least k > 1 with k^4 − 1 divisible by an n-th power (Israel 2019)

For n >= 4 the least k > 1 such that m^n | k^4 − 1 for some m > 1 is 2^(n−2) − 1, and Barker's recurrence a(n) = 3a(n−1) − 2a(n−2) holds for n > 5. Proved by Robert Israel (2019).

- Statement: `OeisA88041.isLeast_S`, `OeisA88041.a_recurrence`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/88041.lean`, which does not exist upstream yet.
- Mathematics: formula and recurrence conjectured in OEIS A088041 (recurrence by Colin Barker, Feb 05 2013); proved by Robert Israel, Proof of conjectured formula (2019), https://oeis.org/A088041/a088041.pdf.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
