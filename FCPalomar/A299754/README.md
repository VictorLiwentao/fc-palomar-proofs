# OEIS A299754: sums of p complex p-th roots of unity (Israel's formula, Alekseyev 2018)

For a prime p, the number of distinct sums z_1 + ... + z_p with every z_i^p = 1 is C(2p−1, p). Conjectured by Robert Israel and proved by Max Alekseyev (2018).

- Statement: `OeisA299754.a_prime`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/299754.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Robert Israel (OEIS A299754, Feb 18 2018); proof by Max Alekseyev in the entry (Feb 20 2018).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
