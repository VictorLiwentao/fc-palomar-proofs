# OEIS A014442: each Pythagorean prime p is the largest prime factor of n^2+1 for exactly two n <= p (Kaltman's conjecture)

Every prime p ≡ 1 (mod 4) equals a(n), the largest prime factor of n^2+1, for exactly two n in [1, p], and two such distinct n below p add to p and multiply to 1 mod p. Conjectured by Michael Kaltman, proved by Robert Israel (2015).

- Statement: `OeisA14442.kaltman`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/14442.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Michael Kaltman (OEIS A014442, Jun 10 2015); proof by Robert Israel (Jun 11 2015) in the entry.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
