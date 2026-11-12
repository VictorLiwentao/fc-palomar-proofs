# OEIS A001006: Motzkin numbers at p − 2 modulo p (Batalov's conjecture; Burns, Kohen)

For every prime p, p | M(p−2) iff p ≡ 1 (mod 3), and M(p−2) ≡ −1 (mod p) when p ≡ 5 (mod 6). Conjectured by Serge Batalov (2022) for p ≡ 1 (mod 6); proved by Rob Burns (2017) and Nadav Kohen (2024).

- Statement: `OeisA1006.prime_dvd_iff`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/1006.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Serge Batalov (OEIS A001006, Feb 08 2022); R. Burns, arXiv:1703.00826 (2017), Tables 4–5; N. Kohen, arXiv:2411.03681 (2024), Proposition 6, Integers 26 (2026), A22.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
