# Bell numbers modulo a prime are periodic with period (p^p−1)/(p−1) (Touchard, Hall)

For a prime p, B(n + (p^p − 1)/(p − 1)) ≡ B(n) (mod p) (Touchard 1933, Hall 1934). This settles G. C. Greubel's conjectured periods in OEIS A146107, A146109, A146113, A146119 and A146121 (p = 17, 19, 23, 29, 31). Minimality is not claimed.

- Statement: `OeisA54767.bell_period`, `OeisA54767.a146107`, `OeisA54767.a146109`, `OeisA54767.a146113`, `OeisA54767.a146119`, `OeisA54767.a146121`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/54767.lean`, which does not exist upstream yet.
- Mathematics: J. Touchard, Ann. Soc. Sci. Bruxelles A 53 (1933), 21–31; M. Hall, Bull. Amer. Math. Soc. 40 (1934), 387; G. T. Williams, Amer. Math. Monthly 52 (1945), 323–327. Conjectures for p = 17..31 by G. C. Greubel (OEIS).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
