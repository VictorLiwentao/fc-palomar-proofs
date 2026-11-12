# OEIS A000262 and A082579: Bala's Theorem 1 (periodicity modulo every k)

If Σ a(n) x^n/n! = F(x) exp(x G(x)) with F, G integer power series and G(0) = 1, then a(n+k) ≡ a(n) (mod k) for all n, k (Bala 2017, Theorem 1). Hence A000262 (exp(x/(1−x))) and A082579 (exp(x/(1−x)^2)) satisfy k | a(n+k) − a(n) for k >= 2.

- Statement: `OeisA262.bala_theorem1`, `OeisA262.a000262`, `OeisA262.a082579`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/262.lean`, which does not exist upstream yet.
- Mathematics: P. Bala, Integer sequences that become periodic on reduction modulo k for all k (Dec 03 2017), Theorem 1 and Lemma 1; conjecture and proof recorded in OEIS A000262 and A082579.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
