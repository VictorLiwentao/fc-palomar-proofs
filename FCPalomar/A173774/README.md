# OEIS A173774: Sun's integrality conjecture (Andersen 2010)

a(n) = (1/n) Σ_{k<n} (21k+8) C(2k,k)^3 is an integer divisible by 4 C(2n,n). Conjectured by Zhi-Wei Sun and confirmed by Kasper Andersen (2010), who identified a(n)/(4 C(2n,n)) with A112029(n−1).

- Statement: `OeisA173774.conjecture`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/173774.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Zhi-Wei Sun (OEIS A173774); confirmed by Kasper Andersen (Feb 2011 comment / 2010), via a(n) = 4 C(2n,n) b(n−1) with b(m) = Σ_{k<=m} C(m+k,k)^2 (A112029).
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
