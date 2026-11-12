# Sun's determinants det[(i−j)^m + δ_ij] for m = 1, 2, 3

Closed forms for det[(i−j)^m + δ_ij]_{1<=i,j<=n}: m = 1 (A079034; Wang–Sun 2022), and Zhi-Wei Sun's conjectured formulas for m = 2 (A355175) and m = 3 (A355326, Conjecture 1), proved by Fried (2026).

- Statement: `OeisA79034.det_one`, `OeisA79034.det_two`, `OeisA79034.det_three`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/79034.lean`, which does not exist upstream yet.
- Mathematics: m = 1: B. Cloitre's formula in OEIS A079034, proved by H. Wang and Z.-W. Sun, Evaluations of three determinants, arXiv:2206.12317 (2022); m = 2, 3: conjectures of Z.-W. Sun (OEIS A355175, A355326, 2022), proved by S. Fried, Proofs of several OEIS conjectures on determinants and permanents, arXiv:2606.09913 (2026), Theorem 9 and Corollary 4.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
