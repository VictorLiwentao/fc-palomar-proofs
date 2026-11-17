# OEIS A173774: Sun's integrality conjecture (Andersen 2010)

a(n) = (1/n) Σ_{k<n} (21k+8) C(2k,k)^3 is an integer divisible by 4 C(2n,n). Zhi-Wei Sun conjectured this in February 2010. Kasper Andersen confirmed it in a reply on the NMBRTHRY list by identifying a(n)/(4 C(2n,n)) with A112029(n−1). Sun records Andersen's identity in his paper Super congruences and Euler numbers (Sci. China Math. 2011).

- Statement: `OeisA173774.conjecture`, written for this package from the source. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/173774.lean`, which does not exist upstream yet.
- Mathematics: conjecture by Zhi-Wei Sun (OEIS A173774, February 2010); confirmed by Kasper Andersen in a reply on the NMBRTHRY list (Sun dates it Feb. 11, 2010; the OEIS comment gives Feb 11 2011), via a(n) = 4 C(2n,n) b(n−1) with b(m) = Σ_{k<=m} C(m+k,k)^2 (A112029). Sun states this identity as Lemma 4.1 (Kasper Andersen) in Z.-W. Sun, Super congruences and Euler numbers, Sci. China Math. 54 (2011), 2509–2535 (lemma number from arXiv:1001.4453).
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
