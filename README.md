# Lean proofs of Formal Conjectures statements, packaged for Palomar

This repository holds 45 independent [Palomar](https://palomar-registry.org/) packages.
Each package proves statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
or statements proposed for it, in Lean 4 with Mathlib. The mathematics in every package is due to
the authors cited in its `formalization.yaml` and `README.md`. The Lean proofs are by Wentao Li,
written with AI assistance (Claude Code, Claude Opus 5.5).

## Layout

The repository root is one Lean project (Lean `v4.35.0`, Mathlib `ccbef15e`). Each package is a
folder `FCPalomar/<ID>/` with:

- `Challenge.lean`: the statement, with `sorry`. It imports only Mathlib.
- `Solution.lean`: the same declarations with proofs.
- `comparator.json`: the declarations that `lake comparator` checks.
- `formalization.yaml`: sources, authorship, automation and review metadata.
- `README.md`: a short description of the package.

Each package is a separate Palomar submission. Its Comparator path is
`FCPalomar/<ID>/comparator.json` and its metadata path is `FCPalomar/<ID>/formalization.yaml`.
The selected project is the repository root.

| Package | Result | Theorems |
| --- | --- | --- |
| [`A000262`](FCPalomar/A000262/README.md) | OEIS A000262 and A082579: Bala's Theorem 1 (periodicity modulo every k) | 3 |
| [`A000350`](FCPalomar/A000350/README.md) | OEIS A000350: Fibonacci numbers whose binary expansion ends with their index (Stephan's conjecture, Alekseyev 2009) | 1 |
| [`A001006`](FCPalomar/A001006/README.md) | OEIS A001006: Motzkin numbers at p − 2 modulo p (Batalov's conjecture; Burns, Kohen) | 1 |
| [`A002454`](FCPalomar/A002454/README.md) | OEIS A002454: the odd-order permanent identity (She–Sun–Xia) | 1 |
| [`A014442`](FCPalomar/A014442/README.md) | OEIS A014442: each Pythagorean prime p is the largest prime factor of n^2+1 for exactly two n <= p (Kaltman's conjecture) | 1 |
| [`A053175`](FCPalomar/A053175/README.md) | OEIS A053175: Hankel determinants of the Catalan–Larcombe–French numbers | 1 |
| [`A088041`](FCPalomar/A088041/README.md) | OEIS A088041: the least k > 1 with k^4 − 1 divisible by an n-th power (Israel 2019) | 2 |
| [`A101368`](FCPalomar/A101368/README.md) | OEIS A101368: pairs with i \| 1+j+j^2 and j \| 1+i+i^2 (Stephan's g.f., Alekseyev 2006) | 1 |
| [`A113052`](FCPalomar/A113052/README.md) | OEIS A113052 and A113047: Fuss–Catalan numbers modulo p (Barry's conjecture, Israel 2018) | 2 |
| [`A158110`](FCPalomar/A158110/README.md) | OEIS A158110: exp(Σ q^(n^m) x^n/n) has integer coefficients (Hanna's conjecture, Fried 2025) | 1 |
| [`A173774`](FCPalomar/A173774/README.md) | OEIS A173774: Sun's integrality conjecture (Andersen 2010) | 1 |
| [`A190940`](FCPalomar/A190940/README.md) | OEIS A190940: lcm of partial sums of compositions (Oudra's conjecture, Alekseyev 2024) | 1 |
| [`A265100`](FCPalomar/A265100/README.md) | OEIS A265100: Catalan numbers divisible by 3 and block numbers (Jeffery's Conjectures 5, 1, 2, 3) | 4 |
| [`A289682`](FCPalomar/A289682/README.md) | OEIS A289682: Catalan numbers at 2^n − 1 and 2^n modulo 16 (Israel's conjecture) | 1 |
| [`A299754`](FCPalomar/A299754/README.md) | OEIS A299754: sums of p complex p-th roots of unity (Israel's formula, Alekseyev 2018) | 1 |
| [`A368630`](FCPalomar/A368630/README.md) | OEIS A368630: three congruences (Hanna's conjectures) | 4 |
| [`A389535`](FCPalomar/A389535/README.md) | OEIS A389535: Hanna's formula (7), A(x)^5 ≡ A(x^5) (mod 5) | 2 |
| [`A395839`](FCPalomar/A395839/README.md) | OEIS A395839: parity and residues mod 3 of 10C(x)^2 − C(x) (Hanna's conjectures) | 2 |
| [`A396804`](FCPalomar/A396804/README.md) | OEIS A396804: a(n) mod 5 is never 3 (Hanna's conjecture) | 2 |
| [`A396843`](FCPalomar/A396843/README.md) | OEIS A396843: integral construction and oddness (Hanna's conjecture) | 2 |
| [`BellPeriod`](FCPalomar/BellPeriod/README.md) | Bell numbers modulo a prime are periodic with period (p^p−1)/(p−1) (Touchard, Hall) | 6 |
| [`BurningPath`](FCPalomar/BurningPath/README.md) | The burning number of a path | 1 |
| [`DiracJoin`](FCPalomar/DiracJoin/README.md) | Dirac's joins of odd cycles: Erdős Problems 917 (Dirac, Erdős 3 \| k) and 1032 (Dirac 6-critical) | 3 |
| [`Erdos1009`](FCPalomar/Erdos1009/README.md) | Erdős Problem 1009: Sauer's example | 1 |
| [`Erdos1111`](FCPalomar/Erdos1111/README.md) | Erdős Problem 1111: Wagon's bound | 1 |
| [`Erdos1186`](FCPalomar/Erdos1186/README.md) | Erdős Problem 1186: bounds on the density of monochromatic progressions | 2 |
| [`Erdos151`](FCPalomar/Erdos151/README.md) | Erdős Problem 151: the triangle-free case and the square-root bound | 2 |
| [`Erdos494`](FCPalomar/Erdos494/README.md) | Erdős Problem 494: Selfridge–Straus, A is determined by its k-sums when \|A\| has a prime factor p > k, and when k = 4, \|A\| > 12 | 2 |
| [`Erdos506`](FCPalomar/Erdos506/README.md) | Erdős Problem 506: Segre's eight points determining fewer than C(7,2) circles | 1 |
| [`Erdos626`](FCPalomar/Erdos626/README.md) | Erdős Problem 626: Erdős's upper bound g_k(n) <= 2 log n / log(k−2) + 1 | 1 |
| [`Erdos712`](FCPalomar/Erdos712/README.md) | Erdős Problem 712, graph case: Turán's density limit | 2 |
| [`Erdos766`](FCPalomar/Erdos766/README.md) | Erdős Problem 766: the Dirac–Erdős bound | 1 |
| [`Erdos934h1`](FCPalomar/Erdos934h1/README.md) | Erdős Problem 934: h_1(d) = d + 1 for d ≠ 2 | 1 |
| [`Erdos983`](FCPalomar/Erdos983/README.md) | Erdős Problem 983: the Erdős–Straus upper bound f(π(n)+1, n) <= 2π(√n)+1 | 1 |
| [`GowersLongPow`](FCPalomar/GowersLongPow/README.md) | Gowers–Long: F(n) = n^α implies F(m) >= m^β eventually for β < α | 1 |
| [`GowersLongSquare`](FCPalomar/GowersLongSquare/README.md) | Gowers–Long: F(n) ≥ n^{3/2} when n is a perfect square | 1 |
| [`Kolberg`](FCPalomar/Kolberg/README.md) | Kolberg's theorem: the partition function takes each parity infinitely often | 1 |
| [`MeynielTree`](FCPalomar/MeynielTree/README.md) | Meyniel's conjecture for trees: trees are cop-win | 1 |
| [`OhbaERT`](FCPalomar/OhbaERT/README.md) | Erdős–Rubin–Taylor: complete multipartite graphs with parts of size 2 are k-choosable | 1 |
| [`OneTwoThree`](FCPalomar/OneTwoThree/README.md) | The 1-2-3 conjecture with weights 1..5 (Kalkowski–Karoński–Pfender) | 2 |
| [`Reconstruction`](FCPalomar/Reconstruction/README.md) | Graph reconstruction: disconnected graphs (Kelly) and the Lovász and Müller edge bounds | 3 |
| [`SauerSpencer`](FCPalomar/SauerSpencer/README.md) | The Sauer–Spencer packing theorem | 1 |
| [`SunDet`](FCPalomar/SunDet/README.md) | Sun's determinants det[(i−j)^m + δ_ij] for m = 1, 2, 3 | 3 |
| [`TxGraffiti2`](FCPalomar/TxGraffiti2/README.md) | TxGraffiti Conjecture 2 is false (Fischer's counterexample) | 1 |
| [`WOWII291`](FCPalomar/WOWII291/README.md) | WOWII Conjecture 291 is false (a 12-vertex counterexample) | 1 |

## Build

```text
lake exe cache get
lake build
```

`lake build` builds every Challenge and Solution module. Every Solution theorem uses only
`propext`, `Classical.choice` and `Quot.sound`.

## Licence

Apache License 2.0, see `LICENSE`. Statements and definitions copied from Formal Conjectures are
also under Apache-2.0 (The Formal Conjectures Authors). Two packages include code from other
authors:

- `FCPalomar/GowersLongPow` contains code adapted from Daniel Puri under the MIT licence; the MIT notice is kept in `Solution.lean`.
- `FCPalomar/Erdos494` contains lemmas adapted from Linmiao Xu (linrock/math-proofs, Apache-2.0); the copyright line is kept in `Solution.lean`.
