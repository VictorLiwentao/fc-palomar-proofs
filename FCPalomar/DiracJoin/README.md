# Dirac's joins of odd cycles: Erdős Problems 917 (Dirac, Erdős 3 | k) and 1032 (Dirac 6-critical)

The join of q disjoint odd cycles C_m is 3q-critical. This gives Dirac's lower bound f_6(4n+2) >= 4n^2+8n+3 (Erdős 917), Erdős's observation f_k(n) >= ½(1 − 1/(k/3))n^2 + n for 3 | k (Erdős 917), and Dirac's 6-critical graphs with minimum degree > n/2 (Erdős 1032).

- Formal Conjectures statement: `Erdos917.erdos_917.variants.dirac`, `Erdos917.erdos_917.variants.erdos_three_dvd`, `Erdos1032.erdos_1032.variants.dirac_six` in [`FormalConjectures/ErdosProblems/917.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/917.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: G. A. Dirac, A property of 4-chromatic graphs and some remarks on critical graphs, J. London Math. Soc. 27 (1952), 85–92; P. Erdős, Problems and results in chromatic graph theory, in Proof Techniques in Graph Theory (1969), 27–35, p. 28.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
