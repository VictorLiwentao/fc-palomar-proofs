# Erdős Problem 1111: Wagon's bound

Every finite graph with no clique of size t and chromatic number at least C(t,2)+1 has two anticomplete vertex sets that each induce a graph of chromatic number at least 2 (Wagon 1980, as noted by El-Zahar and Erdős). In Erdős Problem 1111, d(t,c) is the least d such that every finite graph with clique number less than t and chromatic number at least d has two anticomplete vertex sets A, B with χ(G[A]) ≥ c and χ(G[B]) ≥ c (El-Zahar and Erdős 1985). So the result says d(t,2) ≤ C(t,2)+1. Two anticomplete sets that each induce a graph of chromatic number at least 2 are the same as an induced 2K₂.

- Formal Conjectures statement: `Erdos1111.erdos_1111.variants.wagon` in [`FormalConjectures/ErdosProblems/1111.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/1111.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: S. Wagon, A bound on the chromatic number of graphs without certain induced subgraphs, J. Combin. Theory Ser. B 29 (1980), 345–346 (χ ≤ C(ω+1,2) for 2K₂-free graphs); the consequence d(t,2) ≤ C(t,2)+1 is noted by El-Zahar and Erdős (1985).
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
