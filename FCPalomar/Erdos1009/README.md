# Erdős Problem 1009: Sauer's example

For every r >= 1 there is a graph on n = 2r+4 vertices with floor(n^2/4)+2n−6 edges in which every family of edge-disjoint triangles has at most 2n−7 members (Sauer's example, reported in Erdős 1971).

- Formal Conjectures statement: `Erdos1009.erdos_1009.variants.sauer` in [`FormalConjectures/ErdosProblems/1009.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/1009.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: Sauer's example, reported in P. Erdős, Some unsolved problems in graph theory and combinatorial analysis, in Combinatorial Mathematics and its Applications (1971), p. 98 [Er71].
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
