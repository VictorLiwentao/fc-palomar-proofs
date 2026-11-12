# Erdős Problem 766: the Dirac–Erdős bound

Every graph on n vertices with floor(n^2/4)+1 edges contains, for each 3 <= k <= n, a subgraph on k vertices with floor(k^2/4)+1 edges (Dirac; Erdős, independently).

- Formal Conjectures statement: `Erdos766.erdos_766.variants.dirac_erdos` in [`FormalConjectures/ErdosProblems/766.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/766.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: Dirac and Erdős, independently; P. Erdős, Extremal problems in graph theory, in Theory of Graphs and its Applications (Smolenice, 1963), 1964, 29–36, p. 34 [Er64c].
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
