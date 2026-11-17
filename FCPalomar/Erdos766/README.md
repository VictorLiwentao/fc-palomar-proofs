# Erdős Problem 766: the Dirac–Erdős bound

Every graph on n vertices with floor(n^2/4)+1 edges contains, for each 3 <= k <= n, a subgraph on k vertices with floor(k^2/4)+1 edges. For k = 3 this is Mantel's theorem. Dirac (1963) and Erdős (1964) proved it independently. It is the case l = floor(k^2/4)+1 of Erdős Problem 766, on the least number of edges f(n;k,l) that forces a k-vertex subgraph with l edges.

- Formal Conjectures statement: `Erdos766.erdos_766.variants.dirac_erdos` in [`FormalConjectures/ErdosProblems/766.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/766.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: Dirac and Erdős, independently: G. A. Dirac, Extensions of Turán's theorem on graphs, Acta Math. Acad. Sci. Hungar. 14 (1963), 417–422; P. Erdős, Extremal problems in graph theory, in Theory of Graphs and its Applications (Smolenice, 1963), 1964, 29–36, p. 34 [Er64c].
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
