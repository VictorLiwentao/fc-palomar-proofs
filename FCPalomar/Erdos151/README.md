# Erdős Problem 151: the triangle-free case and the square-root bound

For a graph G on n vertices, τ(G) <= n − H(n) when G is triangle-free, and τ(G) <= n − floor(sqrt n) in general, where τ is the clique transversal number (remarks on erdosproblems.com/151, from Erdős–Gallai–Tuza 1992).

- Formal Conjectures statement: `Erdos151.erdos_151.variants.cliqueFree_three`, `Erdos151.erdos_151.variants.sqrt_bound` in [`FormalConjectures/ErdosProblems/151.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/151.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: remarks on erdosproblems.com/151, from P. Erdős, T. Gallai and Zs. Tuza, Covering the cliques of a graph with vertices, Discrete Math. 108 (1992), 279–289.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
