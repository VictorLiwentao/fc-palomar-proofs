# The Sauer–Spencer packing theorem

Two graphs on the same n vertices pack if 2 Δ(G1) Δ(G2) < n (Sauer and Spencer 1978).

- Formal Conjectures statement: `BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.sauer_spencer` in [`FormalConjectures/Paper/BollobasEldridgeCatlinConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Paper/BollobasEldridgeCatlinConjecture.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: N. Sauer and J. Spencer, Edge disjoint placement of graphs, J. Combin. Theory Ser. B 25 (1978), 295–302.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
