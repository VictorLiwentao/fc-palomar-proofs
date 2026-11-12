# Meyniel's conjecture for trees: trees are cop-win

Every finite, nonempty, connected, acyclic graph has cop number 1 (Quilliot 1978; Nowakowski–Winkler 1983).

- Formal Conjectures statement: `MeynielConjecture.meyniel_conjecture.variants.tree` in [`FormalConjectures/Wikipedia/MeynielConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Wikipedia/MeynielConjecture.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: A. Quilliot, Jeux et pointes fixes sur les graphes, thèse de 3ème cycle, Université de Paris VI (1978); R. Nowakowski and P. Winkler, Vertex-to-vertex pursuit in a graph, Discrete Math. 43 (1983), 235–239.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
