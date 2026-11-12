# Graph reconstruction: disconnected graphs (Kelly) and the Lovász and Müller edge bounds

Three classical reconstruction theorems: a disconnected graph on at least three vertices is determined by its vertex deck (Kelly 1957); a graph with m > C(n,2)/2 edges (Lovász 1972) or with n! < 2^(m−1) (Müller 1977) is determined by its edge deck.

- Formal Conjectures statement: `ReconstructionConjecture.reconstruction_conjecture.variants.disconnected`, `ReconstructionConjecture.edge_reconstruction_conjecture.variants.lovasz`, `ReconstructionConjecture.edge_reconstruction_conjecture.variants.mueller` in [`FormalConjectures/Wikipedia/ReconstructionConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Wikipedia/ReconstructionConjecture.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: P. J. Kelly, A congruence theorem for trees, Pacific J. Math. 7 (1957), 961–968 (see Bondy, A graph reconstructor's manual, 1991); L. Lovász, A note on the line reconstruction problem, J. Combin. Theory Ser. B 13 (1972), 309–310; V. Müller, The edge reconstruction hypothesis is true for graphs with more than n log₂ n edges, J. Combin. Theory Ser. B 22 (1977), 281–283.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
