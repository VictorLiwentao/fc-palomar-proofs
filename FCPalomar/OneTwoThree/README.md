# The 1-2-3 conjecture with weights 1..5 (Kalkowski–Karoński–Pfender)

Every finite simple graph without an isolated edge has edge weights in {1,...,5} such that adjacent vertices have different weighted degrees (Kalkowski, Karoński and Pfender 2010). The {1,...,30} bound of Addario-Berry et al. (2007) follows as a corollary. The 1-2-3 conjecture itself (Karoński, Łuczak and Thomason 2004), with weights {1, 2, 3}, was later proved by Keusch (2024); this entry formalizes the earlier {1,...,5} theorem, not Keusch's proof.

- Formal Conjectures statement: `OneTwoThreeConjecture.one_two_three_conjecture.variants.one_to_five`, `OneTwoThreeConjecture.one_two_three_conjecture.variants.one_to_thirty` in [`FormalConjectures/Paper/OneTwoThreeConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Paper/OneTwoThreeConjecture.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: M. Kalkowski, M. Karoński and F. Pfender, Vertex-coloring edge-weightings: towards the 1-2-3-conjecture, J. Combin. Theory Ser. B 100 (2010), 347–349; the {1,...,30} bound is L. Addario-Berry, K. Dalal, C. McDiarmid, B. Reed and A. Thomason, Vertex-colouring edge-weightings, Combinatorica 27 (2007), 1–12.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
