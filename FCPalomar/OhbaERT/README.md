# Erdős–Rubin–Taylor: complete multipartite graphs with parts of size 2 are k-choosable

The complete k-partite graph K_{2,...,2} is k-choosable (Erdős, Rubin and Taylor 1979). It is a case of Ohba's conjecture (2002) that ch(G) = χ(G) whenever G has at most 2χ(G)+1 vertices, which Noel, Reed and Wu proved in 2015. This package formalizes only the Erdős–Rubin–Taylor case, by a direct induction with Hall's theorem. The analogous question for parts of size three is harder: ch(K_{3*k}) = ⌈(4k−1)/3⌉ (Kierstead 2000).

- Formal Conjectures statement: `OhbaConjecture.ohba_conjecture.variants.erdos_rubin_taylor` in [`FormalConjectures/Wikipedia/OhbaConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Wikipedia/OhbaConjecture.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: P. Erdős, A. L. Rubin and H. Taylor, Choosability in graphs, Proc. West Coast Conf. on Combinatorics, Graph Theory and Computing (Arcata 1979), Congr. Numer. 26 (1980), 125–157.
- Lean proof: written by Claude Code (Claude Opus 5.5) under the direction of Wentao Li, the author and maintainer.
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
