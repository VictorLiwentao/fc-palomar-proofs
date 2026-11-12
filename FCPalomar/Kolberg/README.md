# Kolberg's theorem: the partition function takes each parity infinitely often

The partition number p(n) is even for infinitely many n and odd for infinitely many n (Kolberg 1959). The proof uses Euler's pentagonal number theorem over F_2.

- Formal Conjectures statement: `PartitionParity.kolberg` in [`FormalConjectures/Paper/PartitionParity.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Paper/PartitionParity.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: O. Kolberg, Note on the parity of the partition function, Math. Scand. 7 (1959), 377–378.
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
