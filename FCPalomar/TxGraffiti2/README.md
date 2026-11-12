# TxGraffiti Conjecture 2 is false (Fischer's counterexample)

TxGraffiti Conjecture 2 asserts Z(G) ≤ α(G) + 1 for every connected graph G of maximum degree at most 3 other than K4, where Z is the zero forcing number and α the independence number (recorded by Davila, Brimkov and Pepper, arXiv:2507.17780). Mikko Fischer found a connected 24-vertex counterexample (arXiv:2607.23664). The package certifies that Fischer's graph is connected, has maximum degree 3, zero forcing number at least 11 and independence number at most 9.

- Formal Conjectures statement: `Arxiv.«2507.17780».tx_graffiti_conjecture_2` in [`FormalConjectures/Arxiv/2507.17780/2.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/Arxiv/2507.17780/2.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: conjecture recorded by R. Davila, B. Brimkov and R. Pepper, arXiv:2507.17780; counterexample by M. Fischer, arXiv:2607.23664.
- Lean proof: Wentao Li, with AI assistance (OpenAI Codex, GPT-6.1 Sol; ported to Lean 4.35 with Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
