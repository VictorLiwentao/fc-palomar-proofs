# WOWII Conjecture 291 is false (a 12-vertex counterexample)

Conjecture 291 of DeLaViña's Written on the Wall II says that every connected graph on more than two vertices satisfies γ_t(G) ≤ k + f, where γ_t is the total domination number, k the first Havel–Hakimi step at which a zero appears, and f the number of vertices lying in the fewest triangles. The package certifies a 12-vertex counterexample with γ_t = 4, k = 2 and f = 1: the m = 6 member of a family posted by vulnix0x4. The source credits the disproof to Zyad Tamimi.

- Formal Conjectures statement: `WrittenOnTheWallII.GraphConjecture291.conjecture291` in [`FormalConjectures/WrittenOnTheWallII/GraphConjecture291.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/WrittenOnTheWallII/GraphConjecture291.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: conjecture by E. DeLaViña (Written on the Wall II, Conjecture 291); disproof credited to Zyad Tamimi; the certified graph is from vulnix0x4's family in formal-conjectures issue 4562.
- Lean proof: Wentao Li, with AI assistance (OpenAI Codex, GPT-6.1 Sol; ported to Lean 4.35 with Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
