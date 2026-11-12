# OEIS A002454: the odd-order permanent identity (She–Sun–Xia)

For every n and every primitive complex (2n+1)-th root of unity ζ, the permanent of the 2n × 2n matrix with entries 1 on the diagonal and (1 + ζ^(j−k))/(1 − ζ^(j−k)) off it equals 4^n (n!)^2/(2n+1). Zhi-Wei Sun posed the identity in OEIS A002454 (2022), and She, Sun and Xia proved it (arXiv:2208.12167, Theorem 1.3(ii)). The proof formalizes the determinant approach of Guo, Li, Tao and Wei.

- Formal Conjectures statement: `OeisA2454.conjecture` in [`FormalConjectures/OEIS/2454.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/OEIS/2454.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: conjectured by Zhi-Wei Sun (OEIS A002454, June 26 2022); proved by Y.-F. She, Z.-W. Sun and W. Xia, A novel permanent identity with applications, arXiv:2208.12167, Theorem 1.3(ii); the determinant step follows X. Guo, X. Li, Z. Tao and T. Wei, arXiv:2206.02592, equation (1.3).
- Lean proof: Wentao Li, with AI assistance (OpenAI Codex, GPT-6.1 Sol, and Cursor, Grok 4.6; ported to Lean 4.35 with Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
