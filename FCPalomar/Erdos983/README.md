# Erdős Problem 983: the Erdős–Straus upper bound f(π(n)+1, n) <= 2π(√n)+1

Let f(k,n) be the least r such that every k-subset A of {1..n} has a set S of r primes with more than r elements of A divisible only by primes in S. Erdős and Straus proved f(π(n)+1, n) <= 2π(n^{1/2})+1.

- Formal Conjectures statement: `Erdos983.erdos_983.variants.upper_bound` in [`FormalConjectures/ErdosProblems/983.lean`](https://github.com/google-deepmind/formal-conjectures/blob/691719db2653905d5fa0775408370fb058e4c59f/FormalConjectures/ErdosProblems/983.lean) (copied verbatim into `Challenge.lean`).
- Mathematics: Erdős and Straus, in P. Erdős, Some applications of graph theory to number theory, Proc. Second Chapel Hill Conf. (1970), 136–145, p. 139, (14) [Er70b].
- Lean proof: Wentao Li, with AI assistance (Claude Code, Claude Opus 5.5).
- Local checks: Lean v4.35.0, Mathlib `ccbef15e`; strict build with no warnings; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound`.
