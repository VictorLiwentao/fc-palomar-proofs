/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Challenge: OEIS A376465, Bala's pair of supercongruences

Let $T(m, k) = \sum_{i=0}^{k} \binom{m}{i}^2 \binom{m+k-i}{k-i}$ (OEIS A108625). OEIS A376465 is
$$a(n) = \sum_{k=0}^{n} \binom{n}{k}^2 \binom{n+k}{k}^2 \, T(n-1, k), \qquad n \ge 0.$$
The Apéry numbers satisfy two towers of supercongruences, for all primes $p \ge 5$ and all
positive integers $n$ and $r$: (U) $u(np^r) \equiv u(np^{r-1})$ and
(S) $u(np^r - 1) \equiv u(np^{r-1} - 1) \pmod{p^{3r}}$. Bala conjectures that $a$ satisfies the
same pair. The statements below are (U) for $a$, and the negation of (S) for $a$.

Written for this package from the OEIS entry; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

*References:*
- Peter Bala, [A376465](https://oeis.org/A376465), Sep 25, 2024.
-/

@[expose] public section

namespace OeisA376465

/-- OEIS A108625: $T(m, k) = \sum_{i=0}^{k} \binom{m}{i}^2 \binom{m+k-i}{k-i}$. -/
def T (m k : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), m.choose i ^ 2 * (m + k - i).choose (k - i)

/-- OEIS A376465: $a(n) = \sum_{k=0}^{n} \binom{n}{k}^2 \binom{n+k}{k}^2 T(n-1, k)$.
At $n = 0$ the factor $T(-1, 0) = 1$ is `T 0 0 = 1`, with the same value. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (n + k).choose k ^ 2 * T (n - 1) k

/--
For every prime $p \ge 5$ and all $n, r \ge 1$: $a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$.
- Peter Bala, OEIS A376465, Sep 25 2024 (the first congruence of the pair).
-/
theorem tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

/--
Bala's second congruence fails: it is not true that for every prime $p \ge 5$ and all
$n, r \ge 1$, $a(np^r - 1) \equiv a(np^{r-1} - 1) \pmod{p^{3r}}$.
- Peter Bala, OEIS A376465, Sep 25 2024 (the second congruence of the pair, conjectured).
-/
theorem not_shifted_tower : ¬ ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 0 < n → 0 < r →
    a (n * p ^ r - 1) ≡ a (n * p ^ (r - 1) - 1) [MOD p ^ (3 * r)] := by
  sorry

end OeisA376465

end
