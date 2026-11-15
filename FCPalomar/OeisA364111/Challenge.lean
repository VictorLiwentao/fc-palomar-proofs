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
# Challenge: OEIS A364111, Bala's supercongruences

Peter Bala considers
$$u(N) = \sum_{k=0}^{N} \binom{N+k-1}{k}^A \binom{2N-2k}{N-k}^B \binom{2k}{k}^C.$$
OEIS A364111 is the case $(A, B, C) = (2, 1, 1)$. Bala conjectures that
$u(np^r) \equiv u(np^{r-1}) \pmod{p^{3r}}$ for all primes $p \ge 5$ and all positive integers
$n$ and $r$: for A364111, and more generally for all integers $A \ge 2$ and $B, C \ge 1$.

Written for this package from the OEIS entry; not copied from an existing formalization.
The `sorry` marks the statements to be proved; it is not a proof.

*References:*
- Peter Bala, [A364111](https://oeis.org/A364111), July 7, 2023.
-/

@[expose] public section

namespace OeisA364111

/-- Bala's sum $u(N) = \sum_{k=0}^{N} \binom{N+k-1}{k}^A \binom{2N-2k}{N-k}^B \binom{2k}{k}^C$.
At $N = k = 0$ the factor $\binom{-1}{0} = 1$ is `Nat.choose 0 0 = 1`, with the same value. -/
def u (A B C N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (N + 1),
    (N + k - 1).choose k ^ A * (2 * N - 2 * k).choose (N - k) ^ B * (2 * k).choose k ^ C

/-- OEIS A364111: $a(n) = \sum_{k=0}^{n} \binom{n+k-1}{k}^2 \binom{2n-2k}{n-k} \binom{2k}{k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    (n + k - 1).choose k ^ 2 * (2 * n - 2 * k).choose (n - k) * (2 * k).choose k

/--
For integers $A \ge 2$ and $B, C \ge 1$, every prime $p \ge 5$ and all $n, r \ge 1$:
$u(np^r) \equiv u(np^{r-1}) \pmod{p^{3r}}$.
- Peter Bala, OEIS A364111, Jul 07 2023 (the general conjecture).
-/
theorem u_supercongruence {A B C : ℕ} (hA : 2 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    u A B C (n * p ^ r) ≡ u A B C (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$.
- Peter Bala, OEIS A364111, Jul 07 2023 (the conjecture for A364111).
-/
theorem a_supercongruence {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) : a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

end OeisA364111

end
