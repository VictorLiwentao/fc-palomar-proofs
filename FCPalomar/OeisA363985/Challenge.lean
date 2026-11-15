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
# Challenge: OEIS A363985, A363987, A363989 and A362676, Bala's supercongruences

For an integer parameter $m$, Peter Bala defines
$$u_m(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{mn+k}{k} \binom{2k}{k}.$$
The binomial $\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$ is the polynomial one (`Ring.choose` on
`ℤ`), so $\binom{mn+k}{k}$ is defined for negative $m$. For $m \ge 0$ it is the usual binomial
coefficient. OEIS A363985, A363987 and A363989 are $u_2$, $u_3$ and $u_4$. OEIS A362676 is
$a(n) = \sum_k 4^{n-k} \binom{n}{k} \binom{n-1}{k} \binom{2k}{k}$, which equals
$(-1)^n u_{-1}(n)$ by its OEIS comment.

On A363985 Bala conjectures that for all $m \in \mathbb{Z}$, every prime $p \ge 5$ and all
positive integers $n$ and $r$, $u_m(np^r) \equiv u_m(np^{r-1}) \pmod{p^{3r}}$. He makes the same
conjecture for a second family
$v_m(n) = \sum_k (-4)^{n-k} \binom{n}{k} \binom{mn+2k}{2k} \binom{2k}{k}$. The statements below
are the $u$-half: every $m \in \mathbb{Z}$, and the four entries. The $v$-family (A363986,
A363988, A363990) is not stated here.

Written for this package from the OEIS entries; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

*References:*
- Peter Bala, [A363985](https://oeis.org/A363985), July 2, 2023.
- Peter Bala, [A363987](https://oeis.org/A363987), July 2, 2023.
- Peter Bala, [A363989](https://oeis.org/A363989), July 2, 2023.
- Peter Bala, [A362676](https://oeis.org/A362676), July 3, 2023.
-/

@[expose] public section

namespace OeisA363985

/-- Bala's sequence $u_m(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{mn+k}{k}
\binom{2k}{k}$, with the polynomial binomial $\binom{mn+k}{k}$ (`Ring.choose`). -/
def u (m : ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-4) ^ (n - k) * (n.choose k : ℤ) * Ring.choose (m * n + k) k * ((2 * k).choose k : ℤ)

/-- OEIS A363985: $a(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{2n+k}{k} \binom{2k}{k}$. -/
def a363985 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-4) ^ (n - k) * (n.choose k : ℤ) * ((2 * n + k).choose k : ℤ) * ((2 * k).choose k : ℤ)

/-- OEIS A363987: $a(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{3n+k}{k} \binom{2k}{k}$. -/
def a363987 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-4) ^ (n - k) * (n.choose k : ℤ) * ((3 * n + k).choose k : ℤ) * ((2 * k).choose k : ℤ)

/-- OEIS A363989: $a(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{4n+k}{k} \binom{2k}{k}$. -/
def a363989 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-4) ^ (n - k) * (n.choose k : ℤ) * ((4 * n + k).choose k : ℤ) * ((2 * k).choose k : ℤ)

/-- OEIS A362676: $a(n) = \sum_{k=0}^{n} 4^{n-k} \binom{n}{k} \binom{n-1}{k} \binom{2k}{k}$.
At $n = 0$ the factor $\binom{-1}{0} = 1$ is `Nat.choose 0 0 = 1`, with the same value. -/
def a362676 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), 4 ^ (n - k) * n.choose k * (n - 1).choose k * (2 * k).choose k

/--
For every integer $m$, every prime $p \ge 5$ and all $n, r \ge 1$:
$u_m(np^r) \equiv u_m(np^{r-1}) \pmod{p^{3r}}$.
- Peter Bala, OEIS A363985, Jul 02 2023 (the conjecture for $u_m$, for all $m \in \mathbb{Z}$).
-/
theorem u_tower (m : ℤ) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) : u m (n * p ^ r) ≡ u m (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  sorry

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$ for OEIS A363985.
- Peter Bala, OEIS A363985, Jul 02 2023.
-/
theorem a363985_tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) :
    a363985 (n * p ^ r) ≡ a363985 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  sorry

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$ for OEIS A363987.
- Peter Bala, OEIS A363987, Jul 02 2023.
-/
theorem a363987_tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) :
    a363987 (n * p ^ r) ≡ a363987 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  sorry

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$ for OEIS A363989.
- Peter Bala, OEIS A363989, Jul 02 2023.
-/
theorem a363989_tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) :
    a363989 (n * p ^ r) ≡ a363989 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  sorry

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$ for OEIS A362676.
- Peter Bala, OEIS A362676, Jul 03 2023.
-/
theorem a362676_tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) : a362676 (n * p ^ r) ≡ a362676 (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

end OeisA363985

end
