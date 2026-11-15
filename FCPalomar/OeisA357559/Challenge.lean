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
# Challenge: Bala's divisibility conjectures on OEIS A357559

Written for this package from the OEIS entry; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

For $m, n \ge 0$, Peter Bala (A357559, October 2022) defines
$$S_m(n) = \sum_{k=0}^{n} (-1)^{n+k}\, k^m \binom{n}{k}\binom{n+k}{k}^2 .$$
$S_3$ is A357559, and $S_0$ is the Apéry sequence A005258. The entry conjectures:

- Conjecture 1: $S_2(2n)$ is divisible by $n^2(2n+1)^2$.
- FORMULA section: $3\,a(2n) \equiv 0 \pmod{n^2(2n+1)^3}$, where $a = S_3$.

The statements below take every $n \ge 0$. At $n = 0$ both sides are $0$, and $0 \mid 0$.
Bala's Conjectures 2 and 3, for $m \ge 4$, are not stated here.

*Statements.*
- `S_two_dvd`, `S_two_dvd_of_odd`: $n^2(n+1)^2 \mid 2S_2(n)$ for every $n$, and
  $n^2(n+1)^2 \mid S_2(n)$ for odd $n$.
- `S_three_dvd`: $n^2(n+1)^3 \mid 6S_3(n)$ for every $n$.
- `conjecture_one`, `formula_conjecture`: Bala's two conjectures in his form, for every $n$.
- `conjecture_one_two`, `formula_conjecture_two`: the same with an extra factor $2$,
  $2n^2(2n+1)^2 \mid S_2(2n)$ and $2n^2(2n+1)^3 \mid 3S_3(2n)$.

*References:*
- Peter Bala, [A357559](https://oeis.org/A357559). The FORMULA conjecture dates from
  October 4, 2022, and Conjecture 1 has its current form from October 6, 2022.
- [A005258](https://oeis.org/A005258), the Apéry numbers $S_0(n)$.
-/

@[expose] public section

namespace OeisA357559

open Finset

/-- Bala's sum $S_m(n) = \sum_{k=0}^{n} (-1)^{n+k} k^m \binom{n}{k}\binom{n+k}{k}^2$.
`S 3` is OEIS A357559. -/
def S (m n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (-1) ^ (n + k) * (k : ℤ) ^ m * (n.choose k : ℤ) * ((n + k).choose k : ℤ) ^ 2

/-- $n^2(n+1)^2$ divides $2S_2(n)$ for every $n \ge 0$. -/
theorem S_two_dvd (n : ℕ) : (n : ℤ) ^ 2 * (n + 1) ^ 2 ∣ 2 * S 2 n := by
  sorry

/-- $n^2(n+1)^2$ divides $S_2(n)$ for every odd $n$. -/
theorem S_two_dvd_of_odd (n : ℕ) (hn : Odd n) : (n : ℤ) ^ 2 * (n + 1) ^ 2 ∣ S 2 n := by
  sorry

/-- $n^2(n+1)^3$ divides $6S_3(n)$ for every $n \ge 0$. -/
theorem S_three_dvd (n : ℕ) : (n : ℤ) ^ 2 * (n + 1) ^ 3 ∣ 6 * S 3 n := by
  sorry

/-- Bala's Conjecture 1 on OEIS A357559: $n^2(2n+1)^2$ divides $S_2(2n)$ for every $n \ge 0$. -/
theorem conjecture_one (n : ℕ) : (n : ℤ) ^ 2 * (2 * n + 1) ^ 2 ∣ S 2 (2 * n) := by
  sorry

/-- Conjecture 1 with an extra factor $2$: $2n^2(2n+1)^2$ divides $S_2(2n)$ for every $n \ge 0$. -/
theorem conjecture_one_two (n : ℕ) : 2 * (n : ℤ) ^ 2 * (2 * n + 1) ^ 2 ∣ S 2 (2 * n) := by
  sorry

/-- Bala's FORMULA conjecture on OEIS A357559: $3\,a(2n) \equiv 0 \pmod{n^2(2n+1)^3}$ for every
$n \ge 0$, where $a = S_3$. -/
theorem formula_conjecture (n : ℕ) : (n : ℤ) ^ 2 * (2 * n + 1) ^ 3 ∣ 3 * S 3 (2 * n) := by
  sorry

/-- The FORMULA conjecture with an extra factor $2$: $2n^2(2n+1)^3$ divides $3S_3(2n)$ for every
$n \ge 0$. -/
theorem formula_conjecture_two (n : ℕ) :
    2 * (n : ℤ) ^ 2 * (2 * n + 1) ^ 3 ∣ 3 * S 3 (2 * n) := by
  sorry

end OeisA357559

end
