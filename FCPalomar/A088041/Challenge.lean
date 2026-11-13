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
# Challenge: OEIS A088041, Israel's formula and Barker's recurrence

Written for this package; not copied from an existing formalization. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/88041.lean` (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`), in a pull request that will link this entry. Only that file's imports, attributes, test lemmas and unrelated declarations are left out here.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA88041

/-- The `k > 1` such that `k⁴ - 1` is divisible by `mⁿ` for some `m > 1`. -/
def S (n : ℕ) : Set ℕ := {k | 1 < k ∧ ∃ m, 1 < m ∧ m ^ n ∣ k ^ 4 - 1}

/-- The sequence: the least such `k`. -/
noncomputable def a (n : ℕ) : ℕ := sInf (S n)

theorem isLeast_S (n : ℕ) (hn : 4 ≤ n) : IsLeast (S n) (2 ^ (n - 2) - 1) := by
  sorry

theorem a_recurrence (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2) := by
  sorry

end OeisA88041

end
