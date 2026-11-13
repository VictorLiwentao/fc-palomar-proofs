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
# Challenge: OEIS A173774, Sun's integrality conjecture

Written for this package; not copied from an existing formalization. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/173774.lean` (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`), in a pull request that will link this entry. Only that file's imports, attributes, test lemmas and unrelated declarations are left out here.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA173774

/-- $a(n) = \frac{1}{n} \sum_{k=0}^{n-1} (21k+8)\binom{2k}{k}^3$, for $n \ge 1$. The sum is a
natural number and the division is in $\mathbb{Q}$. -/
def a (n : ℕ) : ℚ := ((∑ k ∈ Finset.range n, (21 * k + 8) * (2 * k).choose k ^ 3 : ℕ) : ℚ) / n

theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, a n = z ∧ 4 * ((2 * n).choose n : ℤ) ∣ z := by
  sorry

end OeisA173774

end
