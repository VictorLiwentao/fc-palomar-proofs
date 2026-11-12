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
# Challenge: OEIS A265100, Jeffery's Conjectures 5, 1, 2 and 3

Copied verbatim from `FormalConjectures/OEIS/265100.lean` as added by the accompanying formal-conjectures PR (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`) (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA265100

/-- A005836 with offset 1: the `i`-th number whose base-3 expansion has no digit 2. -/
noncomputable def A005836 (i : ℕ) : ℕ := Nat.nth (fun m => ∀ k : ℕ, m / 3 ^ k % 3 ≠ 2) (i - 1)

/-- A265100 with offset 1: $a(n) = 9\,\mathrm{A005836}(n) + 5$. -/
noncomputable def a (n : ℕ) : ℕ := 9 * A005836 n + 5

/-- A block number: $n \ge 1$ with $C(n) \equiv 0$ and $C(n - 1) \not\equiv 0 \pmod 3$. -/
def IsBlockNumber (n : ℕ) : Prop := 1 ≤ n ∧ catalan n % 3 = 0 ∧ catalan (n - 1) % 3 ≠ 0

theorem conjecture5 :
    ∀ n : ℕ, catalan n % 3 = 0 ↔ (∃ k : ℕ, n / 3 ^ k % 3 = 2) ∧ ∃ k : ℕ, (n + 1) / 3 ^ k % 3 = 2 := by
  sorry

theorem conjecture1 :
    ∀ n : ℕ, IsBlockNumber n → ∃ i ≥ 1, a i = n := by
  sorry

theorem conjecture2 :
    ∀ m : ℕ, IsBlockNumber m → IsBlockNumber (3 * m - 1) := by
  sorry

theorem conjecture3 :
    ∀ n : ℕ, catalan n % 3 = 0 → catalan (3 * n - 1) % 3 = 0 := by
  sorry

end OeisA265100

end
