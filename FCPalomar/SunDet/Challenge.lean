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
# Challenge: Sun's determinants det[(i−j)^m + δ_ij] for m = 1, 2, 3

Copied verbatim from `FormalConjectures/OEIS/79034.lean` as added by the accompanying formal-conjectures PR (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`) (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA79034

/-- The matrix $[(i-j)^m + \delta_{ij}]_{1 \le i,j \le n}$. -/
def M (m n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (((i : ℕ) + 1 : ℤ) - ((j : ℕ) + 1 : ℤ)) ^ m + if i = j then 1 else 0

/-- The polynomial of A355326, Conjecture 1. -/
def P (x : ℚ) : ℚ :=
  x ^ 6 - 19 * x ^ 5 + 123 * x ^ 4 - 337 * x ^ 3 + 12376 * x ^ 2 - 44144 * x + 40000

theorem det_one :
    ∀ n : ℕ, ((M 1 n).det : ℚ) = ((n : ℚ) ^ 4 - (n : ℚ) ^ 2 + 12) / 12 := by
  sorry

theorem det_two :
    ∀ n : ℕ, ((M 2 n).det : ℚ) = ((n : ℚ) ^ 2 - 4) * ((n : ℚ) ^ 2 + 2 * n + 3) *
      ((n : ℚ) ^ 5 - 2 * (n : ℚ) ^ 4 - (n : ℚ) ^ 3 - 28 * (n : ℚ) ^ 2 + 60 * n - 90) / 1080 := by
  sorry

theorem det_three :
    ∀ n : ℕ, ((M 3 n).det : ℚ) = 1 + P ((n : ℚ) ^ 2) * (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) / 672000 := by
  sorry

end OeisA79034

end
