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
# Challenge: OEIS A101368, Chao's divisibility problem

Copied verbatim from `FormalConjectures/OEIS/101368.lean` as added by the accompanying formal-conjectures PR (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`) (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA101368

open PowerSeries

/-- The coefficient of $x^n$ in Stephan's generating function
$x(1 - 5x + 3x^2)/((1 - x)(1 - 5x + x^2))$. -/
noncomputable def c (n : ℕ) : ℚ :=
  coeff n (X * (1 - 5 * X + 3 * X ^ 2) * ((1 - X) * (1 - 5 * X + X ^ 2))⁻¹ : ℚ⟦X⟧)

theorem solutions_iff :
    ∀ i j : ℕ, (0 < i ∧ 0 < j ∧ i ∣ 1 + j + j ^ 2 ∧ j ∣ 1 + i + i ^ 2) ↔
      ∃ n : ℕ, 1 ≤ n ∧
        (((i : ℚ) = c n ∧ (j : ℚ) = c (n + 1)) ∨ ((j : ℚ) = c n ∧ (i : ℚ) = c (n + 1))) := by
  sorry

end OeisA101368

end
