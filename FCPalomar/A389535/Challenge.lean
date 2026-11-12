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
# Challenge: OEIS A389535, Hanna's conjecture (7)

Copied verbatim from `FormalConjectures/OEIS/389535.lean` as added by the accompanying formal-conjectures PR (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`) (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA389535

open PowerSeries

/-- The defining equation, normalized by $A(0) = 0$ and $a(1) = 1$. The normalization excludes
the solution $A = 0$. -/
def IsSolution (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ subst (X * A ^ 4 + X * A ^ 5) A = A ^ 5

theorem exists_unique_solution : ∃! A : ℚ⟦X⟧, IsSolution A := by
  sorry

theorem conjecture_seven (A : ℚ⟦X⟧) (hA : IsSolution A) :
    ∃ a : ℕ → ℤ, (∀ n, coeff n A = a n) ∧
      ∀ n, (5 : ℤ) ∣ coeff n (PowerSeries.mk a ^ 5) - (if 5 ∣ n then a (n / 5) else 0) := by
  sorry

end OeisA389535

end
