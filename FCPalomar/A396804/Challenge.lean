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
# Challenge: OEIS A396804, Hanna's mod 5 conjecture

Copied verbatim from `FormalConjectures/OEIS/396804.lean` as added by the accompanying formal-conjectures PR (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`) (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA396804

open PowerSeries

/-- The compositional iterate: `iterate A 0 = X` and `iterate A (k + 1) = A ∘ iterate A k`. -/
noncomputable def iterate (A : ℚ⟦X⟧) : ℕ → ℚ⟦X⟧
  | 0 => X
  | k + 1 => A.subst (iterate A k)

/-- The defining equation $A(x) = x \exp(A^{\circ 4}(x))$, normalized by $A(0) = 0$. -/
def IsSolution (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ A = X * (exp ℚ).subst (iterate A 4)

theorem exists_unique_solution : ∃! A : ℚ⟦X⟧, IsSolution A := by
  sorry

theorem conjecture_mod_five (A : ℚ⟦X⟧) (hA : IsSolution A) (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℤ, (n.factorial : ℚ) * coeff n A = m ∧ m % 5 ≠ 3 := by
  sorry

end OeisA396804

end
