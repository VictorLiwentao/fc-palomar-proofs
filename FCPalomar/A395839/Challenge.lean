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
# Challenge: OEIS A395839, Hanna's two conjectures

Written for this package; not copied from an existing formalization. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/395839.lean` (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`), in a pull request that will link this entry. Only that file's imports, attributes, test lemmas and unrelated declarations are left out here.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA395839

open PowerSeries

/-- The equation for the Catalan g.f.: $C = 1 + x C^2$. -/
def IsCatalanEquation (G : ℤ⟦X⟧) : Prop := G = 1 + X * G ^ 2

/-- The coefficients of $10 C^2 - C$. -/
noncomputable def coeffs (G : ℤ⟦X⟧) (n : ℕ) : ℤ := coeff n (10 * G ^ 2 - G)

theorem odd_iff :
    (∃! G : ℤ⟦X⟧, IsCatalanEquation G) ∧
      ∀ G : ℤ⟦X⟧, IsCatalanEquation G → ∀ n, Odd (coeffs G n) ↔ ∃ k, n = 2 ^ k - 1 := by
  sorry

theorem mod_three :
    (∃! G : ℤ⟦X⟧, IsCatalanEquation G) ∧
      ∀ G : ℤ⟦X⟧, IsCatalanEquation G → ∀ n, coeffs G (3 * n + 1) ≡ (catalan n : ℤ) [ZMOD 3] ∧
        coeffs G (3 * n) ≡ 0 [ZMOD 3] ∧ coeffs G (3 * n + 2) ≡ 0 [ZMOD 3] := by
  sorry

end OeisA395839

end
