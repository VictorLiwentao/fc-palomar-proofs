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
# Challenge: OEIS A000262 and A082579, Bala's Theorem 1

Written for this package; not copied from an existing formalization. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/262.lean` (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`), in a pull request that will link this entry. Only that file's imports, attributes, test lemmas and unrelated declarations are left out here.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA262

open PowerSeries

/-- The rational e.g.f. $\sum a(n) x^n / n!$ of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- $k \mid a(n + k) - a(n)$ for every $k \ge 2$ and every $n$. -/
def PeriodicModAll (a : ℕ → ℤ) : Prop :=
  ∀ n k : ℕ, 2 ≤ k → a (n + k) ≡ a n [ZMOD k]

theorem bala_theorem1 :
    ∀ F G : ℤ⟦X⟧, constantCoeff G = 1 → ∀ a : ℕ → ℤ,
      egf a = map (Int.castRingHom ℚ) F * (exp ℚ).subst (X * map (Int.castRingHom ℚ) G) →
        ∀ n k : ℕ, a (n + k) ≡ a n [ZMOD k] := by
  sorry

theorem a000262 :
    (∃! a : ℕ → ℤ, egf a = (exp ℚ).subst (X * (1 - X)⁻¹)) ∧
      ∀ a : ℕ → ℤ, egf a = (exp ℚ).subst (X * (1 - X)⁻¹) → PeriodicModAll a := by
  sorry

theorem a082579 :
    (∃! a : ℕ → ℤ, egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)) ∧
      ∀ a : ℕ → ℤ, egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹) → PeriodicModAll a := by
  sorry

end OeisA262

end
