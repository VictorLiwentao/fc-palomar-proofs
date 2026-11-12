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
# Challenge: OEIS A396843, integral construction and oddness (Hanna's conjecture)

Copied verbatim from `FormalConjectures/OEIS/396843.lean` as added by the accompanying formal-conjectures PR (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`) (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open PowerSeries

namespace OeisA396843

/-- The normalized ordinary generating-function equation defining OEIS A396843. -/
def SourceEquation (A : PowerSeries ℤ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    A.subst (X * A - 3 * X * A ^ 2) = X ^ 2

/-- The normalized generating series of OEIS A396843. -/
noncomputable def series : PowerSeries ℤ := Classical.epsilon SourceEquation

/-- OEIS A396843, extended by $a(0)=0$ outside its offset-one domain. -/
noncomputable def a (n : ℕ) : ℤ := coeff n series

/-- The defining equation has a unique normalized integral solution; see [Li26]. -/
theorem source_existence : ∃! A : PowerSeries ℤ, SourceEquation A := by
  sorry

/--
"Conjecture: all terms are odd."
- Paul D. Hanna, Jul 01 2026.

An earlier Lean parity proof appears in `the-omega-institute/trureturing` PR #6773.
Wentao Li's formalization also proves integral existence and uniqueness; see [Li26].
AI assistance was used for development and verification.
-/
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : Odd (a n) := by
  sorry

end OeisA396843

end
