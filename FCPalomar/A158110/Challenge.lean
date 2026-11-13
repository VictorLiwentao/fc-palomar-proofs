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
# Challenge: OEIS A158110, Hanna's integrality conjecture

Written for this package; not copied from an existing formalization. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/158110.lean` (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`), in a pull request that will link this entry. Only that file's imports, attributes, test lemmas and unrelated declarations are left out here.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA158110

open PowerSeries

/-- The series $\sum_{n \ge 1} q^{n^m} x^n / n$ over $\mathbb{Q}$. The sum starts at $n = 1$,
so the exponent $n^m$ is at least $1$ and $0^0$ never occurs. -/
noncomputable def logSeries (q m : ℕ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (q : ℚ) ^ (n ^ m) / n

theorem conjecture (q m n : ℕ) : ∃ z : ℤ, coeff n (subst (logSeries q m) (exp ℚ)) = z := by
  sorry

end OeisA158110

end
