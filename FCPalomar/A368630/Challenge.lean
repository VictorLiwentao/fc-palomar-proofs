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
# Challenge: OEIS A368630, three congruences (Hanna's conjectures)

Copied verbatim from `FormalConjectures/OEIS/368630.lean` as added by the accompanying formal-conjectures PR (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`) (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open PowerSeries

namespace OeisA368630

/-- The rational exponential generating series of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- The defining equation for the integer EGF coefficients of OEIS A368630. -/
def IsGeneratingSequence (c : ℕ → ℤ) : Prop :=
  (egf c).constantCoeff = 1 ∧
    (egf c).subst (X * ((egf c)⁻¹) ^ 2) = (exp ℚ).subst (X * egf c)

/-- The integer coefficients of the normalized exponential generating function. -/
noncomputable def a : ℕ → ℤ := Classical.epsilon IsGeneratingSequence

/-- The original equation defines a unique integer coefficient sequence; see [Li26]. -/
theorem exists_unique_sequence : ∃! c : ℕ → ℤ, IsGeneratingSequence c := by
  sorry

/--
For every $n \ge 0$, "a(n) == 1 (mod 3)".
- Paul D. Hanna, Jan 02 2024.

Proved by Wentao Li with OpenAI Codex assistance; see [Li26].
-/
theorem conjecture_mod_three (n : ℕ) : a n % 3 = 1 := by
  sorry

/--
For every $n \ge 0$, "a(2*n) == 1 (mod 2)".
- Paul D. Hanna, Jan 02 2024.

Proved by Wentao Li with OpenAI Codex assistance; see [Li26].
-/
theorem conjecture_even (n : ℕ) : a (2 * n) % 2 = 1 := by
  sorry

/--
For every $n \ge 1$, "a(2*n+1) == 0 (mod 2)". The term $a(1)=1$ is excluded.
- Paul D. Hanna, Jan 02 2024.

Proved by Wentao Li with OpenAI Codex assistance; see [Li26].
-/
theorem conjecture_odd (n : ℕ) (hn : 1 ≤ n) : a (2 * n + 1) % 2 = 0 := by
  sorry

end OeisA368630

end
