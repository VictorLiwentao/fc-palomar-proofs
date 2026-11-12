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
# Challenge: OEIS A113052 and A113047, Barry's conjecture

Copied verbatim from `FormalConjectures/OEIS/113052.lean` as added by the accompanying formal-conjectures PR (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`) (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA113052

open scoped Classical

theorem conjecture :
    ∀ p : ℕ, p.Prime → ∀ n : ℕ, ∃ c : ℕ,
      (c : ℚ) = (Nat.choose (p * n) n : ℚ) / (((p : ℚ) - 1) * n + 1) ∧
        c % p = if ∃ k : ℕ, (n : ℚ) = ((p : ℚ) ^ k - 1) / ((p : ℚ) - 1) then 1 else 0 := by
  sorry

theorem a113047 :
    ∀ n : ℕ, ∃ c : ℕ, (c : ℚ) = (Nat.choose (3 * n) n : ℚ) / (2 * n + 1) ∧
      c % 3 = if ∃ j : ℕ, (n : ℚ) = ((3 : ℚ) ^ j - 1) / 2 then 1 else 0 := by
  sorry

end OeisA113052

end
