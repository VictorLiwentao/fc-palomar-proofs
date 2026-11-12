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
# Challenge: OEIS A014442, Kaltman's conjecture

Copied verbatim from `FormalConjectures/OEIS/14442.lean` as added by the accompanying formal-conjectures PR (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`) (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA14442

/-- $a(n)$ is the largest prime factor of $n^2 + 1$ (offset 1; `a 0 = 0`). -/
def a (n : ℕ) : ℕ := (n ^ 2 + 1).primeFactors.sup id

theorem kaltman :
    ∀ p : ℕ, p.Prime → p % 4 = 1 →
      ((Finset.Icc 1 p).filter fun n => a n = p).card = 2 ∧
      ∀ i j : ℕ, 1 ≤ i → i < p → 1 ≤ j → j < p → i ≠ j → a i = p → a j = p →
        i + j = p ∧ i * j % p = 1 := by
  sorry

end OeisA14442

end
