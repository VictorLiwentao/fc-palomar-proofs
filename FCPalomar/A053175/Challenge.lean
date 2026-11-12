/-
Copyright 2026 The Formal Conjectures Authors.

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
# Challenge: OEIS A053175 Hankel determinants

The definitions `a` and `hankelMatrix` and the statement of `conjecture` are copied verbatim
from `FormalConjectures/OEIS/53175.lean` in google-deepmind/formal-conjectures at commit
`691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0).
Only the `FormalConjecturesUtil` import, the attributes, the test lemmas and the docstrings
are left out. The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA53175

/-- Catalan-Larcombe-French sequence. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 8
  | n + 2 =>
    let n' := n + 2
    let an1 := a (n + 1)
    let an2 := a n
    let term1 := 8 * (3 * n' ^ 2 - 3 * n' + 1) * an1
    let term2 := 128 * (n' - 1) ^ 2 * an2
    (term1 - term2) / (n' ^ 2)

/-- The $(n+1) \times (n+1)$ Hankel-type matrix with $(i,j)$-entry $a(i+j)$. -/
def hankelMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦ (a (i.val + j.val) : ℤ)

theorem conjecture (n : ℕ) :
    let detP := (hankelMatrix n).det
    let pow2 := (2 : ℤ) ^ (n * (n + 3))
    pow2 ∣ detP ∧ 0 < detP / pow2 ∧ (detP / pow2) % 2 = 1 := by
  sorry

end OeisA53175
