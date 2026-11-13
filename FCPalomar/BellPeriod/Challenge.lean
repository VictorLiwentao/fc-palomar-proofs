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
# Challenge: Bell numbers modulo a prime, periods (Touchard, Hall, Williams)

Written for this package; not copied from an existing formalization. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/54767.lean` (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`), in a pull request that will link this entry. Only that file's imports, attributes, test lemmas and unrelated declarations are left out here.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA54767

/-- The Bell numbers read modulo `p`. -/
def a (p n : ℕ) : ℕ := Nat.bell n % p

theorem bell_period :
    ∀ p : ℕ, p.Prime → ∀ n : ℕ, a p (n + (p ^ p - 1) / (p - 1)) = a p n := by
  sorry

theorem a146107 :
    ∀ n : ℕ, a 17 (n + 51702516367896047761) = a 17 n := by
  sorry

theorem a146109 :
    ∀ n : ℕ, a 19 (n + 109912203092239643840221) = a 19 n := by
  sorry

theorem a146113 :
    ∀ n : ℕ, a 23 (n + 949112181811268728834319677753) = a 23 n := by
  sorry

theorem a146119 :
    ∀ n : ℕ, a 29 (n + 91703076898614683377208150526107718802981) = a 29 n := by
  sorry

theorem a146121 :
    ∀ n : ℕ, a 31 (n + 568972471024107865287021434301977158534824481) = a 31 n := by
  sorry

end OeisA54767

end
