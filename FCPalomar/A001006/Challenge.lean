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
# Challenge: OEIS A001006, Motzkin numbers at p − 2 (Burns, Kohen)

Written for this package; not copied from an existing formalization. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/1006.lean` (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`), in a pull request that will link this entry. Only that file's imports, attributes, test lemmas and unrelated declarations are left out here.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA1006

/-- The coefficient form of $A(x) = 1 + x A(x) + x^2 A(x)^2$: $a(0) = a(1) = 1$ and
$a(n+2) = a(n+1) + \sum_{i+j=n} a(i) a(j)$. -/
def IsMotzkin (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 1 ∧ ∀ n, a (n + 2) = a (n + 1) + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, a x.1 * a x.2

theorem prime_dvd_iff :
    (∃ a, IsMotzkin a) ∧ ∀ a, IsMotzkin a → ∀ p : ℕ, p.Prime →
      (p ∣ a (p - 2) ↔ p % 3 = 1) ∧ (p % 6 = 5 → (a (p - 2) : ZMod p) = -1) := by
  sorry

end OeisA1006

end
