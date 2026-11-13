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
# Challenge: OEIS A299754, Israel's formula at primes

Written for this package; not copied from an existing formalization. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/299754.lean` (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`), in a pull request that will link this entry. Only that file's imports, attributes, test lemmas and unrelated declarations are left out here.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA299754

/-- The set of sums $z_1 + \cdots + z_n$ of $n$ complex numbers with every $z_i^n = 1$. -/
def rootSums (n : ℕ) : Set ℂ :=
  {s | ∃ z : Fin n → ℂ, (∀ i, z i ^ n = 1) ∧ ∑ i, z i = s}

/-- The number of distinct such sums. -/
noncomputable def a (n : ℕ) : ℕ := (rootSums n).ncard

theorem a_prime (p : ℕ) (hp : p.Prime) : a p = (2 * p - 1).choose p := by
  sorry

end OeisA299754

end
