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
# Challenge: OEIS A190940, Oudra's conjecture

Written for this package; not copied from an existing formalization. The same declarations are proposed for Formal Conjectures as `FormalConjectures/OEIS/190940.lean` (on top of commit `691719db2653905d5fa0775408370fb058e4c59f`), in a pull request that will link this entry. Only that file's imports, attributes, test lemmas and unrelated declarations are left out here.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace OeisA190940

open Finset

/-- The partial sums of a composition: `c.sizeUpTo i` is the sum of the first `i` parts. -/
def partialSums {n : ℕ} (c : Composition n) : Finset ℕ :=
  (Finset.Icc 1 c.length).image c.sizeUpTo

/-- $\operatorname{lcm}(a, a+b, \ldots, n)$ for the composition $c = (a, b, \ldots)$ of $n$. -/
def lcmPartialSums {n : ℕ} (c : Composition n) : ℕ :=
  (partialSums c).lcm id

/-- The number of divisors of $\operatorname{lcm}(1, \ldots, n)/n$. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).lcm id / n).divisors.card

theorem card_lcmPartialSums :
    ∀ n : ℕ, 1 ≤ n → (Finset.univ.image (lcmPartialSums (n := n))).card = a n := by
  sorry

end OeisA190940

end
