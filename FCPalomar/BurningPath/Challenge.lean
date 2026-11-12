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
# Challenge: the burning number of a path

Copied verbatim from `FormalConjectures/Paper/BurningNumberConjecture.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace BurningNumberConjecture

variable {V : Type*}

/-- The ball-cover condition for burning a graph: every vertex is reachable from some
centre `x i` at distance at most `k - 1 - i`. The centres may repeat or already be burning
when their round starts. For finite graphs, the least such `k` is the usual burning number
[BJR16, Corollary 3]. -/
def IsBurningSequence (G : SimpleGraph V) {k : ℕ} (x : Fin k → V) : Prop :=
  ∀ v, ∃ i, G.Reachable (x i) v ∧ G.dist (x i) v + (i : ℕ) < k

/-- The **burning number** `b(G)`: the least number of rounds needed to burn every vertex
of `G`. -/
noncomputable def burningNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ x : Fin k → V, IsBurningSequence G x}

/--
**Paths attain the conjectured bound** (Bonato–Janssen–Roshanbin [BJR16]).

The burning number of the path on `n ≥ 1` vertices is exactly `⌈√n⌉`, so the bound in the
burning number conjecture cannot be improved.
-/
theorem burning_number_conjecture.variants.path (n : ℕ) (hn : 1 ≤ n) :
    burningNumber (SimpleGraph.pathGraph n) = ⌈Real.sqrt n⌉₊ := by
  sorry

end BurningNumberConjecture

end
