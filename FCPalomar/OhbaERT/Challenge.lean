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
# Challenge: Ohba's conjecture, the Erdős–Rubin–Taylor case

Copied verbatim from `FormalConjectures/Wikipedia/OhbaConjecture.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open SimpleGraph Finset

namespace OhbaConjecture

variable {V : Type*}

/-- `G` is **`k`-choosable** if for every assignment `L` of a list of `k` colours to each
vertex there is a proper colouring `c` with `c v ∈ L v` for all `v`. -/
def Choosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) →
    ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/--
**Complete multipartite graphs with parts of size at most $2$ (Erdős–Rubin–Taylor 1979).**

The complete multipartite graph $K_{2,2,\dots,2}$ with $k$ parts has $2k$ vertices
and is $k$-choosable, as shown by Erdős, Rubin and Taylor.

*Reference:* [ERT79].
-/
theorem ohba_conjecture.variants.erdos_rubin_taylor (k : ℕ) :
    Choosable (completeMultipartiteGraph (fun _ : Fin k => Fin 2)) k := by
  sorry

end OhbaConjecture

end
