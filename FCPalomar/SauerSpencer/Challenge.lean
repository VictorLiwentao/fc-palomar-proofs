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
# Challenge: Bollobás–Eldridge–Catlin, the Sauer–Spencer packing theorem

Copied verbatim from `FormalConjectures/Paper/BollobasEldridgeCatlinConjecture.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open SimpleGraph

namespace BollobasEldridgeCatlinConjecture

variable {V : Type*}

/-- Two graphs `G₁`, `G₂` on the same finite vertex set **pack** if some permutation of the
vertices makes their edge sets disjoint. -/
def Packs (G₁ G₂ : SimpleGraph V) : Prop :=
  ∃ σ : Equiv.Perm V, ∀ u v, G₁.Adj u v → ¬ G₂.Adj (σ u) (σ v)

/--
**The Sauer–Spencer theorem (1978).**

If $2\Delta_1\Delta_2 < n$ then $G_1$ and $G_2$ pack.

*Reference:* [SS78].
-/
theorem bollobas_eldridge_catlin_conjecture.variants.sauer_spencer
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) : Packs G₁ G₂ := by
  sorry

end BollobasEldridgeCatlinConjecture

end
