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
# Challenge: the 1-2-3 conjecture, weights 1..5 (Kalkowski–Karoński–Pfender)

Copied verbatim from `FormalConjectures/Paper/OneTwoThreeConjecture.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open SimpleGraph Finset

namespace OneTwoThreeConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **weighted degree** of `v` under the edge weighting `w`: the sum of the weights of the
edges incident to `v`. -/
def weightedDegree (G : SimpleGraph V) [DecidableRel G.Adj] (w : Sym2 V → ℕ) (v : V) : ℕ :=
  ∑ e ∈ G.incidenceFinset v, w e

/-- An edge weighting `w` of `G` is **vertex-colouring** if adjacent vertices receive different
weighted degrees. -/
def IsVertexColouringWeighting (G : SimpleGraph V) [DecidableRel G.Adj] (w : Sym2 V → ℕ) : Prop :=
  ∀ u v, G.Adj u v → weightedDegree G w u ≠ weightedDegree G w v

/-- `G` has **no isolated edge**: no edge has both endpoints of degree `1` (equivalently, no
connected component is a single edge). -/
def NoIsolatedEdge (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v, G.Adj u v → 2 ≤ G.degree u ∨ 2 ≤ G.degree v

/--
**Kalkowski–Karoński–Pfender (2010): weights in $\{1, \dots, 5\}$ suffice.**

*Reference:* [KKP10].
-/
theorem one_two_three_conjecture.variants.one_to_five
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolatedEdge G) :
    ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 5) ∧
      IsVertexColouringWeighting G w := by
  sorry

/--
**Addario-Berry–Dalal–McDiarmid–Reed–Thomason (2007): weights in $\{1, \dots, 30\}$ suffice.**

*Reference:* [ABDMRT07]; see also the introduction of [KKP10].
-/
theorem one_two_three_conjecture.variants.one_to_thirty
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolatedEdge G) :
    ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 30) ∧
      IsVertexColouringWeighting G w := by
  sorry

end OneTwoThreeConjecture

end
