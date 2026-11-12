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
# Challenge: Reconstruction conjectures: disconnected graphs, and the Lovász and Müller edge bounds

Copied verbatim from `FormalConjectures/Wikipedia/ReconstructionConjecture.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace ReconstructionConjecture

variable {V W : Type*}

/-- Two graphs are **hypomorphic** if there is a bijection `σ` between their vertex sets such
that the vertex-deleted subgraphs `G - v` and `H - σ v` are isomorphic for every vertex `v`;
i.e. `G` and `H` have the same deck of vertex-deleted subgraphs. -/
def Hypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)

/-- Two graphs are **edge-hypomorphic** if there is a bijection `σ` between their edge sets
such that the edge-deleted subgraphs `G - e` and `H - σ e` are isomorphic for every edge `e`;
i.e. `G` and `H` have the same deck of edge-deleted subgraphs. -/
def EdgeHypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
    Nonempty (G.deleteEdges {(e : Sym2 V)} ≃g H.deleteEdges {((σ e : H.edgeSet) : Sym2 W)})

/--
**Disconnected graphs are reconstructible.**

Every disconnected graph on at least three vertices is determined up to isomorphism by its
deck of vertex-deleted subgraphs; see [Bo91].
-/
theorem reconstruction_conjecture.variants.disconnected {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hd : ¬G.Connected) (h : Hypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/--
**Lovász (1972): graphs with more than half of all possible edges are edge-reconstructible.**

If a graph on `n` vertices has more than `n (n - 1) / 4` edges, then it is determined up to
isomorphism by its deck of edge-deleted subgraphs.

*Reference:* [Lo72].
-/
theorem edge_reconstruction_conjecture.variants.lovasz {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : (Fintype.card V).choose 2 < 2 * G.edgeSet.ncard)
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/--
**Müller (1977): graphs with many edges are edge-reconstructible.**

If a graph on `n` vertices with `m` edges satisfies `n! < 2 ^ (m - 1)`, then it is determined
up to isomorphism by its deck of edge-deleted subgraphs.

*Reference:* [Mu77].
-/
theorem edge_reconstruction_conjecture.variants.mueller {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1))
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

end ReconstructionConjecture

end
