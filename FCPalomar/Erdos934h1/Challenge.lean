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
# Challenge: Erdős Problem 934, the case t = 1

Copied verbatim from `FormalConjectures/ErdosProblems/934.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open Filter

namespace Erdos934

/-- The graph `G` has two edges at distance at least `t`: there are edges `uv` and `wx` of `G`
such that every vertex of `{u, v}` is at graph distance at least `t` from every vertex of
`{w, x}`, i.e. the shortest path between the two edges has length at least `t`. We use the
extended distance `SimpleGraph.edist`, so vertices in different components are at distance `⊤`.
For `1 ≤ t` the two edges are automatically distinct (indeed vertex-disjoint): `t = 1` means
vertex-disjoint edges and `t = 2` means an induced `2K₂`. Only `1 ≤ t` is intended. -/
def HasFarEdges {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ u v w x : V, G.Adj u v ∧ G.Adj w x ∧
    ∀ a ∈ ({u, v} : Set V), ∀ b ∈ ({w, x} : Set V), (t : ℕ∞) ≤ G.edist a b

/-- `h t d` is $h_t(d)$: the least `m` such that every graph with at least `m` edges and maximum
degree at most `d` contains two edges at distance at least `t`. As in [CCJK22] and [KMP26],
"at least `m` edges" is used, so `h t d - 1` is the largest number of edges of a graph with
maximum degree at most `d` in which any two edges are at distance less than `t`, i.e. whose line
graph has diameter at most `t`. Graphs on `Fin n` for arbitrary `n` cover all finite graphs. The
set is nonempty (for example `3 * d ^ t / 2 + 1` belongs to it by [CCJK22, Theorem 6]), so
`sInf` is a genuine minimum. -/
noncomputable def h (t d : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → HasFarEdges G t}

/--
It is easy to see that $h_t(d)\leq 2d^t$ always and $h_1(d)=d+1$.

The site (and [CCJK22, p. 1]) states $h_1(d)=d+1$ without restriction; it fails for $d=2$ (the
triangle has three pairwise intersecting edges, so $h_1(2)=4$), hence we assume $d\neq 2$.
-/
theorem erdos_934.variants.h_one : ∀ d : ℕ, d ≠ 2 → h 1 d = d + 1 := by
  sorry

end Erdos934

end
