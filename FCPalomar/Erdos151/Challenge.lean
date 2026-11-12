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
# Challenge: Erdős Problem 151, the triangle-free and square-root bounds

Copied verbatim from `FormalConjectures/ErdosProblems/151.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f`, and `SimpleGraph.IsBigMaximalClique`, `SimpleGraph.IsCliqueTransversal` and `SimpleGraph.cliqueTransversalNumber` from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

open Finset List

/-- `s` is a maximal clique of `G` with at least two vertices. -/
def IsBigMaximalClique (G : SimpleGraph V) (s : Finset V) : Prop :=
  Maximal (fun t : Finset V ↦ G.IsClique (t : Set V)) s ∧ 2 ≤ s.card

/-- `T` meets every maximal clique of `G` with at least two vertices. -/
def IsCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ s, G.IsBigMaximalClique s → ∃ v ∈ s, v ∈ T

/-- The clique transversal number $\tau(G)$: the minimal number of vertices that meet every
maximal clique of `G` with at least two vertices, so isolated vertices are not counted. -/
noncomputable def cliqueTransversalNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ T : Finset V, G.IsCliqueTransversal T ∧ T.card = k}

end SimpleGraph

namespace Erdos151

open SimpleGraph

/-- $H(n)$: the largest `k` such that every triangle-free graph on `n` vertices contains an
independent set on `k` vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}

/--
If $G$ is triangle-free, then $\tau(G)\leq n-H(n)$: the complement of an independent set meets
every edge.
-/
theorem erdos_151.variants.cliqueFree_three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNumber G ≤ n - H n := by
  sorry

/--
It is easy to see that $\tau(G)\leq n-\sqrt{n}$. We state this with $\lfloor\sqrt{n}\rfloor$:
with the real square root the bound fails for a single edge ($n = 2$, $\tau = 1$).
-/
theorem erdos_151.variants.sqrt_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueTransversalNumber G ≤ n - Nat.sqrt n := by
  sorry

end Erdos151

end
