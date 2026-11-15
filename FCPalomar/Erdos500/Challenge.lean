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
# Challenge: Erdős Problem 500, Turán's lower bound for the tetrahedron

Copied verbatim from `FormalConjectures/ErdosProblems/500.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f`, and `Finset.ContainsCompleteHypergraph`, `Hypergraph.extremalNumber` and `Hypergraph.cliqueExtremalNumber` from `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace Finset

variable {V : Type*} [DecidableEq V]

/-- A copy of the complete `r`-uniform hypergraph on `k` vertices. -/
def ContainsCompleteHypergraph (H : Finset (Finset V)) (r k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k ∧ S.powersetCard r ⊆ H

end Finset

namespace Hypergraph

open scoped Classical in
/-- Maximum number of edges among `r`-uniform families satisfying `P` on `n` labeled vertices.
The value is zero if no family is admissible. -/
noncomputable def extremalNumber (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter P).sup Finset.card

/-- The extremal number forbidding a complete uniform hypergraph. -/
noncomputable def cliqueExtremalNumber (n r k : ℕ) : ℕ :=
  extremalNumber n r fun H ↦ ¬ H.ContainsCompleteHypergraph r k

end Hypergraph

open Filter Asymptotics
open scoped Topology

namespace Erdos500

/--
A problem of Turán. Turán observed that dividing the vertices into three equal parts
$X_1,X_2,X_3$, and taking the edges to be those triples that either have exactly one vertex in
each part or two vertices in $X_i$ and one vertex in $X_{i+1}$ (where $X_4=X_1$) shows that
$$\mathrm{ex}_3(n,K_4^3)\geq\left(\frac{5}{9}+o(1)\right)\binom{n}{3}.$$
-/
theorem erdos_500.variants.lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  sorry

end Erdos500

end
