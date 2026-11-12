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
# Challenge: Erdős Problem 712, the graph case (Turán)

Copied verbatim from `FormalConjectures/ErdosProblems/712.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f`, and `Finset.ContainsCompleteHypergraph`, `Hypergraph.extremalNumber` and `Hypergraph.cliqueExtremalNumber` from `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
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

namespace Erdos712

/-- Turán's theorem gives the graph case:
$\mathrm{ex}_2(n,K_k)/\binom{n}{2}\to 1-1/(k-1)$. -/
theorem erdos_712.variants.graph_case (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / n.choose 2)
      atTop (𝓝 (1 - 1 / ((k : ℝ) - 1))) := by
  sorry

/-- With denominator $n^2$, Turán's graph limit is
$\frac12(1-1/(k-1))$. The factor $\frac12$ comes from the normalization. -/
theorem erdos_712.variants.graph_case_div_sq (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 ((1 / 2) * (1 - 1 / ((k : ℝ) - 1)))) := by
  sorry

end Erdos712

end
