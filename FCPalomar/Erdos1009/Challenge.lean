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
# Challenge: Erdős Problem 1009, Sauer's example

Copied verbatim from `FormalConjectures/ErdosProblems/1009.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace Erdos1009

/--
Sauer gave an example of a graph on $n$ vertices with $\lfloor n^2/4\rfloor+2n-6$ many edges
which contains only $2n-7$ many edge disjoint triangles: if $n=2r+4$ then $G$ is the complete
tripartite graph on $[r]\times [r]\times [4]$, with a $K_4$ on the $[4]$ vertices also.
-/
theorem erdos_1009.variants.sauer : ∀ r : ℕ, 1 ≤ r → ∃ G : SimpleGraph (Fin (2 * r + 4)),
    G.edgeSet.ncard = (2 * r + 4) ^ 2 / 4 + 2 * (2 * r + 4) - 6 ∧
      ∀ T : Finset (Finset (Fin (2 * r + 4))), (∀ t ∈ T, G.IsNClique 3 t) →
        (T : Set (Finset (Fin (2 * r + 4)))).Pairwise (fun s t => (s ∩ t).card ≤ 1) →
          T.card ≤ 2 * (2 * r + 4) - 7 := by
  sorry

end Erdos1009

end
