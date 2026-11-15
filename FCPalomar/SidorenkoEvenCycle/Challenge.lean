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
# Challenge: Sidorenko's inequality for even cycles

Copied verbatim from `FormalConjectures/Wikipedia/SidorenkoConjecture.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f`, and `SimpleGraph.homCount` and `SimpleGraph.homDensity` from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/HomDensity.lean` at the same commit (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*}

/-- The number of graph homomorphisms `H → G`, as a natural number. For finite vertex
types this is just the cardinality of the `Hom` type. -/
noncomputable def homCount [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℕ :=
  Fintype.card (H →g G)

/-- The **homomorphism density** `t(H, G)` of a simple graph `H` in a simple graph `G` with
finite vertex sets is `#Hom(H, G) / |V(G)|^{|V(H)|}`. -/
noncomputable def homDensity [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℝ :=
  (homCount H G : ℝ) / (Fintype.card W : ℝ) ^ (Fintype.card V)

end SimpleGraph

open Finset SimpleGraph

namespace SidorenkoConjecture

variable {V W : Type*}

/--
**Case: even cycles `C_{2k}` (Sidorenko 1993).**

Sidorenko's inequality holds for every even cycle `C_{2k}` with `k ≥ 2`
(`cycleGraph (2 * k)`). Even cycles are bipartite; the `k = 2` case `C_4` coincides
with `K_{2,2}` (`sidorenko_K22`).

*Reference:* [Si93].
-/
theorem sidorenko_conjecture.variants.even_cycle (k : ℕ) (hk : 2 ≤ k)
    {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G := by
  sorry

end SidorenkoConjecture

end
