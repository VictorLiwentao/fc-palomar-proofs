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
# Challenge: Erdős Problem 506, Segre's eight-point example

Copied verbatim from `FormalConjectures/ErdosProblems/506.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f`, and the notation `ℝ²` from `FormalConjecturesForMathlib/Geometry/2d.lean` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace Erdos506

open EuclideanGeometry

/--
The number of circles determined by a set of points `P` in the plane: the number of distinct
circles (spheres) passing through at least three of the points of `P`. (Three distinct points lie
on a common circle precisely when they are not collinear, so this counts exactly the circumcircles
of the non-collinear triples of `P`.)
-/
noncomputable def numCircles (P : Set ℝ²) : ℕ :=
  Set.ncard { s : Sphere ℝ² | 3 ≤ {p ∈ P | p ∈ s}.ncard }

/--
Segre's observation: the lower bound $\binom{n-1}{2}$ (without the correction of [PuSm]) is
already false for $n = 8$, as witnessed by the projection of a cube onto a plane. Hence the minimum
number of circles determined by $8$ such points is strictly less than $\binom{7}{2} = 21$.
-/
theorem erdos_506.variants.segre_n_eq_eight :
    ∃ P : Finset ℝ²,
      P.card = 8 ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
      numCircles (P : Set ℝ²) < (8 - 1).choose 2 := by
  sorry

end Erdos506

end
