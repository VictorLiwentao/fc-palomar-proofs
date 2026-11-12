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
# Challenge: Erdős Problem 1111, Wagon's bound

Copied verbatim from `FormalConjectures/ErdosProblems/1111.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace Erdos1111

/-- Two sets `A` and `B` of vertices of `G` are *anticomplete* if they are disjoint and `G` has
no edge between `A` and `B`. -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

/--
El-Zahar and Erdős note that a result of Wagon [Wa80b] implies $d(t,2)\leq \binom{t}{2}+1$, where
$d(t,c)$ is the minimal $d$ in the problem.
-/
theorem erdos_1111.variants.wagon (t : ℕ) :
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      ((t.choose 2 + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
        ∃ A B : Set V, Anticomplete G A B ∧
          2 ≤ (G.induce A).chromaticNumber ∧ 2 ≤ (G.induce B).chromaticNumber := by
  sorry

end Erdos1111

end
