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
# Challenge: Gowers–Long, the square-size lower bound F(n) ≥ n^{3/2}

Copied verbatim from `FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out. The namespace `Arxiv.«1609.08688»` is renamed `Arxiv1609_08688`, because Palomar requires plain identifier components in declaration names.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace Arxiv1609_08688

/--
Let $a = (a_1, a_2, a_3)$ and $b = (b_1, b_2, b_3)$ be two triples of integers.
Say that $a$ is $2$-less than $b$, or $a <_2 b$, if $a_i < b_i$ for at least
two coordinates $i$.
-/
def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

/--
Since the $2$-less relation is not transitive, we make a further definition to
specify transivity.
-/
def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop := s.Pairwise lt₂

/--
Let $F(n)$ be the maximal length of a $2$-increasing sequence of triples with each coordinate
belong to $[n]$ ($= \{1, 2, ..., n\}$).
-/
noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

local notation "F" => maximalLength

/-- Moreover, whenever $n$ is a perfect square we have $F(n) \geq n^{3/2}$. -/
theorem maximalLength_ge_of_isSquare {n : ℕ} (h : IsSquare n) :
    n.sqrt ^ 3 ≤ F n := by
  sorry

end Arxiv1609_08688

end
