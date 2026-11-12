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
# Solution: the Gowers–Long square-size lower bound

This file proves the lower bound $F(m^2) \ge m^3$ from Proposition 1.4 of W. T. Gowers and
J. Long, *The length of an $s$-increasing sequence of $r$-tuples*,
[arXiv:1609.08688](https://arxiv.org/abs/1609.08688). For digits $a, b, c < m$ it lists the
triples $(am + b + 1, am + c + 1, bm + c + 1)$ in lexicographic order of $(a, b, c)$; any two of
them differ upward in two coordinates.

The bound $F(n) \le n^2$ that makes the supremum finite uses the pigeonhole lemma
`exists_pair_of_mem_Icc` from the Formal Conjectures file (DeepMind PR 4207, ChakshuGupta13) and
follows the proof pattern of DeepMind PR 4616 (MiskinAleksandr23).

An earlier Lean proof of this bound is in
[weiyangzen/awesome_theorems](https://github.com/weiyangzen/awesome_theorems/blob/32e5f75412a804463a0b0c6fff1362d4ab5275b3/Formalizations/Lean/AwesomeTheorems/Stage5/Theorems/S5_CLM_00003491/Proof.lean).
An October 2026 version of the present proof adapted its block lemmas. This version replaces
that code with new proofs of the construction.
-/

@[expose] public section

namespace Arxiv.«1609.08688»

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

end Arxiv.«1609.08688»

namespace Arxiv.«1609.08688»

local infix:50 " <₂ " => lt₂

/- `not_lt₂`, `not_lt₂_of_exists`, `isIncreasing₂_const_length` and `exists_pair_of_mem_Icc` are copied from the same Formal Conjectures file, with the
repository-specific `category` and `AMS` attributes removed. -/

@[simp]
theorem not_lt₂ {α : Type*} [LinearOrder α] {a b : Fin 3 → α} :
    ¬a <₂ b ↔ ∀ i j, i ≠ j → a i < b i → b j ≤ a j := by simp [lt₂]

theorem not_lt₂_of_exists {α : Type*} [LinearOrder α] {a b : Fin 3 → α}
    (i j : Fin 3) (hij : i ≠ j) (hi : b i ≤ a i) (hj : b j ≤ a j) :
    ¬a <₂ b := by
  refine not_lt₂.2 fun k l hkl h => ?_
  have : k ≠ i := fun hk => not_lt.2 hi (hk ▸ h)
  have : k ≠ j := fun hk => not_lt.2 hj (hk ▸ h)
  have : l = i ∨ l = j := by omega
  rcases this with (rfl | rfl); exact hi; exact hj

theorem isIncreasing₂_const_length {α : Type*} [LinearOrder α] {val : α} {s : List (Fin 3 → α)}
    (h : IsIncreasing₂ s)
    (h_const : ∀ a ∈ s, ∀ j, a j = val) : s.length < 2 := by
  by_contra!
  obtain ⟨i, j, -, hi, -⟩ :=
    List.pairwise_iff_getElem.1 h 0 1 (by linarith) (by linarith) zero_lt_one
  rw [h_const _ (List.getElem_mem _) i, h_const _ (List.getElem_mem _) i] at hi
  exact lt_irrefl _ hi

/-- In a set of more than $n^2$ triples with coordinates from $\{1, ..., n\}$ we must
have two triples that are equal in their first two coordinates. -/
lemma exists_pair_of_mem_Icc {s : List (Fin 3 → ℕ)} {n : ℕ} (_hn : 2 ≤ n)
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : s.length > n ^ 2) :
    ∃ (i j : Fin s.length), i ≠ j ∧ s[i] 0 = s[j] 0 ∧ s[i] 1 = s[j] 1 := by
  classical
  let f : Fin s.length → ℕ × ℕ := fun k => (s[k] 0, s[k] 1)
  let t : Finset (ℕ × ℕ) := Finset.Icc 1 n ×ˢ Finset.Icc 1 n
  have ht_card : t.card < (Finset.univ : Finset (Fin s.length)).card := by
    simp only [t, Finset.card_univ, Fintype.card_fin, Finset.card_product,
      Nat.card_Icc, Nat.add_sub_cancel, ← sq]
    exact hs₂
  have hf : ∀ k ∈ (Finset.univ : Finset (Fin s.length)), f k ∈ t := by
    intro k _
    have hmem : s[k] ∈ s := List.getElem_mem k.isLt
    have h0 := hs₁ _ hmem ⟨0, rfl⟩
    have h1 := hs₁ _ hmem ⟨1, rfl⟩
    rw [Set.mem_Icc] at h0 h1
    simp only [t, f, Finset.mem_product, Finset.mem_Icc]
    exact ⟨h0, h1⟩
  obtain ⟨i, _, j, _, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to ht_card hf
  exact ⟨i, j, hij, congrArg Prod.fst hfij, congrArg Prod.snd hfij⟩

end Arxiv.«1609.08688»

namespace GowersLongLowerBound

open Arxiv.«1609.08688»

/-! ### Two-digit numbers in base `m` -/

/-- If `y < m` and `x < x'`, then the two-digit number `x m + y` is below `x' m + y'`. -/
theorem digits_lt {m x x' y y' : ℕ} (hy : y < m) (hx : x < x') :
    x * m + y < x' * m + y' :=
  calc x * m + y < x * m + m := Nat.add_lt_add_left hy _
    _ = (x + 1) * m := (Nat.succ_mul x m).symm
    _ ≤ x' * m := Nat.mul_le_mul_right m hx
    _ ≤ x' * m + y' := Nat.le_add_right _ _

/-- A two-digit number with digits below `m`, shifted by one, lies in `{1, …, m²}`. -/
theorem digits_mem_Icc {m x y : ℕ} (hx : x < m) (hy : y < m) :
    x * m + y + 1 ∈ Set.Icc 1 (m ^ 2) := by
  have h := digits_lt (y' := 0) hy hx
  rw [Nat.add_zero, ← pow_two] at h
  exact ⟨Nat.le_add_left 1 _, h⟩

/-! ### The Gowers–Long triples -/

/-- The triple attached to the digits `(a, b, c)`. -/
def triple (m a b c : ℕ) : Fin 3 → ℕ :=
  ![a * m + b + 1, a * m + c + 1, b * m + c + 1]

theorem triple_lt₂_of_first {m a b c a' b' c' : ℕ} (hb : b < m) (hc : c < m) (ha : a < a') :
    lt₂ (triple m a b c) (triple m a' b' c') :=
  ⟨0, 1, by decide, Nat.succ_lt_succ (digits_lt hb ha), Nat.succ_lt_succ (digits_lt hc ha)⟩

theorem triple_lt₂_of_second {m a b c b' c' : ℕ} (hc : c < m) (hb : b < b') :
    lt₂ (triple m a b c) (triple m a b' c') :=
  ⟨0, 2, by decide, Nat.succ_lt_succ (Nat.add_lt_add_left hb _),
    Nat.succ_lt_succ (digits_lt hc hb)⟩

theorem triple_lt₂_of_third {m a b c c' : ℕ} (hc : c < c') :
    lt₂ (triple m a b c) (triple m a b c') :=
  ⟨1, 2, by decide, Nat.succ_lt_succ (Nat.add_lt_add_left hc _),
    Nat.succ_lt_succ (Nat.add_lt_add_left hc _)⟩

/-- A list built block by block over `0, …, m - 1` is pairwise related when every block is,
and every element of an earlier block is related to every element of a later one. -/
theorem pairwise_flatMap_of_lt {α : Type*} {R : α → α → Prop} (m : ℕ) (f : ℕ → List α)
    (inner : ∀ i < m, (f i).Pairwise R)
    (outer : ∀ i j, i < j → j < m → ∀ x ∈ f i, ∀ y ∈ f j, R x y) :
    ((List.range m).flatMap f).Pairwise R := by
  rw [List.pairwise_flatMap]
  constructor
  · intro i hi
    exact inner i (List.mem_range.1 hi)
  · have hlt : (List.range m).Pairwise (fun i j => i < j ∧ j < m) :=
      (List.pairwise_lt_range (n := m)).imp_of_mem fun {_ j} _ hj hij =>
        ⟨hij, List.mem_range.1 hj⟩
    exact hlt.imp fun {i j} h => outer i j h.1 h.2

/-- The $m^3$ triples in lexicographic order of their digits. -/
def squareSequence (m : ℕ) : List (Fin 3 → ℕ) :=
  (List.range m).flatMap fun a =>
    (List.range m).flatMap fun b =>
      (List.range m).map fun c => triple m a b c

theorem mem_squareSequence {m : ℕ} {t : Fin 3 → ℕ} :
    t ∈ squareSequence m ↔ ∃ a < m, ∃ b < m, ∃ c < m, triple m a b c = t := by
  simp [squareSequence]

theorem squareSequence_length (m : ℕ) : (squareSequence m).length = m ^ 3 := by
  simp [squareSequence, List.length_flatMap, pow_succ, Nat.mul_assoc]

theorem squareSequence_range (m : ℕ) :
    ∀ t ∈ squareSequence m, Set.range t ⊆ Set.Icc 1 (m ^ 2) := by
  intro t ht
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_squareSequence.1 ht
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact digits_mem_Icc ha hb
  · exact digits_mem_Icc ha hc
  · exact digits_mem_Icc hb hc

theorem squareSequence_isIncreasing₂ (m : ℕ) : IsIncreasing₂ (squareSequence m) := by
  unfold IsIncreasing₂ squareSequence
  refine pairwise_flatMap_of_lt m _ (fun a _ => ?_) ?_
  · refine pairwise_flatMap_of_lt m _ (fun b _ => ?_) ?_
    · rw [List.pairwise_map]
      exact (List.pairwise_lt_range (n := m)).imp fun h => triple_lt₂_of_third h
    · intro b b' hbb' _ x hx y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      obtain ⟨c', -, rfl⟩ := List.mem_map.1 hy
      exact triple_lt₂_of_second (List.mem_range.1 hc) hbb'
  · intro a a' haa' _ x hx y hy
    obtain ⟨b, hb, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b', -, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨c', -, rfl⟩ := List.mem_map.1 hy
    exact triple_lt₂_of_first (List.mem_range.1 hb) (List.mem_range.1 hc) haa'

/-! ### The supremum is attained -/

/-- Every $2$-increasing sequence in $[n]^3$ has at most $n^2$ terms. -/
theorem length_le_square {n : ℕ} {s : List (Fin 3 → ℕ)}
    (hs_range : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs_inc : IsIncreasing₂ s) :
    s.length ≤ n ^ 2 := by
  by_cases hn : 2 ≤ n
  · by_contra hle
    obtain ⟨i, j, hij, h0, h1⟩ :=
      exists_pair_of_mem_Icc hn hs_range (Nat.lt_of_not_ge hle)
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.ge h1.ge)
        (List.pairwise_iff_get.1 hs_inc i j hij)
    · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.le h1.le)
        (List.pairwise_iff_get.1 hs_inc j i hji)
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · cases s with
      | nil => simp
      | cons a s =>
        have h0 := hs_range a List.mem_cons_self ⟨0, rfl⟩
        simp at h0
    · have hs_const : ∀ a ∈ s, ∀ i, a i = 1 := by
        intro a ha i
        simpa using hs_range a ha ⟨i, rfl⟩
      have := isIncreasing₂_const_length hs_inc hs_const
      simpa using Nat.le_of_lt_succ this

/-- For each $m$, the construction gives $m^3 \le F(m^2)$. -/
theorem cube_le_maximalLength_square (m : ℕ) : m ^ 3 ≤ maximalLength (m ^ 2) := by
  unfold maximalLength
  apply le_csSup
  · refine ⟨(m ^ 2) ^ 2, ?_⟩
    rintro _ ⟨s, hs_range, hs_inc, rfl⟩
    exact length_le_square hs_range hs_inc
  · exact ⟨squareSequence m, squareSequence_range m,
      squareSequence_isIncreasing₂ m, squareSequence_length m⟩

/-- For every natural perfect square $n$, $\lfloor\sqrt n\rfloor^3 \leq F(n)$. -/
theorem maximalLength_ge_of_isSquare {n : ℕ} (h : IsSquare n) :
    n.sqrt ^ 3 ≤ maximalLength n := by
  obtain ⟨m, rfl⟩ := h
  simpa [pow_two] using cube_le_maximalLength_square m

end GowersLongLowerBound

namespace Arxiv.«1609.08688»

local notation "F" => maximalLength

theorem maximalLength_ge_of_isSquare {n : ℕ} (h : IsSquare n) :
    n.sqrt ^ 3 ≤ F n :=
  GowersLongLowerBound.maximalLength_ge_of_isSquare h

end Arxiv.«1609.08688»

end
