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
# Sauer's example for Erdős Problem 1009

This file proves the upstream statement `Erdos1009.erdos_1009.variants.sauer`: for every `r ≥ 1`
there is a graph on `n = 2r + 4` vertices with $\lfloor n^2/4 \rfloor + 2n - 6$ edges in which every
family of edge-disjoint triangles has at most $2n - 7$ members.

The graph is Sauer's: split the vertices into $A$, $B$ (size $r$) and $C$ (size $4$), join every
two vertices in different parts, and add all six edges inside $C$. It has $r^2 + 8r + 6$ edges
(`card_edgeFinset_sauerGraph`, from the degree sum).

Bound (`card_le_of_edgeDisjoint`). $A \cup B$ spans a bipartite graph, so every triangle meets
$C$. Two triangles inside $C$ share two vertices, so at most one triangle of the family lies in
$C$. Every other triangle $t$ has exactly two pairs $(u, c)$ with $u \in t \setminus C$,
$c \in t \cap C$. Edge-disjoint triangles have disjoint sets of such pairs, and there are
$|A \cup B| \cdot |C| = 8r$ pairs in all. So the family has at most $4r + 1 = 2n - 7$ members.

*References:*
* [erdosproblems.com/1009](https://www.erdosproblems.com/1009)
* Győri, E. (1988). "On the number of edge-disjoint triangles in graphs of given size."
-/

@[expose] public section

namespace Erdos1009Sauer

open Finset SimpleGraph

/-- The part of a vertex: `0` for `A`, `1` for `B`, `2` for `C`. -/
def part (r i : ℕ) : ℕ := if i < r then 0 else if i < 2 * r then 1 else 2

lemma part_lt_two {r i : ℕ} (h : i < 2 * r) : part r i < 2 := by
  unfold part
  split_ifs <;> omega

lemma part_eq_two {r i : ℕ} (h : 2 * r ≤ i) : part r i = 2 := by
  unfold part
  split_ifs <;> omega

/-- Sauer's graph: complete tripartite on `A, B, C` plus `K₄` on `C`. -/
def sauerGraph (r : ℕ) : SimpleGraph (Fin (2 * r + 4)) where
  Adj i j := i ≠ j ∧ (part r i ≠ part r j ∨ part r i = 2)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by have h2 := h.2; omega⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (r : ℕ) : DecidableRel (sauerGraph r).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ (part r i ≠ part r j ∨ part r i = 2)))

lemma sauerGraph_adj {r : ℕ} {i j : Fin (2 * r + 4)} :
    (sauerGraph r).Adj i j ↔ i ≠ j ∧ (part r i ≠ part r j ∨ part r i = 2) := Iff.rfl

/- Edge count. -/

lemma card_filter_fin (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun j : Fin n => P j).card = ((range n).filter P).card := by
  rw [← card_map Fin.valEmbedding]
  congr 1
  ext m
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.isLt, hj⟩
  · rintro ⟨hm, hP⟩
    exact ⟨⟨m, hm⟩, hP, rfl⟩

lemma degree_sauerGraph (r : ℕ) (i : Fin (2 * r + 4)) :
    (sauerGraph r).degree i = if (i : ℕ) < 2 * r then r + 4 else 2 * r + 3 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  split_ifs with h
  · have hpi := part_lt_two h
    have hfil : (univ.filter ((sauerGraph r).Adj i)) =
        univ.filter fun j : Fin (2 * r + 4) => part r j ≠ part r i := by
      refine filter_congr fun j _ => ?_
      rw [sauerGraph_adj]
      constructor
      · rintro ⟨-, h1 | h1⟩ <;> omega
      · intro h1
        exact ⟨fun hij => h1 (hij ▸ rfl), Or.inl (Ne.symm h1)⟩
    rw [hfil, card_filter_fin (2 * r + 4) fun m => part r m ≠ part r i]
    by_cases hir : (i : ℕ) < r
    · have hp0 : part r i = 0 := by unfold part; simp [hir]
      have : (range (2 * r + 4)).filter (fun m => part r m ≠ part r i) = Ico r (2 * r + 4) := by
        ext m
        rw [mem_filter, mem_range, mem_Ico, hp0]
        unfold part
        split_ifs <;> omega
      rw [this, Nat.card_Ico]
      omega
    · have hp1 : part r i = 1 := by unfold part; simp [hir, h]
      have : (range (2 * r + 4)).filter (fun m => part r m ≠ part r i) =
          range r ∪ Ico (2 * r) (2 * r + 4) := by
        ext m
        rw [mem_filter, mem_range, mem_union, mem_range, mem_Ico, hp1]
        unfold part
        split_ifs <;> omega
      rw [this, card_union_of_disjoint, card_range, Nat.card_Ico]
      · omega
      · rw [Finset.disjoint_left]
        intro m hm hm'
        simp only [mem_range, mem_Ico] at hm hm'
        omega
  · have hp2 := part_eq_two (not_lt.mp h)
    have hfil : (univ.filter ((sauerGraph r).Adj i)) = univ.filter fun j => i ≠ j := by
      refine filter_congr fun j _ => ?_
      rw [sauerGraph_adj]
      exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, Or.inr hp2⟩⟩
    rw [hfil, filter_ne, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    omega

lemma card_edgeFinset_sauerGraph (r : ℕ) :
    #(sauerGraph r).edgeFinset = r ^ 2 + 8 * r + 6 := by
  have h := (sauerGraph r).sum_degrees_eq_twice_card_edges
  simp only [degree_sauerGraph] at h
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < 2 * r then r + 4 else 2 * r + 3),
    sum_range_add] at h
  have h1 : ∑ x ∈ range (2 * r), (if x < 2 * r then r + 4 else 2 * r + 3) =
      ∑ _x ∈ range (2 * r), (r + 4) :=
    sum_congr rfl fun x hx => ite_eq_left (mem_range.mp hx)
  have h2 : ∑ x ∈ range 4, (if 2 * r + x < 2 * r then r + 4 else 2 * r + 3) =
      ∑ _x ∈ range 4, (2 * r + 3) :=
    sum_congr rfl fun x _ => ite_eq_right (by omega)
  rw [h1, h2, sum_const, sum_const, card_range, card_range, smul_eq_mul, smul_eq_mul] at h
  nlinarith

/- The triangle bound. -/

/-- The four vertices of `C`. -/
def partC (r : ℕ) : Finset (Fin (2 * r + 4)) := univ.filter fun i => 2 * r ≤ (i : ℕ)

lemma card_partC (r : ℕ) : #(partC r) = 4 := by
  rw [partC, card_filter_fin (2 * r + 4) fun m => 2 * r ≤ m]
  have : (range (2 * r + 4)).filter (fun m => 2 * r ≤ m) = Ico (2 * r) (2 * r + 4) := by
    ext m
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [this, Nat.card_Ico]
  omega

/-- Every triangle of Sauer's graph meets `C`. -/
lemma inter_partC_nonempty {r : ℕ} {t : Finset (Fin (2 * r + 4))}
    (ht : (sauerGraph r).IsNClique 3 t) : (t ∩ partC r).Nonempty := by
  by_contra hne
  have hout : ∀ x ∈ t, part r x < 2 := by
    intro x hx
    refine part_lt_two (not_le.mp fun hle => hne ⟨x, mem_inter.mpr ⟨hx, ?_⟩⟩)
    simp [partC, hle]
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht.card_eq
  have h1 := ht.isClique (by simp) (by simp) hab
  have h2 := ht.isClique (by simp) (by simp) hac
  have h3 := ht.isClique (by simp) (by simp) hbc
  have pa := hout a (by simp)
  have pb := hout b (by simp)
  have pc := hout c (by simp)
  rw [sauerGraph_adj] at h1 h2 h3
  omega

/-- A family of edge-disjoint triangles of Sauer's graph has at most `4 r + 1` members. -/
lemma card_le_of_edgeDisjoint {r : ℕ} (T : Finset (Finset (Fin (2 * r + 4))))
    (hT : ∀ t ∈ T, (sauerGraph r).IsNClique 3 t)
    (hP : (T : Set (Finset (Fin (2 * r + 4)))).Pairwise fun s t => (s ∩ t).card ≤ 1) :
    T.card ≤ 4 * r + 1 := by
  set C := partC r with hCdef
  have hC : #C = 4 := card_partC r
  have hCc : #Cᶜ = 2 * r := by
    rw [card_compl, hC, Fintype.card_fin]
    omega
  have hsplit := card_filter_add_card_filter_not (s := T) (fun t => t ⊆ C)
  -- at most one triangle lies inside `C`
  have hZ : #(T.filter fun t => t ⊆ C) ≤ 1 := by
    rw [card_le_one]
    intro s hs t ht
    rw [mem_filter] at hs ht
    by_contra hst
    have h1 := hP hs.1 ht.1 hst
    have h2 := card_union_add_card_inter s t
    have h3 : #(s ∪ t) ≤ 4 := (card_le_card (union_subset hs.2 ht.2)).trans hC.le
    have h4 := (hT s hs.1).card_eq
    have h5 := (hT t ht.1).card_eq
    omega
  -- the other triangles have disjoint sets of cross pairs
  set X := T.filter fun t => ¬t ⊆ C with hXdef
  let cross : Finset (Fin (2 * r + 4)) → Finset (Fin (2 * r + 4) × Fin (2 * r + 4)) :=
    fun t => (t \ C) ×ˢ (t ∩ C)
  have hcross : ∀ t ∈ X, 2 ≤ #(cross t) := by
    intro t ht
    rw [hXdef, mem_filter] at ht
    have h3 := (hT t ht.1).card_eq
    have hsum := card_sdiff_add_card_inter t C
    have ha : 1 ≤ #(t \ C) := by
      obtain ⟨x, hxt, hxC⟩ := not_subset.mp ht.2
      exact card_pos.mpr ⟨x, mem_sdiff.mpr ⟨hxt, hxC⟩⟩
    have hb : 1 ≤ #(t ∩ C) := card_pos.mpr (inter_partC_nonempty (hT t ht.1))
    show 2 ≤ #((t \ C) ×ˢ (t ∩ C))
    rw [card_product]
    have ha2 : #(t \ C) ≤ 2 := by omega
    interval_cases h : #(t \ C) <;> omega
  have hdisj : (X : Set (Finset (Fin (2 * r + 4)))).PairwiseDisjoint cross := by
    intro s hs t ht hst
    rw [Function.onFun, Finset.disjoint_left]
    rintro ⟨u, c⟩ h1 h2
    simp only [cross, mem_product, mem_sdiff, mem_inter] at h1 h2
    have huc : u ≠ c := fun h => h1.1.2 (h ▸ h1.2.2)
    have hsub : ({u, c} : Finset (Fin (2 * r + 4))) ⊆ s ∩ t := by
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_inter.mpr ⟨h1.1.1, h2.1.1⟩
      · exact mem_inter.mpr ⟨h1.2.1, h2.2.1⟩
    have hle := card_le_card hsub
    rw [card_pair huc] at hle
    have := hP (mem_filter.mp (mem_coe.mp hs)).1 (mem_filter.mp (mem_coe.mp ht)).1 hst
    omega
  have hsubP : X.biUnion cross ⊆ Cᶜ ×ˢ C := by
    intro p hp
    obtain ⟨t, -, hpt⟩ := mem_biUnion.mp hp
    simp only [cross, mem_product, mem_sdiff, mem_inter] at hpt
    exact mem_product.mpr ⟨mem_compl.mpr hpt.1.2, hpt.2.2⟩
  have hX : 2 * #X ≤ 8 * r :=
    calc 2 * #X = ∑ _t ∈ X, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ t ∈ X, #(cross t) := sum_le_sum hcross
      _ = #(X.biUnion cross) := (card_biUnion hdisj).symm
      _ ≤ #(Cᶜ ×ˢ C) := card_le_card hsubP
      _ = 8 * r := by rw [card_product, hCc, hC]; ring
  omega

/-- **Sauer's example.** The exact statement of `Erdos1009.erdos_1009.variants.sauer`. -/
theorem erdos_1009_variants_sauer : ∀ r : ℕ, 1 ≤ r → ∃ G : SimpleGraph (Fin (2 * r + 4)),
    G.edgeSet.ncard = (2 * r + 4) ^ 2 / 4 + 2 * (2 * r + 4) - 6 ∧
      ∀ T : Finset (Finset (Fin (2 * r + 4))), (∀ t ∈ T, G.IsNClique 3 t) →
        (T : Set (Finset (Fin (2 * r + 4)))).Pairwise (fun s t => (s ∩ t).card ≤ 1) →
          T.card ≤ 2 * (2 * r + 4) - 7 := by
  intro r _
  refine ⟨sauerGraph r, ?_, fun T hT hP => ?_⟩
  · rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_sauerGraph]
    have h4 : (2 * r + 4) ^ 2 / 4 = (r + 2) ^ 2 := by
      rw [show (2 * r + 4) ^ 2 = 4 * (r + 2) ^ 2 by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [h4, show (r + 2) ^ 2 = r ^ 2 + 4 * r + 4 by ring]
    generalize r ^ 2 = s
    omega
  · have := card_le_of_edgeDisjoint T hT hP
    omega

end Erdos1009Sauer

namespace Erdos1009

theorem erdos_1009.variants.sauer : ∀ r : ℕ, 1 ≤ r → ∃ G : SimpleGraph (Fin (2 * r + 4)),
    G.edgeSet.ncard = (2 * r + 4) ^ 2 / 4 + 2 * (2 * r + 4) - 6 ∧
      ∀ T : Finset (Finset (Fin (2 * r + 4))), (∀ t ∈ T, G.IsNClique 3 t) →
        (T : Set (Finset (Fin (2 * r + 4)))).Pairwise (fun s t => (s ∩ t).card ≤ 1) →
          T.card ≤ 2 * (2 * r + 4) - 7 :=
  Erdos1009Sauer.erdos_1009_variants_sauer

end Erdos1009

end
