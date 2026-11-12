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
# The Sauer–Spencer packing theorem

This file proves the upstream statement
`BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.sauer_spencer`:
if $2 \Delta_1 \Delta_2 < n$, then two graphs $G_1$, $G_2$ on the same $n$ vertices pack.

A *conflict* of a permutation $\sigma$ is an ordered pair $(x, y)$ with $xy \in G_1$ and
$\sigma x \sigma y \in G_2$. Take $\sigma$ with the fewest conflicts and suppose $(u, v)$ is a
conflict. Call $w$ *bad* if some $G_1$-neighbour $x$ of $u$ has $\sigma x \sigma w \in G_2$
(set $A$), or some $G_1$-neighbour $y$ of $w$ has $\sigma y \sigma u \in G_2$ (set $B$), or
$w = v$. Both $A$ and $B$ have at most $\Delta_1 \Delta_2$ elements and both contain $u$, so
there are at most $2 \Delta_1 \Delta_2 < n$ bad vertices. For a vertex $w$ that is not bad,
swapping the images of $u$ and $w$ removes the conflict $(u, v)$ and adds none.

The definitions are those of `FormalConjectures/Paper/BollobasEldridgeCatlinConjecture.lean`.

*Reference:* Sauer, N. and Spencer, J. (1978). "Edge disjoint placement of graphs."
*J. Combin. Theory Ser. B* 25, pp. 295--302.
-/

@[expose] public section

open SimpleGraph

namespace BollobasEldridgeCatlinConjecture

variable {V : Type*}

/-- Two graphs `G₁`, `G₂` on the same finite vertex set **pack** if some permutation of the
vertices makes their edge sets disjoint. -/
def Packs (G₁ G₂ : SimpleGraph V) : Prop :=
  ∃ σ : Equiv.Perm V, ∀ u v, G₁.Adj u v → ¬ G₂.Adj (σ u) (σ v)

end BollobasEldridgeCatlinConjecture

namespace SauerSpencer

open SimpleGraph BollobasEldridgeCatlinConjecture

variable {V : Type*} [Fintype V] {G₁ G₂ : SimpleGraph V}
  [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]

variable (G₁ G₂) in
/-- The conflicts of `σ`: ordered pairs `(x, y)` with `xy ∈ G₁` and `σ x σ y ∈ G₂`. -/
def conflicts (σ : Equiv.Perm V) : Finset (V × V) :=
  Finset.univ.filter fun p => G₁.Adj p.1 p.2 ∧ G₂.Adj (σ p.1) (σ p.2)

variable (G₁ G₂) in
/-- Vertices `w` such that some `G₁`-neighbour `x` of `u` has `σ x σ w ∈ G₂`. -/
def badLeft (σ : Equiv.Perm V) (u : V) : Finset V :=
  Finset.univ.filter fun w => ∃ x, G₁.Adj u x ∧ G₂.Adj (σ x) (σ w)

variable (G₁ G₂) in
/-- Vertices `w` with a `G₁`-neighbour `y` such that `σ y σ u ∈ G₂`. -/
def badRight (σ : Equiv.Perm V) (u : V) : Finset V :=
  Finset.univ.filter fun w => ∃ y, G₁.Adj w y ∧ G₂.Adj (σ y) (σ u)

lemma mem_conflicts {σ : Equiv.Perm V} {p : V × V} :
    p ∈ conflicts G₁ G₂ σ ↔ G₁.Adj p.1 p.2 ∧ G₂.Adj (σ p.1) (σ p.2) := by
  simp [conflicts]

lemma mem_badLeft {σ : Equiv.Perm V} {u w : V} :
    w ∈ badLeft G₁ G₂ σ u ↔ ∃ x, G₁.Adj u x ∧ G₂.Adj (σ x) (σ w) := by
  simp [badLeft]

lemma mem_badRight {σ : Equiv.Perm V} {u w : V} :
    w ∈ badRight G₁ G₂ σ u ↔ ∃ y, G₁.Adj w y ∧ G₂.Adj (σ y) (σ u) := by
  simp [badRight]

variable [DecidableEq V]

lemma card_badLeft_le (σ : Equiv.Perm V) (u : V) :
    (badLeft G₁ G₂ σ u).card ≤ G₁.maxDegree * G₂.maxDegree := by
  calc (badLeft G₁ G₂ σ u).card
      ≤ ((G₁.neighborFinset u).biUnion fun x => (G₂.neighborFinset (σ x)).image σ.symm).card := by
        refine Finset.card_le_card fun w hw => ?_
        obtain ⟨x, hux, hx⟩ := mem_badLeft.mp hw
        simp only [Finset.mem_biUnion, mem_neighborFinset, Finset.mem_image]
        exact ⟨x, hux, σ w, hx, by simp⟩
    _ ≤ ∑ x ∈ G₁.neighborFinset u, ((G₂.neighborFinset (σ x)).image σ.symm).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ G₁.neighborFinset u, G₂.maxDegree :=
        Finset.sum_le_sum fun x _ => Finset.card_image_le.trans (G₂.degree_le_maxDegree _)
    _ = G₁.degree u * G₂.maxDegree := by rw [Finset.sum_const, smul_eq_mul]; rfl
    _ ≤ G₁.maxDegree * G₂.maxDegree := Nat.mul_le_mul_right _ (G₁.degree_le_maxDegree u)

lemma card_badRight_le (σ : Equiv.Perm V) (u : V) :
    (badRight G₁ G₂ σ u).card ≤ G₁.maxDegree * G₂.maxDegree := by
  calc (badRight G₁ G₂ σ u).card
      ≤ (((G₂.neighborFinset (σ u)).image σ.symm).biUnion fun y => G₁.neighborFinset y).card := by
        refine Finset.card_le_card fun w hw => ?_
        obtain ⟨y, hwy, hy⟩ := mem_badRight.mp hw
        simp only [Finset.mem_biUnion, mem_neighborFinset, Finset.mem_image]
        exact ⟨y, ⟨σ y, hy.symm, by simp⟩, hwy.symm⟩
    _ ≤ ∑ y ∈ (G₂.neighborFinset (σ u)).image σ.symm, (G₁.neighborFinset y).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ (G₂.neighborFinset (σ u)).image σ.symm, G₁.maxDegree :=
        Finset.sum_le_sum fun y _ => G₁.degree_le_maxDegree y
    _ = ((G₂.neighborFinset (σ u)).image σ.symm).card * G₁.maxDegree := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ G₂.maxDegree * G₁.maxDegree :=
        Nat.mul_le_mul_right _ (Finset.card_image_le.trans (G₂.degree_le_maxDegree _))
    _ = G₁.maxDegree * G₂.maxDegree := Nat.mul_comm _ _

/-- Swapping the images of `u` and a vertex `w` that is not bad removes the conflict `(u, v)`
and adds no conflict. -/
lemma conflicts_swap_ssubset (σ : Equiv.Perm V) {u v w : V}
    (huv : (u, v) ∈ conflicts G₁ G₂ σ) (hwv : w ≠ v)
    (hA : ∀ x, G₁.Adj u x → ¬G₂.Adj (σ x) (σ w))
    (hB : ∀ y, G₁.Adj w y → ¬G₂.Adj (σ y) (σ u)) :
    conflicts G₁ G₂ (σ * Equiv.swap u w) ⊂ conflicts G₁ G₂ σ := by
  rw [mem_conflicts] at huv
  have hsub : conflicts G₁ G₂ (σ * Equiv.swap u w) ⊆ conflicts G₁ G₂ σ := by
    rintro ⟨x, y⟩ hp
    simp only [mem_conflicts, Equiv.Perm.mul_apply] at hp ⊢
    obtain ⟨hxy, h2⟩ := hp
    refine ⟨hxy, ?_⟩
    by_cases hxu : x = u
    · subst hxu
      rw [Equiv.swap_apply_left] at h2
      by_cases hyw : y = w
      · subst hyw
        rw [Equiv.swap_apply_right] at h2
        exact h2.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hxy.ne' hyw] at h2
        exact absurd h2.symm (hA y hxy)
    by_cases hxw : x = w
    · subst hxw
      rw [Equiv.swap_apply_right] at h2
      by_cases hyu : y = u
      · subst hyu
        rw [Equiv.swap_apply_left] at h2
        exact h2.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hyu hxy.ne'] at h2
        exact absurd h2.symm (hB y hxy)
    rw [Equiv.swap_apply_of_ne_of_ne hxu hxw] at h2
    by_cases hyu : y = u
    · subst hyu
      rw [Equiv.swap_apply_left] at h2
      exact absurd h2 (hA x hxy.symm)
    by_cases hyw : y = w
    · subst hyw
      rw [Equiv.swap_apply_right] at h2
      exact absurd h2 (hB x hxy.symm)
    rwa [Equiv.swap_apply_of_ne_of_ne hyu hyw] at h2
  refine (Finset.ssubset_iff_of_subset hsub).2 ⟨(u, v), mem_conflicts.mpr huv, ?_⟩
  simp only [mem_conflicts, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne huv.1.ne' hwv.symm]
  exact fun h => hA v huv.1 h.2.symm

/-- **The Sauer–Spencer theorem.** The exact statement of
`BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.sauer_spencer`. -/
theorem bollobas_eldridge_catlin_conjecture_variants_sauer_spencer
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) : Packs G₁ G₂ := by
  obtain ⟨σ, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun σ : Equiv.Perm V => (conflicts G₁ G₂ σ).card) Finset.univ_nonempty
  refine ⟨σ, fun u v huv h2 => ?_⟩
  have hc : (u, v) ∈ conflicts G₁ G₂ σ := mem_conflicts.mpr ⟨huv, h2⟩
  have huA : u ∈ badLeft G₁ G₂ σ u := mem_badLeft.mpr ⟨v, huv, h2.symm⟩
  have huB : u ∈ badRight G₁ G₂ σ u := mem_badRight.mpr ⟨v, huv, h2.symm⟩
  have hcard : (insert v (badLeft G₁ G₂ σ u ∪ badRight G₁ G₂ σ u)).card <
      (Finset.univ : Finset V).card := by
    have hA := card_badLeft_le (G₁ := G₁) (G₂ := G₂) σ u
    have hB := card_badRight_le (G₁ := G₁) (G₂ := G₂) σ u
    have hi : 1 ≤ (badLeft G₁ G₂ σ u ∩ badRight G₁ G₂ σ u).card :=
      Finset.card_pos.mpr ⟨u, Finset.mem_inter.mpr ⟨huA, huB⟩⟩
    have hu := Finset.card_union_add_card_inter (badLeft G₁ G₂ σ u) (badRight G₁ G₂ σ u)
    have hins := Finset.card_insert_le v (badLeft G₁ G₂ σ u ∪ badRight G₁ G₂ σ u)
    rw [Finset.card_univ]
    rw [mul_assoc] at h
    generalize G₁.maxDegree * G₂.maxDegree = D at h hA hB
    omega
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_union, not_or] at hw
  obtain ⟨hwv, hwA, hwB⟩ := hw
  have hlt := Finset.card_lt_card (conflicts_swap_ssubset σ hc hwv
    (fun x hx hx' => hwA (mem_badLeft.mpr ⟨x, hx, hx'⟩))
    (fun y hy hy' => hwB (mem_badRight.mpr ⟨y, hy, hy'⟩)))
  exact absurd (hmin _ (Finset.mem_univ _)) (not_le.mpr hlt)

end SauerSpencer

open SimpleGraph

namespace BollobasEldridgeCatlinConjecture

theorem bollobas_eldridge_catlin_conjecture.variants.sauer_spencer
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) : Packs G₁ G₂ :=
  SauerSpencer.bollobas_eldridge_catlin_conjecture_variants_sauer_spencer G₁ G₂ h

end BollobasEldridgeCatlinConjecture

end
