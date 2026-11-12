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
# Two solved variants of Erdős Problem 151

This file proves the upstream statements `Erdos151.erdos_151.variants.cliqueFree_three` and
`Erdos151.erdos_151.variants.sqrt_bound` about the clique transversal number $\tau(G)$ of a graph
$G$ on $n$ vertices.

Two kinds of vertex sets meet every maximal clique with at least two vertices:

* the complement of an independent set $I$, since a clique has at most one vertex in $I$
  (`isCliqueTransversal_compl_of_isIndepSet`);
* the complement of a neighbourhood $N(v)$, since a clique inside $N(v)$ extends by $v$
  (`isCliqueTransversal_compl_neighborFinset`).

So $\tau(G) \le n - \alpha(G)$ and $\tau(G) \le n - \deg v$ for every $v$.

* Triangle-free case: $H(n) \le \alpha(G)$ when $G$ is triangle-free, so
  $\tau(G) \le n - H(n)$.
* Square-root bound: a maximum independent set $I$ dominates $G$, so
  $n \le \sum_{u \in I} (\deg u + 1)$ (`card_le_sum_degree_add_one`). If $|I| < s = \lfloor\sqrt
  n\rfloor$ and every degree were below $s$, then $n \le |I| \cdot s < s^2 \le n$. Hence
  $\alpha(G) \ge s$ or some vertex has degree at least $s$, and $\tau(G) \le n - s$.

*References:*
* [erdosproblems.com/151](https://www.erdosproblems.com/151)
* [EGT92] Erdős, P. and Gallai, T. and Tuza, Zs., *Covering the cliques of a graph with
  vertices*. Discrete Math. (1992), 279-289.
-/

@[expose] public section

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

open Finset List

/-- `s` is a maximal clique of `G` with at least two vertices. -/
def IsBigMaximalClique (G : SimpleGraph V) (s : Finset V) : Prop :=
  Maximal (fun t : Finset V ↦ G.IsClique (t : Set V)) s ∧ 2 ≤ s.card

/-- `T` meets every maximal clique of `G` with at least two vertices. -/
def IsCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ s, G.IsBigMaximalClique s → ∃ v ∈ s, v ∈ T

/-- The clique transversal number $\tau(G)$: the minimal number of vertices that meet every
maximal clique of `G` with at least two vertices, so isolated vertices are not counted. -/
noncomputable def cliqueTransversalNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ T : Finset V, G.IsCliqueTransversal T ∧ T.card = k}

end SimpleGraph

namespace Erdos151

open SimpleGraph

/-- $H(n)$: the largest `k` such that every triangle-free graph on `n` vertices contains an
independent set on `k` vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}

end Erdos151

namespace Erdos151Variants

open Finset SimpleGraph

/-- $\tau(G)$ is at most the size of any clique transversal. -/
lemma cliqueTransversalNumber_le_card {V : Type*} {G : SimpleGraph V} {T : Finset V}
    (hT : G.IsCliqueTransversal T) : G.cliqueTransversalNumber ≤ #T :=
  Nat.sInf_le ⟨T, hT, rfl⟩

/-- The complement of an independent set meets every clique with at least two vertices. -/
lemma isCliqueTransversal_compl_of_isIndepSet {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {I : Finset V} (hI : G.IsIndepSet (I : Set V)) :
    G.IsCliqueTransversal Iᶜ := by
  intro s hs
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < #s by have := hs.2; omega)
  by_contra h
  push Not at h
  have haI : a ∈ I := by simpa using h a ha
  have hbI : b ∈ I := by simpa using h b hb
  exact hI haI hbI hab (hs.1.prop ha hb hab)

/-- The complement of a neighbourhood meets every maximal clique with at least two vertices: a
clique inside `N(v)` extends by `v`. -/
lemma isCliqueTransversal_compl_neighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (v : V) :
    G.IsCliqueTransversal (G.neighborFinset v)ᶜ := by
  intro s hs
  by_contra h
  push Not at h
  have hsN : ∀ x ∈ s, G.Adj v x := fun x hx => by simpa using h x hx
  have hv : v ∉ s := fun hv => (hsN v hv).ne rfl
  have hclique : G.IsClique ((insert v s : Finset V) : Set V) := by
    rw [coe_insert, isClique_insert]
    exact ⟨hs.1.prop, fun b hb _ => hsN b hb⟩
  exact hv ((hs.1.2 hclique (subset_insert v s) : insert v s ⊆ s) (mem_insert_self v s))

/-- Every finite graph has an independent set of largest size. -/
lemma exists_isIndepSet_forall_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      ∀ J : Finset V, G.IsIndepSet (J : Set V) → #J ≤ #I := by
  classical
  obtain ⟨I, hI, hmax⟩ := (univ.powerset.filter fun J : Finset V => G.IsIndepSet (J : Set V))
    |>.exists_max_image card ⟨∅, by simp⟩
  rw [mem_filter] at hI
  exact ⟨I, hI.2, fun J hJ => hmax J (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ J), hJ⟩)⟩

/-- A largest independent set `I` dominates the graph, so `|V| ≤ ∑_{u ∈ I} (deg u + 1)`. -/
lemma card_le_sum_degree_add_one {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {I : Finset V} (hI : G.IsIndepSet (I : Set V))
    (hmax : ∀ J : Finset V, G.IsIndepSet (J : Set V) → #J ≤ #I) :
    Fintype.card V ≤ ∑ u ∈ I, (G.degree u + 1) := by
  have hdom : ∀ x, x ∈ I ∨ ∃ u ∈ I, G.Adj u x := by
    intro x
    by_contra h
    push Not at h
    obtain ⟨hx, hadj⟩ := h
    have hind : G.IsIndepSet ((insert x I : Finset V) : Set V) := by
      rw [coe_insert]
      intro a ha b hb hab
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact fun h' => hadj b hb h'.symm
      · exact hadj a ha
      · exact hI ha hb hab
    have := hmax _ hind
    rw [card_insert_of_notMem hx] at this
    omega
  have hcover : (univ : Finset V) ⊆ I.biUnion fun u => insert u (G.neighborFinset u) := by
    intro x _
    rw [mem_biUnion]
    rcases hdom x with hx | ⟨u, hu, hux⟩
    · exact ⟨x, hx, mem_insert_self _ _⟩
    · exact ⟨u, hu, mem_insert_of_mem ((mem_neighborFinset _ _ _).mpr hux)⟩
  calc Fintype.card V = #(univ : Finset V) := card_univ.symm
    _ ≤ #(I.biUnion fun u => insert u (G.neighborFinset u)) := card_le_card hcover
    _ ≤ ∑ u ∈ I, #(insert u (G.neighborFinset u)) := card_biUnion_le
    _ ≤ ∑ u ∈ I, (G.degree u + 1) := sum_le_sum fun u _ =>
        (card_insert_le _ _).trans_eq (by rw [card_neighborFinset_eq_degree])

/-- **Erdős 151, triangle-free case.** The exact statement of
`Erdos151.erdos_151.variants.cliqueFree_three`. -/
theorem erdos_151_variants_cliqueFree_three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  classical
  obtain ⟨I, hI, hmax⟩ := exists_isIndepSet_forall_card_le G
  have hH : Erdos151.H n ≤ #I := by
    unfold Erdos151.H
    refine csSup_le' fun k hk => ?_
    obtain ⟨s, hs⟩ := hk G hG
    rw [← hs.card_eq]
    exact hmax s hs.isIndepSet
  calc cliqueTransversalNumber G ≤ #Iᶜ :=
        cliqueTransversalNumber_le_card (isCliqueTransversal_compl_of_isIndepSet hI)
    _ = n - #I := by rw [card_compl, Fintype.card_fin]
    _ ≤ n - Erdos151.H n := by omega

/-- **Erdős 151, square-root bound.** The exact statement of
`Erdos151.erdos_151.variants.sqrt_bound`. -/
theorem erdos_151_variants_sqrt_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueTransversalNumber G ≤ n - Nat.sqrt n := by
  classical
  obtain ⟨I, hI, hmax⟩ := exists_isIndepSet_forall_card_le G
  by_cases hα : Nat.sqrt n ≤ #I
  · calc cliqueTransversalNumber G ≤ #Iᶜ :=
          cliqueTransversalNumber_le_card (isCliqueTransversal_compl_of_isIndepSet hI)
      _ = n - #I := by rw [card_compl, Fintype.card_fin]
      _ ≤ n - Nat.sqrt n := by omega
  · push Not at hα
    obtain ⟨u, hu⟩ : ∃ u, Nat.sqrt n ≤ G.degree u := by
      by_contra h
      push Not at h
      have hsum : n ≤ #I * Nat.sqrt n := by
        calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
          _ ≤ ∑ u ∈ I, (G.degree u + 1) := card_le_sum_degree_add_one hI hmax
          _ ≤ ∑ _ ∈ I, Nat.sqrt n := sum_le_sum fun u _ => by have := h u; omega
          _ = #I * Nat.sqrt n := by rw [sum_const, smul_eq_mul]
      have hsq := Nat.sqrt_le n
      have hlt := Nat.mul_le_mul_right (Nat.sqrt n) (by omega : #I + 1 ≤ Nat.sqrt n)
      nlinarith
    calc cliqueTransversalNumber G ≤ #(G.neighborFinset u)ᶜ :=
          cliqueTransversalNumber_le_card (isCliqueTransversal_compl_neighborFinset u)
      _ = n - G.degree u := by rw [card_compl, Fintype.card_fin, card_neighborFinset_eq_degree]
      _ ≤ n - Nat.sqrt n := by omega

end Erdos151Variants

namespace Erdos151

open SimpleGraph

theorem erdos_151.variants.cliqueFree_three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNumber G ≤ n - H n :=
  Erdos151Variants.erdos_151_variants_cliqueFree_three n G hG

theorem erdos_151.variants.sqrt_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueTransversalNumber G ≤ n - Nat.sqrt n :=
  Erdos151Variants.erdos_151_variants_sqrt_bound n G

end Erdos151

end
