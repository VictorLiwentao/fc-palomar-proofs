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
# Kalkowski–Karoński–Pfender: edge weights `1, …, 5`

Every finite simple graph without an isolated edge has edge weights in `{1, …, 5}` such that
adjacent vertices have different weighted degrees (Kalkowski, Karoński and Pfender 2010).
`OneTwoThree.exists_weighting` proves this; it is the statement of
`one_two_three_conjecture.variants.one_to_five` in
`FormalConjectures/Paper/OneTwoThreeConjecture.lean`, with the definitions unfolded.

The proof follows the paper. Order the vertices so that each vertex, except the last vertex of
each connected component, has a later neighbour, and each last vertex has degree `0` or at
least `2`. Start with all weights `3` and process the vertices in order. A processed vertex `x`
gets a base `β x ≡ 0, 1 (mod 4)` and keeps its weighted degree in `{β x, β x + 2}`; adjacent
processed vertices get different bases, so their sets are disjoint. When `v` is processed, each
edge to an earlier neighbour `u` may change by `±2`, moving `u` within its set, and the edge to
the first later neighbour may change by `±1`. This gives `2d + 3` consecutive values for `v`,
of which at most `2d + 2` are excluded. The last vertex of a component uses the final states of
its neighbours instead.

*Reference:* M. Kalkowski, M. Karoński and F. Pfender, "Vertex-coloring edge-weightings: towards
the 1-2-3-conjecture", *J. Combin. Theory Ser. B* 100 (2010), 347–349. The argument is also
written out for hypergraphs in M. Kalkowski, M. Karoński and F. Pfender, "The 1-2-3-conjecture
for hypergraphs", arXiv:1308.0611, Section 3.
-/

@[expose] public section

namespace OneTwoThree

open Finset SimpleGraph

section Weights

variable {V : Type*} [DecidableEq V]

/-- `W` with the weights of the pairs at `v` replaced by `g`. -/
def upd (W : V → V → ℤ) (v : V) (g : V → ℤ) : V → V → ℤ :=
  fun a b => if a = v then g b else if b = v then g a else W a b

/-- The base of `x`: the element `b ≡ 0, 1 (mod 4)` with `x ∈ {b, b + 2}`. -/
def base (x : ℤ) : ℤ := x - 2 * (x % 4 / 2)

lemma upd_symm {W : V → V → ℤ} (hW : ∀ a b, W a b = W b a) (v : V) (g : V → ℤ) (a b : V) :
    upd W v g a b = upd W v g b a := by
  unfold upd
  by_cases ha : a = v <;> by_cases hb : b = v
  · rw [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb, hW a b]

lemma upd_self (W : V → V → ℤ) (v : V) (g : V → ℤ) (b : V) : upd W v g v b = g b := by
  simp [upd]

lemma upd_of_ne {W : V → V → ℤ} {v : V} (g : V → ℤ) {a b : V} (ha : a ≠ v) (hb : b ≠ v) :
    upd W v g a b = W a b := by
  simp [upd, ha, hb]

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The weighted degree of `x` for integer weights `W`. -/
def rho (W : V → V → ℤ) (x : V) : ℤ :=
  ∑ y ∈ G.neighborFinset x, W x y

lemma rho_upd_self (W : V → V → ℤ) (v : V) (g : V → ℤ) :
    rho G (upd W v g) v = ∑ z ∈ G.neighborFinset v, g z := by
  simp [rho, upd]

lemma rho_upd_of_ne (W : V → V → ℤ) {v y : V} (g : V → ℤ) (hy : y ≠ v) :
    rho G (upd W v g) y = rho G W y + if G.Adj y v then g y - W y v else 0 := by
  have h : ∀ z ∈ G.neighborFinset y,
      upd W v g y z = W y z + if z = v then g y - W y v else 0 := by
    intro z _
    by_cases hz : z = v
    · subst hz
      simp [upd, hy]
    · simp [upd, hy, hz]
  rw [rho, rho, sum_congr rfl h, sum_add_distrib, sum_ite_eq']
  by_cases hyv : G.Adj y v <;> simp [hyv]

lemma sum_incidenceFinset (x : V) (w : Sym2 V → ℕ) :
    ∑ e ∈ G.incidenceFinset x, w e = ∑ y ∈ G.neighborFinset x, w s(x, y) := by
  have h : G.incidenceFinset x = (G.neighborFinset x).image (fun y => s(x, y)) := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_incidenceFinset, mk'_mem_incidenceSet_iff, mem_image, mem_neighborFinset,
        Sym2.eq_iff]
      constructor
      · rintro ⟨hab, rfl | rfl⟩
        · exact ⟨b, hab, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨a, hab.symm, Or.inr ⟨rfl, rfl⟩⟩
      · rintro ⟨y, hy, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨hy, Or.inl rfl⟩
        · exact ⟨hy.symm, Or.inr rfl⟩
  rw [h, sum_image fun y _ y' _ hyy' => Sym2.congr_right.1 hyy']

/-- Choice of the new value at a vertex with `d` earlier neighbours: `x = L + 2 t + c` with
`t ≤ d` and `c ∈ {-1, 0, 1}`, where `c = -1` only for a lower value and `c = 1` only for an
upper value. -/
lemma choose_tc (L x : ℤ) (d : ℕ) (h1 : L - 1 < x) (h2 : x < L + 2 * d + 1) :
    ∃ (t : ℕ) (c : ℤ), t ≤ d ∧ x = L + 2 * t + c ∧
      (c = 0 ∨ (c = -1 ∧ x % 4 < 2) ∨ (c = 1 ∧ 2 ≤ x % 4)) := by
  rcases Int.emod_two_eq_zero_or_one (x - L) with he | ho
  · obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le (a := (x - L) / 2) (by omega)
    exact ⟨t, 0, by omega, by omega, by omega⟩
  · by_cases hs : x % 4 < 2
    · obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le (a := (x - L + 1) / 2) (by omega)
      exact ⟨t, -1, by omega, by omega, by omega⟩
    · obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le (a := (x - L - 1) / 2) (by omega)
      exact ⟨t, 1, by omega, by omega, by omega⟩

omit [Fintype V] in
/-- Choice at the last vertex of a component: a set `T` of edges to raise by `2`. -/
lemma choose_root (N : Finset V) (β : V → ℤ) (a : ℤ) (hN : 2 ≤ N.card)
    (hβ : ∀ y ∈ N, β y % 4 = 0 ∨ β y % 4 = 1) :
    ∃ T ⊆ N, ∀ y ∈ N, a + 2 * T.card ≠ β y + if y ∈ T then 2 else 0 := by
  by_cases ha : 2 ≤ a % 4
  · refine ⟨∅, empty_subset _, fun y hy => ?_⟩
    have := hβ y hy
    simp only [card_empty, Nat.cast_zero, notMem_empty, ite_false]
    omega
  · by_cases hu : ∃ u ∈ N, β u ≠ a
    · obtain ⟨u, hu, hβu⟩ := hu
      refine ⟨{u}, singleton_subset_iff.2 hu, fun y hy => ?_⟩
      have := hβ y hy
      by_cases hyu : y = u
      · rw [hyu, ite_eq_left (mem_singleton_self u), card_singleton]
        omega
      · rw [ite_eq_right (by simpa using hyu), card_singleton]
        omega
    · push Not at hu
      obtain ⟨T, hTN, hT⟩ := exists_subset_card_eq hN
      refine ⟨T, hTN, fun y hy => ?_⟩
      rw [hT, hu y hy]
      split_ifs <;> omega

end Weights

section Core

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A processing order: `r` ranks the vertices, and `f x` is the first later neighbour of `x`.
A vertex without a later neighbour has degree `0`, or degree at least `2` and comes after all
neighbours of its neighbours. -/
structure Schedule (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The rank of a vertex. -/
  r : V → ℕ
  /-- The first later neighbour. -/
  f : V → V
  inj : Function.Injective r
  fwd : ∀ x y, G.Adj x y → r x < r y →
    G.Adj x (f x) ∧ r x < r (f x) ∧ ∀ z, G.Adj x z → r x < r z → r (f x) ≤ r z
  root : ∀ x, (∀ y, G.Adj x y → r y < r x) →
    G.degree x = 0 ∨ (2 ≤ G.degree x ∧ ∀ u, G.Adj x u → ∀ y, G.Adj u y → r y ≤ r x)

variable (O : Schedule G)

/-- `x` has a later neighbour. -/
def NR (x : V) : Prop := ∃ y, G.Adj x y ∧ O.r x < O.r y

lemma lt_of_not_NR {x y : V} (hx : ¬ NR O x) (hxy : G.Adj x y) : O.r y < O.r x := by
  have hne : O.r y ≠ O.r x := fun h => G.ne_of_adj hxy (O.inj h).symm
  have : ¬ O.r x < O.r y := fun h => hx ⟨y, hxy, h⟩
  omega

/-- The invariant after all vertices of rank `< k` are processed, for weights `W` and bases
`β`. -/
structure Invariant (k : ℕ) (W : V → V → ℤ) (β : V → ℤ) : Prop where
  symm : ∀ x y, W x y = W y x
  bound : ∀ x y, G.Adj x y → 1 ≤ W x y ∧ W x y ≤ 5
  three : ∀ x y, G.Adj x y → O.r x < O.r y → k ≤ O.r y → (k ≤ O.r x ∨ y ≠ O.f x) →
    W x y = 3
  fwd : ∀ x, O.r x < k → NR O x → k ≤ O.r (O.f x) →
    (rho G W x = β x → 2 ≤ W x (O.f x) ∧ W x (O.f x) ≤ 3) ∧
    (rho G W x = β x + 2 → 3 ≤ W x (O.f x) ∧ W x (O.f x) ≤ 4)
  state : ∀ x, O.r x < k → NR O x →
    (β x % 4 = 0 ∨ β x % 4 = 1) ∧ (rho G W x = β x ∨ rho G W x = β x + 2)
  sep : ∀ x y, G.Adj x y → O.r x < k → O.r y < k → NR O x → NR O y → β x ≠ β y
  roots : ∀ x, O.r x < k → ¬ NR O x → ∀ y, G.Adj x y → rho G W x ≠ rho G W y

lemma invariant_zero : Invariant O 0 (fun _ _ => 3) (fun _ => 0) :=
  { symm := fun _ _ => rfl
    bound := fun _ _ _ => by omega
    three := fun _ _ _ _ _ _ => rfl
    fwd := fun _ h => absurd h (Nat.not_lt_zero _)
    state := fun _ h => absurd h (Nat.not_lt_zero _)
    sep := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
    roots := fun _ h => absurd h (Nat.not_lt_zero _) }

variable {O}

lemma invariant_skip {k : ℕ} {W : V → V → ℤ} {β : V → ℤ} (h : Invariant O k W β)
    (hk : ∀ v, O.r v ≠ k) : Invariant O (k + 1) W β := by
  have hlt : ∀ x, O.r x < k + 1 → O.r x < k := fun x hx => by have := hk x; omega
  exact
    { symm := h.symm
      bound := h.bound
      three := fun x y hxy h1 h2 h3 => h.three x y hxy h1 (by omega)
        (h3.imp (fun h' => by omega) id)
      fwd := fun x hx hnr _ => h.fwd x (hlt x hx) hnr (by omega)
      state := fun x hx hnr => h.state x (hlt x hx) hnr
      sep := fun x y hxy hx hy => h.sep x y hxy (hlt x hx) (hlt y hy)
      roots := fun x hx => h.roots x (hlt x hx) }

/-- The lower choice for the edge from `v` to an earlier neighbour `z` is at least `1`, and the
upper choice (two more) is at most `5`. -/
lemma lo_bound {k : ℕ} {W : V → V → ℤ} {β : V → ℤ} (h : Invariant O k W β) {v z : V}
    (hv : O.r v = k) (hvz : G.Adj v z) (hz : O.r z < k) :
    1 ≤ W v z - (rho G W z - β z) ∧ W v z - (rho G W z - β z) + 2 ≤ 5 := by
  have hnr : NR O z := ⟨v, hvz.symm, by omega⟩
  have hst := (h.state z hz hnr).2
  rw [h.symm v z]
  by_cases hfz : v = O.f z
  · have hf := h.fwd z hz hnr (by rw [← hfz]; omega)
    rw [← hfz] at hf
    rcases hst with hs | hs
    · have := hf.1 hs
      omega
    · have := hf.2 hs
      omega
  · have h3 := h.three z v hvz.symm (by omega) (by omega) (Or.inr hfz)
    rcases hst with hs | hs <;> omega

lemma rank_succ_iff {k : ℕ} {v : V} (hv : O.r v = k) (y : V) :
    O.r y < k + 1 ↔ O.r y < k ∨ y = v := by
  constructor
  · intro hy
    by_cases hyk : O.r y = k
    · exact Or.inr (O.inj (hyk.trans hv.symm))
    · exact Or.inl (by omega)
  · rintro (hy | rfl) <;> omega

/-- A processed vertex whose first later neighbour comes after `v` is not adjacent to `v`. -/
lemma not_adj_of_fwd {k : ℕ} {v a : V} (hv : O.r v = k) (ha : O.r a < k)
    (hfa : k + 1 ≤ O.r (O.f a)) : ¬ G.Adj a v := fun hadj => by
  have := (O.fwd a v hadj (by omega)).2.2 v hadj (by omega)
  omega

variable [DecidableEq V]

/-- Processing a vertex that has a later neighbour. -/
lemma invariant_step_nonroot {k : ℕ} {W : V → V → ℤ} {β : V → ℤ} (h : Invariant O k W β) {v : V}
    (hv : O.r v = k) (hnr : NR O v) : ∃ W' β', Invariant O (k + 1) W' β' := by
  obtain ⟨y₀, hy₀, hry₀⟩ := hnr
  obtain ⟨hf, hrf, -⟩ := O.fwd v y₀ hy₀ hry₀
  have hnr : NR O v := ⟨y₀, hy₀, hry₀⟩
  have hrk := rank_succ_iff hv
  obtain ⟨B, hB⟩ : ∃ B : Finset V, B = (G.neighborFinset v).filter (fun z => O.r z < k) :=
    ⟨_, rfl⟩
  have hBmem : ∀ z, z ∈ B ↔ G.Adj v z ∧ O.r z < k := fun z => by simp [hB]
  obtain ⟨d, hd⟩ : ∃ d, d = B.card := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = rho G W v - ∑ z ∈ B, (rho G W z - β z) := ⟨_, rfl⟩
  -- Choose the new weighted degree `x` of `v`.
  obtain ⟨S, hS⟩ : ∃ S : Finset ℤ,
      S = (B.image β).biUnion (fun b => ({b, b + 2} : Finset ℤ)) ∪ {L - 1, L + 2 * d + 1} :=
    ⟨_, rfl⟩
  have hScard : S.card < (Icc (L - 1) (L + 2 * d + 1)).card := by
    have h1 : ((B.image β).biUnion (fun b => ({b, b + 2} : Finset ℤ))).card ≤ B.card * 2 :=
      (card_biUnion_le_card_mul _ _ 2 fun b _ => card_le_two).trans
        (Nat.mul_le_mul_right 2 card_image_le)
    have h2 : ({L - 1, L + 2 * (d : ℤ) + 1} : Finset ℤ).card ≤ 2 := card_le_two
    have h3 := card_union_le ((B.image β).biUnion (fun b => ({b, b + 2} : Finset ℤ)))
      {L - 1, L + 2 * (d : ℤ) + 1}
    have h4 := Int.card_Icc_of_le (L - 1) (L + 2 * d + 1) (by omega)
    rw [hS]
    omega
  obtain ⟨x, hxI, hxS⟩ := exists_mem_notMem_of_card_lt_card hScard
  rw [mem_Icc] at hxI
  have hx1 : x ≠ L - 1 := fun hx => hxS (by rw [hS]; exact mem_union_right _ (by simp [hx]))
  have hx2 : x ≠ L + 2 * d + 1 := fun hx =>
    hxS (by rw [hS]; exact mem_union_right _ (by simp [hx]))
  have hxβ : ∀ z ∈ B, x ≠ β z ∧ x ≠ β z + 2 := fun z hz => by
    constructor <;> intro hx <;> exact hxS (by
      rw [hS]
      exact mem_union_left _ (mem_biUnion.2 ⟨β z, mem_image_of_mem β hz, by simp [hx]⟩))
  obtain ⟨t, c, htd, hxtc, hc⟩ := choose_tc L x d (by omega) (by omega)
  obtain ⟨T, hTB, hTc⟩ := exists_subset_card_eq (s := B) (n := t) (by omega)
  -- The new weights at `v`.
  obtain ⟨g, hg⟩ : ∃ g : V → ℤ, ∀ z, g z = if O.r z < k then
      W v z - (rho G W z - β z) + (if z ∈ T then 2 else 0)
      else if z = O.f v then 3 + c else W v z := ⟨_, fun _ => rfl⟩
  have hgB : ∀ z ∈ B, g z = W v z - (rho G W z - β z) + (if z ∈ T then 2 else 0) :=
    fun z hz => by rw [hg, ite_eq_left ((hBmem z).1 hz).2]
  have hfk : ¬ O.r (O.f v) < k := by omega
  have hgf : g (O.f v) = 3 + c := by rw [hg, ite_eq_right hfk, ite_eq_left rfl]
  have hgo : ∀ z, ¬ O.r z < k → z ≠ O.f v → g z = W v z := fun z h1 h2 => by
    rw [hg, ite_eq_right h1, ite_eq_right h2]
  have hW3 : W v (O.f v) = 3 := h.three v (O.f v) hf hrf (by omega) (Or.inl (by omega))
  have hgbd : ∀ z, G.Adj v z → 1 ≤ g z ∧ g z ≤ 5 := by
    intro z hz
    by_cases hzk : O.r z < k
    · have := lo_bound h hv hz hzk
      rw [hgB z ((hBmem z).2 ⟨hz, hzk⟩)]
      split_ifs <;> omega
    · by_cases hzf : z = O.f v
      · rw [hzf, hgf]
        rcases hc with hc | hc | hc <;> omega
      · rw [hgo z hzk hzf]
        exact h.bound v z hz
  -- The new weighted degrees.
  have hrv : rho G (upd W v g) v = x := by
    rw [rho_upd_self, ← sum_filter_add_sum_filter_not (G.neighborFinset v)
      (fun z => O.r z < k) g, ← hB]
    have e1 : ∑ z ∈ B, g z = ∑ z ∈ B, W v z - ∑ z ∈ B, (rho G W z - β z) + 2 * t := by
      rw [sum_congr rfl hgB, sum_add_distrib, sum_sub_distrib, sum_ite_mem,
        inter_eq_right.2 hTB, sum_const, hTc, nsmul_eq_mul]
      omega
    have hfR : O.f v ∈ (G.neighborFinset v).filter (fun z => ¬ O.r z < k) := by
      rw [mem_filter, mem_neighborFinset]
      exact ⟨hf, hfk⟩
    have e2 : ∑ z ∈ (G.neighborFinset v).filter (fun z => ¬ O.r z < k), g z
        = ∑ z ∈ (G.neighborFinset v).filter (fun z => ¬ O.r z < k), W v z + c := by
      have : ∀ z ∈ (G.neighborFinset v).filter (fun z => ¬ O.r z < k),
          g z = W v z + if z = O.f v then c else 0 := by
        intro z hz
        have hz' := (mem_filter.1 hz).2
        by_cases hzf : z = O.f v
        · rw [hzf, hgf, hW3, ite_eq_left rfl]
        · rw [hgo z hz' hzf, ite_eq_right hzf, add_zero]
      rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq', ite_eq_left hfR]
    have e3 := sum_filter_add_sum_filter_not (G.neighborFinset v) (fun z => O.r z < k) (W v)
    rw [← hB] at e3
    have e4 : rho G W v = ∑ z ∈ G.neighborFinset v, W v z := rfl
    rw [e1, e2]
    omega
  have hrB : ∀ y ∈ B, rho G (upd W v g) y = β y + if y ∈ T then 2 else 0 := by
    intro y hy
    have hyv : y ≠ v := fun e => by
      have := ((hBmem y).1 hy).2
      rw [e] at this
      omega
    rw [rho_upd_of_ne W g hyv, ite_eq_left ((hBmem y).1 hy).1.symm, hgB y hy, h.symm y v]
    omega
  have hrN : ∀ y, y ≠ v → ¬ G.Adj y v → rho G (upd W v g) y = rho G W y := by
    intro y hy hyv
    rw [rho_upd_of_ne W g hy, ite_eq_right hyv, add_zero]
  have hne : ∀ y, O.r y < k → y ≠ v := fun y hy e => by rw [e] at hy; omega
  refine ⟨upd W v g, Function.update β v (base x), ?_⟩
  have hβv : Function.update β v (base x) v = base x := by simp
  have hβo : ∀ y, y ≠ v → Function.update β v (base x) y = β y := fun y hy => by simp [hy]
  exact
    { symm := upd_symm h.symm v g
      bound := fun a b hab => by
        by_cases ha : a = v
        · rw [ha, upd_self]
          exact hgbd b (ha ▸ hab)
        · by_cases hb : b = v
          · rw [hb, upd_symm h.symm, upd_self]
            exact hgbd a (hb ▸ hab).symm
          · rw [upd_of_ne g ha hb]
            exact h.bound a b hab
      three := fun a b hab hlt hkb hor => by
        have hbv : b ≠ v := fun e => by rw [e] at hkb; omega
        by_cases ha : a = v
        · rw [ha, upd_self]
          rw [ha] at hab hlt hor
          have hbf : b ≠ O.f v := by
            rcases hor with h' | h'
            · omega
            · exact h'
          rw [hgo b (by omega) hbf]
          exact h.three v b hab hlt (by omega) (Or.inl (by omega))
        · rw [upd_of_ne g ha hbv]
          exact h.three a b hab hlt (by omega) (hor.imp (fun h' => by omega) id)
      fwd := fun a ha hnra hfa => by
        rcases (hrk a).1 ha with ha' | hav
        · have hav := hne a ha'
          have hfav : O.f a ≠ v := fun e => by rw [e] at hfa; omega
          rw [hrN a hav (not_adj_of_fwd hv ha' hfa), upd_of_ne g hav hfav, hβo a hav]
          exact h.fwd a ha' hnra (by omega)
        · rw [hav, hrv, hβv, upd_self, hgf]
          constructor <;> intro hx <;> unfold base at hx <;> rcases hc with hc | hc | hc <;>
            omega
      state := fun a ha hnra => by
        rcases (hrk a).1 ha with ha' | hav
        · have hav := hne a ha'
          rw [hβo a hav]
          refine ⟨(h.state a ha' hnra).1, ?_⟩
          by_cases hadj : G.Adj a v
          · rw [hrB a ((hBmem a).2 ⟨hadj.symm, ha'⟩)]
            split_ifs <;> omega
          · rw [hrN a hav hadj]
            exact (h.state a ha' hnra).2
        · rw [hav, hrv, hβv]
          unfold base
          omega
      sep := fun a b hab ha hb hnra hnrb => by
        rcases (hrk a).1 ha with ha' | hav <;> rcases (hrk b).1 hb with hb' | hbv
        · rw [hβo a (hne a ha'), hβo b (hne b hb')]
          exact h.sep a b hab ha' hb' hnra hnrb
        · rw [hbv] at hab ⊢
          rw [hβo a (hne a ha'), hβv]
          have := hxβ a ((hBmem a).2 ⟨hab.symm, ha'⟩)
          unfold base
          omega
        · rw [hav] at hab ⊢
          rw [hβv, hβo b (hne b hb')]
          have := hxβ b ((hBmem b).2 ⟨hab, hb'⟩)
          unfold base
          omega
        · rw [hav, hbv] at hab
          exact absurd hab (G.irrefl)
      roots := fun a ha hnra b hab => by
        rcases (hrk a).1 ha with ha' | hav
        · have hall := fun y (hy : G.Adj a y) => lt_of_not_NR O hnra hy
          rcases O.root a hall with hdeg | ⟨-, hclosed⟩
          · have := (G.degree_pos_iff_exists_adj a).2 ⟨b, hab⟩
            omega
          · have hbv : b ≠ v := fun e => by
              have := hall b hab
              rw [e] at this
              omega
            have hav' : ¬ G.Adj a v := fun hadj => by
              have := hall v hadj
              omega
            have hbv' : ¬ G.Adj b v := fun hadj => by
              have := hclosed b hab v hadj
              omega
            rw [hrN a (hne a ha') hav', hrN b hbv hbv']
            exact h.roots a ha' hnra b hab
        · exact absurd (by rw [hav]; exact hnr) hnra }

/-- Processing a vertex without a later neighbour. -/
lemma invariant_step_root {k : ℕ} {W : V → V → ℤ} {β : V → ℤ} (h : Invariant O k W β) {v : V}
    (hv : O.r v = k) (hnr : ¬ NR O v) : ∃ W' β', Invariant O (k + 1) W' β' := by
  have hall : ∀ y, G.Adj v y → O.r y < k := fun y hy => by
    have := lt_of_not_NR O hnr hy
    omega
  have hrk := rank_succ_iff hv
  have hne : ∀ y, O.r y < k → y ≠ v := fun y hy e => by rw [e] at hy; omega
  have hnrv : ∀ a, a = v → ¬ NR O a := fun a e => by rw [e]; exact hnr
  -- Earlier roots and their neighbours are not adjacent to `v`.
  have hroots : ∀ a, O.r a < k → ¬ NR O a → ∀ b, G.Adj a b →
      ¬ G.Adj a v ∧ ¬ G.Adj b v ∧ b ≠ v := by
    intro a ha hnra b hab
    have hall' := fun y (hy : G.Adj a y) => lt_of_not_NR O hnra hy
    rcases O.root a hall' with hdeg | ⟨-, hclosed⟩
    · have := (G.degree_pos_iff_exists_adj a).2 ⟨b, hab⟩
      omega
    · refine ⟨fun hadj => ?_, fun hadj => ?_, fun e => ?_⟩
      · have := hall' v hadj
        omega
      · have := hclosed b hab v hadj
        omega
      · have := hall' b hab
        rw [e] at this
        omega
  rcases O.root v (fun y hy => lt_of_not_NR O hnr hy) with hdeg | ⟨hdeg, -⟩
  · -- `v` is isolated: nothing changes.
    have hnoadj : ∀ y, ¬ G.Adj v y := fun y hy => by
      have := (G.degree_pos_iff_exists_adj v).2 ⟨y, hy⟩
      omega
    refine ⟨W, β, ?_⟩
    exact
      { symm := h.symm
        bound := h.bound
        three := fun a b hab hlt hkb hor => h.three a b hab hlt (by omega)
          (hor.imp (fun h' => by omega) id)
        fwd := fun a ha hnra hfa => by
          rcases (hrk a).1 ha with ha' | hav
          · exact h.fwd a ha' hnra (by omega)
          · exact absurd hnra (hnrv a hav)
        state := fun a ha hnra => by
          rcases (hrk a).1 ha with ha' | hav
          · exact h.state a ha' hnra
          · exact absurd hnra (hnrv a hav)
        sep := fun a b hab ha hb hnra hnrb => by
          rcases (hrk a).1 ha with ha' | hav
          · rcases (hrk b).1 hb with hb' | hbv
            · exact h.sep a b hab ha' hb' hnra hnrb
            · exact absurd hnrb (hnrv b hbv)
          · exact absurd hnra (hnrv a hav)
        roots := fun a ha hnra b hab => by
          rcases (hrk a).1 ha with ha' | hav
          · exact h.roots a ha' hnra b hab
          · rw [hav] at hab
            exact absurd hab (hnoadj b) }
  · -- `v` has at least two neighbours, all earlier.
    have hNβ : ∀ y ∈ G.neighborFinset v, β y % 4 = 0 ∨ β y % 4 = 1 := fun y hy => by
      have hy' := (by simpa using hy)
      exact (h.state y (hall y hy') ⟨v, hy'.symm, by have := hall y hy'; omega⟩).1
    obtain ⟨T, hTN, hT⟩ := choose_root (G.neighborFinset v) β
      (rho G W v - ∑ z ∈ G.neighborFinset v, (rho G W z - β z))
      (by rw [card_neighborFinset_eq_degree]; exact hdeg) hNβ
    obtain ⟨g, hg⟩ : ∃ g : V → ℤ,
        ∀ z, g z = W v z - (rho G W z - β z) + (if z ∈ T then 2 else 0) := ⟨_, fun _ => rfl⟩
    have hgbd : ∀ z, G.Adj v z → 1 ≤ g z ∧ g z ≤ 5 := by
      intro z hz
      have := lo_bound h hv hz (hall z hz)
      rw [hg]
      split_ifs <;> omega
    have hrv : rho G (upd W v g) v =
        rho G W v - ∑ z ∈ G.neighborFinset v, (rho G W z - β z) + 2 * T.card := by
      rw [rho_upd_self, sum_congr rfl (fun z _ => hg z), sum_add_distrib, sum_sub_distrib,
        sum_ite_mem, inter_eq_right.2 hTN, sum_const, nsmul_eq_mul]
      rw [rho]
      omega
    have hrB : ∀ y, G.Adj v y → rho G (upd W v g) y = β y + if y ∈ T then 2 else 0 := by
      intro y hy
      rw [rho_upd_of_ne W g (hne y (hall y hy)), ite_eq_left hy.symm, hg y, h.symm y v]
      omega
    have hrN : ∀ y, y ≠ v → ¬ G.Adj y v → rho G (upd W v g) y = rho G W y := by
      intro y hy hyv
      rw [rho_upd_of_ne W g hy, ite_eq_right hyv, add_zero]
    refine ⟨upd W v g, β, ?_⟩
    exact
      { symm := upd_symm h.symm v g
        bound := fun a b hab => by
          by_cases ha : a = v
          · rw [ha, upd_self]
            exact hgbd b (ha ▸ hab)
          · by_cases hb : b = v
            · rw [hb, upd_symm h.symm, upd_self]
              exact hgbd a (hb ▸ hab).symm
            · rw [upd_of_ne g ha hb]
              exact h.bound a b hab
        three := fun a b hab hlt hkb hor => by
          have hbv : b ≠ v := fun e => by rw [e] at hkb; omega
          have hav : a ≠ v := fun e => by
            rw [e] at hab hlt
            have := hall b hab
            omega
          rw [upd_of_ne g hav hbv]
          exact h.three a b hab hlt (by omega) (hor.imp (fun h' => by omega) id)
        fwd := fun a ha hnra hfa => by
          rcases (hrk a).1 ha with ha' | hav
          · have hav := hne a ha'
            have hfav : O.f a ≠ v := fun e => by rw [e] at hfa; omega
            rw [hrN a hav (not_adj_of_fwd hv ha' hfa), upd_of_ne g hav hfav]
            exact h.fwd a ha' hnra (by omega)
          · exact absurd hnra (hnrv a hav)
        state := fun a ha hnra => by
          rcases (hrk a).1 ha with ha' | hav
          · refine ⟨(h.state a ha' hnra).1, ?_⟩
            by_cases hadj : G.Adj a v
            · rw [hrB a hadj.symm]
              split_ifs <;> omega
            · rw [hrN a (hne a ha') hadj]
              exact (h.state a ha' hnra).2
          · exact absurd hnra (hnrv a hav)
        sep := fun a b hab ha hb hnra hnrb => by
          rcases (hrk a).1 ha with ha' | hav
          · rcases (hrk b).1 hb with hb' | hbv
            · exact h.sep a b hab ha' hb' hnra hnrb
            · exact absurd hnrb (hnrv b hbv)
          · exact absurd hnra (hnrv a hav)
        roots := fun a ha hnra b hab => by
          rcases (hrk a).1 ha with ha' | hav
          · obtain ⟨hav', hbv', hbv⟩ := hroots a ha' hnra b hab
            rw [hrN a (hne a ha') hav', hrN b hbv hbv']
            exact h.roots a ha' hnra b hab
          · rw [hav] at hab ⊢
            rw [hrv, hrB b hab]
            exact hT b ((by simpa using hab)) }

theorem exists_invariant (k : ℕ) : ∃ W β, Invariant O k W β := by
  induction k with
  | zero => exact ⟨_, _, invariant_zero O⟩
  | succ k ih =>
    obtain ⟨W, β, h⟩ := ih
    by_cases hk : ∃ v, O.r v = k
    · obtain ⟨v, hv⟩ := hk
      by_cases hnr : NR O v
      · exact invariant_step_nonroot h hv hnr
      · exact invariant_step_root h hv hnr
    · push Not at hk
      exact ⟨W, β, invariant_skip h hk⟩

/-- The weighting given by a processing order. -/
theorem exists_weighting_of_order (O : Schedule G) :
    ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 5) ∧
      ∀ u v, G.Adj u v → ∑ e ∈ G.incidenceFinset u, w e ≠ ∑ e ∈ G.incidenceFinset v, w e := by
  obtain ⟨W, β, h⟩ := exists_invariant (O := O) (univ.sup O.r + 1)
  have hall : ∀ x, O.r x < univ.sup O.r + 1 := fun x => Nat.lt_succ_of_le (le_sup (mem_univ x))
  refine ⟨fun e => (Sym2.lift ⟨W, h.symm⟩ e).toNat, ?_, ?_⟩
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      have := h.bound a b he
      simp only [Sym2.lift_mk]
      omega
  · intro u v huv hsum
    have hcast : ∀ x, ((∑ e ∈ G.incidenceFinset x, (Sym2.lift ⟨W, h.symm⟩ e).toNat : ℕ) : ℤ) =
        rho G W x := by
      intro x
      rw [sum_incidenceFinset, rho, Nat.cast_sum]
      refine sum_congr rfl fun y hy => ?_
      simp only [Sym2.lift_mk]
      have := (h.bound x y ((by simpa using hy))).1
      omega
    have hne : rho G W u ≠ rho G W v := by
      by_cases hu : NR O u
      · by_cases hv : NR O v
        · have h1 := h.state u (hall u) hu
          have h2 := h.state v (hall v) hv
          have h3 := h.sep u v huv (hall u) (hall v) hu hv
          omega
        · exact (h.roots v (hall v) hv u huv.symm).symm
      · exact h.roots u (hall u) hu v huv
    apply hne
    rw [← hcast u, ← hcast v]
    exact congrArg _ hsum

end Core

section Construction

variable {V : Type*} {G : SimpleGraph V}

lemma exists_adj_dist_lt {a v : V} (h : G.Reachable v a) (hne : v ≠ a) :
    ∃ u, G.Adj v u ∧ G.dist u a < G.dist v a := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  cases p with
  | nil => exact absurd rfl hne
  | cons hadj q =>
    refine ⟨_, hadj, ?_⟩
    rw [Walk.length_cons] at hp
    have := G.dist_le q
    omega

variable [Fintype V] [DecidableRel G.Adj]

variable (G) in
open scoped Classical in
/-- The last vertex of a component: a vertex of degree at least `2` if there is one. -/
noncomputable def compRoot (C : G.ConnectedComponent) : V :=
  if h : ∃ u, G.connectedComponentMk u = C ∧ 2 ≤ G.degree u then h.choose
  else (C.ind (β := fun C => ∃ v, G.connectedComponentMk v = C) fun v => ⟨v, rfl⟩).choose

lemma compRoot_mk (C : G.ConnectedComponent) : G.connectedComponentMk (compRoot G C) = C := by
  unfold compRoot
  split_ifs with h
  · exact h.choose_spec.1
  · exact (C.ind (β := fun C => ∃ v, G.connectedComponentMk v = C) fun v => ⟨v, rfl⟩).choose_spec

lemma degree_compRoot (hG : ∀ u v, G.Adj u v → 2 ≤ G.degree u ∨ 2 ≤ G.degree v)
    (C : G.ConnectedComponent) : G.degree (compRoot G C) = 0 ∨ 2 ≤ G.degree (compRoot G C) := by
  by_cases h : ∃ u, G.connectedComponentMk u = C ∧ 2 ≤ G.degree u
  · right
    unfold compRoot
    rw [dite_eq_left h]
    exact h.choose_spec.2
  · by_contra hc
    push Not at hc
    obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj (compRoot G C)).1 (by omega)
    have hdu : G.degree u < 2 := by
      by_contra hu2
      push Not at hu2
      exact h ⟨u, by rw [← ConnectedComponent.connectedComponentMk_eq_of_adj hu, compRoot_mk], hu2⟩
    rcases hG _ _ hu with h1 | h1 <;> omega

variable (G) in
/-- The root of the component of `v`. -/
noncomputable def rootOf (v : V) : V := compRoot G (G.connectedComponentMk v)

lemma reachable_rootOf (v : V) : G.Reachable v (rootOf G v) :=
  ConnectedComponent.exact (compRoot_mk (G.connectedComponentMk v)).symm

lemma rootOf_eq_of_adj {u v : V} (h : G.Adj u v) : rootOf G u = rootOf G v := by
  unfold rootOf
  rw [ConnectedComponent.connectedComponentMk_eq_of_adj h]

variable (G) in
/-- The sort key: component, then distance to the root (larger first), then a tie-break. -/
noncomputable def sortKey (v : V) : ℕ ×ₗ ℤ ×ₗ ℕ :=
  toLex ((Fintype.equivFin V (rootOf G v) : ℕ),
    toLex (-(G.dist v (rootOf G v) : ℤ), (Fintype.equivFin V v : ℕ)))

lemma sortKey_injective : Function.Injective (sortKey G) := by
  intro u v h
  have := congrArg (fun p => (ofLex (ofLex p).2).2) h
  simp only [sortKey, ofLex_toLex] at this
  exact (Fintype.equivFin V).injective (Fin.ext this)

variable (G) in
/-- The rank of `v`: the number of vertices with a smaller key. -/
noncomputable def position (v : V) : ℕ := #{u | sortKey G u < sortKey G v}

lemma position_lt_of_sortKey_lt {u v : V} (h : sortKey G u < sortKey G v) :
    position G u < position G v := by
  unfold position
  refine card_lt_card ⟨fun w hw => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact hw.trans h
  · have := hsub (by simp [h] : u ∈ ({w | sortKey G w < sortKey G v} : Finset V))
    simp at this

lemma position_le_of_sortKey_le {u v : V} (h : sortKey G u ≤ sortKey G v) :
    position G u ≤ position G v := by
  unfold position
  refine card_le_card fun w hw => ?_
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  exact hw.trans_le h

lemma position_injective : Function.Injective (position G) := by
  intro u v h
  refine sortKey_injective (G := G) (le_antisymm ?_ ?_)
  · exact not_lt.1 fun h' => absurd h (position_lt_of_sortKey_lt h').ne'
  · exact not_lt.1 fun h' => absurd h (position_lt_of_sortKey_lt h').ne

/-- A vertex that is not the root of its component has a later neighbour. -/
lemma exists_later_of_ne_rootOf {x : V} (hx : x ≠ rootOf G x) :
    ∃ u, G.Adj x u ∧ position G x < position G u := by
  obtain ⟨u, hxu, hd⟩ := exists_adj_dist_lt (reachable_rootOf x) hx
  refine ⟨u, hxu, position_lt_of_sortKey_lt ?_⟩
  have hR := rootOf_eq_of_adj hxu
  rw [hR] at hd
  unfold sortKey
  rw [hR]
  refine Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl ?_)⟩)
  dsimp only
  omega

/-- A processing order for a graph without isolated edges. -/
noncomputable def mkSchedule (hG : ∀ u v, G.Adj u v → 2 ≤ G.degree u ∨ 2 ≤ G.degree v) :
    Schedule G where
  r := position G
  f x := if h : ((G.neighborFinset x).filter (fun y => position G x < position G y)).Nonempty then
      (exists_min_image _ (position G) h).choose else x
  inj := position_injective
  fwd x y hxy hlt := by
    have hne : ((G.neighborFinset x).filter (fun y => position G x < position G y)).Nonempty :=
      ⟨y, by simp [hxy, hlt]⟩
    simp only [dite_eq_left hne]
    obtain ⟨hmem, hmin⟩ := (exists_min_image _ (position G) hne).choose_spec
    rw [mem_filter, mem_neighborFinset] at hmem
    exact ⟨hmem.1, hmem.2, fun z hz hlt' => hmin z (by simp [hz, hlt'])⟩
  root x hx := by
    have hxR : rootOf G x = x := by
      by_contra hxR
      obtain ⟨u, hxu, hlt⟩ := exists_later_of_ne_rootOf (Ne.symm hxR)
      exact absurd (hx u hxu) (not_lt.2 hlt.le)
    have hdeg := degree_compRoot hG (G.connectedComponentMk x)
    change G.degree (rootOf G x) = 0 ∨ 2 ≤ G.degree (rootOf G x) at hdeg
    rw [hxR] at hdeg
    rcases hdeg with hdeg | hdeg
    · exact Or.inl hdeg
    refine Or.inr ⟨hdeg, fun u hxu y huy => position_le_of_sortKey_le ?_⟩
    have hRy : rootOf G y = x := by rw [← rootOf_eq_of_adj huy, ← rootOf_eq_of_adj hxu, hxR]
    have hyx : G.Reachable y x := hRy ▸ reachable_rootOf y
    by_cases hyx' : y = x
    · exact hyx' ▸ le_rfl
    · apply le_of_lt
      have hpos := hyx.pos_dist_of_ne hyx'
      unfold sortKey
      rw [hRy, hxR, SimpleGraph.dist_self]
      refine Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl ?_)⟩)
      dsimp only
      omega

end Construction

/-- **Kalkowski–Karoński–Pfender (2010).** Every finite simple graph in which no edge has both
endpoints of degree `1` has edge weights in `{1, …, 5}` such that adjacent vertices have
different weighted degrees. -/
theorem exists_weighting {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v → 2 ≤ G.degree u ∨ 2 ≤ G.degree v) :
    ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 5) ∧
      ∀ u v, G.Adj u v → ∑ e ∈ G.incidenceFinset u, w e ≠ ∑ e ∈ G.incidenceFinset v, w e :=
  exists_weighting_of_order (mkSchedule hG)

end OneTwoThree

open SimpleGraph Finset

namespace OneTwoThreeConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

def weightedDegree (G : SimpleGraph V) [DecidableRel G.Adj] (w : Sym2 V → ℕ) (v : V) : ℕ :=
  ∑ e ∈ G.incidenceFinset v, w e

def IsVertexColouringWeighting (G : SimpleGraph V) [DecidableRel G.Adj] (w : Sym2 V → ℕ) : Prop :=
  ∀ u v, G.Adj u v → weightedDegree G w u ≠ weightedDegree G w v

def NoIsolatedEdge (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v, G.Adj u v → 2 ≤ G.degree u ∨ 2 ≤ G.degree v

theorem one_two_three_conjecture.variants.one_to_five
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolatedEdge G) :
    ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 5) ∧
      IsVertexColouringWeighting G w :=
  OneTwoThree.exists_weighting G hG

theorem one_two_three_conjecture.variants.one_to_thirty
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolatedEdge G) :
    ∃ w : Sym2 V → ℕ, (∀ e ∈ G.edgeFinset, 1 ≤ w e ∧ w e ≤ 30) ∧
      IsVertexColouringWeighting G w := by
  obtain ⟨w, hw, hc⟩ := OneTwoThree.exists_weighting G hG
  exact ⟨w, fun e he => ⟨(hw e he).1, (hw e he).2.trans (by omega)⟩, hc⟩

end OneTwoThreeConjecture

end
