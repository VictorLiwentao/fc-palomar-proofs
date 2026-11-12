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
# Disconnected graphs are reconstructible

This file proves the upstream statement
`ReconstructionConjecture.reconstruction_conjecture.variants.disconnected`: if `G` has at least
three vertices, `G` is not connected, and `H` has the same deck as `G`, then `G ≃g H`.

For graphs `F`, `G` and a vertex set `P`, let `emb F G P` be the number of induced embeddings of
`F` into `G` with image in `P`.

1. **Kelly's lemma** (`sum_emb_compl_singleton`): $\sum_v \mathrm{emb}(F, G - v) =
   (n - |F|)\,\mathrm{emb}(F, G)$. So hypomorphic graphs have the same number of embeddings of
   every graph with fewer than $n$ vertices (`card_embedding_eq_of_hypomorphic`).
2. `H` is not connected (`not_connected_of_hypomorphic`): a connected `H` has two vertices whose
   deletion leaves it connected (two leaves of a spanning tree), and then `G` would be
   connected too (`connected_of_connected_cards`).
3. **Peeling** (`iso_of_hyp`). Suppose `G.induce P` and `H.induce Q` have the same number of
   embeddings of every connected graph with fewer than $n$ vertices. Take a largest connected
   set `C ⊆ P`. It embeds into `H` with image `T ⊆ Q`, and `T` is a largest connected subset of
   `Q`. Both pieces are closed, so the counts split, and the remainders `P \ C` and `Q \ T`
   satisfy the same hypothesis. By induction they are isomorphic; glue the two isomorphisms.

The definitions are those of `FormalConjectures/Wikipedia/ReconstructionConjecture.lean`.

*References:*
* Kelly, P. J. (1957). "A congruence theorem for trees." *Pacific J. Math.* 7, pp. 961--968.
* Bondy, J. A. (1991). "A graph reconstructor's manual." In *Surveys in Combinatorics*,
  LMS Lecture Note Series 166, Cambridge University Press, pp. 221--252.
-/

@[expose] public section

namespace ReconstructionConjecture

variable {V W : Type*}

/-- Two graphs are **hypomorphic** if there is a bijection `σ` between their vertex sets such
that the vertex-deleted subgraphs `G - v` and `H - σ v` are isomorphic for every vertex `v`;
i.e. `G` and `H` have the same deck of vertex-deleted subgraphs. -/
def Hypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)

/-- Two graphs are **edge-hypomorphic** if there is a bijection `σ` between their edge sets
such that the edge-deleted subgraphs `G - e` and `H - σ e` are isomorphic for every edge `e`;
i.e. `G` and `H` have the same deck of edge-deleted subgraphs. -/
def EdgeHypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
    Nonempty (G.deleteEdges {(e : Sym2 V)} ≃g H.deleteEdges {((σ e : H.edgeSet) : Sym2 W)})

/-- Isomorphic graphs are hypomorphic: an isomorphism restricts to an isomorphism between
corresponding vertex-deleted subgraphs. -/
lemma Hypomorphic.of_iso {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    Hypomorphic G H := by
  refine ⟨f.toEquiv, fun v => ⟨⟨Equiv.subtypeEquiv f.toEquiv fun x => ?_, ?_⟩⟩⟩
  · simp
  · intro a b
    exact f.map_rel_iff

/-- Hypomorphic graphs have the same number of vertices. -/
lemma Hypomorphic.card_eq [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Hypomorphic G H) : Fintype.card V = Fintype.card W := by
  obtain ⟨σ, -⟩ := h
  exact Fintype.card_congr σ

/-- Any two graphs on subsingleton vertex types are isomorphic. -/
lemma nonempty_iso_of_subsingleton [Subsingleton V] [Subsingleton W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ≃ W) : Nonempty (G ≃g H) := by
  refine ⟨⟨e, ?_⟩⟩
  intro a b
  cases Subsingleton.elim a b
  exact iff_of_false (H.irrefl) (G.irrefl)

end ReconstructionConjecture

namespace ReconstructionDisconnected

open SimpleGraph ReconstructionConjecture

section Embeddings

variable {U V W : Type*} {F : SimpleGraph U} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The number of induced embeddings of `F` into `G` with image in `P`. -/
noncomputable def emb (F : SimpleGraph U) (G : SimpleGraph V) (P : Set V) : ℕ :=
  Nat.card {f : F ↪g G // ∀ u, f u ∈ P}

lemma finite_embedding [Finite U] [Finite V] : Finite (F ↪g G) :=
  Finite.of_injective _ DFunLike.coe_injective

/-- An embedding with image in `P`, as an embedding into `G.induce P`. -/
def restrict (f : F ↪g G) {P : Set V} (hf : ∀ u, f u ∈ P) : F ↪g G.induce P where
  toFun u := ⟨f u, hf u⟩
  inj' _ _ h := f.injective (congrArg Subtype.val h)
  map_rel_iff' := f.map_rel_iff

/-- Push an embedding with image in `P` through `G.induce P ≃g H.induce Q`. -/
def transport {P : Set V} {Q : Set W} (φ : G.induce P ≃g H.induce Q) (f : F ↪g G)
    (hf : ∀ u, f u ∈ P) : F ↪g H :=
  (Embedding.induce Q).comp (φ.toEmbedding.comp (restrict f hf))

lemma transport_apply {P : Set V} {Q : Set W} (φ : G.induce P ≃g H.induce Q) (f : F ↪g G)
    (hf : ∀ u, f u ∈ P) (u : U) : transport φ f hf u = (φ ⟨f u, hf u⟩ : W) := rfl

/-- Isomorphic induced subgraphs have the same embedding counts. -/
lemma emb_eq_of_iso {P : Set V} {Q : Set W} (φ : G.induce P ≃g H.induce Q)
    (F : SimpleGraph U) : emb F G P = emb F H Q := by
  refine Nat.card_congr
    { toFun := fun f => ⟨transport φ f.1 f.2, fun u => (φ ⟨f.1 u, f.2 u⟩).2⟩
      invFun := fun g => ⟨transport φ.symm g.1 g.2, fun u => (φ.symm ⟨g.1 u, g.2 u⟩).2⟩
      left_inv := fun f => ?_
      right_inv := fun g => ?_ }
  · refine Subtype.ext (DFunLike.ext _ _ fun u => ?_)
    simp only [transport_apply, Subtype.coe_eta, RelIso.symm_apply_apply]
  · refine Subtype.ext (DFunLike.ext _ _ fun u => ?_)
    simp only [transport_apply, Subtype.coe_eta, RelIso.apply_symm_apply]

lemma emb_univ (F : SimpleGraph U) (G : SimpleGraph V) :
    emb F G Set.univ = Nat.card (F ↪g G) :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun _ _ => Set.mem_univ _)

/-- **Kelly's lemma** for induced embeddings. -/
lemma sum_emb_compl_singleton [Fintype U] [Fintype V] [DecidableEq V] (F : SimpleGraph U)
    (G : SimpleGraph V) :
    ∑ v, emb F G {v}ᶜ = (Fintype.card V - Fintype.card U) * Nat.card (F ↪g G) := by
  classical
  have : Finite (F ↪g G) := finite_embedding
  let : Fintype (F ↪g G) := Fintype.ofFinite _
  have h1 : ∀ v, emb F G {v}ᶜ =
      ∑ f : F ↪g G, if ∀ u, f u ≠ v then 1 else 0 := by
    intro v
    rw [emb, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hf : ∀ u, f u ≠ v
    · rw [ite_eq_left hf, ite_eq_left fun u => by simpa using hf u]
    · rw [ite_eq_right hf, ite_eq_right fun h => hf fun u => by simpa using h u]
  have h2 : ∀ f : F ↪g G, (∑ v, if ∀ u, f u ≠ v then 1 else 0) =
      Fintype.card V - Fintype.card U := by
    intro f
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun v => ∀ u, f u ≠ v) = (Finset.univ.image f)ᶜ := by
      ext v
      simp
    rw [this, Finset.card_compl, Finset.card_image_of_injective _ f.injective, Finset.card_univ]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun f _ => h2 f, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Nat.card_eq_fintype_card, mul_comm]

/-- Hypomorphic graphs have the same number of embeddings of each graph with fewer vertices. -/
lemma card_embedding_eq_of_hypomorphic [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (h : Hypomorphic G H) [Finite U] (F : SimpleGraph U) (hU : Nat.card U < Fintype.card V) :
    Nat.card (F ↪g G) = Nat.card (F ↪g H) := by
  obtain ⟨σ, hσ⟩ := h
  let := Fintype.ofFinite U
  have hsum : ∑ v, emb F G {v}ᶜ = ∑ w, emb F H {w}ᶜ :=
    Fintype.sum_equiv σ _ _ fun v => emb_eq_of_iso (hσ v).some F
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  rw [sum_emb_compl_singleton, sum_emb_compl_singleton, ← hcard] at hsum
  rw [Nat.card_eq_fintype_card] at hU
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hU) hsum

/-- A property closed under adjacency propagates along reachability. -/
lemma of_reachable {p : U → Prop} (hp : ∀ a b, F.Adj a b → p a → p b) {a b : U}
    (h : F.Reachable a b) (ha : p a) : p b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hp _ _ hadj ha)

/-- For connected `F`, the embeddings into a set split over a closed piece `C`. -/
lemma emb_eq_add [Finite U] [Finite V] {P C : Set V} (hF : F.Connected) (hC : C ⊆ P)
    (hGC : ∀ x ∈ C, ∀ y ∈ P, G.Adj x y → y ∈ C) :
    emb F G P = emb F G C + emb F G (P \ C) := by
  classical
  have : Finite (F ↪g G) := finite_embedding
  obtain ⟨u₀⟩ := hF.nonempty
  have hstep : ∀ f : F ↪g G, (∀ u, f u ∈ P) → ∀ a b, F.Adj a b → f a ∈ C → f b ∈ C :=
    fun f hf a b hab ha => hGC _ ha _ (hf b) (f.map_adj_iff.mpr hab)
  have key : ∀ f : F ↪g G, (∀ u, f u ∈ P) ↔ (∀ u, f u ∈ C) ∨ (∀ u, f u ∈ P \ C) := by
    intro f
    constructor
    · intro hf
      by_cases h0 : f u₀ ∈ C
      · exact Or.inl fun u => of_reachable (hstep f hf) (hF.preconnected u₀ u) h0
      · exact Or.inr fun u =>
          ⟨hf u, fun hu => h0 (of_reachable (hstep f hf) (hF.preconnected u u₀) hu)⟩
    · rintro (h | h) u
      · exact hC (h u)
      · exact (h u).1
  have hdisj : Disjoint (fun f : F ↪g G => ∀ u, f u ∈ C) (fun f => ∀ u, f u ∈ P \ C) := by
    intro r hr1 hr2 f hf
    exact ((hr2 f hf) u₀).2 ((hr1 f hf) u₀)
  unfold emb
  rw [Nat.card_congr (Equiv.subtypeEquivRight key), Nat.card_congr (subtypeOrEquiv _ _ hdisj),
    Nat.card_sum]

lemma exists_of_emb_pos {P : Set W} (h : 0 < emb F H P) :
    ∃ f : F ↪g H, ∀ u, f u ∈ P := by
  by_contra hcon
  push Not at hcon
  have : IsEmpty {f : F ↪g H // ∀ u, f u ∈ P} := ⟨fun f => by
    obtain ⟨u, hu⟩ := hcon f.1
    exact hu (f.2 u)⟩
  simp [emb, Nat.card_of_isEmpty] at h

end Embeddings

section Connectivity

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma reachable_of_connected_card {a x y : V} (h : (G.induce {a}ᶜ).Connected) (hx : x ≠ a)
    (hy : y ≠ a) : G.Reachable x y :=
  (h.preconnected ⟨x, hx⟩ ⟨y, hy⟩).map (Embedding.induce _).toHom

/-- With at least three vertices, two distinct connected cards force `G` to be connected. -/
lemma connected_of_connected_cards [Fintype V] (hV : 3 ≤ Fintype.card V) {a b : V} (hab : a ≠ b)
    (ha : (G.induce {a}ᶜ).Connected) (hb : (G.induce {b}ᶜ).Connected) : G.Connected := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, z ≠ a ∧ z ≠ b := by
    by_contra hcon
    push Not at hcon
    have : (Finset.univ : Finset V) ⊆ {a, b} := fun z _ => by
      by_cases hza : z = a
      · simp [hza]
      · simp [hcon z hza]
    have := Finset.card_le_card this
    rw [Finset.card_univ, Finset.card_pair hab] at this
    omega
  refine (connected_iff G).mpr ⟨fun x y => ?_, ⟨a⟩⟩
  by_cases hxa : x = a
  · by_cases hya : y = a
    · rw [hxa, hya]
    · by_cases hyb : y = b
      · subst hxa hyb
        exact (reachable_of_connected_card hb hab hz.2).trans
          (reachable_of_connected_card ha hz.1 (Ne.symm hab))
      · exact reachable_of_connected_card hb (hxa ▸ hab) hyb
  · by_cases hya : y = a
    · by_cases hxb : x = b
      · subst hya hxb
        exact (reachable_of_connected_card ha (Ne.symm hab) hz.1).trans
          (reachable_of_connected_card hb hz.2 hab)
      · exact reachable_of_connected_card hb hxb (hya ▸ hab)
    · exact reachable_of_connected_card ha hxa hya

/-- A graph hypomorphic to a disconnected graph on at least three vertices is disconnected. -/
lemma not_connected_of_hypomorphic [Fintype V] [Fintype W] (hV : 3 ≤ Fintype.card V)
    (hd : ¬G.Connected) (h : Hypomorphic G H) : ¬H.Connected := by
  intro hH
  obtain ⟨σ, hσ⟩ := h
  have hW : 3 ≤ Fintype.card W := Fintype.card_congr σ ▸ hV
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨T, hTH, hT⟩ := hH.exists_isTree_le
  classical
  obtain ⟨u, w, huw, hu, hw⟩ := hT.exists_ne_and_degree_eq_one
  have hcu : (H.induce {u}ᶜ).Connected :=
    (hT.1.induce_compl_singleton_of_degree_eq_one hu).mono fun _ _ h => hTH h
  have hcw : (H.induce {w}ᶜ).Connected :=
    (hT.1.induce_compl_singleton_of_degree_eq_one hw).mono fun _ _ h => hTH h
  have iu := hσ (σ.symm u)
  have iw := hσ (σ.symm w)
  rw [σ.apply_symm_apply] at iu iw
  exact hd (connected_of_connected_cards hV (σ.symm.injective.ne huw)
    (iu.some.connected_iff.mpr hcu) (iw.some.connected_iff.mpr hcw))

/-- A connected induced subgraph of a disconnected graph misses a vertex. -/
lemma ncard_lt_of_not_connected [Fintype V] (hd : ¬G.Connected) {S : Set V}
    (hS : (G.induce S).Connected) : S.ncard < Fintype.card V := by
  by_contra hlt
  have hS' : S = Set.univ := Set.eq_of_subset_of_ncard_le (Set.subset_univ S)
    (by rw [Set.ncard_univ, Nat.card_eq_fintype_card]; omega)
  subst hS'
  exact hd ((induceUnivIso G).connected_iff.mp hS)

/-- Adding a neighbour to a connected set keeps it connected. -/
lemma connected_insert {C : Set V} (hC : (G.induce C).Connected) {x y : V} (hx : x ∈ C)
    (hxy : G.Adj x y) : (G.induce (insert y C)).Connected := by
  let ι := G.induceHomOfLE (Set.subset_insert y C)
  have hreach : ∀ c : (insert y C : Set V), (G.induce (insert y C)).Reachable ⟨x, Or.inr hx⟩ c := by
    rintro ⟨c, hc⟩
    by_cases hcC : c ∈ C
    · exact (hC.preconnected ⟨x, hx⟩ ⟨c, hcC⟩).map ι.toHom
    · have hcy : c = y := by
        rcases hc with hc | hc
        · exact hc
        · exact absurd hc hcC
      have hxc : G.Adj x c := hcy ▸ hxy
      exact Adj.reachable hxc
  exact (connected_iff _).mpr ⟨fun a b => (hreach a).symm.trans (hreach b), ⟨⟨y, Set.mem_insert _ _⟩⟩⟩

lemma connected_induce_singleton (v : V) : (G.induce {v}).Connected :=
  (connected_iff _).mpr ⟨fun a b => by
    have : a = b := Subtype.ext ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)
    subst this
    exact Reachable.refl _, ⟨⟨v, rfl⟩⟩⟩

/-- A largest connected subset is closed under adjacency inside `P`. -/
lemma closed_of_max {P C : Set V} [Finite V] (hCP : C ⊆ P) (hC : (G.induce C).Connected)
    (hmax : ∀ S ⊆ P, (G.induce S).Connected → S.ncard ≤ C.ncard) :
    ∀ x ∈ C, ∀ y ∈ P, G.Adj x y → y ∈ C := by
  intro x hx y hy hxy
  by_contra hyC
  have := hmax (insert y C) (Set.insert_subset hy hCP) (connected_insert hC hx hxy)
  rw [Set.ncard_insert_of_notMem hyC] at this
  omega

end Connectivity

section Glue

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Glue isomorphisms on a closed piece and on its complement. -/
lemma nonempty_iso_glue {P C : Set V} {Q T : Set W} (hC : C ⊆ P) (hT : T ⊆ Q)
    (hGC : ∀ x ∈ C, ∀ y ∈ P, G.Adj x y → y ∈ C) (hHT : ∀ x ∈ T, ∀ y ∈ Q, H.Adj x y → y ∈ T)
    (φ : G.induce C ≃g H.induce T) (ψ : G.induce (P \ C) ≃g H.induce (Q \ T)) :
    Nonempty (G.induce P ≃g H.induce Q) := by
  classical
  let f : P → Q := fun x =>
    if h : (x : V) ∈ C then ⟨(φ ⟨x, h⟩).1, hT (φ ⟨x, h⟩).2⟩
    else ⟨(ψ ⟨x, x.2, h⟩).1, (ψ ⟨x, x.2, h⟩).2.1⟩
  let g : Q → P := fun y =>
    if h : (y : W) ∈ T then ⟨(φ.symm ⟨y, h⟩).1, hC (φ.symm ⟨y, h⟩).2⟩
    else ⟨(ψ.symm ⟨y, y.2, h⟩).1, (ψ.symm ⟨y, y.2, h⟩).2.1⟩
  have f_in {x : P} (h : (x : V) ∈ C) : (f x : W) = φ ⟨x, h⟩ := by simp [f, h]
  have f_out {x : P} (h : (x : V) ∉ C) : (f x : W) = ψ ⟨x, x.2, h⟩ := by simp [f, h]
  have g_in {y : Q} (h : (y : W) ∈ T) : (g y : V) = φ.symm ⟨y, h⟩ := by simp [g, h]
  have g_out {y : Q} (h : (y : W) ∉ T) : (g y : V) = ψ.symm ⟨y, y.2, h⟩ := by simp [g, h]
  have fT {x : P} : ((f x : W) ∈ T ↔ (x : V) ∈ C) := by
    by_cases h : (x : V) ∈ C
    · rw [f_in h]
      exact iff_of_true (φ ⟨x, h⟩).2 h
    · rw [f_out h]
      exact iff_of_false (ψ ⟨x, x.2, h⟩).2.2 h
  have gC {y : Q} : ((g y : V) ∈ C ↔ (y : W) ∈ T) := by
    by_cases h : (y : W) ∈ T
    · rw [g_in h]
      exact iff_of_true (φ.symm ⟨y, h⟩).2 h
    · rw [g_out h]
      exact iff_of_false (ψ.symm ⟨y, y.2, h⟩).2.2 h
  refine ⟨⟨⟨f, g, fun x => ?_, fun y => ?_⟩, fun {a b} => ?_⟩⟩
  · apply Subtype.ext
    by_cases h : (x : V) ∈ C
    · have e : (⟨(f x : W), fT.mpr h⟩ : T) = φ ⟨x, h⟩ := Subtype.ext (f_in h)
      rw [g_in (fT.mpr h), e, RelIso.symm_apply_apply]
    · have e : (⟨(f x : W), (f x).2, mt fT.mp h⟩ : ↥(Q \ T)) = ψ ⟨x, x.2, h⟩ :=
        Subtype.ext (f_out h)
      rw [g_out (mt fT.mp h), e, RelIso.symm_apply_apply]
  · apply Subtype.ext
    by_cases h : (y : W) ∈ T
    · have e : (⟨(g y : V), gC.mpr h⟩ : C) = φ.symm ⟨y, h⟩ := Subtype.ext (g_in h)
      rw [f_in (gC.mpr h), e, RelIso.apply_symm_apply]
    · have e : (⟨(g y : V), (g y).2, mt gC.mp h⟩ : ↥(P \ C)) = ψ.symm ⟨y, y.2, h⟩ :=
        Subtype.ext (g_out h)
      rw [f_out (mt gC.mp h), e, RelIso.apply_symm_apply]
  · change H.Adj (f a : W) (f b : W) ↔ G.Adj (a : V) (b : V)
    by_cases ha : (a : V) ∈ C <;> by_cases hb : (b : V) ∈ C
    · rw [f_in ha, f_in hb]
      exact φ.map_adj_iff
    · rw [f_in ha, f_out hb]
      exact iff_of_false (fun h => (ψ ⟨b, b.2, hb⟩).2.2 (hHT _ (φ ⟨a, ha⟩).2 _
        (ψ ⟨b, b.2, hb⟩).2.1 h)) (fun h => hb (hGC _ ha _ b.2 h))
    · rw [f_out ha, f_in hb]
      exact iff_of_false (fun h => (ψ ⟨a, a.2, ha⟩).2.2 (hHT _ (φ ⟨b, hb⟩).2 _
        (ψ ⟨a, a.2, ha⟩).2.1 h.symm)) (fun h => ha (hGC _ hb _ a.2 h.symm))
    · rw [f_out ha, f_out hb]
      exact ψ.map_adj_iff

end Glue

section Peeling

variable {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

/-- `G.induce P` and `H.induce Q` have the same embedding counts of connected graphs with
fewer than `|V|` vertices. -/
def Hyp (G : SimpleGraph V) (H : SimpleGraph W) (P : Set V) (Q : Set W) : Prop :=
  ∀ (U : Type) [Finite U] (F : SimpleGraph U), F.Connected → Nat.card U < Fintype.card V →
    emb F G P = emb F H Q

lemma emb_induce_pos {S P : Set V} (hSP : S ⊆ P) : 0 < emb (G.induce S) G P := by
  have : Finite (G.induce S ↪g G) := finite_embedding
  have : Nonempty {f : G.induce S ↪g G // ∀ u, f u ∈ P} :=
    ⟨⟨Embedding.induce S, fun u => hSP u.2⟩⟩
  exact Nat.card_pos

omit [Fintype W] in
/-- An embedding of `G.induce C` with image in `Q` gives a set `T ⊆ Q` with
`G.induce C ≃g H.induce T`. -/
lemma exists_iso_of_hyp {P : Set V} {Q : Set W} (hyp : Hyp G H P Q) {C : Set V} (hCP : C ⊆ P)
    (hC : (G.induce C).Connected) (hCn : C.ncard < Fintype.card V) :
    ∃ T ⊆ Q, Nonempty (G.induce C ≃g H.induce T) := by
  have h := hyp C (G.induce C) hC hCn
  have h2 : 0 < emb (G.induce C) H Q := h ▸ emb_induce_pos hCP
  obtain ⟨f, hf⟩ := exists_of_emb_pos h2
  exact ⟨Set.range f, Set.range_subset_iff.mpr hf, ⟨f.isoInduceRange⟩⟩

lemma hyp_symm {P : Set V} {Q : Set W} (hcard : Fintype.card V = Fintype.card W)
    (hyp : Hyp G H P Q) : Hyp H G Q P :=
  fun U _ F hF hU => (hyp U F hF (hcard ▸ hU)).symm

lemma iso_of_hyp_empty {P : Set V} {Q : Set W} (hV : 3 ≤ Fintype.card V) (hP : P = ∅)
    (hyp : Hyp G H P Q) : Nonempty (G.induce P ≃g H.induce Q) := by
  have hQ : Q = ∅ := by
    by_contra hQ
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hQ
    have hF : (⊥ : SimpleGraph Unit).Connected :=
      (connected_iff _).mpr ⟨fun _ _ => Reachable.refl _, ⟨()⟩⟩
    have h := hyp Unit ⊥ hF (by rw [Nat.card_unique]; omega)
    have e1 : emb (⊥ : SimpleGraph Unit) G P = 0 := by
      have : IsEmpty {f : (⊥ : SimpleGraph Unit) ↪g G // ∀ u, f u ∈ P} :=
        ⟨fun f => by simpa [hP] using f.2 ()⟩
      exact Nat.card_of_isEmpty
    let ι : (⊥ : SimpleGraph Unit) ↪g H :=
      ⟨⟨fun _ => w, fun _ _ _ => rfl⟩, fun {_ _} => iff_of_false (H.irrefl (v := w)) id⟩
    have e2 : 0 < emb (⊥ : SimpleGraph Unit) H Q := by
      have : Finite ((⊥ : SimpleGraph Unit) ↪g H) := finite_embedding
      have : Nonempty {f : (⊥ : SimpleGraph Unit) ↪g H // ∀ u, f u ∈ Q} := ⟨⟨ι, fun _ => hw⟩⟩
      exact Nat.card_pos
    omega
  subst hP hQ
  have : IsEmpty (∅ : Set V) := Set.isEmpty_coe_sort.mpr rfl
  have : IsEmpty (∅ : Set W) := Set.isEmpty_coe_sort.mpr rfl
  exact ⟨⟨Equiv.equivOfIsEmpty _ _, fun {a} => isEmptyElim a⟩⟩

/-- **Peeling.** Equal embedding counts of connected graphs give an isomorphism. -/
lemma iso_of_hyp (hV : 3 ≤ Fintype.card V) (hcard : Fintype.card V = Fintype.card W)
    (hGn : ∀ S : Set V, (G.induce S).Connected → S.ncard < Fintype.card V)
    (hHn : ∀ T : Set W, (H.induce T).Connected → T.ncard < Fintype.card V) :
    ∀ m (P : Set V) (Q : Set W), P.ncard ≤ m → Hyp G H P Q →
      Nonempty (G.induce P ≃g H.induce Q) := by
  intro m
  induction m with
  | zero =>
    intro P Q hP hyp
    exact iso_of_hyp_empty hV ((Set.ncard_eq_zero (Set.toFinite P)).mp (Nat.le_zero.mp hP)) hyp
  | succ m ih =>
    intro P Q hP hyp
    rcases P.eq_empty_or_nonempty with hPe | ⟨v, hv⟩
    · exact iso_of_hyp_empty hV hPe hyp
    -- a largest connected subset `C` of `P`
    obtain ⟨C, ⟨hCP, hC⟩, hmax⟩ := Set.exists_max_image
      {S : Set V | S ⊆ P ∧ (G.induce S).Connected} Set.ncard (Set.toFinite _)
      ⟨{v}, Set.singleton_subset_iff.mpr hv, connected_induce_singleton v⟩
    have hmax' : ∀ S ⊆ P, (G.induce S).Connected → S.ncard ≤ C.ncard :=
      fun S hS hSc => hmax S ⟨hS, hSc⟩
    obtain ⟨T, hTQ, ⟨φ⟩⟩ := exists_iso_of_hyp hyp hCP hC (hGn C hC)
    have hTc : (H.induce T).Connected := φ.connected_iff.mp hC
    have hCT : C.ncard = T.ncard := Nat.card_congr φ.toEquiv
    -- `T` is a largest connected subset of `Q`
    have hmaxT : ∀ S ⊆ Q, (H.induce S).Connected → S.ncard ≤ T.ncard := by
      intro S hSQ hSc
      obtain ⟨S', hS'P, ⟨χ⟩⟩ :=
        exists_iso_of_hyp (hyp_symm hcard hyp) hSQ hSc (hcard ▸ hHn S hSc)
      have : S.ncard = S'.ncard := Nat.card_congr χ.toEquiv
      rw [this, ← hCT]
      exact hmax' S' hS'P (χ.connected_iff.mp hSc)
    have hGC := closed_of_max hCP hC hmax'
    have hHT := closed_of_max hTQ hTc hmaxT
    -- the remainders satisfy the hypothesis
    have hyp' : Hyp G H (P \ C) (Q \ T) := by
      intro U _ F hF hU
      have e1 := emb_eq_add (G := G) hF hCP hGC
      have e2 := emb_eq_add (G := H) hF hTQ hHT
      have e3 := emb_eq_of_iso φ F
      have e4 := hyp U F hF hU
      omega
    have hlt : (P \ C).ncard < P.ncard := by
      obtain ⟨⟨c, hc⟩⟩ := hC.nonempty
      exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset Set.sdiff_subset).mpr
        ⟨c, hCP hc, fun h => h.2 hc⟩)
    obtain ⟨ψ⟩ := ih (P \ C) (Q \ T) (by omega) hyp'
    exact nonempty_iso_glue hCP hTQ hGC hHT φ ψ

end Peeling

/-- **Disconnected graphs are reconstructible.** The exact statement of
`ReconstructionConjecture.reconstruction_conjecture.variants.disconnected`. -/
theorem reconstruction_conjecture_variants_disconnected {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hd : ¬G.Connected) (h : Hypomorphic G H) : Nonempty (G ≃g H) := by
  classical
  have hcard : Fintype.card V = Fintype.card W := h.card_eq
  have hHd := not_connected_of_hypomorphic hV hd h
  have hyp : Hyp G H Set.univ Set.univ := fun U _ F _ hU => by
    rw [emb_univ, emb_univ]
    exact card_embedding_eq_of_hypomorphic h F hU
  obtain ⟨φ⟩ := iso_of_hyp hV hcard (fun S hS => ncard_lt_of_not_connected hd hS)
    (fun T hT => hcard ▸ ncard_lt_of_not_connected hHd hT) _ Set.univ Set.univ le_rfl hyp
  exact ⟨(induceUnivIso G).symm.trans (φ.trans (induceUnivIso H))⟩

end ReconstructionDisconnected

/-!
# The edge reconstruction theorems of Lovász and Müller

A graph on $n$ vertices with $m$ edges is determined up to isomorphism by its deck of
edge-deleted subgraphs if $m > \binom{n}{2} / 2$ (Lovász) or if $n! < 2^{m-1}$ (Müller).

The definition `EdgeHypomorphic` is copied verbatim from
`FormalConjectures/Wikipedia/ReconstructionConjecture.lean` (Copyright 2026 The Formal
Conjectures Authors, Apache 2.0) at upstream commit `7bdc4a42f24c0316f81c73b26121794b2bed96a3`,
in the namespace `EdgeReconstruction` instead of `ReconstructionConjecture`. The theorems
`lovasz` and `mueller` are the statements of `edge_reconstruction_conjecture.variants.lovasz`
and `edge_reconstruction_conjecture.variants.mueller` there.

*References:*
* L. Lovász, "A note on the line reconstruction problem", *J. Combin. Theory Ser. B* 13 (1972),
  309--310.
* V. Müller, "The edge reconstruction hypothesis is true for graphs with more than
  $n \log_2 n$ edges", *J. Combin. Theory Ser. B* 22 (1977), 281--283.

## Proof

Identify a graph on `V` with its edge set `A : Finset (Sym2 V)`, and let `B` be the edge set of
an edge-hypomorphic graph. For edge sets `F` and `X`, `embCount F X` is the number of
permutations `π` of `V` with `π(F) ⊆ X`.

* Kelly's lemma for edge decks (`embCount_eq_of_card_lt`):
  $\sum_{e \in A} i(F, A - e) = (|A| - |F|)\, i(F, A)$, so $i(F, A) = i(F, B)$ if $|F| < |A|$.
* Inclusion–exclusion (`card_fiber_sub`): for $F \subseteq A$ let $N_X(F)$ be the number of `π`
  that map the edges in `F`, and no other edge of `A`, into `X`. Then
  $N_A(F) - N_B(F) = (-1)^{|A \setminus F|} (i(A, A) - i(A, B))$.
* Lovász: if $2|A| > \binom{n}{2}$, then $N_A(\emptyset) = N_B(\emptyset) = 0$ by pigeonhole,
  so $i(A, B) = i(A, A) \ge 1$.
* Müller: if $i(A, B) = 0$, then $N_A(F) \ge 1$ whenever $|A \setminus F|$ is even. Distinct
  such `F` need distinct permutations, so $2^{|A| - 1} \le n!$.

A permutation with $\pi(A) \subseteq B$ is an isomorphism, because $|A| = |B|$.
-/

namespace EdgeReconstruction

open Finset

variable {V W : Type*}

/-- Two graphs are **edge-hypomorphic** if there is a bijection `σ` between their edge sets
such that the edge-deleted subgraphs `G - e` and `H - σ e` are isomorphic for every edge `e`;
i.e. `G` and `H` have the same deck of edge-deleted subgraphs. -/
def EdgeHypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
    Nonempty (G.deleteEdges {(e : Sym2 V)} ≃g H.deleteEdges {((σ e : H.edgeSet) : Sym2 W)})

lemma map_perm_inv_map (τ : Equiv.Perm V) (x : Sym2 V) :
    Sym2.map ⇑τ⁻¹ (Sym2.map τ x) = x := by
  induction x using Sym2.ind with
  | h a b => simp

lemma map_perm_mul (τ π : Equiv.Perm V) (x : Sym2 V) :
    Sym2.map ⇑(τ * π) x = Sym2.map τ (Sym2.map π x) := by
  induction x using Sym2.ind with
  | h a b => simp

lemma card_image_map [DecidableEq V] (F : Finset (Sym2 V)) (π : Equiv.Perm V) :
    #(F.image (Sym2.map π)) = #F :=
  card_image_of_injective _ (Sym2.map.injective π.injective)

section Counting

variable [Fintype V] [DecidableEq V]

/-- The number of permutations `π` of `V` that map every element of `F` into `X`. -/
def embCount (F X : Finset (Sym2 V)) : ℕ :=
  #(univ.filter fun π : Equiv.Perm V => F.image (Sym2.map π) ⊆ X)

/-- The permutations that map the elements of `F`, and no other element of `A`, into `X`. -/
def fiber (A F X : Finset (Sym2 V)) : Finset (Equiv.Perm V) :=
  univ.filter fun π => F.image (Sym2.map π) ⊆ X ∧ ∀ e ∈ A \ F, Sym2.map π e ∉ X

lemma embCount_self_pos (A : Finset (Sym2 V)) : 0 < embCount A A := by
  refine card_pos.mpr ⟨1, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
  simpa using hy

lemma exists_perm_of_embCount_pos {A B : Finset (Sym2 V)} (hcard : #B = #A)
    (h : 0 < embCount A B) : ∃ π : Equiv.Perm V, A.image (Sym2.map π) = B := by
  obtain ⟨π, hπ⟩ := card_pos.mp h
  exact ⟨π, eq_of_subset_of_card_le (mem_filter.mp hπ).2 (by rw [card_image_map, hcard])⟩

/-- `embCount F X` depends only on `X` up to a permutation of `V`. -/
lemma embCount_eq_of_image_eq {F X Y : Finset (Sym2 V)} (τ : Equiv.Perm V)
    (h : X.image (Sym2.map τ) = Y) : embCount F X = embCount F Y := by
  unfold embCount
  refine card_nbij' (τ * ·) (τ⁻¹ * ·) ?_ ?_ ?_ ?_
  · intro π hπ
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, image_subset_iff] at hπ ⊢
    intro x hx
    rw [map_perm_mul, ← h]
    exact mem_image_of_mem _ (hπ x hx)
  · intro π hπ
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, image_subset_iff] at hπ ⊢
    rw [← h] at hπ
    intro x hx
    obtain ⟨y, hy, hyx⟩ := mem_image.mp (hπ x hx)
    rw [map_perm_mul, ← hyx, map_perm_inv_map]
    exact hy
  · intro π _
    exact inv_mul_cancel_left τ π
  · intro π _
    exact mul_inv_cancel_left τ π

/-- Kelly's lemma for edge decks, before cancelling the factor `#A - #F`. -/
lemma sum_embCount_erase (F A : Finset (Sym2 V)) :
    ∑ e ∈ A, embCount F (A.erase e) = (#A - #F) * embCount F A := by
  simp only [embCount, card_filter]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun π _ => ?_
  by_cases hπ : F.image (Sym2.map π) ⊆ A
  · simp only [subset_erase, hπ, true_and, ↓reduceIte, mul_one]
    rw [← card_filter, ← sdiff_eq_filter, card_sdiff_of_subset hπ, card_image_map]
  · have h : ∀ e, ¬ F.image (Sym2.map π) ⊆ A.erase e := fun e he =>
      hπ (he.trans (erase_subset _ _))
    simp [h, hπ]

/-- **Kelly's lemma for edge decks.** If `A - e` and `B - σ e` agree up to a permutation for
every `e`, then `A` and `B` contain the same number of images of each smaller `F`. -/
lemma embCount_eq_of_card_lt {A B : Finset (Sym2 V)} (hcard : #B = #A) (σ : A ≃ B)
    (τ : A → Equiv.Perm V) (hτ : ∀ e : A, (A.erase e).image (Sym2.map (τ e)) = B.erase (σ e))
    {F : Finset (Sym2 V)} (hF : #F < #A) : embCount F A = embCount F B := by
  have h : ∑ e ∈ A, embCount F (A.erase e) = ∑ f ∈ B, embCount F (B.erase f) := by
    rw [← sum_coe_sort A, ← sum_coe_sort B]
    exact Fintype.sum_equiv σ _ _ fun e => embCount_eq_of_image_eq (τ e) (hτ e)
  rw [sum_embCount_erase, sum_embCount_erase, hcard] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

/-- Inclusion–exclusion over the elements of `A` outside `F`. -/
lemma sum_powerset_sdiff_embCount (A F X : Finset (Sym2 V)) :
    ∑ D ∈ (A \ F).powerset, (-1 : ℤ) ^ #D * embCount (F ∪ D) X = #(fiber A F X) := by
  simp only [embCount, fiber, card_filter]
  push_cast
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun π _ => ?_
  simp only [image_union, union_subset_iff, mul_ite, mul_one, mul_zero]
  by_cases hF : F.image (Sym2.map π) ⊆ X
  · have hfilter : (A \ F).powerset.filter (fun D => D.image (Sym2.map π) ⊆ X) =
        ((A \ F).filter fun e => Sym2.map π e ∈ X).powerset := by
      ext D
      rw [mem_filter, mem_powerset, mem_powerset, image_subset_iff]
      constructor
      · rintro ⟨h1, h2⟩ x hx
        exact mem_filter.mpr ⟨h1 hx, h2 x hx⟩
      · intro h
        exact ⟨fun x hx => (mem_filter.mp (h hx)).1, fun x hx => (mem_filter.mp (h hx)).2⟩
    simp only [hF, true_and]
    rw [← sum_filter, hfilter, sum_powerset_neg_one_pow_card]
    by_cases h0 : ∀ e ∈ A \ F, Sym2.map π e ∉ X
    · rw [ite_eq_left (filter_eq_empty_iff.mpr fun x hx => h0 x hx), ite_eq_left h0]
    · have hne : ¬ ((A \ F).filter fun e => Sym2.map π e ∈ X) = ∅ := fun h =>
        h0 fun x hx => filter_eq_empty_iff.mp h hx
      rw [ite_eq_right hne, ite_eq_right h0]
  · simp [hF]

/-- The fibers over `F` for `A` and `B` differ only through the term `F = A`. -/
lemma card_fiber_sub {A B F : Finset (Sym2 V)} (hFA : F ⊆ A)
    (hk : ∀ F' : Finset (Sym2 V), #F' < #A → embCount F' A = embCount F' B) :
    (#(fiber A F A) : ℤ) - #(fiber A F B) =
      (-1 : ℤ) ^ #(A \ F) * ((embCount A A : ℤ) - embCount A B) := by
  rw [← sum_powerset_sdiff_embCount, ← sum_powerset_sdiff_embCount, ← sum_sub_distrib]
  simp only [← mul_sub]
  rw [sum_eq_single_of_mem (A \ F) (mem_powerset_self _), union_sdiff_of_subset hFA]
  intro D hD hne
  have hD' := mem_powerset.mp hD
  have hlt : #(F ∪ D) < #A := by
    refine card_lt_card (ssubset_of_subset_of_ne (union_subset hFA (hD'.trans sdiff_subset)) ?_)
    intro hFD
    apply hne
    refine Subset.antisymm hD' fun x hx => ?_
    obtain ⟨hxA, hxF⟩ := mem_sdiff.mp hx
    rw [← hFD] at hxA
    exact (mem_union.mp hxA).resolve_left hxF
  rw [hk _ hlt, sub_self, mul_zero]

/-- **Lovász's theorem** for edge sets. -/
theorem exists_perm_image_eq_of_choose_lt {A B : Finset (Sym2 V)}
    (hA : ∀ e ∈ A, ¬ e.IsDiag) (hB : ∀ e ∈ B, ¬ e.IsDiag) (hcard : #B = #A)
    (hm : (Fintype.card V).choose 2 < 2 * #A) (σ : A ≃ B) (τ : A → Equiv.Perm V)
    (hτ : ∀ e : A, (A.erase e).image (Sym2.map (τ e)) = B.erase (σ e)) :
    ∃ π : Equiv.Perm V, A.image (Sym2.map π) = B := by
  have hk := fun F (hF : #F < #A) => embCount_eq_of_card_lt hcard σ τ hτ hF
  -- By pigeonhole, every permutation maps some edge of `A` into `X`.
  have h0 : ∀ X : Finset (Sym2 V), #X = #A → (∀ e ∈ X, ¬ e.IsDiag) → #(fiber A ∅ X) = 0 := by
    intro X hX hXd
    rw [card_eq_zero, fiber, filter_eq_empty_iff]
    rintro π - ⟨-, hπ⟩
    let D : Finset (Sym2 V) := univ.filter fun e => ¬ e.IsDiag
    have hD : #D = (Fintype.card V).choose 2 :=
      (Fintype.card_of_subtype D (by simp [D])).symm.trans Sym2.card_subtype_not_diag
    have h1 : A.image (Sym2.map π) ⊆ D := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := mem_image.mp hx
      simpa [D, Sym2.isDiag_map π.injective] using hA e he
    have h2 : X ⊆ D := fun x hx => by simpa [D] using hXd x hx
    have h3 : #D < #(A.image (Sym2.map π)) + #X := by
      rw [hD, card_image_map, hX]
      omega
    obtain ⟨x, hx⟩ := inter_nonempty_of_card_lt_card_add_card h1 h2 h3
    obtain ⟨hx1, hx2⟩ := mem_inter.mp hx
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx1
    exact hπ e (by simpa using he) hx2
  have h := card_fiber_sub (B := B) (empty_subset A) hk
  rw [h0 A rfl hA, h0 B hcard hB, Nat.cast_zero, sub_self] at h
  have heq : embCount A A = embCount A B := by
    rcases mul_eq_zero.mp h.symm with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact_mod_cast sub_eq_zero.mp h
  exact exists_perm_of_embCount_pos hcard (heq ▸ embCount_self_pos A)

/-- **Müller's theorem** for edge sets. -/
theorem exists_perm_image_eq_of_factorial_lt {A B : Finset (Sym2 V)} (hcard : #B = #A)
    (hm : (Fintype.card V).factorial < 2 ^ (#A - 1)) (σ : A ≃ B) (τ : A → Equiv.Perm V)
    (hτ : ∀ e : A, (A.erase e).image (Sym2.map (τ e)) = B.erase (σ e)) :
    ∃ π : Equiv.Perm V, A.image (Sym2.map π) = B := by
  by_contra hno
  have hAB : embCount A B = 0 := by
    by_contra h
    exact hno (exists_perm_of_embCount_pos hcard (Nat.pos_of_ne_zero h))
  have hk := fun F (hF : #F < #A) => embCount_eq_of_card_lt hcard σ τ hτ hF
  rcases A.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · simp only [card_empty, zero_tsub, pow_zero, Nat.lt_one_iff] at hm
    exact Nat.factorial_ne_zero _ hm
  -- If `E ⊆ A` has even size, some permutation maps exactly the edges outside `E` into `A`.
  have key : ∀ E ⊆ A, Even #E → ∃ π : Equiv.Perm V,
      (A \ E).image (Sym2.map π) ⊆ A ∧ ∀ e ∈ A \ (A \ E), Sym2.map π e ∉ A := by
    intro E hE hev
    have h := card_fiber_sub (B := B) (sdiff_subset (s := A) (t := E)) hk
    rw [Finset.sdiff_sdiff_eq_self hE, hev.neg_one_pow, one_mul, hAB, Nat.cast_zero, sub_zero] at h
    have hpos := embCount_self_pos A
    obtain ⟨π, hπ⟩ := card_pos.mp (show 0 < #(fiber A (A \ E) A) by omega)
    exact ⟨π, (mem_filter.mp hπ).2⟩
  -- Choose such an even set for every subset of `A.erase e₀`.
  let even : Finset (Sym2 V) → Finset (Sym2 V) := fun D => if Even #D then D else insert e₀ D
  have heven : ∀ D ∈ (A.erase e₀).powerset,
      even D ⊆ A ∧ Even #(even D) ∧ (even D).erase e₀ = D := by
    intro D hD
    have hD' := mem_powerset.mp hD
    have he₀D : e₀ ∉ D := fun h => (mem_erase.mp (hD' h)).1 rfl
    have hDA : D ⊆ A := hD'.trans (erase_subset _ _)
    by_cases hev : Even #D
    · rw [show even D = D from ite_eq_left hev]
      exact ⟨hDA, hev, erase_eq_of_notMem he₀D⟩
    · rw [show even D = insert e₀ D from ite_eq_right hev]
      refine ⟨insert_subset he₀ hDA, ?_, erase_insert he₀D⟩
      rw [card_insert_of_notMem he₀D]
      exact (Nat.not_even_iff_odd.mp hev).add_one
  choose! π hπ using fun D (hD : D ∈ (A.erase e₀).powerset) =>
    key (even D) (heven D hD).1 (heven D hD).2.1
  -- The permutation determines the even set.
  have hrecover : ∀ D ∈ (A.erase e₀).powerset,
      even D = A.filter fun e => Sym2.map (π D) e ∉ A := by
    intro D hD
    obtain ⟨hsub, hout⟩ := hπ D hD
    have hEA := (heven D hD).1
    ext e
    rw [mem_filter]
    constructor
    · intro he
      exact ⟨hEA he, hout e (by rw [Finset.sdiff_sdiff_eq_self hEA]; exact he)⟩
    · rintro ⟨heA, he⟩
      by_contra hne
      exact he (image_subset_iff.mp hsub e (mem_sdiff.mpr ⟨heA, hne⟩))
  have hinj : Set.InjOn π ((A.erase e₀).powerset : Set (Finset (Sym2 V))) := by
    intro D hD D' hD' h
    rw [← (heven D hD).2.2, ← (heven D' hD').2.2, hrecover D hD, hrecover D' hD', h]
  have hle := card_le_card_of_injOn π (t := univ) (fun _ _ => mem_coe.mpr (mem_univ _)) hinj
  rw [card_powerset, card_erase_of_mem he₀, card_univ, Fintype.card_perm] at hle
  omega

end Counting

/-! ### The graph statements -/

lemma map_mem_edgeSet_iff_of_iso {G' H' : SimpleGraph V} (ι : G' ≃g H') (x : Sym2 V) :
    Sym2.map ι.toEquiv x ∈ H'.edgeSet ↔ x ∈ G'.edgeSet := by
  induction x using Sym2.ind with
  | h a b =>
    simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet, RelIso.coe_fn_toEquiv]
    exact ι.map_rel_iff

section Graphs

variable [DecidableEq V]

/-- Edge-hypomorphic graphs on `V` give the data used by the counting theorems. -/
lemma EdgeHypomorphic.exists_perm {G H : SimpleGraph V} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (h : EdgeHypomorphic G H) :
    #H.edgeFinset = #G.edgeFinset ∧ ∃ (σ : G.edgeFinset ≃ H.edgeFinset)
      (τ : G.edgeFinset → Equiv.Perm V),
      ∀ e : G.edgeFinset,
        (G.edgeFinset.erase e).image (Sym2.map (τ e)) = H.edgeFinset.erase (σ e) := by
  obtain ⟨σ, hσ⟩ := h
  have hι : ∀ e : G.edgeSet, ∃ τ : Equiv.Perm V, ∀ x,
      Sym2.map τ x ∈ (H.deleteEdges {((σ e : H.edgeSet) : Sym2 V)}).edgeSet ↔
        x ∈ (G.deleteEdges {(e : Sym2 V)}).edgeSet := fun e =>
    let ⟨ι⟩ := hσ e
    ⟨ι.toEquiv, map_mem_edgeSet_iff_of_iso ι⟩
  choose τ hτ using hι
  have hncard : G.edgeSet.ncard = H.edgeSet.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr σ
  refine ⟨?_, (Equiv.subtypeEquivRight fun _ => SimpleGraph.mem_edgeFinset).trans
      (σ.trans (Equiv.subtypeEquivRight fun _ => SimpleGraph.mem_edgeFinset.symm)),
    fun e => τ ⟨e, SimpleGraph.mem_edgeFinset.mp e.2⟩, fun e => ?_⟩
  · rw [← Set.ncard_coe_finset, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
      SimpleGraph.coe_edgeFinset, hncard]
  set τe := τ ⟨e, SimpleGraph.mem_edgeFinset.mp e.2⟩
  have key : ∀ x, (Sym2.map τe x ∈ H.edgeSet ∧
      ¬ Sym2.map τe x = ((σ ⟨e, SimpleGraph.mem_edgeFinset.mp e.2⟩ : H.edgeSet) : Sym2 V)) ↔
        (x ∈ G.edgeSet ∧ ¬ x = e) := by
    intro x
    have := hτ ⟨e, SimpleGraph.mem_edgeFinset.mp e.2⟩ x
    simp only [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff] at this
    exact this
  ext y
  simp only [mem_image, mem_erase, SimpleGraph.mem_edgeFinset, Equiv.trans_apply,
    Equiv.subtypeEquivRight_apply_coe]
  constructor
  · rintro ⟨x, ⟨hxe, hx⟩, rfl⟩
    obtain ⟨h1, h2⟩ := (key x).mpr ⟨hx, hxe⟩
    exact ⟨h2, h1⟩
  · rintro ⟨hye, hy⟩
    have hy' : Sym2.map τe (Sym2.map ⇑τe⁻¹ y) = y := by
      simpa using map_perm_inv_map τe⁻¹ y
    refine ⟨Sym2.map ⇑τe⁻¹ y, ?_, hy'⟩
    obtain ⟨h1, h2⟩ := (key (Sym2.map ⇑τe⁻¹ y)).mp (by rw [hy']; exact ⟨hy, hye⟩)
    exact ⟨h2, h1⟩

/-- A permutation that maps the edges of `G` onto the edges of `H` is an isomorphism. -/
lemma nonempty_iso_of_image_eq {G H : SimpleGraph V} [Fintype G.edgeSet] [Fintype H.edgeSet]
    {π : Equiv.Perm V} (hπ : G.edgeFinset.image (Sym2.map π) = H.edgeFinset) :
    Nonempty (G ≃g H) := by
  refine ⟨⟨π, fun {a b} => ?_⟩⟩
  rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset, ← hπ, mem_image]
  constructor
  · rintro ⟨x, hx, hxe⟩
    have hx' := SimpleGraph.mem_edgeFinset.mp hx
    rw [Sym2.map.injective π.injective (hxe.trans (Sym2.map_mk _ _ _).symm)] at hx'
    exact hx'
  · intro hab
    exact ⟨s(a, b), SimpleGraph.mem_edgeFinset.mpr hab, Sym2.map_mk _ _ _⟩

end Graphs

/-- **Lovász (1972).** A graph on `n` vertices with more than `n (n - 1) / 4` edges is
determined up to isomorphism by its deck of edge-deleted subgraphs. -/
theorem lovasz {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hE : (Fintype.card V).choose 2 < 2 * G.edgeSet.ncard)
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  classical
  obtain ⟨hcard, σ, τ, hτ⟩ := h.exists_perm
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at hE
  obtain ⟨π, hπ⟩ := exists_perm_image_eq_of_choose_lt
    (fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he))
    (fun e he => H.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)) hcard hE σ τ hτ
  exact nonempty_iso_of_image_eq hπ

/-- **Müller (1977).** A graph on `n` vertices with `m` edges and `n! < 2 ^ (m - 1)` is
determined up to isomorphism by its deck of edge-deleted subgraphs. -/
theorem mueller {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1))
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  classical
  obtain ⟨hcard, σ, τ, hτ⟩ := h.exists_perm
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at hE
  obtain ⟨π, hπ⟩ := exists_perm_image_eq_of_factorial_lt hcard hE σ τ hτ
  exact nonempty_iso_of_image_eq hπ

end EdgeReconstruction

namespace ReconstructionConjecture

theorem reconstruction_conjecture.variants.disconnected {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hd : ¬G.Connected) (h : Hypomorphic G H) : Nonempty (G ≃g H) :=
  ReconstructionDisconnected.reconstruction_conjecture_variants_disconnected hV G H hd h

theorem edge_reconstruction_conjecture.variants.lovasz {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : (Fintype.card V).choose 2 < 2 * G.edgeSet.ncard)
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) :=
  EdgeReconstruction.lovasz G H hE h

theorem edge_reconstruction_conjecture.variants.mueller {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1))
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) :=
  EdgeReconstruction.mueller G H hE h

end ReconstructionConjecture

end
