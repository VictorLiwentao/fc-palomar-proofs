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
# Erdős Problem 934: the value of $h_1(d)$

We prove $h_1(d) = d + 1$ for every $d \ne 2$.

The definitions `HasFarEdges` and `h` are copied verbatim from
`FormalConjectures/ErdosProblems/934.lean` (Copyright 2026 The Formal Conjectures Authors,
Apache 2.0) at upstream commit `7bdc4a42f24c0316f81c73b26121794b2bed96a3`, in the namespace
`Erdos934H1` instead of `Erdos934`. The final theorem is the statement of
`erdos_934.variants.h_one` there.

*References:* [erdosproblems.com/934](https://www.erdosproblems.com/934);
S. Cambie, W. Cames van Batenburg, R. de Joannis de Verclos and R. J. Kang, "Maximising line
subgraphs of diameter at most $t$", *SIAM J. Discrete Math.* 36 (2022), 939--950,
[arXiv:2103.11898](https://arxiv.org/abs/2103.11898).

## Proof

Two edges are at distance at least $1$ exactly when they are vertex-disjoint. If no two edges
of $G$ are disjoint, then all edges contain one vertex, or they form a triangle. In the first
case there are at most $d$ edges. In the second case there are $3$ edges and some vertex has
degree $2$, so $d \ge 3$ when $d \ne 2$. Hence $d + 1$ edges force two disjoint edges. The star
$K_{1,d}$ has $d$ edges, maximum degree $d$, and no two disjoint edges.
-/

@[expose] public section

namespace Erdos934

open SimpleGraph

/-- The graph `G` has two edges at distance at least `t`: there are edges `uv` and `wx` of `G`
such that every vertex of `{u, v}` is at graph distance at least `t` from every vertex of
`{w, x}`, i.e. the shortest path between the two edges has length at least `t`. We use the
extended distance `SimpleGraph.edist`, so vertices in different components are at distance `⊤`.
For `1 ≤ t` the two edges are automatically distinct (indeed vertex-disjoint): `t = 1` means
vertex-disjoint edges and `t = 2` means an induced `2K₂`. Only `1 ≤ t` is intended. -/
def HasFarEdges {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ u v w x : V, G.Adj u v ∧ G.Adj w x ∧
    ∀ a ∈ ({u, v} : Set V), ∀ b ∈ ({w, x} : Set V), (t : ℕ∞) ≤ G.edist a b

/-- `h t d` is $h_t(d)$: the least `m` such that every graph with at least `m` edges and maximum
degree at most `d` contains two edges at distance at least `t`. As in [CCJK22] and [KMP26],
"at least `m` edges" is used, so `h t d - 1` is the largest number of edges of a graph with
maximum degree at most `d` in which any two edges are at distance less than `t`, i.e. whose line
graph has diameter at most `t`. Graphs on `Fin n` for arbitrary `n` cover all finite graphs. The
set is nonempty (for example `3 * d ^ t / 2 + 1` belongs to it by [CCJK22, Theorem 6]), so
`sInf` is a genuine minimum. -/
noncomputable def h (t d : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → HasFarEdges G t}

/-! ### Edges at distance at least one -/

lemma hasFarEdges_one_iff {V : Type*} {G : SimpleGraph V} :
    HasFarEdges G 1 ↔
      ∃ u v w x, G.Adj u v ∧ G.Adj w x ∧ u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x := by
  have key : ∀ a b : V, (1 : ℕ∞) ≤ G.edist a b ↔ a ≠ b := fun a b => by
    rw [Order.one_le_iff_ne_zero, ne_eq, edist_eq_zero_iff]
  simp only [HasFarEdges, Nat.cast_one, key, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  constructor <;> rintro ⟨u, v, w, x, hx⟩ <;> exact ⟨u, v, w, x, by tauto⟩

/-- Without two disjoint edges, every two edges meet. -/
lemma meet_of_not_hasFarEdges {V : Type*} {G : SimpleGraph V} (hG : ¬ HasFarEdges G 1)
    {a b c e : V} (hab : G.Adj a b) (hce : G.Adj c e) : a = c ∨ a = e ∨ b = c ∨ b = e := by
  by_contra hne
  push Not at hne
  exact hG (hasFarEdges_one_iff.mpr ⟨a, b, c, e, hab, hce, hne⟩)

lemma ncard_incidenceSet {V : Type*} (G : SimpleGraph V) (v : V) :
    (G.incidenceSet v).ncard = (G.neighborSet v).ncard := by
  classical
  exact Set.ncard_congr' (G.incidenceSetEquivNeighborSet v)

/-! ### Upper bound -/

/-- A graph on `Fin n` with maximum degree at most `d ≠ 2` and no two disjoint edges has at
most `d` edges. -/
lemma ncard_edgeSet_le {n d : ℕ} {G : SimpleGraph (Fin n)} (hd : d ≠ 2)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d) (hG : ¬ HasFarEdges G 1) :
    G.edgeSet.ncard ≤ d := by
  have meet : ∀ {a b c e : Fin n}, G.Adj a b → G.Adj c e → a = c ∨ a = e ∨ b = c ∨ b = e :=
    fun hab hce => meet_of_not_hasFarEdges hG hab hce
  by_cases hE : ∃ u v, G.Adj u v
  swap
  · push Not at hE
    have : G = ⊥ := by
      ext a b
      simpa using hE a b
    simp [this]
  obtain ⟨u, v, huv⟩ := hE
  -- All edges contain one vertex `c`.
  have star : ∀ c, (∀ a b, G.Adj a b → a = c ∨ b = c) → G.edgeSet.ncard ≤ d := by
    intro c hc
    refine (Set.ncard_le_ncard (t := G.incidenceSet c) (fun e he => ?_)).trans
      ((ncard_incidenceSet G c).trans_le (hdeg c))
    induction e using Sym2.ind with
    | h a b =>
      exact ⟨he, Sym2.mem_iff.mpr ((hc a b he).imp Eq.symm Eq.symm)⟩
  by_cases hu : ∀ a b, G.Adj a b → a = u ∨ b = u
  · exact star u hu
  by_cases hv : ∀ a b, G.Adj a b → a = v ∨ b = v
  · exact star v hv
  -- Otherwise the edges form a triangle `u v w`.
  push Not at hu hv
  obtain ⟨w, hvw, hwu⟩ : ∃ w, G.Adj v w ∧ w ≠ u := by
    obtain ⟨a, b, hab, hau, hbu⟩ := hu
    rcases meet hab huv with h | h | h | h
    · exact absurd h hau
    · exact ⟨b, h ▸ hab, hbu⟩
    · exact absurd h hbu
    · exact ⟨a, h ▸ hab.symm, hau⟩
  obtain ⟨x, hux, hxv⟩ : ∃ x, G.Adj u x ∧ x ≠ v := by
    obtain ⟨a, b, hab, hav, hbv⟩ := hv
    rcases meet hab huv with h | h | h | h
    · exact ⟨b, h ▸ hab, hbv⟩
    · exact absurd h hav
    · exact ⟨a, h ▸ hab.symm, hav⟩
    · exact absurd h hbv
  obtain rfl : x = w := by
    rcases meet hvw hux with h | h | h | h
    · exact absurd h huv.ne.symm
    · exact absurd h.symm hxv
    · exact absurd h hwu
    · exact h.symm
  have huw := hux
  have hsub : G.edgeSet ⊆ {s(u, v), s(v, x), s(u, x)} := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := he
      have h1 := meet hab huv
      have h2 := meet hab hvw
      have h3 := meet hab huw
      have hne := hab.ne
      have h4 := huv.ne
      have h5 := hvw.ne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
      grind
  have h3 : ({s(u, v), s(v, x), s(u, x)} : Set (Sym2 (Fin n))).ncard ≤ 3 := by
    have h31 := Set.ncard_insert_le s(u, v) {s(v, x), s(u, x)}
    have h32 := Set.ncard_insert_le s(v, x) {s(u, x)}
    rw [Set.ncard_singleton] at h32
    omega
  have h2 : 2 ≤ d := by
    have hpair : ({v, x} : Set (Fin n)) ⊆ G.neighborSet u := by
      intro y hy
      rcases hy with rfl | rfl
      · exact huv
      · exact huw
    exact (Set.ncard_pair hxv.symm).symm.le.trans
      ((Set.ncard_le_ncard hpair).trans (hdeg u))
  exact (Set.ncard_le_ncard hsub).trans (h3.trans (by omega))

/-! ### Lower bound -/

/-- The star with centre `0` and `d` leaves. -/
def star (d : ℕ) : SimpleGraph (Fin (d + 1)) where
  Adj a b := (a = 0 ∨ b = 0) ∧ a ≠ b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

lemma ncard_neighborSet_star_le (d : ℕ) (v : Fin (d + 1)) :
    ((star d).neighborSet v).ncard ≤ d := by
  have hne : (star d).neighborSet v ≠ Set.univ := fun h =>
    (star d).irrefl (h ▸ Set.mem_univ v : v ∈ (star d).neighborSet v)
  have := Set.ncard_lt_card hne
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

lemma le_ncard_edgeSet_star (d : ℕ) : d ≤ (star d).edgeSet.ncard := by
  have hinj : Function.Injective fun i : Fin d => s((0 : Fin (d + 1)), i.succ) := by
    intro i j hij
    rw [Sym2.eq_iff] at hij
    rcases hij with ⟨-, h⟩ | ⟨h, -⟩
    · exact Fin.succ_injective _ h
    · exact absurd h.symm (Fin.succ_ne_zero j)
  have hsub : Set.range (fun i : Fin d => s((0 : Fin (d + 1)), i.succ)) ⊆ (star d).edgeSet := by
    rintro _ ⟨i, rfl⟩
    exact (⟨Or.inl rfl, (Fin.succ_ne_zero i).symm⟩ : (star d).Adj 0 i.succ)
  have := Set.ncard_le_ncard hsub
  rwa [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin] at this

lemma not_hasFarEdges_star (d : ℕ) : ¬ HasFarEdges (star d) 1 := by
  rw [hasFarEdges_one_iff]
  rintro ⟨u, v, w, x, ⟨huv, -⟩, ⟨hwx, -⟩, h1, h2, h3, h4⟩
  rcases huv with rfl | rfl <;> rcases hwx with rfl | rfl <;> simp_all

/-! ### The value of $h_1(d)$ -/

/-- **Erdős Problem 934, $t = 1$.** For $d \ne 2$, $h_1(d) = d + 1$. -/
theorem h_one : ∀ d : ℕ, d ≠ 2 → h 1 d = d + 1 := by
  intro d hd
  have hmem : d + 1 ∈ {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → HasFarEdges G 1} := by
    intro n G hdeg hm
    by_contra hG
    have := ncard_edgeSet_le hd hdeg hG
    omega
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ fun m hm => ?_)
  by_contra hlt
  exact not_hasFarEdges_star d (hm (d + 1) (star d) (ncard_neighborSet_star_le d)
    ((Nat.le_of_lt_succ (Nat.not_le.mp hlt)).trans (le_ncard_edgeSet_star d)))

end Erdos934

namespace Erdos934

theorem erdos_934.variants.h_one : ∀ d : ℕ, d ≠ 2 → h 1 d = d + 1 :=
  _root_.Erdos934.h_one

end Erdos934

end
