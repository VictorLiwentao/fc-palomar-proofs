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
# Trees are cop-win

This file proves the upstream statement `MeynielConjecture.meyniel_conjecture.variants.tree`:
every finite, nonempty, connected, acyclic graph has cop number $1$.

The cop starts at a fixed root $x$. While the cop is at $p$ and the robber is at $r \ne p$,
the cop steps to a neighbour of $p$ that is closer to $r$. The invariant is that $p$ lies on a
shortest path from $x$ to $r$, that is, $d(x, p) + d(p, r) = d(x, r)$. Each cop move increases
$d(x, p)$ by one. In a tree a robber move keeps the invariant, so the cop catches the robber
within $|V|$ rounds.

The definitions of the game are those of `FormalConjectures/Wikipedia/MeynielConjecture.lean`.

*References:*
* Quilliot, A. (1978). "Jeux et pointes fixes sur les graphes." Thèse de 3ème cycle,
  Université de Paris VI.
* Nowakowski, R. and Winkler, P. (1983). "Vertex-to-vertex pursuit in a graph."
  *Discrete Math.* 43, pp. 235--239.
-/

@[expose] public section

open Filter

namespace MeynielConjecture

variable {V : Type*}

/-- A **move** in the cops-and-robbers game: stay put, or slide along an edge. -/
def Step (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v

/-- `CopsCatchWithin G k m c r`: with `k` cops at positions `c`, the robber at `r`, and the cops
to move, the cops can guarantee to catch the robber within `m` further rounds. In each round
every cop moves (or stays), catching the robber if a cop reaches the robber's vertex, and then
the robber moves (or stays). -/
def CopsCatchWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | m + 1, c, r =>
      (∃ i, c i = r) ∨
        ∃ c' : Fin k → V, (∀ i, Step G (c i) (c' i)) ∧
          ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CopsCatchWithin G k m c' r')

/-- `k` cops have a winning strategy on `G`: they can choose starting positions such that,
wherever the robber starts, they catch the robber in finitely many rounds. -/
def CopsWin (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ m, CopsCatchWithin G k m c r

/-- The **cop number** `c(G)`: the least number of cops that can guarantee to catch the
robber on `G`. -/
noncomputable def copNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | CopsWin G k}

/-- Zero cops never catch a robber. -/
lemma not_copsCatchWithin_zero (G : SimpleGraph V) (m : ℕ) (c : Fin 0 → V) (r : V) :
    ¬CopsCatchWithin G 0 m c r := by
  induction m generalizing c r with
  | zero =>
    rintro ⟨i, -⟩
    exact i.elim0
  | succ m ih =>
    rintro (⟨i, -⟩ | ⟨c', -, ⟨i, -⟩ | h⟩)
    · exact i.elim0
    · exact i.elim0
    · exact ih c' r (h r (Or.inl rfl))

/-- On a graph with at least one vertex, zero cops do not win. -/
lemma not_copsWin_zero [Nonempty V] (G : SimpleGraph V) : ¬CopsWin G 0 := by
  rintro ⟨c, hc⟩
  obtain ⟨m, hm⟩ := hc (Classical.arbitrary V)
  exact not_copsCatchWithin_zero G m c _ hm

/-- One cop per vertex wins. -/
lemma copsWin_card [Fintype V] (G : SimpleGraph V) : CopsWin G (Fintype.card V) :=
  ⟨(Fintype.equivFin V).symm, fun r => ⟨0, ⟨Fintype.equivFin V r, by simp⟩⟩⟩

/-- On a graph with at least one vertex, at least one cop is needed. -/
lemma one_le_copNumber [Fintype V] [Nonempty V] (G : SimpleGraph V) : 1 ≤ copNumber G := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rcases Nat.sInf_eq_zero.mp h0 with h | h
  · exact not_copsWin_zero G h
  · exact Set.eq_empty_iff_forall_notMem.mp h _ (copsWin_card G)

end MeynielConjecture

namespace MeynielTree

open SimpleGraph MeynielConjecture

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex of a shortest walk, other than its end, is strictly closer to its start. -/
lemma dist_lt_of_mem_support {x v w : V} (P : G.Walk x v) (hP : P.length = G.dist x v)
    (hw : w ∈ P.support) (hwv : w ≠ v) : G.dist x w < G.dist x v := by
  classical
  calc G.dist x w ≤ (P.takeUntil w hw).length := dist_le _
    _ < P.length := Walk.length_takeUntil_lt_length hw hwv
    _ = G.dist x v := hP

/-- A shortest path to `v`, extended by an edge to a vertex that is not closer, is a path. -/
lemma isPath_concat {x v u : V} (P : G.Walk x v) (hP : P.IsPath)
    (hPl : P.length = G.dist x v) (h : G.Adj v u) (hvu : G.dist x v ≤ G.dist x u) :
    (P.concat h).IsPath :=
  hP.concat (fun hu => absurd hvu (not_le.mpr (dist_lt_of_mem_support P hPl hu h.ne'))) h

/-- The distance changes by at most one along an edge. -/
lemma dist_le_dist_add_one (hc : G.Connected) {x v u : V} (h : G.Adj v u) :
    G.dist x u ≤ G.dist x v + 1 := by
  have := hc.dist_triangle (u := x) (v := v) (w := u)
  rwa [dist_eq_one_iff_adj.mpr h] at this

/-- In a tree, the distance from a fixed vertex strictly changes along each edge. -/
lemma dist_eq_add_one_of_adj (ha : G.IsAcyclic) (hc : G.Connected) {x v u : V}
    (h : G.Adj v u) (hvu : G.dist x v ≤ G.dist x u) : G.dist x u = G.dist x v + 1 := by
  obtain ⟨P, hP, hPl⟩ := hc.exists_path_of_dist x v
  obtain ⟨Q, hQ, hQl⟩ := hc.exists_path_of_dist x u
  have hQP : Q = P.concat h :=
    Subtype.mk.inj <| (ha.subsingleton_path x u).elim ⟨Q, hQ⟩
      ⟨_, isPath_concat P hP hPl h hvu⟩
  rw [← hQl, ← hPl, hQP, Walk.length_concat]

/-- In a tree, each vertex `r` has at most one neighbour that is closer to `x`. -/
lemma eq_of_adj_of_dist_add_one (ha : G.IsAcyclic) (hc : G.Connected) {x q q' r : V}
    (h : G.Adj q r) (h' : G.Adj q' r) (hq : G.dist x q + 1 = G.dist x r)
    (hq' : G.dist x q' + 1 = G.dist x r) : q = q' := by
  obtain ⟨P, hP, hPl⟩ := hc.exists_path_of_dist x q
  obtain ⟨P', hP', hP'l⟩ := hc.exists_path_of_dist x q'
  have he : P.concat h = P'.concat h' :=
    Subtype.mk.inj <| (ha.subsingleton_path x r).elim
      ⟨_, isPath_concat P hP hPl h (by omega)⟩ ⟨_, isPath_concat P' hP' hP'l h' (by omega)⟩
  obtain ⟨hqq, -⟩ := Walk.concat_inj he
  exact hqq

/-- A vertex `p ≠ r` has a neighbour that is closer to `r`. -/
lemma exists_adj_dist_lt (hc : G.Connected) {p r : V} (hpr : p ≠ r) :
    ∃ q, G.Adj p q ∧ G.dist q r < G.dist p r := by
  obtain ⟨W, hW⟩ := hc.exists_walk_length_eq_dist p r
  cases W with
  | nil => exact absurd rfl hpr
  | cons h W' =>
    refine ⟨_, h, ?_⟩
    have := dist_le W'
    rw [Walk.length_cons] at hW
    omega

/-- Every distance in a finite connected graph is less than the number of vertices. -/
lemma dist_lt_card [Fintype V] (hc : G.Connected) (x y : V) : G.dist x y < Fintype.card V := by
  obtain ⟨P, hP, hPl⟩ := hc.exists_path_of_dist x y
  rw [← hPl]
  exact hP.length_lt

/-- If `p` lies on a shortest path from `x` to `r`, then a step from `p` towards `r` moves one
step away from `x` and stays on a shortest path from `x` to `r`. -/
lemma cop_step (hc : G.Connected) {x p p' r : V}
    (hinv : G.dist x p + G.dist p r = G.dist x r) (h : G.Adj p p')
    (hcl : G.dist p' r < G.dist p r) :
    G.dist x p' = G.dist x p + 1 ∧ G.dist x p' + G.dist p' r = G.dist x r := by
  have h1 := dist_le_dist_add_one hc (x := x) h
  have h2 := hc.dist_triangle (u := x) (v := p') (w := r)
  omega

/-- In a tree, if `p ≠ r` lies on a shortest path from `x` to `r`, then `p` also lies on a
shortest path from `x` to each neighbour of `r`. -/
lemma robber_step (ha : G.IsAcyclic) (hc : G.Connected) {x p r r' : V}
    (hinv : G.dist x p + G.dist p r = G.dist x r) (hpr : p ≠ r) (h : G.Adj r r') :
    G.dist x p + G.dist p r' = G.dist x r' := by
  have t1 := hc.dist_triangle (u := x) (v := p) (w := r')
  have t2 := dist_le_dist_add_one hc (x := p) h
  rcases le_or_gt (G.dist x r) (G.dist x r') with hle | hlt
  · have := dist_eq_add_one_of_adj ha hc h hle
    omega
  · have hr := dist_eq_add_one_of_adj ha hc h.symm hlt.le
    obtain ⟨q, hq, hql⟩ := exists_adj_dist_lt hc (Ne.symm hpr)
    have e1 : G.dist q p = G.dist p q := dist_comm
    have e2 : G.dist r p = G.dist p r := dist_comm
    have t3 := hc.dist_triangle (u := x) (v := p) (w := q)
    have t4 := dist_le_dist_add_one hc (x := x) hq.symm
    have hqr : q = r' := eq_of_adj_of_dist_add_one ha hc (x := x) hq.symm h.symm
      (by omega) (by omega)
    subst hqr
    omega

/-- The cop at `p` on a shortest path from `x` to the robber at `r` wins within `m` rounds when
`|V| ≤ m + d(x, p)`. -/
lemma copsCatchWithin_of_dist [Fintype V] (ha : G.IsAcyclic) (hc : G.Connected) (x : V) (m : ℕ) :
    ∀ p r, G.dist x p + G.dist p r = G.dist x r → Fintype.card V ≤ m + G.dist x p →
      CopsCatchWithin G 1 m (fun _ => p) r := by
  induction m with
  | zero =>
    intro p r _ hm
    exact absurd (dist_lt_card hc x p) (by omega)
  | succ m ih =>
    intro p r hinv hm
    by_cases hpr : p = r
    · exact Or.inl ⟨0, hpr⟩
    obtain ⟨p', hp', hcl⟩ := exists_adj_dist_lt hc hpr
    obtain ⟨hx, hinv'⟩ := cop_step hc hinv hp' hcl
    refine Or.inr ⟨fun _ => p', fun _ => Or.inr hp', ?_⟩
    by_cases hp'r : p' = r
    · exact Or.inl ⟨0, hp'r⟩
    refine Or.inr fun r' hr' => ih p' r' ?_ (by omega)
    rcases hr' with rfl | hr'
    · exact hinv'
    · exact robber_step ha hc hinv' hp'r hr'

/-- One cop wins on a finite tree. -/
theorem copsWin_one [Fintype V] (ha : G.IsAcyclic) (hc : G.Connected) : CopsWin G 1 := by
  obtain ⟨x⟩ := hc.nonempty
  exact ⟨fun _ => x, fun r =>
    ⟨Fintype.card V, copsCatchWithin_of_dist ha hc x _ x r (by simp) (by simp)⟩⟩

/-- **Trees are cop-win.** The exact statement of
`MeynielConjecture.meyniel_conjecture.variants.tree`. -/
theorem meyniel_conjecture_variants_tree {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hc : G.Connected) (ha : G.IsAcyclic) :
    copNumber G = 1 :=
  le_antisymm (Nat.sInf_le (copsWin_one ha hc)) (one_le_copNumber G)

end MeynielTree

namespace MeynielConjecture

theorem meyniel_conjecture.variants.tree {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hc : G.Connected) (ha : G.IsAcyclic) :
    copNumber G = 1 :=
  MeynielTree.meyniel_conjecture_variants_tree G hc ha

end MeynielConjecture

end
