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
# Fischer's counterexample to TxGraffiti Conjecture 2

Mikko Fischer constructed the graph in [arXiv:2607.23664](https://arxiv.org/abs/2607.23664).
Randy Davila, Boris Brimkov and Ryan Pepper recorded the conjecture in
[arXiv:2507.17780](https://arxiv.org/abs/2507.17780).
The frozen statement and zero forcing definitions are due to the Formal Conjectures Authors.
Chakshu Gupta introduced the statement in DeepMind PR 4278. Srijan Roy recorded
the false answer in PR 6783. Auguste Poiroux added module exposure in PR 6625.

New Lean formalization: Wentao Li. AI assistance: GPT-6.1 Sol in Codex.
-/

@[expose] public section

open SimpleGraph

namespace Arxiv2507_17780

/-- One step of the zero forcing colour-change rule: add to $S$ every vertex $w$
that is the unique neighbour of some $v \in S$ outside $S$. -/
noncomputable def zeroForcingStep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter fun w =>
    w ∉ S ∧ ∃ v ∈ S, G.Adj v w ∧ ∀ u, G.Adj v u → u ∉ S → u = w

/-- The zero forcing closure: iterate `zeroForcingStep` until it stabilises. -/
noncomputable def zeroForcingClosure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  (zeroForcingStep G)^[Fintype.card V] S

/-- A set $S$ is a *zero forcing set* of $G$ if its zero forcing closure is all
of $V$. -/
def IsZeroForcingSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  zeroForcingClosure G S = Finset.univ

/-- The zero forcing number of a finite simple graph: the minimum cardinality of
a zero forcing set. -/
noncomputable def zeroForcingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ S : Finset V, S.card = k ∧ IsZeroForcingSet G S}

end Arxiv2507_17780

noncomputable section

namespace TxGraffitiC2

open SimpleGraph
open Arxiv2507_17780

section Forts

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A nonempty set with no unique neighbour at any vertex outside it. -/
def IsFort (F : Finset V) : Prop :=
  F.Nonempty ∧ ∀ v, v ∉ F → ∀ w ∈ F, G.Adj v w →
    ∃ u ∈ F, G.Adj v u ∧ u ≠ w

instance (F : Finset V) : Decidable (IsFort G F) := by
  unfold IsFort
  infer_instance

lemma step_disjoint_fort {S F : Finset V} (hF : IsFort G F)
    (hSF : Disjoint S F) : Disjoint (zeroForcingStep G S) F := by
  apply Finset.disjoint_left.mpr
  intro w hw hwF
  rcases Finset.mem_union.mp hw with hwS | hwNew
  · exact Finset.disjoint_left.mp hSF hwS hwF
  · obtain ⟨_, _, v, hvS, hvw, hforce⟩ := Finset.mem_filter.mp hwNew
    have hvF : v ∉ F := fun hvF => Finset.disjoint_left.mp hSF hvS hvF
    obtain ⟨u, huF, hvu, huw⟩ := hF.2 v hvF w hwF hvw
    have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hSF huS huF
    exact huw (hforce u hvu huS)

/-- Every zero forcing set meets every fort, for the frozen synchronous closure. -/
lemma zero_forcing_hits_fort {S F : Finset V} (hS : IsZeroForcingSet G S)
    (hF : IsFort G F) : ∃ v ∈ F, v ∈ S := by
  by_contra h
  have hSF : Disjoint S F := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvF
    exact h ⟨v, hvF, hvS⟩
  have hi : ∀ n, Disjoint ((zeroForcingStep G)^[n] S) F := by
    intro n
    induction n with
    | zero => exact hSF
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact step_disjoint_fort G hF ih
  have hc := hi (Fintype.card V)
  change Disjoint (zeroForcingClosure G S) F at hc
  change zeroForcingClosure G S = Finset.univ at hS
  rw [hS] at hc
  obtain ⟨v, hvF⟩ := hF.1
  exact Finset.disjoint_left.mp hc (Finset.mem_univ v) hvF

end Forts

/-- Each block contains its central vertex, branch vertex, and two terminal triangles. -/
abbrev Vertex := Fin 3 × Fin 8

/-- Adjacency within one block. -/
def localAdj (a b : Fin 8) : Prop :=
  a ≠ b ∧
    ((a ≤ 1 ∧ b ≤ 1) ∨
     (2 ≤ a ∧ a ≤ 4 ∧ 2 ≤ b ∧ b ≤ 4) ∨
     (5 ≤ a ∧ 5 ≤ b) ∨
     (a = 1 ∧ (b = 2 ∨ b = 5)) ∨
     (b = 1 ∧ (a = 2 ∨ a = 5)))

instance : DecidableRel localAdj := fun _ _ => by
  unfold localAdj
  infer_instance

/-- Fischer's 24-vertex graph, with the three blocks indexed by `Fin 3`. -/
def graph : SimpleGraph Vertex where
  Adj u v :=
    (u.2 = 0 ∧ v.2 = 0 ∧ u.1 ≠ v.1) ∨ (u.1 = v.1 ∧ localAdj u.2 v.2)
  symm := ⟨by
    rintro u v (h | h)
    · exact Or.inl ⟨h.2.1, h.1, Ne.symm h.2.2⟩
    · exact Or.inr ⟨h.1.symm, by
        rcases h.2 with ⟨hne, h⟩
        refine ⟨Ne.symm hne, ?_⟩
        tauto⟩⟩
  loopless := ⟨by
    intro v
    simp [localAdj]⟩

instance : DecidableRel graph.Adj := fun _ _ => by
  dsimp [graph]
  infer_instance

lemma adj_local (j : Fin 3) {a b : Fin 8} (h : localAdj a b) :
    graph.Adj (j, a) (j, b) := Or.inr ⟨rfl, h⟩

def weight (S : Finset Vertex) (j : Fin 3) (k : Fin 8) : ℕ :=
  if (j, k) ∈ S then 1 else 0

def row (S : Finset Vertex) (j : Fin 3) : ℕ := ∑ k, weight S j k

lemma weight_le_one (S : Finset Vertex) (j : Fin 3) (k : Fin 8) :
    weight S j k ≤ 1 := by
  simp only [weight]
  split <;> omega

lemma weight_eq_zero {S : Finset Vertex} {j : Fin 3} {k : Fin 8} :
    weight S j k = 0 ↔ (j, k) ∉ S := by
  simp [weight]

lemma row_eq (S : Finset Vertex) (j : Fin 3) :
    row S j = weight S j 0 + weight S j 1 + weight S j 2 + weight S j 3 +
      weight S j 4 + weight S j 5 + weight S j 6 + weight S j 7 := by
  simp [row, Fin.sum_univ_succ]
  omega

lemma card_eq_rows (S : Finset Vertex) : S.card = row S 0 + row S 1 + row S 2 := by
  have h : (∑ j, row S j) = S.card := by
    simp only [row]
    rw [← Fintype.sum_prod_type (fun v : Vertex => weight S v.1 v.2)]
    simp [weight]
  simp [Fin.sum_univ_succ] at h
  omega

def tipZ (t : Fin 2) : Fin 8 := ⟨2 + 3 * t.val, by omega⟩

def tipOther (t e : Fin 2) : Fin 8 := ⟨3 + 3 * t.val + e.val, by omega⟩

/-- The two terminal vertices other than the attachment vertex. -/
def leafPair (j : Fin 3) (t : Fin 2) : Finset Vertex :=
  {(j, tipOther t 0), (j, tipOther t 1)}

/-- The attachment vertex and one of the other terminal vertices. -/
def tipPair (j : Fin 3) (t e : Fin 2) : Finset Vertex :=
  {(j, tipZ t), (j, tipOther t e)}

/-- Two attachment-containing pairs in one block. -/
def branchFort (j : Fin 3) (e f : Fin 2) : Finset Vertex :=
  tipPair j 0 e ∪ tipPair j 1 f

/-- Two central vertices and one attachment-containing pair in each block. -/
def crossFort (i j : Fin 3) (t u e f : Fin 2) : Finset Vertex :=
  {(i, 0), (j, 0)} ∪ tipPair i t e ∪ tipPair j u f

set_option maxRecDepth 4096 in
lemma leaf_forts : ∀ j t, IsFort graph (leafPair j t) := by decide

set_option maxRecDepth 4096 in
lemma branch_forts : ∀ j e f, IsFort graph (branchFort j e f) := by decide

set_option maxRecDepth 4096 in
lemma cross_forts : ∀ i j, i ≠ j → ∀ t u e f, IsFort graph (crossFort i j t u e f) := by
  decide

lemma fort_weight {S F : Finset Vertex} (hS : IsZeroForcingSet graph S)
    (hF : IsFort graph F) : 1 ≤ ∑ v ∈ F, weight S v.1 v.2 := by
  obtain ⟨⟨j, k⟩, hvF, hvS⟩ := zero_forcing_hits_fort graph hS hF
  have hw : weight S j k = 1 := by simp [weight, hvS]
  rw [← hw]
  exact Finset.single_le_sum (f := fun v : Vertex => weight S v.1 v.2)
    (fun _ _ => Nat.zero_le _) hvF

lemma leaf_weights {S : Finset Vertex} (hS : IsZeroForcingSet graph S) (j : Fin 3) :
    1 ≤ weight S j 3 + weight S j 4 ∧ 1 ≤ weight S j 6 + weight S j 7 := by
  constructor
  · simpa [leafPair, tipOther] using fort_weight hS (leaf_forts j 0)
  · simpa [leafPair, tipOther] using fort_weight hS (leaf_forts j 1)

lemma terminal_weight_lower {S : Finset Vertex} (hS : IsZeroForcingSet graph S)
    (j : Fin 3) :
    3 ≤ weight S j 2 + weight S j 3 + weight S j 4 +
      weight S j 5 + weight S j 6 + weight S j 7 := by
  obtain ⟨ha, hb⟩ := leaf_weights hS j
  have h00 := fort_weight hS (branch_forts j 0 0)
  have h01 := fort_weight hS (branch_forts j 0 1)
  have h10 := fort_weight hS (branch_forts j 1 0)
  have h11 := fort_weight hS (branch_forts j 1 1)
  simp [branchFort, tipPair, tipZ, tipOther] at h00 h01 h10 h11
  omega

lemma row_lower {S : Finset Vertex} (hS : IsZeroForcingSet graph S) (j : Fin 3) :
    3 ≤ row S j := by
  have ht := terminal_weight_lower hS j
  rw [row_eq]
  omega

lemma gap_arithmetic (x₂ x₃ x₄ x₅ x₆ x₇ : ℕ)
    (h₂ : x₂ ≤ 1) (h₅ : x₅ ≤ 1)
    (ha : 1 ≤ x₃ + x₄) (hb : 1 ≤ x₆ + x₇)
    (hs : x₂ + x₃ + x₄ + x₅ + x₆ + x₇ ≤ 3) :
    (x₂ = 0 ∧ x₃ = 0) ∨ (x₂ = 0 ∧ x₄ = 0) ∨
      (x₅ = 0 ∧ x₆ = 0) ∨ (x₅ = 0 ∧ x₇ = 0) := by
  omega

lemma small_row_gap {S : Finset Vertex} (hS : IsZeroForcingSet graph S)
    (j : Fin 3) (hj : row S j ≤ 3) :
    (j, 0) ∉ S ∧ ∃ t e, Disjoint S (tipPair j t e) := by
  have ht := terminal_weight_lower hS j
  have hr := row_eq S j
  have hc : weight S j 0 = 0 := by omega
  have hs : weight S j 2 + weight S j 3 + weight S j 4 +
      weight S j 5 + weight S j 6 + weight S j 7 ≤ 3 := by omega
  obtain ⟨ha, hb⟩ := leaf_weights hS j
  have hg := gap_arithmetic _ _ _ _ _ _ (weight_le_one S j 2)
    (weight_le_one S j 5) ha hb hs
  refine ⟨weight_eq_zero.mp hc, ?_⟩
  rcases hg with h | h | h | h
  · refine ⟨0, 0, ?_⟩
    simpa [tipPair, tipZ, tipOther] using
      And.intro (weight_eq_zero.mp h.1) (weight_eq_zero.mp h.2)
  · refine ⟨0, 1, ?_⟩
    simpa [tipPair, tipZ, tipOther] using
      And.intro (weight_eq_zero.mp h.1) (weight_eq_zero.mp h.2)
  · refine ⟨1, 0, ?_⟩
    simpa [tipPair, tipZ, tipOther] using
      And.intro (weight_eq_zero.mp h.1) (weight_eq_zero.mp h.2)
  · refine ⟨1, 1, ?_⟩
    simpa [tipPair, tipZ, tipOther] using
      And.intro (weight_eq_zero.mp h.1) (weight_eq_zero.mp h.2)

lemma pair_rows_lower {S : Finset Vertex} (hS : IsZeroForcingSet graph S)
    {i j : Fin 3} (hij : i ≠ j) : 7 ≤ row S i + row S j := by
  by_contra h
  have hi := row_lower hS i
  have hj := row_lower hS j
  have his : row S i ≤ 3 := by omega
  have hjs : row S j ≤ 3 := by omega
  obtain ⟨hci, t, e, hti⟩ := small_row_gap hS i his
  obtain ⟨hcj, u, f, htj⟩ := small_row_gap hS j hjs
  have hd : Disjoint S (crossFort i j t u e f) := by
    simpa [crossFort, Finset.disjoint_union_right, and_assoc] using
      And.intro (And.intro (And.intro hci hcj) hti) htj
  obtain ⟨v, hvF, hvS⟩ := zero_forcing_hits_fort graph hS (cross_forts i j hij t u e f)
  exact Finset.disjoint_left.mp hd hvS hvF

/-- Every zero forcing set in Fischer's graph has at least eleven vertices. -/
lemma zero_forcing_card_lower {S : Finset Vertex} (hS : IsZeroForcingSet graph S) :
    11 ≤ S.card := by
  have h01 := pair_rows_lower hS (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := pair_rows_lower hS (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := pair_rows_lower hS (show (1 : Fin 3) ≠ 2 by decide)
  rw [card_eq_rows]
  omega

lemma indep_edge_weight {S : Finset Vertex} (hS : graph.IsIndepSet (S : Set Vertex))
    {i j : Fin 3} {a b : Fin 8} (hab : graph.Adj (i, a) (j, b)) :
    weight S i a + weight S j b ≤ 1 := by
  by_cases ha : (i, a) ∈ S <;> by_cases hb : (j, b) ∈ S
  · exact False.elim (hS ha hb hab.ne hab)
  all_goals simp [weight, ha, hb]

lemma indep_row_upper {S : Finset Vertex} (hS : graph.IsIndepSet (S : Set Vertex))
    (j : Fin 3) : row S j ≤ 3 := by
  have h01 := indep_edge_weight hS (adj_local j (show localAdj 0 1 by decide))
  have h23 := indep_edge_weight hS (adj_local j (show localAdj 2 3 by decide))
  have h24 := indep_edge_weight hS (adj_local j (show localAdj 2 4 by decide))
  have h34 := indep_edge_weight hS (adj_local j (show localAdj 3 4 by decide))
  have h56 := indep_edge_weight hS (adj_local j (show localAdj 5 6 by decide))
  have h57 := indep_edge_weight hS (adj_local j (show localAdj 5 7 by decide))
  have h67 := indep_edge_weight hS (adj_local j (show localAdj 6 7 by decide))
  rw [row_eq]
  omega

lemma indep_card_upper {S : Finset Vertex} (hS : graph.IsIndepSet (S : Set Vertex)) :
    S.card ≤ 9 := by
  have h0 := indep_row_upper hS 0
  have h1 := indep_row_upper hS 1
  have h2 := indep_row_upper hS 2
  rw [card_eq_rows]
  omega

/-- The nine-clique partition bounds the independence number by nine. -/
lemma indepNum_upper : graph.indepNum ≤ 9 := by
  obtain ⟨S, hS⟩ := graph.exists_isNIndepSet_indepNum
  rw [← hS.card_eq]
  exact indep_card_upper hS.isIndepSet

/-- The full vertex set is zero forcing under the frozen closure definition. -/
lemma univ_zero_forcing : IsZeroForcingSet graph Finset.univ := by
  unfold IsZeroForcingSet zeroForcingClosure
  apply Function.iterate_fixed
  simp [zeroForcingStep]

/-- The minimum cardinality in the frozen definition is at least eleven. -/
lemma zeroForcingNumber_lower : 11 ≤ zeroForcingNumber graph := by
  unfold zeroForcingNumber
  apply le_csInf
  · exact ⟨Finset.univ.card, Finset.univ, rfl, univ_zero_forcing⟩
  · rintro k ⟨S, hcard, hS⟩
    rw [← hcard]
    exact zero_forcing_card_lower hS

lemma graph_connected : graph.Connected := by
  have hl : ∀ (j : Fin 3) (k : Fin 8), graph.Reachable (j, 0) (j, k) := by
    intro j k
    have h01 := (adj_local j (show localAdj 0 1 by decide)).reachable
    have h12 := (adj_local j (show localAdj 1 2 by decide)).reachable
    have h15 := (adj_local j (show localAdj 1 5 by decide)).reachable
    have h23 := (adj_local j (show localAdj 2 3 by decide)).reachable
    have h24 := (adj_local j (show localAdj 2 4 by decide)).reachable
    have h56 := (adj_local j (show localAdj 5 6 by decide)).reachable
    have h57 := (adj_local j (show localAdj 5 7 by decide)).reachable
    fin_cases k
    · exact .refl _
    · exact h01
    · exact h01.trans h12
    · exact (h01.trans h12).trans h23
    · exact (h01.trans h12).trans h24
    · exact h01.trans h15
    · exact (h01.trans h15).trans h56
    · exact (h01.trans h15).trans h57
  refine (SimpleGraph.connected_iff_exists_forall_reachable graph).mpr ⟨(0, 0), ?_⟩
  rintro ⟨j, k⟩
  have hc : graph.Reachable (0, 0) (j, 0) := by
    by_cases hj : j = 0
    · subst j
      exact .refl _
    · exact (show graph.Adj (0, 0) (j, 0) from Or.inl ⟨rfl, rfl, Ne.symm hj⟩).reachable
  exact hc.trans (hl j k)

lemma graph_maxDegree : graph.maxDegree ≤ 3 := by
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  decide

lemma graph_notK4 : graph = ⊤ → Fintype.card Vertex ≠ 4 := by
  intro _
  decide

/-- Fischer's graph violates the proposed zero forcing bound. -/
theorem counterexample : ¬ zeroForcingNumber graph ≤ graph.indepNum + 1 := by
  have hz := zeroForcingNumber_lower
  have ha := indepNum_upper
  omega

end TxGraffitiC2

end

open SimpleGraph

namespace Arxiv2507_17780

theorem tx_graffiti_conjecture_2 :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (_hConn : G.Connected)
      (_hDeg : G.maxDegree ≤ 3)
      (_hNotK4 : G = ⊤ → Fintype.card V ≠ 4),
      zeroForcingNumber G ≤ G.indepNum + 1 := fun h =>
  TxGraffitiC2.counterexample (h TxGraffitiC2.Vertex TxGraffitiC2.graph
    TxGraffitiC2.graph_connected TxGraffitiC2.graph_maxDegree TxGraffitiC2.graph_notK4)

end Arxiv2507_17780

end
