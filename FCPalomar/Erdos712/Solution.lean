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
# The graph case of Erdős Problem 712

This file proves the upstream statements `Erdos712.erdos_712.variants.graph_case` and
`Erdos712.erdos_712.variants.graph_case_div_sq`: for $k \ge 2$,
$$\frac{\mathrm{ex}_2(n, K_k)}{\binom{n}{2}} \to 1 - \frac{1}{k-1}, \qquad
\frac{\mathrm{ex}_2(n, K_k)}{n^2} \to \frac12 \left(1 - \frac{1}{k-1}\right).$$

A $2$-uniform family on `Fin n` is the edge set of a simple graph, and it contains all
$\binom{k}{2}$ pairs of a $k$-set exactly when the graph has a $k$-clique. So
`Hypergraph.cliqueExtremalNumber n 2 k` equals Mathlib's `SimpleGraph.extremalNumber n` of
the complete graph on `Fin k`. By Turán's theorem (`SimpleGraph.extremalNumber_top`) this is
the number of edges of `turanGraph n (k - 1)`. The exact edge count
(`SimpleGraph.card_edgeFinset_turanGraph`) is $(1 - 1/r)\, n^2/2 - O(r^2)$ with $r = k - 1$,
which gives both limits.

The definitions are those of `FormalConjectures/ErdosProblems/712.lean` and
`FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean`.

*References:*
* Turán, P. (1941). "On an extremal problem in graph theory." *Mat. Fiz. Lapok* 48, pp. 436--452.
* [erdosproblems.com/712](https://www.erdosproblems.com/712)
-/

@[expose] public section

namespace Finset

variable {V : Type*} [DecidableEq V]

/-- A copy of the complete `r`-uniform hypergraph on `k` vertices. -/
def ContainsCompleteHypergraph (H : Finset (Finset V)) (r k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k ∧ S.powersetCard r ⊆ H

end Finset

namespace Hypergraph

open scoped Classical in
/-- Maximum number of edges among `r`-uniform families satisfying `P` on `n` labeled vertices.
The value is zero if no family is admissible. -/
noncomputable def extremalNumber (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter P).sup Finset.card

/-- The extremal number forbidding a complete uniform hypergraph. -/
noncomputable def cliqueExtremalNumber (n r k : ℕ) : ℕ :=
  extremalNumber n r fun H ↦ ¬ H.ContainsCompleteHypergraph r k

end Hypergraph

namespace Erdos712Graph

open Filter SimpleGraph
open scoped Topology Finset

section Bridge

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma toFinset_injective : Function.Injective (Sym2.toFinset : Sym2 V → Finset V) :=
  fun z w h => Sym2.ext fun a => by rw [← Sym2.mem_toFinset, h, Sym2.mem_toFinset]

/-- The edges of a graph, as a family of `2`-element sets. -/
def edgeSets (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  G.edgeFinset.image Sym2.toFinset

variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma card_edgeSets : (edgeSets G).card = G.edgeFinset.card :=
  Finset.card_image_of_injective _ toFinset_injective

lemma pair_mem_edgeSets {u v : V} : ({u, v} : Finset V) ∈ edgeSets G ↔ G.Adj u v := by
  simp only [edgeSets, Finset.mem_image, mem_edgeFinset]
  constructor
  · rintro ⟨z, hz, hzuv⟩
    obtain rfl : z = s(u, v) := toFinset_injective (hzuv.trans Sym2.toFinset_mk_eq.symm)
    exact hz
  · exact fun h => ⟨s(u, v), h, Sym2.toFinset_mk_eq⟩

lemma edgeSets_subset : edgeSets G ⊆ (Finset.univ : Finset V).powersetCard 2 := by
  intro e he
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
    Sym2.card_toFinset_of_not_isDiag z (G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp hz))⟩

/-- All pairs of `S` are edges exactly when `S` is a clique. -/
lemma powersetCard_two_subset_edgeSets_iff {S : Finset V} :
    S.powersetCard 2 ⊆ edgeSets G ↔ G.IsClique (S : Set V) := by
  constructor
  · intro h u hu v hv huv
    refine pair_mem_edgeSets.mp (h (Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair huv⟩))
    exact Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩
  · intro h e he
    obtain ⟨heS, he2⟩ := Finset.mem_powersetCard.mp he
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp he2
    exact pair_mem_edgeSets.mpr
      (h (heS (Finset.mem_insert_self u {v})) (heS (by simp)) huv)

lemma containsCompleteHypergraph_edgeSets_iff {k : ℕ} :
    (edgeSets G).ContainsCompleteHypergraph 2 k ↔ ¬G.CliqueFree k := by
  simp only [Finset.ContainsCompleteHypergraph, powersetCard_two_subset_edgeSets_iff,
    CliqueFree, not_forall, not_not, isNClique_iff]
  exact ⟨fun ⟨S, hS, hc⟩ => ⟨S, hc, hS⟩, fun ⟨S, hc, hS⟩ => ⟨S, hS, hc⟩⟩

/-- A `2`-uniform family is the edge family of the graph it defines. -/
lemma edgeSets_eq {H : Finset (Finset V)} (hH : H ⊆ (Finset.univ : Finset V).powersetCard 2)
    (hG : ∀ u v, G.Adj u v ↔ u ≠ v ∧ ({u, v} : Finset V) ∈ H) : edgeSets G = H := by
  ext e
  constructor
  · intro he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    induction z using Sym2.ind with
    | _ u v =>
      rw [Sym2.toFinset_mk_eq]
      exact ((hG u v).mp (mem_edgeFinset.mp hz)).2
  · intro he
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp (hH he)).2
    exact pair_mem_edgeSets.mpr ((hG u v).mpr ⟨huv, he⟩)

end Bridge

section HypergraphExtremal

variable {n r : ℕ} {P : Finset (Finset (Fin n)) → Prop}

open scoped Classical in
lemma le_hypergraphExtremalNumber {H : Finset (Finset (Fin n))}
    (hH : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r) (hP : P H) :
    H.card ≤ Hypergraph.extremalNumber n r P := by
  unfold Hypergraph.extremalNumber
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hH, hP⟩)

open scoped Classical in
lemma hypergraphExtremalNumber_le {m : ℕ}
    (h : ∀ H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r, P H → H.card ≤ m) :
    Hypergraph.extremalNumber n r P ≤ m := by
  unfold Hypergraph.extremalNumber
  refine Finset.sup_le fun H hH => ?_
  rw [Finset.mem_filter, Finset.mem_powerset] at hH
  exact h H hH.1 hH.2

end HypergraphExtremal

/-- The `2`-uniform clique extremal number is the graph extremal number of `K_k`. -/
theorem cliqueExtremalNumber_two_eq (n k : ℕ) :
    Hypergraph.cliqueExtremalNumber n 2 k = extremalNumber n (⊤ : SimpleGraph (Fin k)) := by
  unfold Hypergraph.cliqueExtremalNumber
  apply le_antisymm
  · refine hypergraphExtremalNumber_le fun H hH1 hH2 => ?_
    have hH : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2 ∧
        ¬H.ContainsCompleteHypergraph 2 k := ⟨hH1, hH2⟩
    classical
    let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun u v => ({u, v} : Finset (Fin n)) ∈ H
    have hG : ∀ u v, G.Adj u v ↔ u ≠ v ∧ ({u, v} : Finset (Fin n)) ∈ H := by
      intro u v
      simp only [G, fromRel_adj, Finset.pair_comm v u, or_self]
    have hEq := edgeSets_eq hH.1 hG
    have hfree : G.CliqueFree k := by
      have h2 := hH.2
      rw [← hEq, containsCompleteHypergraph_edgeSets_iff, not_not] at h2
      exact h2
    have hfree' : (⊤ : SimpleGraph (Fin k)).Free G :=
      cliqueFree_card_iff_free_top.mp (by rwa [Fintype.card_fin])
    have := card_edgeFinset_le_extremalNumber hfree'
    rw [Fintype.card_fin] at this
    rwa [← hEq, card_edgeSets]
  · have key := (extremalNumber_le_iff (V := Fin n) (⊤ : SimpleGraph (Fin k))
      (Hypergraph.extremalNumber n 2 fun H ↦ ¬H.ContainsCompleteHypergraph 2 k)).mpr ?_
    · rwa [Fintype.card_fin] at key
    intro G _ hfree
    rw [← card_edgeSets]
    refine le_hypergraphExtremalNumber edgeSets_subset ?_
    rw [containsCompleteHypergraph_edgeSets_iff, not_not]
    have hc := cliqueFree_card_iff_free_top.mpr hfree
    rwa [Fintype.card_fin] at hc

/-- Two-sided bounds on the number of edges of `turanGraph n (m + 1)`. -/
lemma turanGraph_bounds (n m : ℕ) :
    2 * (m + 1) * #(turanGraph n (m + 1)).edgeFinset ≤ m * n ^ 2 ∧
      m * n ^ 2 ≤
        2 * (m + 1) * #(turanGraph n (m + 1)).edgeFinset + 2 * (m + 1) + (m + 1) ^ 3 := by
  refine ⟨by simpa using mul_turanNumber_le (n := n) (r := m + 1), ?_⟩
  rw [show #(turanGraph n (m + 1)).edgeFinset = turanNumber n (m + 1) from rfl, turanNumber_eq]
  have hs : n % (m + 1) < m + 1 := Nat.mod_lt _ (Nat.succ_pos m)
  have hsq : (n % (m + 1)) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.mod_le _ _) 2
  generalize n % (m + 1) = s at hs hsq ⊢
  obtain ⟨d, hd⟩ : ∃ d, n ^ 2 = d + s ^ 2 := ⟨n ^ 2 - s ^ 2, (Nat.sub_add_cancel hsq).symm⟩
  rw [hd, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hdiv := Nat.div_add_mod (d * m) (2 * (m + 1))
  have hmod := Nat.mod_lt (d * m) (show 0 < 2 * (m + 1) by omega)
  have hts : m * s ^ 2 ≤ (m + 1) ^ 3 :=
    calc m * s ^ 2 ≤ m * m ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = m ^ 3 := by ring
      _ ≤ (m + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  nlinarith [Nat.zero_le (2 * (m + 1) * s.choose 2)]

/-- `e(T(n, m + 1)) / n² → m / (2 (m + 1))`. -/
lemma tendsto_turanGraph_div_sq (m : ℕ) :
    Tendsto (fun n : ℕ ↦ (#(turanGraph n (m + 1)).edgeFinset : ℝ) / (n : ℝ) ^ 2) atTop
      (𝓝 ((m : ℝ) / (2 * (m + 1)))) := by
  have hm : (0 : ℝ) < 2 * (m + 1) := by positivity
  have hK : Tendsto (fun n : ℕ ↦ (m : ℝ) / (2 * (m + 1)) - ((m + 1) ^ 2 + 1) / (n : ℝ) ^ 2)
      atTop (𝓝 ((m : ℝ) / (2 * (m + 1)))) := by
    have h0 := (tendsto_const_nhds (x := ((m + 1) ^ 2 + 1 : ℝ))).div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds (x := (m : ℝ) / (2 * (m + 1)))).sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hK tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hn) 2
    have h2 : (m : ℝ) * n ^ 2 ≤ 2 * (m + 1) * #(turanGraph n (m + 1)).edgeFinset +
        2 * (m + 1) + (m + 1) ^ 3 := by exact_mod_cast (turanGraph_bounds n m).2
    have key : (m : ℝ) / (2 * (m + 1)) ≤
        ((#(turanGraph n (m + 1)).edgeFinset : ℝ) + ((m + 1) ^ 2 + 1)) / (n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hm hn2]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ m + 1 by positivity) 3]
    rw [add_div] at key
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hn) 2
    have h1 : 2 * (m + 1) * (#(turanGraph n (m + 1)).edgeFinset : ℝ) ≤ m * n ^ 2 := by
      exact_mod_cast (turanGraph_bounds n m).1
    rw [div_le_div_iff₀ hn2 hm]
    linarith

/-- `n² / C(n, 2) → 2`. -/
lemma tendsto_sq_div_choose_two :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 / (n.choose 2 : ℝ)) atTop (𝓝 2) := by
  have h := (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (-1)).const_mul 2
  rw [mul_one] at h
  refine Tendsto.congr' ?_ h
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (n : ℝ) ≠ 0 := by positivity
  have h1 : (n : ℝ) + -1 ≠ 0 := by linarith
  have h2 : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [Nat.cast_choose_two]
  field_simp
  ring

/-- **Turán's theorem, normalized by $n^2$.** The exact statement of
`Erdos712.erdos_712.variants.graph_case_div_sq`. -/
theorem erdos_712_variants_graph_case_div_sq (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 ((1 / 2) * (1 - 1 / ((k : ℝ) - 1)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have e : ∀ n, Hypergraph.cliqueExtremalNumber n 2 (m + 2) =
      #(turanGraph n (m + 1)).edgeFinset := fun n => by
    rw [cliqueExtremalNumber_two_eq, extremalNumber_top, Fintype.card_fin,
      show m + 2 - 1 = m + 1 by omega]
  have hc : (1 / 2 : ℝ) * (1 - 1 / (((m + 2 : ℕ) : ℝ) - 1)) = (m : ℝ) / (2 * (m + 1)) := by
    rw [show ((m + 2 : ℕ) : ℝ) - 1 = (m : ℝ) + 1 by push_cast; ring]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hc]
  simp only [e]
  exact tendsto_turanGraph_div_sq m

/-- **Turán's theorem, normalized by $\binom{n}{2}$.** The exact statement of
`Erdos712.erdos_712.variants.graph_case`. -/
theorem erdos_712_variants_graph_case (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / n.choose 2)
      atTop (𝓝 (1 - 1 / ((k : ℝ) - 1))) := by
  have h := (erdos_712_variants_graph_case_div_sq k hk).mul tendsto_sq_div_choose_two
  rw [show (1 / 2 : ℝ) * (1 - 1 / ((k : ℝ) - 1)) * 2 = 1 - 1 / ((k : ℝ) - 1) by ring] at h
  refine Tendsto.congr' ?_ h
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact div_mul_div_cancel₀ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hn.ne'))

end Erdos712Graph

open Filter Asymptotics
open scoped Topology

namespace Erdos712

theorem erdos_712.variants.graph_case (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / n.choose 2)
      atTop (𝓝 (1 - 1 / ((k : ℝ) - 1))) :=
  Erdos712Graph.erdos_712_variants_graph_case k hk

theorem erdos_712.variants.graph_case_div_sq (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 ((1 / 2) * (1 - 1 / ((k : ℝ) - 1)))) :=
  Erdos712Graph.erdos_712_variants_graph_case_div_sq k hk

end Erdos712

end
