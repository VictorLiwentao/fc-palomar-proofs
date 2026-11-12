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
# Erdős's upper bound for Erdős Problem 626

This file proves the upstream statement `Erdos626.erdos_626.variants.erdos_upper`: for $k \ge 4$
and every $n$,
$$g_k(n) \le \frac{2 \log n}{\log (k - 2)} + 1.$$

Let $G$ on $n$ vertices have chromatic number $k$ and girth greater than $m$.

1. $G$ is not $(k-1)$-colourable. A smallest vertex set $S$ that cannot be properly coloured with
   $k - 1$ colours has minimum degree at least $k - 1$ inside $S$: otherwise colour $S \setminus
   \{v\}$ and give $v$ a free colour (`exists_le_card_filter_adj`).
2. Moore-type count (`exists_finset_of_two_mul_lt_egirth`). In a graph with minimum degree at least
   $d + 1$ and no cycle of length at most $2j$, every edge $uw$ has at least $d^j$ vertices that
   $w$ reaches by walks of length at most $j$ avoiding $u$. The branches at the $d$ or more
   neighbours $w' \ne u$ of $w$ are disjoint, since a common vertex closes a cycle of length at
   most $2j$ (`egirth_le_length_add_one`).
3. With $d = k - 2$ and $j = \lfloor m/2 \rfloor$ this gives $(k-2)^{\lfloor m/2 \rfloor} \le n$
   (`pow_le_of_chromaticNumber_eq`), so $m - 1 \le 2 \log n / \log(k-2)$.

The bound holds for every `n`, so in particular eventually.

*References:*
* [erdosproblems.com/626](https://www.erdosproblems.com/626)
* [Er62b] Erdős, P., *On circuits and subgraphs of chromatic graphs*. Mathematika 9 (1962),
  170-175, Theorem 1. (erdosproblems.com and the Formal Conjectures docstring cite [Er59b],
  *Graph theory and probability*, Canad. J. Math. 11 (1959), 34-38, which proves only the
  existence direction.)
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos626

/--
`g k n` is $g_k(n)$: the largest $m$ such that some graph on $n$ vertices has chromatic number
exactly $k$ and girth $> m$, that is, no cycle of length $\leq m$.

The girth is `SimpleGraph.egirth`, which is `⊤` for an acyclic graph. The value `sSup ∅ = 0`
for $n < k$ affects only finitely many $n$. For $k \leq 2$ the set is unbounded whenever an
acyclic graph on $n$ vertices with chromatic number $k$ exists, and then `sSup` is also $0$; this
case is not used below, where $k \geq 4$.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.chromaticNumber = k ∧ (m : ℕ∞) < G.egirth}

end Erdos626

namespace Erdos626Upper

open Finset SimpleGraph Filter

/-- An edge `uv` and a walk from `v` back to `u` that avoids the edge `uv` give a cycle. -/
lemma egirth_le_length_add_one {V : Type*} [DecidableEq V] {H : SimpleGraph V} {u v : V}
    (h : H.Adj u v) (p : H.Walk v u) (hp : s(u, v) ∉ p.edges) : H.egirth ≤ p.length + 1 := by
  have hc : (Walk.cons h p.bypass).IsCycle := (Walk.cons_isCycle_iff _ h).mpr
    ⟨p.bypass_isPath, fun he => hp (p.edges_bypass_subset_edges he)⟩
  calc H.egirth ≤ (Walk.cons h p.bypass).length := SimpleGraph.Walk.IsCycle.egirth_le_length hc
    _ ≤ p.length + 1 := by
      rw [Walk.length_cons]
      exact_mod_cast Nat.succ_le_succ p.length_bypass_le_length

/-- **Moore-type count.** Let every endpoint of an edge of `H` have degree at least `d + 1`, and
let `H` have no cycle of length at most `2j`. Then for every edge `uw` there are at least `d ^ j`
vertices that `w` reaches by a walk of length at most `j` that avoids `u`. -/
lemma exists_finset_of_two_mul_lt_egirth {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ)
    (hdeg : ∀ u w, H.Adj u w → d + 1 ≤ H.degree w) :
    ∀ j : ℕ, ((2 * j : ℕ) : ℕ∞) < H.egirth → ∀ u w, H.Adj u w →
      ∃ S : Finset V, d ^ j ≤ #S ∧ ∀ x ∈ S, ∃ p : H.Walk w x, p.length ≤ j ∧ u ∉ p.support := by
  intro j
  induction j with
  | zero =>
    intro _ u w huw
    refine ⟨{w}, by simp, fun x hx => ?_⟩
    rw [mem_singleton] at hx
    subst hx
    exact ⟨Walk.nil, le_rfl, by simpa using huw.ne⟩
  | succ j ih =>
    intro hj u w huw
    have hj' : ((2 * j : ℕ) : ℕ∞) < H.egirth :=
      lt_of_le_of_lt (by exact_mod_cast (by omega : 2 * j ≤ 2 * (j + 1))) hj
    choose! T hTcard hTwalk using ih hj'
    have hNadj : ∀ w' ∈ (H.neighborFinset w).erase u, H.Adj w w' :=
      fun w' hw' => (mem_neighborFinset _ _ _).mp (mem_of_mem_erase hw')
    -- Two branches at `w` are disjoint: a common vertex closes a cycle of length `≤ 2j + 2`.
    have hdisj : (((H.neighborFinset w).erase u : Finset V) : Set V).PairwiseDisjoint (T w) := by
      intro w₁ hw₁ w₂ hw₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx₁ hx₂
      obtain ⟨p₁, hp₁, hwp₁⟩ := hTwalk w w₁ (hNadj w₁ hw₁) x hx₁
      obtain ⟨p₂, hp₂, hwp₂⟩ := hTwalk w w₂ (hNadj w₂ hw₂) x hx₂
      have h₂ : H.Adj w₂ w := (hNadj w₂ hw₂).symm
      have key := egirth_le_length_add_one (hNadj w₁ hw₁) ((p₁.append p₂.reverse).concat h₂) ?_
      · rw [Walk.length_concat, Walk.length_append, Walk.length_reverse] at key
        have : 2 * (j + 1) < p₁.length + p₂.length + 1 + 1 := by exact_mod_cast hj.trans_le key
        omega
      · intro he
        simp only [Walk.edges_concat, Walk.edges_append, Walk.edges_reverse,
          List.concat_eq_append, List.mem_append, List.mem_reverse, List.mem_singleton] at he
        rcases he with (he | he) | he
        · exact hwp₁ (p₁.fst_mem_support_of_mem_edges he)
        · exact hwp₂ (p₂.fst_mem_support_of_mem_edges he)
        · rcases Sym2.eq_iff.mp he with ⟨h, -⟩ | ⟨-, h⟩
          · exact h₂.ne h.symm
          · exact hne h
    refine ⟨((H.neighborFinset w).erase u).biUnion (T w), ?_, fun x hx => ?_⟩
    · have hcard : d ≤ #((H.neighborFinset w).erase u) := by
        rw [card_erase_of_mem ((mem_neighborFinset _ _ _).mpr huw.symm),
          card_neighborFinset_eq_degree]
        have := hdeg u w huw
        omega
      rw [card_biUnion hdisj]
      calc d ^ (j + 1) = d * d ^ j := by ring
        _ ≤ #((H.neighborFinset w).erase u) * d ^ j := Nat.mul_le_mul_right _ hcard
        _ = ∑ _ ∈ (H.neighborFinset w).erase u, d ^ j := by rw [sum_const, smul_eq_mul]
        _ ≤ ∑ w' ∈ (H.neighborFinset w).erase u, #(T w w') :=
          sum_le_sum fun w' hw' => hTcard w w' (hNadj w' hw')
    · obtain ⟨w', hw', hx⟩ := mem_biUnion.mp hx
      obtain ⟨q, hq, hwq⟩ := hTwalk w w' (hNadj w' hw') x hx
      refine ⟨Walk.cons (hNadj w' hw') q, by rw [Walk.length_cons]; omega, ?_⟩
      rw [Walk.support_cons, List.mem_cons, not_or]
      refine ⟨huw.ne, fun hu => ?_⟩
      -- A walk from `w'` to `u` that avoids `w` closes a cycle through the edge `wu`.
      have hsub := q.support_takeUntil_subset_support hu
      have hlen := q.length_takeUntil_le_length hu
      have key := egirth_le_length_add_one huw.symm
        ((q.takeUntil u hu).reverse.concat (hNadj w' hw').symm) ?_
      · rw [Walk.length_concat, Walk.length_reverse] at key
        have : 2 * (j + 1) < (q.takeUntil u hu).length + 1 + 1 := by
          exact_mod_cast hj.trans_le key
        omega
      · intro he
        simp only [Walk.edges_concat, Walk.edges_reverse, List.concat_eq_append, List.mem_append,
          List.mem_reverse, List.mem_singleton] at he
        rcases he with he | he
        · exact hwq (hsub ((q.takeUntil u hu).fst_mem_support_of_mem_edges he))
        · rcases Sym2.eq_iff.mp he with ⟨h, -⟩ | ⟨-, h⟩
          · exact (hNadj w' hw').ne h
          · exact ne_of_mem_erase hw' h.symm

/-- A graph that is not `c`-colourable has a nonempty vertex set `S` in which every vertex has
at least `c` neighbours. -/
lemma exists_le_card_filter_adj {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {c : ℕ} (hc : 0 < c) (hG : ¬ G.Colorable c) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, c ≤ #(S.filter (G.Adj v)) := by
  classical
  -- `Good s`: the vertices of `s` can be properly coloured with `c` colours.
  let Good : Finset V → Prop := fun s => ∃ f : V → Fin c, ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → f x ≠ f y
  have hbad : ¬ Good univ := by
    rintro ⟨f, hf⟩
    exact hG ⟨Coloring.mk f fun {x y} h => hf x (mem_univ x) y (mem_univ y) h⟩
  obtain ⟨S, hS, hmin⟩ := (univ.filter fun s : Finset V => ¬ Good s).exists_min_image card
    ⟨univ, mem_filter.mpr ⟨mem_univ _, hbad⟩⟩
  rw [mem_filter] at hS
  refine ⟨S, ?_, fun v hv => ?_⟩
  · rw [nonempty_iff_ne_empty]
    rintro rfl
    exact hS.2 ⟨fun _ => ⟨0, hc⟩, by simp⟩
  · by_contra hlt
    push Not at hlt
    -- Colour `S.erase v` by minimality, then give `v` a colour unused on its neighbours.
    have hgood : Good (S.erase v) := by
      by_contra h
      have := hmin (S.erase v) (mem_filter.mpr ⟨mem_univ _, h⟩)
      rw [card_erase_of_mem hv] at this
      have := card_pos.mpr ⟨v, hv⟩
      omega
    obtain ⟨f, hf⟩ := hgood
    obtain ⟨a, ha⟩ : ∃ a : Fin c, a ∉ (S.filter (G.Adj v)).image f := by
      by_contra h
      push Not at h
      have h₁ := card_le_card fun a (_ : a ∈ (univ : Finset (Fin c))) => h a
      rw [card_univ, Fintype.card_fin] at h₁
      have h₂ := card_image_le (s := S.filter (G.Adj v)) (f := f)
      omega
    apply hS.2
    refine ⟨Function.update f v a, fun x hx y hy hxy => ?_⟩
    by_cases hxv : x = v
    · have hyv : y ≠ v := fun h => hxy.ne (hxv.trans h.symm)
      rw [hxv, Function.update_self, Function.update_of_ne hyv]
      intro h
      exact ha (mem_image.mpr ⟨y, mem_filter.mpr ⟨hy, hxv ▸ hxy⟩, h.symm⟩)
    · by_cases hyv : y = v
      · rw [hyv, Function.update_self, Function.update_of_ne hxv]
        intro h
        exact ha (mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, hyv ▸ hxy.symm⟩, h⟩)
      · rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
        exact hf x (mem_erase.mpr ⟨hxv, hx⟩) y (mem_erase.mpr ⟨hyv, hy⟩) hxy

/-- The graph `G` with only the edges inside `S`. -/
def restrict {V : Type*} (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    DecidableRel (restrict G S).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ x ∈ S ∧ y ∈ S))

/-- A graph on `n` vertices with chromatic number `k ≥ 4` and girth greater than `m` satisfies
`(k - 2) ^ (m / 2) ≤ n`. -/
lemma pow_le_of_chromaticNumber_eq {n k m : ℕ} (hk : 4 ≤ k) (G : SimpleGraph (Fin n))
    (hχ : G.chromaticNumber = k) (hm : (m : ℕ∞) < G.egirth) : (k - 2) ^ (m / 2) ≤ n := by
  classical
  have hcol : ¬ G.Colorable (k - 1) := by
    intro h
    have := h.chromaticNumber_le
    rw [hχ] at this
    have : k ≤ k - 1 := by exact_mod_cast this
    omega
  obtain ⟨S, ⟨v, hv⟩, hS⟩ := exists_le_card_filter_adj G (by omega : 0 < k - 1) hcol
  have hdeg : ∀ u w, (restrict G S).Adj u w → k - 2 + 1 ≤ (restrict G S).degree w := by
    intro u w huw
    have hw : w ∈ S := huw.2.2
    have hN : (restrict G S).neighborFinset w = S.filter (G.Adj w) := by
      ext x
      rw [mem_neighborFinset, mem_filter]
      exact ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, hw, h.1⟩⟩
    rw [← card_neighborFinset_eq_degree, hN]
    have := hS w hw
    omega
  obtain ⟨w, hw⟩ : (S.filter (G.Adj v)).Nonempty := by
    have := hS v hv
    exact card_pos.mp (by omega)
  rw [mem_filter] at hw
  have hg : ((2 * (m / 2) : ℕ) : ℕ∞) < (restrict G S).egirth :=
    lt_of_le_of_lt (by exact_mod_cast (by omega : 2 * (m / 2) ≤ m))
      (hm.trans_le (egirth_anti fun _ _ h => h.1))
  obtain ⟨T, hT, -⟩ :=
    exists_finset_of_two_mul_lt_egirth _ (k - 2) hdeg (m / 2) hg v w ⟨hw.2, hv, hw.1⟩
  calc (k - 2) ^ (m / 2) ≤ #T := hT
    _ ≤ Fintype.card (Fin n) := card_le_univ T
    _ = n := Fintype.card_fin n

/-- **Erdős 626, Erdős's upper bound.** The exact statement of
`Erdos626.erdos_626.variants.erdos_upper`. -/
theorem erdos_626_variants_erdos_upper :
    ∀ k : ℕ, 4 ≤ k → ∀ᶠ n : ℕ in atTop,
      (Erdos626.g k n : ℝ) ≤ 2 * Real.log n / Real.log ((k : ℝ) - 2) + 1 := by
  intro k hk
  refine Eventually.of_forall fun n => ?_
  have hk2 : (2 : ℝ) ≤ (k : ℝ) - 2 := by
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hL : 0 < Real.log ((k : ℝ) - 2) := Real.log_pos (by linarith)
  have hB : 0 ≤ 2 * Real.log n / Real.log ((k : ℝ) - 2) + 1 := by
    have := div_nonneg (mul_nonneg zero_le_two (Real.log_natCast_nonneg n)) hL.le
    linarith
  have hle : Erdos626.g k n ≤ ⌊2 * Real.log n / Real.log ((k : ℝ) - 2) + 1⌋₊ := by
    unfold Erdos626.g
    refine csSup_le' fun m ⟨G, hχ, hm⟩ => Nat.le_floor ?_
    have hpow : (((k - 2) ^ (m / 2) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast pow_le_of_chromaticNumber_eq hk G hχ hm
    rw [Nat.cast_pow, Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_ofNat] at hpow
    have hlog : ((m / 2 : ℕ) : ℝ) * Real.log ((k : ℝ) - 2) ≤ Real.log n := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos (by linarith) _) hpow
    have hm2 : (m : ℝ) - 1 ≤ 2 * ((m / 2 : ℕ) : ℝ) := by
      have : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : m ≤ 2 * (m / 2) + 1)
      linarith
    have : (m : ℝ) - 1 ≤ 2 * Real.log n / Real.log ((k : ℝ) - 2) := by
      rw [le_div_iff₀ hL]
      have := mul_le_mul_of_nonneg_right hm2 hL.le
      linarith
    linarith
  calc (Erdos626.g k n : ℝ) ≤ ⌊2 * Real.log n / Real.log ((k : ℝ) - 2) + 1⌋₊ := by
        exact_mod_cast hle
    _ ≤ 2 * Real.log n / Real.log ((k : ℝ) - 2) + 1 := Nat.floor_le hB

end Erdos626Upper

open Filter
open scoped Topology

namespace Erdos626

theorem erdos_626.variants.erdos_upper :
    ∀ k : ℕ, 4 ≤ k → ∀ᶠ n : ℕ in atTop,
      (g k n : ℝ) ≤ 2 * Real.log n / Real.log ((k : ℝ) - 2) + 1 :=
  Erdos626Upper.erdos_626_variants_erdos_upper

end Erdos626

end
