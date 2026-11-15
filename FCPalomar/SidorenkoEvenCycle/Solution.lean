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
# Sidorenko's inequality for even cycles

This file proves the upstream statement
`SidorenkoConjecture.sidorenko_conjecture.variants.even_cycle`: for `k ≥ 2` and every finite graph
`G` on a nonempty vertex set, $t(K_2, G)^{e(C_{2k})} \le t(C_{2k}, G)$.

Write $n = |V(G)|$, $A$ for the adjacency matrix, $\mathbf 1$ for the all-ones vector and
$x_j = A^j \mathbf 1$ (`walkVec`). The proof uses no eigenvalues.

1. **Walks to homomorphisms** (`card_walkPairs_le_homCount`). Two walks of length $k$ from $u$ to
   $v$ make a closed walk of length $2k$, and its vertices form a homomorphism $C_{2k} \to G$.
   This map is injective, so $\hom(C_{2k}, G) \ge \sum_{u,v} (A^k)_{uv}^2$.
2. **Rows** (Cauchy–Schwarz). $\sum_{u,v} (A^k)_{uv}^2 \ge \frac1n \sum_u (x_k)_u^2$.
3. **Log-convexity** (`walkVec_dot`, `logConvex`). Since $A$ is symmetric,
   $x_a \cdot x_b = \mathbf 1 \cdot x_{a+b}$. So $T_j = \|x_j\|^2$ satisfies
   $T_j^2 = (x_{j-1} \cdot x_{j+1})^2 \le T_{j-1} T_{j+1}$, hence $T_k \ge n\,(T_1/n)^k$.
4. **Degrees.** $T_1 = \sum_v \deg(v)^2 \ge (2m)^2/n$ (Cauchy–Schwarz again).

Together, $\hom(C_{2k}, G) \ge (2m/n)^{2k}$, which is the claim after dividing by $n^{2k}$.

The definitions are those of `FormalConjectures/Wikipedia/SidorenkoConjecture.lean` and
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/HomDensity.lean`.

*Reference:* Sidorenko, A. (1993). "A correlation inequality for bipartite graphs."
*Graphs Combin.* 9, pp. 201--204.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*}

/-- The number of graph homomorphisms `H → G`, as a natural number. For finite vertex
types this is just the cardinality of the `Hom` type. -/
noncomputable def homCount [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℕ :=
  Fintype.card (H →g G)

/-- The **homomorphism density** `t(H, G)` of a simple graph `H` in a simple graph `G` with
finite vertex sets is `#Hom(H, G) / |V(G)|^{|V(H)|}`. -/
noncomputable def homDensity [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] : ℝ :=
  (homCount H G : ℝ) / (Fintype.card W : ℝ) ^ (Fintype.card V)

end SimpleGraph

open Finset SimpleGraph

namespace SidorenkoConjecture

variable {V W : Type*}

/-- **Homomorphism count of `K_2` into `G` equals `2 · #edgeFinset`.**

A homomorphism `K_2 →g G` is the same data as an ordered pair `(f 0, f 1)` of distinct
vertices with `G.Adj (f 0) (f 1)`. These are in bijection with the `Dart`s of `G`, and
`#Darts(G) = 2 · #E(G)` by `dart_card_eq_twice_card_edges`. -/
lemma homCount_completeGraph_fin_two_eq_two_mul_card_edgeFinset
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homCount (completeGraph (Fin 2)) G = 2 * #G.edgeFinset := by
  -- Build a bijection `(completeGraph (Fin 2) →g G) ≃ G.Dart`.
  unfold homCount
  rw [← G.dart_card_eq_twice_card_edges]
  -- Now: `Fintype.card (completeGraph (Fin 2) →g G) = Fintype.card G.Dart`.
  refine Fintype.card_congr ?_
  refine
    { toFun := fun f =>
        ⟨(f 0, f 1), f.map_adj (by decide : (completeGraph (Fin 2)).Adj 0 1)⟩
      invFun := fun d =>
        { toFun := fun i => if i = 0 then d.fst else d.snd
          map_rel' := fun {a b} hab => by
            -- `completeGraph (Fin 2)` adjacency means `a ≠ b`.
            simp only [completeGraph, top_adj] at hab
            -- `a, b ∈ Fin 2` with `a ≠ b` means `{a, b} = {0, 1}`.
            fin_cases a <;> fin_cases b
            · simp at hab
            · exact d.adj
            · exact d.adj.symm
            · simp at hab }
      left_inv := fun f => by
        ext i
        fin_cases i <;> simp
      right_inv := fun d => by
        cases d
        rfl }

end SidorenkoConjecture

namespace SidorenkoEvenCycle

open Finset SimpleGraph Matrix

section Main

variable {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]

/- Closed walks give homomorphisms from cycles. -/

/-- The vertices of a closed walk of length `N` form a homomorphism from `C_N`. -/
def closedWalkHom {N : ℕ} {u : W} (c : G.Walk u u) (hc : c.length = N) : cycleGraph N →g G where
  toFun i := c.getVert i
  map_rel' {i j} hij := by
    have step : ∀ a b : Fin N, ((b - a : Fin N) : ℕ) = 1 →
        G.Adj (c.getVert a) (c.getVert b) := by
      intro a b hab
      have ha := a.isLt
      have hb := b.isLt
      rcases le_or_gt a b with h | h
      · rw [Fin.coe_sub_iff_le.mpr h] at hab
        have := c.adj_getVert_succ (i := a) (by omega)
        rwa [show (a : ℕ) + 1 = b by omega] at this
      · rw [Fin.coe_sub_iff_lt.mpr h] at hab
        have := c.adj_getVert_succ (i := a) (by omega)
        rw [show (a : ℕ) + 1 = c.length by omega, c.getVert_length] at this
        have h0 : c.getVert b = u := by rw [show (b : ℕ) = 0 by omega, c.getVert_zero]
        rw [h0]
        exact this
    show G.Adj (c.getVert i) (c.getVert j)
    rcases cycleGraph_adj'.mp hij with h | h
    · exact (step j i h).symm
    · exact step i j h

omit [Fintype W] [DecidableEq W] [DecidableRel G.Adj] in
lemma closedWalkHom_apply {N : ℕ} {u : W} (c : G.Walk u u) (hc : c.length = N) (i : Fin N) :
    closedWalkHom G c hc i = c.getVert i := rfl

/-- Pairs of walks of length `k` with common ends. -/
abbrev WalkPairs (k : ℕ) : Type :=
  Σ u : W, Σ v : W, ({p : G.Walk u v | p.length = k} : Set (G.Walk u v)) ×
    ({p : G.Walk u v | p.length = k} : Set (G.Walk u v))

/-- Join two walks `u → v` of length `k` into a closed walk of length `2k`. -/
def joinPair {k : ℕ} (x : WalkPairs G k) : cycleGraph (2 * k) →g G :=
  closedWalkHom G (x.2.2.1.1.append x.2.2.2.1.reverse) (by
    have h1 : x.2.2.1.1.length = k := x.2.2.1.2
    have h2 : x.2.2.2.1.length = k := x.2.2.2.2
    rw [Walk.length_append, Walk.length_reverse, h1, h2]
    ring)

omit [Fintype W] [DecidableEq W] [DecidableRel G.Adj] in
lemma joinPair_injective {k : ℕ} (hk : 1 ≤ k) : Function.Injective (joinPair G (k := k)) := by
  rintro ⟨u, v, ⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨u', v', ⟨p', hp'⟩, ⟨q', hq'⟩⟩ h
  simp only [Set.mem_ofPred_eq] at hp hq hp' hq'
  have hf : ∀ i (hi : i < 2 * k), (p.append q.reverse).getVert i =
      (p'.append q'.reverse).getVert i := fun i hi =>
    congrArg (fun f : cycleGraph (2 * k) →g G => f ⟨i, hi⟩) h
  -- the first `k + 1` vertices are those of `p`
  have hfirst : ∀ i ≤ k, (p.append q.reverse).getVert i = p.getVert i := fun i hi => by
    rw [Walk.getVert_append', ite_eq_left (hp ▸ hi)]
  have hfirst' : ∀ i ≤ k, (p'.append q'.reverse).getVert i = p'.getVert i := fun i hi => by
    rw [Walk.getVert_append', ite_eq_left (hp' ▸ hi)]
  -- the last vertices are those of `q.reverse`
  have hlast : ∀ j, (p.append q.reverse).getVert (k + j) = q.reverse.getVert j := fun j => by
    rw [Walk.getVert_append, ite_eq_right (by omega), hp, Nat.add_sub_cancel_left]
  have hlast' : ∀ j, (p'.append q'.reverse).getVert (k + j) = q'.reverse.getVert j := fun j => by
    rw [Walk.getVert_append, ite_eq_right (by omega), hp', Nat.add_sub_cancel_left]
  have hu : u = u' := by
    have := hf 0 (by omega)
    rwa [Walk.getVert_zero, Walk.getVert_zero] at this
  subst hu
  have hv : v = v' := by
    have := hf k (by omega)
    rwa [hfirst k le_rfl, hfirst' k le_rfl, ← hp, Walk.getVert_length, hp, ← hp',
      Walk.getVert_length] at this
  subst hv
  have hpp : p = p' := Walk.ext_getVert_le_length (hp.trans hp'.symm) fun i hi => by
    rw [← hfirst i (hp ▸ hi), ← hfirst' i (hp ▸ hi)]
    exact hf i (by omega)
  have hqq : q.reverse = q'.reverse := by
    refine Walk.ext_getVert_le_length (by simp [hq, hq']) fun j hj => ?_
    rw [Walk.length_reverse, hq] at hj
    rcases hj.lt_or_eq with hj | hj
    · rw [← hlast j, ← hlast' j]
      exact hf (k + j) (by omega)
    · rw [Walk.getVert_of_length_le _ (by simp [hq, hj]),
        Walk.getVert_of_length_le _ (by simp [hq', hj])]
  have hqq' : q = q' := by simpa using congrArg Walk.reverse hqq
  subst hpp hqq'
  rfl

/-- `hom(C_{2k}, G) ≥ ∑_{u,v} (A^k)_{uv}^2`. -/
lemma sum_sq_le_homCount {k : ℕ} (hk : 1 ≤ k) :
    ∑ u, ∑ v, ((G.adjMatrix ℝ ^ k) u v) ^ 2 ≤ (homCount (cycleGraph (2 * k)) G : ℝ) := by
  have hcard : Fintype.card (WalkPairs G k) ≤ homCount (cycleGraph (2 * k)) G :=
    Fintype.card_le_of_injective _ (joinPair_injective G hk)
  have hsum : (Fintype.card (WalkPairs G k) : ℝ) = ∑ u, ∑ v, ((G.adjMatrix ℝ ^ k) u v) ^ 2 := by
    simp only [WalkPairs, Fintype.card_sigma, Fintype.card_prod, adjMatrix_pow_apply_eq_card_walk]
    push_cast
    simp only [sq]
  rw [← hsum]
  exact_mod_cast hcard

/- Walk vectors. -/

/-- `x_j = A^j 𝟙`: the number of walks of length `j` from each vertex. -/
noncomputable def walkVec (j : ℕ) : W → ℝ := (G.adjMatrix ℝ ^ j) *ᵥ 1

lemma walkVec_apply (j : ℕ) (u : W) : walkVec G j u = ∑ v, (G.adjMatrix ℝ ^ j) u v := by
  simp [walkVec, mulVec, dotProduct]

lemma pow_adjMatrix_transpose (j : ℕ) : (G.adjMatrix ℝ ^ j)ᵀ = G.adjMatrix ℝ ^ j := by
  rw [transpose_pow, transpose_adjMatrix]

/-- `x_a · x_b = 𝟙 · x_{a+b}`, since `A` is symmetric. -/
lemma walkVec_dot (a b : ℕ) : walkVec G a ⬝ᵥ walkVec G b = 1 ⬝ᵥ walkVec G (a + b) := by
  unfold walkVec
  rw [← pow_adjMatrix_transpose G a, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    ← pow_add]

omit [DecidableEq W] in
lemma dot_sq_le (x y : W → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  simpa only [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y

/-- `T_{j+1}^2 ≤ T_j T_{j+2}` for `T_j = ‖x_j‖^2`. -/
lemma logConvex (j : ℕ) :
    (walkVec G (j + 1) ⬝ᵥ walkVec G (j + 1)) ^ 2 ≤
      (walkVec G j ⬝ᵥ walkVec G j) * (walkVec G (j + 2) ⬝ᵥ walkVec G (j + 2)) := by
  have h : walkVec G (j + 1) ⬝ᵥ walkVec G (j + 1) = walkVec G j ⬝ᵥ walkVec G (j + 2) := by
    rw [walkVec_dot, walkVec_dot, show j + 1 + (j + 1) = j + (j + 2) by ring]
  rw [h]
  exact dot_sq_le _ _

omit [DecidableEq W] in
lemma dot_self_nonneg (x : W → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- `T_1^k T_0 ≤ T_0^k T_k` for `T_j = ‖x_j‖^2`. -/
lemma geom [Nonempty W] (k : ℕ) :
    (walkVec G 1 ⬝ᵥ walkVec G 1) ^ k * (walkVec G 0 ⬝ᵥ walkVec G 0) ≤
      (walkVec G 0 ⬝ᵥ walkVec G 0) ^ k * (walkVec G k ⬝ᵥ walkVec G k) := by
  set T : ℕ → ℝ := fun j => walkVec G j ⬝ᵥ walkVec G j with hTdef
  have hTnn : ∀ j, 0 ≤ T j := fun j => dot_self_nonneg _
  have hT0 : 0 < T 0 := by
    simp only [T, walkVec, pow_zero, one_mulVec, one_dotProduct_one]
    exact_mod_cast Fintype.card_pos
  have hlc : ∀ j, T (j + 1) ^ 2 ≤ T j * T (j + 2) := logConvex G
  show T 1 ^ k * T 0 ≤ T 0 ^ k * T k
  rcases (hTnn 1).eq_or_lt with h1 | h1
  · rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · rw [← h1, zero_pow hk.ne', zero_mul]
      exact mul_nonneg (pow_nonneg (hTnn 0) _) (hTnn k)
  have hratio : ∀ j, 0 < T j ∧ T 1 * T j ≤ T 0 * T (j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨hT0, (mul_comm _ _).le⟩
    | succ j ih =>
      obtain ⟨hpos, hle⟩ := ih
      have hpos' : 0 < T (j + 1) := by
        by_contra hcon
        have h0 : T (j + 1) = 0 := le_antisymm (not_lt.mp hcon) (hTnn _)
        rw [h0, mul_zero] at hle
        exact absurd hle (not_le.mpr (mul_pos h1 hpos))
      refine ⟨hpos', ?_⟩
      show T 1 * T (j + 1) ≤ T 0 * T (j + 2)
      have e1 : T 1 * T j * T (j + 1) ≤ T 0 * T (j + 1) * T (j + 1) :=
        mul_le_mul_of_nonneg_right hle (hTnn _)
      have e2 : T 0 * T (j + 1) ^ 2 ≤ T 0 * (T j * T (j + 2)) :=
        mul_le_mul_of_nonneg_left (hlc j) hT0.le
      have e3 : T 1 * T (j + 1) * T j ≤ T 0 * T (j + 2) * T j := by nlinarith
      exact le_of_mul_le_mul_right e3 hpos
  induction k with
  | zero => simp
  | succ k ih =>
    calc T 1 ^ (k + 1) * T 0 = T 1 * (T 1 ^ k * T 0) := by ring
      _ ≤ T 1 * (T 0 ^ k * T k) := mul_le_mul_of_nonneg_left ih h1.le
      _ = T 0 ^ k * (T 1 * T k) := by ring
      _ ≤ T 0 ^ k * (T 0 * T (k + 1)) :=
        mul_le_mul_of_nonneg_left (hratio k).2 (pow_nonneg (hTnn 0) _)
      _ = T 0 ^ (k + 1) * T (k + 1) := by ring

/-- `(2m/n)^{2k} ≤ hom(C_{2k}, G)`. -/
lemma even_cycle_main [Nonempty W] (k : ℕ) (hk : 1 ≤ k) :
    ((2 * #G.edgeFinset : ℝ) / Fintype.card W) ^ (2 * k) ≤
      (homCount (cycleGraph (2 * k)) G : ℝ) := by
  set n : ℝ := (Fintype.card W : ℝ) with hndef
  have hn : 0 < n := by
    rw [hndef]
    exact_mod_cast Fintype.card_pos
  set T : ℕ → ℝ := fun j => walkVec G j ⬝ᵥ walkVec G j with hTdef
  have hT0 : T 0 = n := by
    simp only [T, walkVec, pow_zero, one_mulVec, one_dotProduct_one, n]
  set s1 : ℝ := 1 ⬝ᵥ walkVec G 1 with hs1def
  have hs1 : s1 = 2 * #G.edgeFinset := by
    have hdeg : ∀ u, walkVec G 1 u = G.degree u := fun u => by
      simp [walkVec, adjMatrix_mulVec_apply]
    rw [hs1def, one_dotProduct]
    simp only [hdeg]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hCS1 : s1 ^ 2 ≤ n * T 1 := by
    have := dot_sq_le (1 : W → ℝ) (walkVec G 1)
    rwa [one_dotProduct_one] at this
  have hrow : T k ≤ n * ∑ u, ∑ v, ((G.adjMatrix ℝ ^ k) u v) ^ 2 := by
    simp only [T, dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [walkVec_apply, ← sq]
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset W))
      (f := fun v => (G.adjMatrix ℝ ^ k) u v)
    simpa [n] using this
  have hgeom : T 1 ^ k * n ≤ n ^ k * T k := by
    rw [← hT0]
    exact geom G k
  have hhom := sum_sq_le_homCount G hk
  have h1 : s1 ^ (2 * k) ≤ (n * T 1) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hCS1 k
  rw [← hs1, div_pow, div_le_iff₀ (by positivity)]
  refine le_of_mul_le_mul_right ?_ hn
  calc s1 ^ (2 * k) * n ≤ (n * T 1) ^ k * n := mul_le_mul_of_nonneg_right h1 hn.le
    _ = n ^ k * (T 1 ^ k * n) := by ring
    _ ≤ n ^ k * (n ^ k * T k) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ n ^ k * (n ^ k * (n * ∑ u, ∑ v, ((G.adjMatrix ℝ ^ k) u v) ^ 2)) := by gcongr
    _ ≤ n ^ k * (n ^ k * (n * (homCount (cycleGraph (2 * k)) G : ℝ))) := by gcongr
    _ = (homCount (cycleGraph (2 * k)) G : ℝ) * n ^ (2 * k) * n := by ring

end Main

/-- `C_N` has `N` edges for `N ≥ 3`. -/
lemma card_edgeFinset_cycleGraph (N : ℕ) (hN : 3 ≤ N) : #(cycleGraph N).edgeFinset = N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 3 := ⟨N - 3, by omega⟩
  have h := (cycleGraph (m + 3)).sum_degrees_eq_twice_card_edges
  simp only [cycleGraph_degree_three_le, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul] at h
  omega

/-- **Sidorenko's inequality for even cycles.** The exact statement of
`SidorenkoConjecture.sidorenko_conjecture.variants.even_cycle`. -/
theorem sidorenko_conjecture_variants_even_cycle (k : ℕ) (hk : 2 ≤ k)
    {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G := by
  rw [card_edgeFinset_cycleGraph (2 * k) (by omega), homDensity, homDensity,
    SidorenkoConjecture.homCount_completeGraph_fin_two_eq_two_mul_card_edgeFinset,
    Fintype.card_fin, Fintype.card_fin]
  have hn : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hmain := even_cycle_main G k (by omega)
  have e : ((2 * #G.edgeFinset : ℕ) : ℝ) / (Fintype.card W : ℝ) ^ 2 =
      ((2 * #G.edgeFinset : ℝ) / Fintype.card W) / Fintype.card W := by
    push_cast
    rw [div_div, sq]
  rw [e, div_pow]
  exact div_le_div_of_nonneg_right hmain (by positivity)

end SidorenkoEvenCycle

open Finset SimpleGraph

namespace SidorenkoConjecture

theorem sidorenko_conjecture.variants.even_cycle (k : ℕ) (hk : 2 ≤ k)
    {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G :=
  SidorenkoEvenCycle.sidorenko_conjecture_variants_even_cycle k hk G

end SidorenkoConjecture

end
