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
# Erdős Problem 766: the Dirac–Erdős bound

Every graph on $n$ vertices with $\lfloor n^2/4 \rfloor + 1$ edges contains, for each
$3 \le k \le n$, a graph on $k$ vertices with $\lfloor k^2/4 \rfloor + 1$ edges.

The definition `forcingNumber` is copied verbatim from `FormalConjectures/ErdosProblems/766.lean`
(Copyright 2026 The Formal Conjectures Authors, Apache 2.0) at upstream commit
`7bdc4a42f24c0316f81c73b26121794b2bed96a3`, in the namespace `Erdos766DE` instead of
`Erdos766`. The theorem `dirac_erdos` is the statement of `erdos_766.variants.dirac_erdos` there.

*Reference:* P. Erdős, "Extremal problems in graph theory", *Theory of Graphs and its
Applications* (Smolenice, 1963), 1964, 29--36, p. 34.

## Proof

Let `inside S` be the set of edges with both ends in `S`. Deleting a vertex of `S` keeps an
edge inside unless the vertex is one of its two ends, so
$\sum_{v \in S} e(S - v) = (|S| - 2)\, e(S)$ (`sum_card_inside_erase`). If $|S| = N \ge 4$ and
$e(S) \ge \lfloor N^2/4 \rfloor + 1$, then
$(N - 2)(\lfloor N^2/4 \rfloor + 1) > N \lfloor (N-1)^2/4 \rfloor$ (`key_ineq`), so some
$e(S - v) \ge \lfloor (N-1)^2/4 \rfloor + 1$. Repeat down to $k$ vertices, then keep exactly
$\lfloor k^2/4 \rfloor + 1$ of the edges.
-/

@[expose] public section

namespace Erdos766

open Finset
open scoped SimpleGraph

/-- $f(n;k,l)$ in the sense of [Er64c], where it is called $f_1(n;k,l)$: the least $m$ such that
every graph with $n$ vertices and $m$ edges contains at least one graph with $k$ vertices and
$l$ edges as a (not necessarily induced) subgraph. There is no graph with $n$ vertices and more
than $\binom{n}{2}$ edges, so the set is nonempty. -/
noncomputable def forcingNumber (n k l : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G}

/-- The arithmetic step: $N \lfloor (N-1)^2/4 \rfloor < (N - 2)(\lfloor N^2/4 \rfloor + 1)$ for
$N \ge 4$. -/
lemma key_ineq (N : ℕ) (hN : 4 ≤ N) : N * ((N - 1) ^ 2 / 4) < (N - 2) * (N ^ 2 / 4 + 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 4 := ⟨N - 4, by omega⟩
  rcases Nat.even_or_odd' M with ⟨a, rfl | rfl⟩
  · have h1 : (2 * a + 4 - 1) ^ 2 / 4 = a ^ 2 + 3 * a + 2 := by
      rw [show 2 * a + 4 - 1 = 2 * a + 3 by omega,
        show (2 * a + 3) ^ 2 = 1 + 4 * (a ^ 2 + 3 * a + 2) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
      simp
    have h2 : (2 * a + 4) ^ 2 / 4 = a ^ 2 + 4 * a + 4 := by
      rw [show (2 * a + 4) ^ 2 = 0 + 4 * (a ^ 2 + 4 * a + 4) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
      simp
    rw [h1, h2, show 2 * a + 4 - 2 = 2 * a + 2 by omega]
    nlinarith
  · have h1 : (2 * a + 1 + 4 - 1) ^ 2 / 4 = a ^ 2 + 4 * a + 4 := by
      rw [show 2 * a + 1 + 4 - 1 = 2 * a + 4 by omega,
        show (2 * a + 4) ^ 2 = 0 + 4 * (a ^ 2 + 4 * a + 4) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
      simp
    have h2 : (2 * a + 1 + 4) ^ 2 / 4 = a ^ 2 + 5 * a + 6 := by
      rw [show (2 * a + 1 + 4) ^ 2 = 1 + 4 * (a ^ 2 + 5 * a + 6) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
      simp
    rw [h1, h2, show 2 * a + 1 + 4 - 2 = 2 * a + 3 by omega]
    nlinarith

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The edges of `G` with both ends in `S`. -/
def inside (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  G.edgeFinset ∩ S.sym2

lemma inside_erase (S : Finset (Fin n)) (v : Fin n) :
    inside G (S.erase v) = (inside G S).filter fun e => v ∉ e := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    simp only [inside, mem_inter, mem_filter, mk_mem_sym2_iff, mem_erase, Sym2.mem_iff,
      ne_eq, not_or]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4, h5⟩
      exact ⟨⟨h1, h3, h5⟩, fun h => h2 h.symm, fun h => h4 h.symm⟩
    · rintro ⟨⟨h1, h3, h5⟩, h2, h4⟩
      exact ⟨h1, ⟨fun h => h2 h.symm, h3⟩, fun h => h4 h.symm, h5⟩

/-- Deleting each vertex of `S` in turn counts every inside edge `#S - 2` times. -/
lemma sum_card_inside_erase (S : Finset (Fin n)) :
    ∑ v ∈ S, #(inside G (S.erase v)) = (#S - 2) * #(inside G S) := by
  simp_rw [inside_erase, card_filter]
  rw [sum_comm, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun e he => ?_
  rw [← card_filter]
  induction e using Sym2.ind with
  | h x y =>
    simp only [inside, mem_inter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      mk_mem_sym2_iff] at he
    obtain ⟨hxy, hx, hy⟩ := he
    have hfilter : S.filter (fun v => v ∉ s(x, y)) = (S.erase x).erase y := by
      ext v
      simp only [mem_filter, mem_erase, Sym2.mem_iff, not_or, ne_eq]
      constructor
      · rintro ⟨hv, h1, h2⟩
        exact ⟨h2, h1, hv⟩
      · rintro ⟨h2, h1, hv⟩
        exact ⟨hv, h1, h2⟩
    have hy' : y ∈ S.erase x := mem_erase.mpr ⟨hxy.ne.symm, hy⟩
    rw [hfilter, card_erase_of_mem hy', card_erase_of_mem hx]
    omega

/-- One vertex can be deleted keeping more than a quarter of the square of the size. -/
lemma exists_dense_erase (S : Finset (Fin n)) (hS : 4 ≤ #S)
    (he : #S ^ 2 / 4 + 1 ≤ #(inside G S)) :
    ∃ v ∈ S, (#S - 1) ^ 2 / 4 + 1 ≤ #(inside G (S.erase v)) := by
  by_contra h
  push Not at h
  have hsum : ∑ v ∈ S, #(inside G (S.erase v)) ≤ #S * ((#S - 1) ^ 2 / 4) := by
    calc ∑ v ∈ S, #(inside G (S.erase v)) ≤ ∑ _v ∈ S, (#S - 1) ^ 2 / 4 :=
          sum_le_sum fun v hv => Nat.lt_succ_iff.mp (h v hv)
      _ = #S * ((#S - 1) ^ 2 / 4) := by rw [sum_const, smul_eq_mul]
  rw [sum_card_inside_erase] at hsum
  have h1 := key_ineq #S hS
  have h2 : (#S - 2) * (#S ^ 2 / 4 + 1) ≤ (#S - 2) * #(inside G S) := Nat.mul_le_mul_left _ he
  omega

/-- Iterated deletion down to `k` vertices. -/
lemma exists_dense_subset (k : ℕ) (hk : 3 ≤ k) : ∀ (d : ℕ) (S : Finset (Fin n)), #S = k + d →
    #S ^ 2 / 4 + 1 ≤ #(inside G S) → ∃ T ⊆ S, #T = k ∧ k ^ 2 / 4 + 1 ≤ #(inside G T)
  | 0, S, hS, he => ⟨S, subset_rfl, hS, by rw [hS] at he; simpa using he⟩
  | d + 1, S, hS, he => by
    obtain ⟨v, hv, hv'⟩ := exists_dense_erase G S (by omega) he
    have hcard : #(S.erase v) = k + d := by rw [card_erase_of_mem hv]; omega
    obtain ⟨T, hT, hTk, hTe⟩ := exists_dense_subset k hk d (S.erase v) hcard
      (by rw [card_erase_of_mem hv]; exact hv')
    exact ⟨T, hT.trans (erase_subset _ _), hTk, hTe⟩

/-- **Dirac and Erdős.** For `3 ≤ k ≤ n`, every graph on `n` vertices with `n ^ 2 / 4 + 1`
edges contains a graph on `k` vertices with `k ^ 2 / 4 + 1` edges. -/
theorem dirac_erdos (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
    forcingNumber n k (k ^ 2 / 4 + 1) ≤ n ^ 2 / 4 + 1 := by
  classical
  refine Nat.sInf_le fun G hG => ?_
  have hE : #G.edgeFinset = n ^ 2 / 4 + 1 := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, hG]
  have huniv : inside G univ = G.edgeFinset := by
    ext e
    simp [inside]
  obtain ⟨T, -, hTk, hTe⟩ := exists_dense_subset G k hk (n - k) univ
    (by rw [card_univ, Fintype.card_fin]; omega)
    (le_of_eq (by rw [card_univ, Fintype.card_fin, huniv, hE]))
  obtain ⟨F, hF, hFcard⟩ := exists_subset_card_eq hTe
  set φ := T.orderEmbOfFin hTk
  have hFG : ∀ x ∈ F, x ∈ G.edgeSet := fun x hx =>
    SimpleGraph.mem_edgeFinset.mp (mem_inter.mp (hF hx)).1
  let H : SimpleGraph (Fin k) := SimpleGraph.fromEdgeSet (Sym2.map φ ⁻¹' (F : Set (Sym2 (Fin n))))
  have hHedge : H.edgeSet = Sym2.map φ ⁻¹' (F : Set (Sym2 (Fin n))) := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [H, SimpleGraph.mem_edgeSet, SimpleGraph.fromEdgeSet_adj, Set.mem_preimage,
        Sym2.map_mk, mem_coe, and_iff_left_iff_imp]
      intro hab heq
      subst heq
      exact G.irrefl (hFG _ hab)
  refine ⟨H, ?_, ⟨⟨⟨φ, fun {a b} hab => ?_⟩, φ.injective⟩⟩⟩
  · rw [hHedge, Set.ncard_preimage_of_injective_subset_range (Sym2.map.injective φ.injective),
      Set.ncard_coe_finset, hFcard]
    intro x hx
    have hxT : x ∈ T.sym2 := (mem_inter.mp (hF hx)).2
    induction x using Sym2.ind with
    | h p q =>
      obtain ⟨hp, hq⟩ := mk_mem_sym2_iff.mp hxT
      have hrange : Set.range φ = (T : Set (Fin n)) := range_orderEmbOfFin T hTk
      obtain ⟨a, rfl⟩ : p ∈ Set.range φ := hrange ▸ mem_coe.mpr hp
      obtain ⟨b, rfl⟩ : q ∈ Set.range φ := hrange ▸ mem_coe.mpr hq
      exact ⟨s(a, b), Sym2.map_mk _ _ _⟩
  · have : s(a, b) ∈ H.edgeSet := hab
    rw [hHedge, Set.mem_preimage, Sym2.map_mk] at this
    exact hFG _ this

end Erdos766

namespace Erdos766

theorem erdos_766.variants.dirac_erdos (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
    forcingNumber n k (k ^ 2 / 4 + 1) ≤ n ^ 2 / 4 + 1 :=
  _root_.Erdos766.dirac_erdos n k hk hkn

end Erdos766

end
