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
# Turán's construction for `ex₃(n, K₄³)`

`Erdos500LB.lower_bound` proves `erdos_500.variants.lower_bound`
(`FormalConjectures/ErdosProblems/500.lean`): for every `ε > 0`, eventually
`(5/9 - ε) C(n, 3) ≤ ex₃(n, K₄³)`.

Turán's construction. Split `Fin n` into three parts by `v mod 3`. A triple is an edge if it
has one vertex in each part, or two vertices in part `i` and one in part `i + 1 (mod 3)`.

- *No `K₄³`.* Let `S` have `c_i` vertices in part `i` (`c₀ + c₁ + c₂ = 4`). If all four triples
  of `S` were edges, then for every part `i` that meets `S`, deleting a vertex of part `i` would
  leave an edge, so `c - e_i` would be an edge count vector. No `c` satisfies this (`omega`).
- *Edge count.* With parts of sizes `a₀, a₁, a₂ ≥ m = ⌊n/3⌋`, the four edge types give at least
  `a₀a₁a₂ + C(a₀,2)a₁ + C(a₁,2)a₂ + C(a₂,2)a₀ ≥ m³ + 3m C(m,2) = (5/2)m³ - (3/2)m²` edges (by
  injections from products). Since `C(n,3) ≤ n³/6 ≤ (3m + 2)³/6`, the bound holds once
  `m ≥ 3/ε`.

*Reference:* P. Turán (1941), see erdosproblems.com/500.

*Prior Lean:* `JSP000401.turan_lower_bound` by ketianzhang1-lang (Justin Sun Prize awards
PR #422, `ketianzhang1-lang/awards@aeccfffa`) proves a stronger all-`n` form, `5 C(n,3) ≤ 9 #E`,
by averaging over colourings, for its own `Valid` predicate. DeepMind PR #7045
(`500_finite.lean`) proves the `K₄³`-freeness of this construction. This file is written
independently and proves the upstream statement for `Hypergraph.cliqueExtremalNumber`.
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

namespace Erdos500LB

open Finset Filter

variable {n : ℕ}

/-- The part of a vertex. -/
def part (v : Fin n) : ℕ := v.val % 3

/-- The number of vertices of `T` in part `i`. -/
def cnt (T : Finset (Fin n)) (i : ℕ) : ℕ := (T.filter fun v => part v = i).card

/-- Count vectors of edges: one vertex in each part, or two in part `i` and one in part
`i + 1 (mod 3)`. -/
def EdgeVec (x y z : ℕ) : Prop :=
  (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = 2 ∧ y = 1) ∨ (y = 2 ∧ z = 1) ∨ (z = 2 ∧ x = 1)

instance (x y z : ℕ) : Decidable (EdgeVec x y z) :=
  inferInstanceAs (Decidable (_ ∨ _))

variable (n) in
/-- Turán's construction on `Fin n`. -/
def turan : Finset (Finset (Fin n)) :=
  (univ.powersetCard 3).filter fun T => EdgeVec (cnt T 0) (cnt T 1) (cnt T 2)

variable (n) in
/-- The vertices of part `i`. -/
def X (i : ℕ) : Finset (Fin n) := univ.filter fun v => part v = i

lemma mem_X {v : Fin n} {i : ℕ} : v ∈ X n i ↔ part v = i := by simp [X]

lemma part_lt (v : Fin n) : part v < 3 := Nat.mod_lt _ (by norm_num)

lemma mem_turan {T : Finset (Fin n)} :
    T ∈ turan n ↔ T.card = 3 ∧ EdgeVec (cnt T 0) (cnt T 1) (cnt T 2) := by
  simp [turan, mem_powersetCard]

lemma cnt_sum (T : Finset (Fin n)) : cnt T 0 + cnt T 1 + cnt T 2 = T.card := by
  rw [card_eq_sum_card_fiberwise (f := part) (t := range 3)
    fun v _ => mem_coe.2 (mem_range.2 (part_lt v))]
  simp [sum_range_succ, cnt]

lemma cnt_erase {T : Finset (Fin n)} {v : Fin n} (hv : v ∈ T) (i : ℕ) :
    cnt (T.erase v) i = cnt T i - if part v = i then 1 else 0 := by
  unfold cnt
  rw [filter_erase]
  split_ifs with h
  · rw [card_erase_of_mem (mem_filter.2 ⟨hv, h⟩)]
  · rw [erase_eq_of_notMem (show v ∉ T.filter (fun w => part w = i) from
      fun h' => h (mem_filter.1 h').2), Nat.sub_zero]

lemma cnt_insert {T : Finset (Fin n)} {y : Fin n} (hy : y ∉ T) (k : ℕ) :
    cnt (insert y T) k = cnt T k + if part y = k then 1 else 0 := by
  unfold cnt
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem fun h' => hy (mem_filter.1 h').1]
  · rw [add_zero]

lemma cnt_of_forall {P : Finset (Fin n)} {i : ℕ} (hP : ∀ v ∈ P, part v = i) (k : ℕ) :
    cnt P k = if i = k then P.card else 0 := by
  unfold cnt
  split_ifs with h
  · rw [filter_true_of_mem fun v hv => (hP v hv).trans h]
  · rw [filter_false_of_mem fun v hv h' => h ((hP v hv).symm.trans h'), card_empty]

/-! ### No `K₄³` -/

lemma turan_free : ¬ (turan n).ContainsCompleteHypergraph 3 4 := by
  rintro ⟨S, hS, hsub⟩
  have hsum := cnt_sum S
  have key : ∀ i, cnt S i = 0 ∨ EdgeVec (cnt S 0 - if i = 0 then 1 else 0)
      (cnt S 1 - if i = 1 then 1 else 0) (cnt S 2 - if i = 2 then 1 else 0) := by
    intro i
    rcases Nat.eq_zero_or_pos (cnt S i) with h0 | h1
    · exact Or.inl h0
    right
    obtain ⟨v, hv⟩ := card_pos.1 h1
    rw [mem_filter] at hv
    have hT : S.erase v ∈ turan n :=
      hsub (mem_powersetCard.2 ⟨erase_subset _ _, by rw [card_erase_of_mem hv.1, hS]⟩)
    have hE := (mem_turan.1 hT).2
    rw [cnt_erase hv.1, cnt_erase hv.1, cnt_erase hv.1, hv.2] at hE
    exact hE
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  norm_num [EdgeVec] at k0 k1 k2
  omega

/-! ### Counting edges -/

lemma card_triples_le :
    (X n 0 ×ˢ X n 1 ×ˢ X n 2).card ≤
      ((turan n).filter fun T => cnt T 0 = 1 ∧ cnt T 1 = 1 ∧ cnt T 2 = 1).card := by
  have filt : ∀ x y z : Fin n, part x = 0 → part y = 1 → part z = 2 →
      ({x, y, z} : Finset (Fin n)).filter (fun v => part v = 0) = {x} ∧
      ({x, y, z} : Finset (Fin n)).filter (fun v => part v = 1) = {y} ∧
      ({x, y, z} : Finset (Fin n)).filter (fun v => part v = 2) = {z} := by
    intro x y z hx hy hz
    refine ⟨?_, ?_, ?_⟩ <;> simp [filter_insert, filter_singleton, hx, hy, hz]
  refine card_le_card_of_injOn (fun p => ({p.1, p.2.1, p.2.2} : Finset (Fin n))) ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe, mem_X] at hp
    obtain ⟨hx, hy, hz⟩ := hp
    obtain ⟨f0, f1, f2⟩ := filt x y z hx hy hz
    have c0 : cnt ({x, y, z} : Finset (Fin n)) 0 = 1 := by rw [cnt, f0, card_singleton]
    have c1 : cnt ({x, y, z} : Finset (Fin n)) 1 = 1 := by rw [cnt, f1, card_singleton]
    have c2 : cnt ({x, y, z} : Finset (Fin n)) 2 = 1 := by rw [cnt, f2, card_singleton]
    have hc := cnt_sum ({x, y, z} : Finset (Fin n))
    refine mem_coe.2 ?_
    show ({x, y, z} : Finset (Fin n)) ∈ _
    exact mem_filter.2 ⟨mem_turan.2 ⟨by omega, Or.inl ⟨c0, c1, c2⟩⟩, c0, c1, c2⟩
  · rintro ⟨x, y, z⟩ hp ⟨x', y', z'⟩ hq h
    simp only [coe_product, Set.mem_prod, mem_coe, mem_X] at hp hq
    obtain ⟨f0, f1, f2⟩ := filt x y z hp.1 hp.2.1 hp.2.2
    obtain ⟨g0, g1, g2⟩ := filt x' y' z' hq.1 hq.2.1 hq.2.2
    have h' : ({x, y, z} : Finset (Fin n)) = {x', y', z'} := h
    rw [h', g0] at f0
    rw [h', g1] at f1
    rw [h', g2] at f2
    rw [singleton_inj.1 f0, singleton_inj.1 f1, singleton_inj.1 f2]

lemma card_pairs_le {i j : ℕ} (hij : i ≠ j)
    (hEV : EdgeVec ((if i = 0 then 2 else 0) + if j = 0 then 1 else 0)
      ((if i = 1 then 2 else 0) + if j = 1 then 1 else 0)
      ((if i = 2 then 2 else 0) + if j = 2 then 1 else 0)) :
    ((X n i).powersetCard 2 ×ˢ X n j).card ≤
      ((turan n).filter fun T => cnt T i = 2 ∧ cnt T j = 1).card := by
  have info : ∀ P : Finset (Fin n), ∀ y : Fin n, P ∈ (X n i).powersetCard 2 → part y = j →
      y ∉ P ∧ (∀ v ∈ P, part v = i) ∧ P.card = 2 := by
    intro P y hP hy
    rw [mem_powersetCard] at hP
    have hPi : ∀ v ∈ P, part v = i := fun v hv => mem_X.1 (hP.1 hv)
    exact ⟨fun h => hij ((hPi y h).symm.trans hy), hPi, hP.2⟩
  refine card_le_card_of_injOn (fun q => insert q.2 q.1) ?_ ?_
  · rintro ⟨P, y⟩ hq
    simp only [coe_product, Set.mem_prod, mem_coe, mem_X] at hq
    obtain ⟨hyP, hPi, hP2⟩ := info P y hq.1 hq.2
    have hc : ∀ k, cnt (insert y P) k = (if i = k then 2 else 0) + if j = k then 1 else 0 := by
      intro k
      rw [cnt_insert hyP, cnt_of_forall hPi, hP2, hq.2]
    refine mem_coe.2 ?_
    show insert y P ∈ _
    refine mem_filter.2 ⟨mem_turan.2 ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [card_insert_of_notMem hyP, hP2]
    · rw [hc, hc, hc]
      exact hEV
    · rw [hc]
      simp [hij.symm]
    · rw [hc]
      simp [hij]
  · rintro ⟨P, y⟩ hp ⟨P', y'⟩ hq h
    simp only [coe_product, Set.mem_prod, mem_coe, mem_X] at hp hq
    obtain ⟨hyP, hPi, -⟩ := info P y hp.1 hp.2
    obtain ⟨hyP', hPi', -⟩ := info P' y' hq.1 hq.2
    have h' : insert y P = insert y' P' := h
    have fi : ∀ (Q : Finset (Fin n)) (w : Fin n), (∀ v ∈ Q, part v = i) → part w = j →
        (insert w Q).filter (fun v => part v = i) = Q ∧
        (insert w Q).filter (fun v => part v = j) = {w} := by
      intro Q w hQ hw
      constructor
      · rw [filter_insert, ite_eq_right (show ¬ part w = i by rw [hw]; exact Ne.symm hij),
          filter_true_of_mem hQ]
      · rw [filter_insert, ite_eq_left hw, filter_false_of_mem
          (show ∀ v ∈ Q, ¬ part v = j from fun v hv h => hij ((hQ v hv).symm.trans h))]
        rfl
    have a := fi P y hPi hp.2
    have b := fi P' y' hPi' hq.2
    rw [h'] at a
    have hP : P = P' := a.1.symm.trans b.1
    have hy : y = y' := singleton_inj.1 (a.2.symm.trans b.2)
    rw [hP, hy]

lemma le_card_X (hn : 0 < n) {i : ℕ} (hi : i < 3) : n / 3 ≤ (X n i).card := by
  have h := le_card_of_inj_on_range (s := X n i) (n := n / 3)
    (fun k => (⟨(3 * k + i) % n, Nat.mod_lt _ hn⟩ : Fin n))
    (fun k hk => by
      rw [mem_X, part]
      simp only
      rw [Nat.mod_eq_of_lt (show 3 * k + i < n by omega)]
      omega)
    (fun a ha b hb h => by
      have := congrArg Fin.val h
      simp only at this
      rw [Nat.mod_eq_of_lt (show 3 * a + i < n by omega),
        Nat.mod_eq_of_lt (show 3 * b + i < n by omega)] at this
      omega)
  exact h

/-- Four pairwise disjoint filters of `s` have at most `#s` elements in total. -/
lemma card_four_filters_le {α : Type*} [DecidableEq α] {s : Finset α} (p₁ p₂ p₃ p₄ : α → Prop)
    [DecidablePred p₁] [DecidablePred p₂] [DecidablePred p₃] [DecidablePred p₄]
    (h12 : ∀ x, p₁ x → ¬ p₂ x) (h13 : ∀ x, p₁ x → ¬ p₃ x) (h14 : ∀ x, p₁ x → ¬ p₄ x)
    (h23 : ∀ x, p₂ x → ¬ p₃ x) (h24 : ∀ x, p₂ x → ¬ p₄ x) (h34 : ∀ x, p₃ x → ¬ p₄ x) :
    (s.filter p₁).card + (s.filter p₂).card + (s.filter p₃).card + (s.filter p₄).card ≤
      s.card := by
  have d2 : Disjoint (s.filter p₁) (s.filter p₂) := disjoint_filter.2 fun x _ => h12 x
  have d3 : Disjoint (s.filter p₁ ∪ s.filter p₂) (s.filter p₃) :=
    disjoint_union_left.2 ⟨disjoint_filter.2 fun x _ => h13 x, disjoint_filter.2 fun x _ => h23 x⟩
  have d4 : Disjoint (s.filter p₁ ∪ s.filter p₂ ∪ s.filter p₃) (s.filter p₄) :=
    disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨disjoint_filter.2 fun x _ => h14 x,
      disjoint_filter.2 fun x _ => h24 x⟩, disjoint_filter.2 fun x _ => h34 x⟩
  rw [← card_union_of_disjoint d2, ← card_union_of_disjoint d3, ← card_union_of_disjoint d4]
  exact card_le_card (union_subset (union_subset (union_subset (filter_subset _ _)
    (filter_subset _ _)) (filter_subset _ _)) (filter_subset _ _))

/-- Turán's construction has at least `m³ + 3m C(m, 2)` edges, `m = ⌊n/3⌋`. -/
lemma le_card_turan (hn : 0 < n) :
    (n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3)) ≤ (turan n).card := by
  have hA := card_triples_le (n := n)
  have hB0 := card_pairs_le (n := n) (i := 0) (j := 1) (by norm_num) (by decide)
  have hB1 := card_pairs_le (n := n) (i := 1) (j := 2) (by norm_num) (by decide)
  have hB2 := card_pairs_le (n := n) (i := 2) (j := 0) (by norm_num) (by decide)
  rw [card_product, card_product] at hA
  rw [card_product, card_powersetCard] at hB0 hB1 hB2
  have h4 := card_four_filters_le (s := turan n)
    (fun T => cnt T 0 = 1 ∧ cnt T 1 = 1 ∧ cnt T 2 = 1) (fun T => cnt T 0 = 2 ∧ cnt T 1 = 1)
    (fun T => cnt T 1 = 2 ∧ cnt T 2 = 1) (fun T => cnt T 2 = 2 ∧ cnt T 0 = 1)
    (by rintro T ⟨a, -, -⟩ ⟨b, -⟩; omega) (by rintro T ⟨-, a, -⟩ ⟨b, -⟩; omega)
    (by rintro T ⟨-, -, a⟩ ⟨b, -⟩; omega) (by rintro T ⟨-, a⟩ ⟨b, -⟩; omega)
    (by rintro T ⟨a, -⟩ ⟨-, b⟩; omega) (by rintro T ⟨-, a⟩ ⟨b, -⟩; omega)
  have h0 := le_card_X hn (i := 0) (by norm_num)
  have h1 := le_card_X hn (i := 1) (by norm_num)
  have h2 := le_card_X hn (i := 2) (by norm_num)
  have m3 := Nat.mul_le_mul h0 (Nat.mul_le_mul h1 h2)
  have p0 := Nat.mul_le_mul (Nat.choose_le_choose 2 h0) h1
  have p1 := Nat.mul_le_mul (Nat.choose_le_choose 2 h1) h2
  have p2 := Nat.mul_le_mul (Nat.choose_le_choose 2 h2) h0
  have e : (n / 3) ^ 3 = n / 3 * (n / 3 * (n / 3)) := by ring
  omega

/-- The extremal number is at least the size of Turán's construction. -/
lemma card_turan_le : (turan n).card ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply le_sup (f := Finset.card)
  simp only [mem_filter, mem_powerset]
  exact ⟨filter_subset _ _, turan_free⟩

/-! ### The asymptotic bound -/

/-- **Turán.** `ex₃(n, K₄³) ≥ (5/9 - ε) C(n, 3)` for all large `n`; this is the statement of
`Erdos500.erdos_500.variants.lower_bound`. -/
theorem lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  rw [eventually_atTop]
  refine ⟨3 * (⌈3 / ε⌉₊ + 1), fun n hn => ?_⟩
  have hm1 : ⌈3 / ε⌉₊ + 1 ≤ n / 3 := by omega
  have hn3 : n ≤ 3 * (n / 3) + 2 := by omega
  have hn0 : 0 < n := by omega
  have hE := (le_card_turan hn0).trans (card_turan_le (n := n))
  by_cases hε' : 5 / 9 ≤ ε
  · have : (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    exact this.trans (by positivity)
  push Not at hε'
  set m := n / 3
  have ht1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hmr : (3 / ε : ℝ) ≤ m := by
    have h1 := Nat.le_ceil (3 / ε)
    have h2 : ((⌈3 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm1
    push_cast at h2
    linarith
  have hεt : 3 ≤ ε * m := by
    have := (div_le_iff₀ hε).1 hmr
    linarith
  have hc : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by
    have := Nat.choose_le_pow_div (α := ℝ) 3 n
    norm_num [Nat.factorial] at this
    linarith
  have hnr : (n : ℝ) ≤ 3 * m + 2 := by exact_mod_cast hn3
  have hpow : (n : ℝ) ^ 3 ≤ (3 * m + 2) ^ 3 := pow_le_pow_left₀ (by positivity) hnr 3
  have hEr : (m : ℝ) ^ 3 + 3 * ((m : ℝ) * (m - 1) / 2 * m) ≤
      (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hE
    push_cast [Nat.cast_choose_two] at this
    linarith
  have h1 : 3 * (m : ℝ) ^ 2 ≤ ε * (m : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hεt (sq_nonneg (m : ℝ))]
  have key : (5 / 9 - ε) * ((3 * m + 2) ^ 3 / 6) ≤
      (m : ℝ) ^ 3 + 3 * ((m : ℝ) * (m - 1) / 2 * m) := by
    nlinarith [h1, ht1, hε, mul_nonneg hε.le (sq_nonneg (m : ℝ)),
      mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ m)]
  calc (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ (5 / 9 - ε) * ((3 * m + 2) ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ _ := key
    _ ≤ _ := hEr

end Erdos500LB

open Filter Asymptotics
open scoped Topology

namespace Erdos500

theorem erdos_500.variants.lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ Hypergraph.cliqueExtremalNumber n 3 4 :=
  Erdos500LB.lower_bound ε hε

end Erdos500

end
