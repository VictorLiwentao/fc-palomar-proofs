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
# OEIS A190940: lcm of the partial sums of a composition

For $n \ge 1$, the number of distinct values of $\operatorname{lcm}(a, a+b, a+b+c, \dots, n)$,
where $(a, b, c, \dots)$ runs over the compositions of $n$, equals the number of divisors of
$\operatorname{lcm}(1, \dots, n)/n$.

The proof is Alekseyev's. Let $L = \operatorname{lcm}(1, \dots, n)$. Every value satisfies
$n \mid \operatorname{lcm}(\dots) \mid L$. Conversely, let $n \mid m \mid L$. Every prime power
$p^e$ exactly dividing $m$ divides $L$, so it divides some $k \le n$, and $p^e \le n$. So the
partial sums $\{g \le n : g \mid m\} \cup \{n\}$ have lcm $m$. A set $S \subseteq \{1,\dots,n\}$
with $n \in S$ is the set of partial sums of a composition.

*References:*
- [A190940](https://oeis.org/A190940): conjectured by Ridouane Oudra (Aug 24 2019), proved by
  Max Alekseyev (Nov 22 2024) in the entry.
-/

@[expose] public section

namespace OeisA190940

open Finset

/-- The partial sums of a composition: `c.sizeUpTo i` is the sum of the first `i` parts. -/
def partialSums {n : ℕ} (c : Composition n) : Finset ℕ :=
  (Finset.Icc 1 c.length).image c.sizeUpTo

/-- `lcm(a, a+b, …, n)` for the composition `c = (a, b, …)` of `n`. -/
def lcmPartialSums {n : ℕ} (c : Composition n) : ℕ :=
  (partialSums c).lcm id

/-- The sequence: the number of divisors of `lcm(1, …, n) / n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).lcm id / n).divisors.card

/-! ### Partial sums -/

lemma sizeUpTo_pos {n : ℕ} (c : Composition n) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ c.length) :
    0 < c.sizeUpTo i := by
  have := c.sizeUpTo_strict_mono (i := i - 1) (by omega)
  rw [Nat.sub_add_cancel h1] at this
  omega

lemma partialSums_subset {n : ℕ} (c : Composition n) : partialSums c ⊆ Icc 1 n := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  rw [mem_Icc] at hi ⊢
  exact ⟨sizeUpTo_pos c hi.1 hi.2, c.sizeUpTo_le i⟩

lemma mem_partialSums {n : ℕ} (hn : 1 ≤ n) (c : Composition n) : n ∈ partialSums c := by
  have hl := c.length_pos_of_pos hn
  exact mem_image.mpr ⟨c.length, mem_Icc.mpr ⟨hl, le_rfl⟩, c.sizeUpTo_length⟩

/-- The partial sums are the nonzero boundaries. -/
lemma partialSums_eq_boundaries {n : ℕ} (c : Composition n) :
    partialSums c = (c.boundaries.filter (· ≠ 0)).image Fin.val := by
  ext x
  simp only [partialSums, mem_image, mem_Icc, mem_filter, Composition.boundaries, mem_map,
    mem_univ, true_and]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
    refine ⟨c.boundary ⟨i, by omega⟩, ⟨⟨⟨i, by omega⟩, rfl⟩, ?_⟩, rfl⟩
    rw [Ne, Fin.ext_iff]
    exact (sizeUpTo_pos c h1 h2).ne'
  · rintro ⟨b, ⟨⟨j, rfl⟩, hj⟩, rfl⟩
    refine ⟨j, ⟨?_, by omega⟩, rfl⟩
    by_contra h
    apply hj
    rw [Fin.ext_iff]
    change c.sizeUpTo j = 0
    rw [show (j : ℕ) = 0 by omega, c.sizeUpTo_zero]

/-- Every `S ⊆ {1, …, n}` with `n ∈ S` is the set of partial sums of a composition. -/
lemma exists_partialSums_eq {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 n) (hnS : n ∈ S) :
    ∃ c : Composition n, partialSums c = S := by
  classical
  let B : Finset (Fin (n + 1)) := insert 0 (univ.filter fun i : Fin (n + 1) => (i : ℕ) ∈ S)
  let cs : CompositionAsSet n := ⟨B, by simp [B], by simp [B, hnS]⟩
  refine ⟨cs.toComposition, ?_⟩
  rw [partialSums_eq_boundaries, CompositionAsSet.toComposition_boundaries]
  ext x
  simp only [cs, B, mem_image, mem_filter, mem_insert, mem_univ, true_and]
  constructor
  · rintro ⟨b, ⟨hb, hb0⟩, rfl⟩
    rcases hb with rfl | hb
    · exact absurd rfl hb0
    · exact hb
  · intro hx
    have := mem_Icc.mp (hS hx)
    refine ⟨⟨x, by omega⟩, ⟨Or.inr hx, ?_⟩, rfl⟩
    rw [Ne, Fin.ext_iff]
    simp only [Fin.val_zero]
    omega

/-! ### The lcm of `1, …, n` -/

lemma lcm_ne_zero_of_pos {s : Finset ℕ} (hs : ∀ x ∈ s, x ≠ 0) : s.lcm id ≠ 0 := by
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨x, hx, h⟩
  exact hs x hx h

/-- A prime power dividing an lcm divides one of the terms. -/
lemma exists_mem_pow_dvd {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ∀ s : Finset ℕ, (∀ x ∈ s, x ≠ 0) → p ^ e ∣ s.lcm id → ∃ k ∈ s, p ^ e ∣ k := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ h
    rw [Finset.lcm_empty, Nat.dvd_one, Nat.pow_eq_one] at h
    rcases h with h | h
    · exact absurd h hp.one_lt.ne'
    · omega
  | insert b s hb ih =>
    intro hs h
    rw [Finset.lcm_insert] at h
    have hb0 : b ≠ 0 := hs b (mem_insert_self b s)
    have hs0 : s.lcm id ≠ 0 := lcm_ne_zero_of_pos fun x hx => hs x (mem_insert_of_mem hx)
    change p ^ e ∣ Nat.lcm b (s.lcm id) at h
    rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hb0 hs0),
      Nat.factorization_lcm hb0 hs0, Finsupp.sup_apply] at h
    rcases le_max_iff.mp h with h | h
    · exact ⟨b, mem_insert_self b s, (hp.pow_dvd_iff_le_factorization hb0).mpr h⟩
    · obtain ⟨k, hk, hdvd⟩ := ih (fun x hx => hs x (mem_insert_of_mem hx))
        ((hp.pow_dvd_iff_le_factorization hs0).mpr h)
      exact ⟨k, mem_insert_of_mem hk, hdvd⟩

/-- For `n ∣ m ∣ lcm(1, …, n)`, the divisors of `m` up to `n`, together with `n`, have
lcm `m`. -/
lemma lcm_divisors_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ∣ m) (hmL : m ∣ (Icc 1 n).lcm id) :
    (insert n ((Icc 1 n).filter (· ∣ m))).lcm id = m := by
  have hL : (Icc 1 n).lcm id ≠ 0 := lcm_ne_zero_of_pos fun x hx => by
    have := mem_Icc.mp hx
    omega
  have hm : m ≠ 0 := fun h => hL (Nat.eq_zero_of_zero_dvd (h ▸ hmL))
  have hS0 : (insert n ((Icc 1 n).filter (· ∣ m))).lcm id ≠ 0 := lcm_ne_zero_of_pos fun x hx => by
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · have := mem_Icc.mp (mem_filter.mp hx).1
      omega
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd fun x hx => ?_
    rcases mem_insert.mp hx with rfl | hx
    · exact hnm
    · exact (mem_filter.mp hx).2
  · refine (Nat.factorization_prime_le_iff_dvd hm hS0).mp fun p hp => ?_
    rcases Nat.eq_zero_or_pos (m.factorization p) with h0 | he
    · rw [h0]
      exact Nat.zero_le _
    have hpm : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
    obtain ⟨k, hk, hdvd⟩ := exists_mem_pow_dvd hp he (Icc 1 n)
      (fun x hx => by have := mem_Icc.mp hx; omega) (hpm.trans hmL)
    have hk' := mem_Icc.mp hk
    have hle : p ^ m.factorization p ≤ n := (Nat.le_of_dvd (by omega) hdvd).trans hk'.2
    have hmem : p ^ m.factorization p ∈ insert n ((Icc 1 n).filter (· ∣ m)) :=
      mem_insert_of_mem (mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, hle⟩, hpm⟩)
    exact (hp.pow_dvd_iff_le_factorization hS0).mp (Finset.dvd_lcm (f := id) hmem)

/-! ### The theorem -/

/-- The set of values is the set of multiples of `n` dividing `lcm(1, …, n)`. -/
lemma image_lcmPartialSums {n : ℕ} (hn : 1 ≤ n) :
    univ.image (lcmPartialSums (n := n)) =
      ((Icc 1 n).lcm id / n).divisors.image (· * n) := by
  set L := (Icc 1 n).lcm id with hLdef
  have hL : L ≠ 0 := lcm_ne_zero_of_pos fun x hx => by
    have := mem_Icc.mp hx
    omega
  have hnL : n ∣ L := Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨hn, le_rfl⟩)
  ext m
  simp only [mem_image, mem_univ, true_and, Nat.mem_divisors]
  constructor
  · rintro ⟨c, rfl⟩
    have hnm : n ∣ lcmPartialSums c := Finset.dvd_lcm (f := id) (mem_partialSums hn c)
    have hmL : lcmPartialSums c ∣ L :=
      Finset.lcm_dvd fun x hx => Finset.dvd_lcm (f := id) (partialSums_subset c hx)
    refine ⟨lcmPartialSums c / n, ⟨Nat.div_dvd_div hnm hmL, ?_⟩, Nat.div_mul_cancel hnm⟩
    intro h
    rw [Nat.div_eq_zero_iff_lt (by omega)] at h
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hnL) (not_le.mpr h)
  · rintro ⟨d, ⟨hd, -⟩, rfl⟩
    have hmL : d * n ∣ L := by
      have := Nat.mul_dvd_mul_right hd n
      rwa [Nat.div_mul_cancel hnL] at this
    have hS : insert n ((Icc 1 n).filter (· ∣ d * n)) ⊆ Icc 1 n := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_Icc.mpr ⟨hn, le_rfl⟩
      · exact (mem_filter.mp hx).1
    obtain ⟨c, hc⟩ := exists_partialSums_eq hS (mem_insert_self _ _)
    refine ⟨c, ?_⟩
    rw [lcmPartialSums, hc]
    exact lcm_divisors_le hn (dvd_mul_left n d) hmL

/-- **OEIS A190940** (Oudra's conjecture, proved by Alekseyev): for `n ≥ 1`, the number of
distinct values of `lcm(a, a+b, …, n)` over the compositions `(a, b, …)` of `n` is the number
of divisors of `lcm(1, …, n) / n`. -/
theorem a190940 (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.image (lcmPartialSums (n := n))).card = a n := by
  rw [image_lcmPartialSums hn, a]
  exact card_image_of_injective _ fun x y h => Nat.eq_of_mul_eq_mul_right hn h

end OeisA190940

namespace OeisA190940

open Finset

theorem card_lcmPartialSums :
    ∀ n : ℕ, 1 ≤ n → (Finset.univ.image (lcmPartialSums (n := n))).card = a n :=
  a190940

end OeisA190940

end
