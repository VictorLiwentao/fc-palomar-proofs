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

The section "Products of sequences" is adapted from `proofs/triplespow/Solution.lean` in
danielpuri1901/erdos-lean-formalization (commit `c838d73`; the file is identical at `cdf6b7b`).
That code is distributed under the following licence:

MIT License

Copyright (c) 2026 Daniel Puri

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
module

public import Mathlib

/-!
# Gowers–Long: powers of $F(n)$

Let $F(n)$ be the maximal length of a $2$-increasing sequence of triples with coordinates in
$\{1, \dots, n\}$. If $F(n) = n^{\alpha}$ for some $n > 1$, then $F(m) \ge m^{\beta}$ for every
$\beta < \alpha$ and all sufficiently large $m$.

The definitions `lt₂`, `IsIncreasing₂` and `maximalLength`, and the lemmas `not_lt₂`,
`not_lt₂_of_exists`, `isIncreasing₂_nil`, `isIncreasing₂_singleton` and `exists_pair_of_mem_Icc`,
are copied from `FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean` (Copyright 2025 The
Formal Conjectures Authors, Apache 2.0) at upstream commit
`7bdc4a42f24c0316f81c73b26121794b2bed96a3`, in the namespace `GowersLongPow` instead of
`Arxiv.«1609.08688»`, without the `category` and `AMS` attributes. The theorem
`maximalLength_pow_eventually` is the statement of the upstream theorem of the same name.

The section "Products of sequences" (`S` to `pow_le`) is adapted from Daniel Puri's MIT-licensed
proof of `maximalLength_pow` (see the licence notice above). The changes are the namespace, the
proof of `length_P`, and references to the local copies of the definitions.

*Reference:* W. T. Gowers and J. Long, "The length of an $s$-increasing sequence of $r$-tuples",
*Combin. Probab. Comput.* 30 (2021), 686--721, [arXiv:1609.08688](https://arxiv.org/abs/1609.08688).

## Proof

`maximalLength` is monotone (`maximalLength_mono`) and supermultiplicative (`prod_le`), so
$F(n)^j \le F(n^j)$ (`pow_le`). For $m \ge n^{J+1}$ let $j = \lfloor \log_n m \rfloor > J$, so
$n^j \le m < n^{j+1}$. For $\beta > 0$ and $J \ge \beta / (\alpha - \beta)$ this gives
$m^{\beta} \le n^{(j+1)\beta} \le n^{j\alpha} = F(n)^j \le F(n^j) \le F(m)$. For $\beta \le 0$,
$m^{\beta} \le 1 \le F(m)$.
-/

@[expose] public section

namespace Arxiv1609_08688

/--
Let $a = (a_1, a_2, a_3)$ and $b = (b_1, b_2, b_3)$ be two triples of integers.
Say that $a$ is $2$-less than $b$, or $a <_2 b$, if $a_i < b_i$ for at least
two coordinates $i$.
-/
def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

local infix:50 " <₂ " => lt₂

@[simp]
theorem not_lt₂ {α : Type*} [LinearOrder α] {a b : Fin 3 → α} :
    ¬a <₂ b ↔ ∀ i j, i ≠ j → a i < b i → b j ≤ a j := by simp [lt₂]

theorem not_lt₂_of_exists {α : Type*} [LinearOrder α] {a b : Fin 3 → α}
    (i j : Fin 3) (hij : i ≠ j) (hi : b i ≤ a i) (hj : b j ≤ a j) :
    ¬a <₂ b := by
  refine not_lt₂.2 fun k l hkl h => ?_
  have : k ≠ i := fun hk => not_lt.2 hi (hk ▸ h)
  have : k ≠ j := fun hk => not_lt.2 hj (hk ▸ h)
  have : l = i ∨ l = j := by omega
  rcases this with (rfl | rfl); exact hi; exact hj

/--
Since the $2$-less relation is not transitive, we make a further definition to
specify transivity.
-/
def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop := s.Pairwise lt₂

@[simp]
theorem isIncreasing₂_nil {α : Type*} [LT α] : IsIncreasing₂ (α := α) [] := by
  simp [IsIncreasing₂]

@[simp]
theorem isIncreasing₂_singleton {α : Type*} [LT α] (a : Fin 3 → α) : IsIncreasing₂ [a] := by
  simp [IsIncreasing₂]

/--
Let $F(n)$ be the maximal length of a $2$-increasing sequence of triples with each coordinate
belong to $[n]$ ($= \{1, 2, ..., n\}$).
-/
noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

/-- In a set of more than $n^2$ triples with coordinates from $\{1, ..., n\}$ we must
have two triples that are equal in their first two coordinates. -/
lemma exists_pair_of_mem_Icc {s : List (Fin 3 → ℕ)} {n : ℕ} (_hn : 2 ≤ n)
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : s.length > n ^ 2) :
    ∃ (i j : Fin s.length), i ≠ j ∧ s[i] 0 = s[j] 0 ∧ s[i] 1 = s[j] 1 := by
  classical
  let f : Fin s.length → ℕ × ℕ := fun k => (s[k] 0, s[k] 1)
  let t : Finset (ℕ × ℕ) := Finset.Icc 1 n ×ˢ Finset.Icc 1 n
  have ht_card : t.card < (Finset.univ : Finset (Fin s.length)).card := by
    simp only [t, Finset.card_univ, Fintype.card_fin, Finset.card_product,
      Nat.card_Icc, Nat.add_sub_cancel, ← sq]
    exact hs₂
  have hf : ∀ k ∈ (Finset.univ : Finset (Fin s.length)), f k ∈ t := by
    intro k _
    have hmem : s[k] ∈ s := List.getElem_mem k.isLt
    have h0 := hs₁ _ hmem ⟨0, rfl⟩
    have h1 := hs₁ _ hmem ⟨1, rfl⟩
    rw [Set.mem_Icc] at h0 h1
    simp only [t, f, Finset.mem_product, Finset.mem_Icc]
    exact ⟨h0, h1⟩
  obtain ⟨i, _, j, _, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to ht_card hf
  exact ⟨i, j, hij, congrArg Prod.fst hfij, congrArg Prod.snd hfij⟩

/-! ### Products of sequences -/

/-- The set whose supremum is `maximalLength n`. -/
def S (n : ℕ) : Set ℕ :=
  { List.length s | (s : List (Fin 3 → ℕ))
      (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

theorem F_eq (n : ℕ) : maximalLength n = sSup (S n) := rfl

theorem bdd {n : ℕ} (hn : 2 ≤ n) : BddAbove (S n) := by
  refine ⟨n ^ 2, ?_⟩
  rintro _ ⟨s, hs_range, hs_inc, rfl⟩
  by_contra hle
  have hs_length : n ^ 2 < s.length := Nat.lt_of_not_ge hle
  obtain ⟨i, j, hij, h0, h1⟩ := exists_pair_of_mem_Icc hn hs_range hs_length
  have hp : s.Pairwise lt₂ := hs_inc
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.ge h1.ge)
      (List.pairwise_iff_get.1 hp i j hij)
  · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.le h1.le)
      (List.pairwise_iff_get.1 hp j i hji)

theorem exists_max {n : ℕ} (hn : 2 ≤ n) :
    ∃ s : List (Fin 3 → ℕ), (∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) ∧ IsIncreasing₂ s ∧
      s.length = maximalLength n := by
  have hne : (S n).Nonempty := ⟨0, ⟨[], by simp, isIncreasing₂_nil, rfl⟩⟩
  have hmem := Nat.sSup_mem hne (bdd hn)
  rw [← F_eq] at hmem
  obtain ⟨s, h1, h2, h3⟩ := hmem
  exact ⟨s, h1, h2, h3⟩

/-- The combined triple. -/
def comb (b : ℕ) (x y : Fin 3 → ℕ) : Fin 3 → ℕ := fun k => (x k - 1) * b + y k

/-- The combined sequence. -/
def P (b : ℕ) (s t : List (Fin 3 → ℕ)) : List (Fin 3 → ℕ) :=
  s.flatMap fun x => t.map (comb b x)

theorem length_P (b : ℕ) (s t : List (Fin 3 → ℕ)) :
    (P b s t).length = s.length * t.length := by
  induction s with
  | nil => simp [P]
  | cons x s ih =>
    rw [P, List.flatMap_cons, List.length_append, List.length_map, ← P, ih, List.length_cons]
    ring

theorem entry_bounds {u v a b : ℕ} (hu1 : 1 ≤ u) (hua : u ≤ a) (hv1 : 1 ≤ v) (hvb : v ≤ b) :
    1 ≤ (u - 1) * b + v ∧ (u - 1) * b + v ≤ a * b := by
  obtain ⟨p, rfl⟩ : ∃ p, u = p + 1 := ⟨u - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : (p + 1) * b ≤ a * b := Nat.mul_le_mul_right _ hua
  constructor
  · omega
  · nlinarith

theorem range_P {a b : ℕ} {s t : List (Fin 3 → ℕ)}
    (hs : ∀ x ∈ s, Set.range x ⊆ Set.Icc 1 a) (ht : ∀ y ∈ t, Set.range y ⊆ Set.Icc 1 b) :
    ∀ c ∈ P b s t, Set.range c ⊆ Set.Icc 1 (a * b) := by
  intro c hc
  simp only [P, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨x, hx, y, hy, rfl⟩ := hc
  rintro _ ⟨k, rfl⟩
  have h1 := hs x hx ⟨k, rfl⟩
  have h2 := ht y hy ⟨k, rfl⟩
  rw [Set.mem_Icc] at h1 h2 ⊢
  exact entry_bounds h1.1 h1.2 h2.1 h2.2

theorem key {p q v v' b : ℕ} (hpq : p < q) (hv : v ≤ b) (hv' : 1 ≤ v') :
    p * b + v < q * b + v' := by
  have : (p + 1) * b ≤ q * b := Nat.mul_le_mul_right _ hpq
  nlinarith

theorem lt₂_same {b : ℕ} {x y y' : Fin 3 → ℕ} (h : lt₂ y y') :
    lt₂ (comb b x y) (comb b x y') := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  exact ⟨i, j, hij, by simp only [comb]; omega, by simp only [comb]; omega⟩

theorem lt₂_diff {a b : ℕ} {x x' y y' : Fin 3 → ℕ}
    (hx : Set.range x ⊆ Set.Icc 1 a) (hy : Set.range y ⊆ Set.Icc 1 b)
    (hy' : Set.range y' ⊆ Set.Icc 1 b) (h : lt₂ x x') :
    lt₂ (comb b x y) (comb b x' y') := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  have step : ∀ k, x k < x' k → comb b x y k < comb b x' y' k := by
    intro k hk
    have h1 := hx ⟨k, rfl⟩
    have h2 := hy ⟨k, rfl⟩
    have h3 := hy' ⟨k, rfl⟩
    rw [Set.mem_Icc] at h1 h2 h3
    exact key (by omega) h2.2 h3.1
  exact ⟨i, j, hij, step i hi, step j hj⟩

theorem pairwise_P {a b : ℕ} {s t : List (Fin 3 → ℕ)}
    (hs : ∀ x ∈ s, Set.range x ⊆ Set.Icc 1 a) (ht : ∀ y ∈ t, Set.range y ⊆ Set.Icc 1 b)
    (hsi : IsIncreasing₂ s) (hti : IsIncreasing₂ t) : IsIncreasing₂ (P b s t) := by
  unfold IsIncreasing₂ P
  rw [List.pairwise_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (show t.Pairwise lt₂ from hti).imp fun h => lt₂_same h
  · refine (show s.Pairwise lt₂ from hsi).imp_of_mem fun {x x'} hx _ hxx' => ?_
    intro c hc d hd
    simp only [List.mem_map] at hc hd
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨y', hy', rfl⟩ := hd
    exact lt₂_diff (hs x hx) (ht y hy) (ht y' hy') hxx'

theorem prod_le {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    maximalLength a * maximalLength b ≤ maximalLength (a * b) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_max ha
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_max hb
  have hab : 2 ≤ a * b := by nlinarith
  rw [← hs3, ← ht3, ← length_P b, F_eq]
  exact le_csSup (bdd hab) ⟨P b s t, range_P hs1 ht1, pairwise_P hs1 ht1 hs2 ht2, rfl⟩

theorem pow_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    maximalLength n ^ (k + 1) ≤ maximalLength (n ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 ≤ n ^ (k + 1) :=
      le_trans hn (Nat.le_self_pow (by omega) n)
    calc maximalLength n ^ (k + 1 + 1)
        = maximalLength n ^ (k + 1) * maximalLength n := pow_succ _ _
      _ ≤ maximalLength (n ^ (k + 1)) * maximalLength n := Nat.mul_le_mul_right _ ih
      _ ≤ maximalLength (n ^ (k + 1) * n) := prod_le h2 hn
      _ = maximalLength (n ^ (k + 1 + 1)) := by rw [← pow_succ]

/-! ### Monotonicity and the main theorem -/

/-- `maximalLength` is monotone. -/
theorem maximalLength_mono {a c : ℕ} (hc : 2 ≤ c) (hac : a ≤ c) :
    maximalLength a ≤ maximalLength c := by
  rw [F_eq, F_eq]
  refine csSup_le_csSup (bdd hc) ⟨0, ⟨[], by simp, isIncreasing₂_nil, rfl⟩⟩ ?_
  rintro _ ⟨s, hs, hsi, rfl⟩
  exact ⟨s, fun x hx => (hs x hx).trans (Set.Icc_subset_Icc le_rfl hac), hsi, rfl⟩

/-- A single triple is a $2$-increasing sequence. -/
theorem one_le_maximalLength {m : ℕ} (hm : 2 ≤ m) : 1 ≤ maximalLength m := by
  rw [F_eq]
  refine le_csSup (bdd hm) ⟨[fun _ => 1], ?_, isIncreasing₂_singleton _, rfl⟩
  intro a ha
  rw [List.mem_singleton] at ha
  subst ha
  rintro _ ⟨i, rfl⟩
  exact ⟨le_rfl, (by omega : 1 ≤ m)⟩

/-- **Gowers–Long.** If $F(n) = n^{\alpha}$ for some $n > 1$, then for every $\beta < \alpha$ we
have $F(m) \ge m^{\beta}$ for all sufficiently large $m$. -/
local notation "F" => maximalLength

theorem maximalLength_pow_eventually {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e)
    {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  rcases le_or_gt b 0 with hb0 | hb0
  · filter_upwards [Filter.eventually_ge_atTop 2] with m hm
    calc (m : ℝ) ^ b ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ m)) hb0
      _ ≤ (maximalLength m : ℝ) := by exact_mod_cast one_le_maximalLength hm
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
    have heb : 0 < e - b := by linarith
    filter_upwards [Filter.eventually_ge_atTop (n ^ (⌈b / (e - b)⌉₊ + 1))] with m hm
    have hm0 : m ≠ 0 := by
      have : 0 < n ^ (⌈b / (e - b)⌉₊ + 1) := pow_pos (by omega) _
      omega
    have hlow : n ^ Nat.log n m ≤ m := Nat.pow_log_le_self n hm0
    have hup : m < n ^ (Nat.log n m + 1) := Nat.lt_pow_succ_log_self hn m
    have hjJ : ⌈b / (e - b)⌉₊ + 1 ≤ Nat.log n m := Nat.le_log_of_pow_le hn hm
    obtain ⟨j, hj⟩ : ∃ j, Nat.log n m = j := ⟨_, rfl⟩
    rw [hj] at hlow hup hjJ
    have hexp : ((j : ℝ) + 1) * b ≤ j * e := by
      have hJ : b / (e - b) ≤ ⌈b / (e - b)⌉₊ := Nat.le_ceil _
      have hJj : ((⌈b / (e - b)⌉₊ : ℕ) : ℝ) ≤ j := by
        exact_mod_cast (by omega : ⌈b / (e - b)⌉₊ ≤ j)
      rw [div_le_iff₀ heb] at hJ
      nlinarith [mul_le_mul_of_nonneg_right hJj heb.le]
    have hF : ((maximalLength n : ℕ) : ℝ) ^ j ≤ (maximalLength m : ℝ) := by
      have h1 : maximalLength n ^ j ≤ maximalLength (n ^ j) := by
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        exact pow_le (by omega) k
      have h2 : 2 ≤ n ^ j := le_trans (by omega : 2 ≤ n) (Nat.le_self_pow (by omega) n)
      have h3 : maximalLength (n ^ j) ≤ maximalLength m := maximalLength_mono (by omega) hlow
      exact_mod_cast h1.trans h3
    calc (m : ℝ) ^ b ≤ ((n : ℝ) ^ (j + 1)) ^ b :=
          Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hup.le) hb0.le
      _ = (n : ℝ) ^ (((j : ℝ) + 1) * b) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn0, Nat.cast_add, Nat.cast_one]
      _ ≤ (n : ℝ) ^ ((j : ℝ) * e) := Real.rpow_le_rpow_of_exponent_le hn1 hexp
      _ = ((n : ℝ) ^ e) ^ j := by rw [mul_comm, Real.rpow_mul hn0, Real.rpow_natCast]
      _ = (maximalLength n : ℝ) ^ j := by rw [h]
      _ ≤ (maximalLength m : ℝ) := hF

end Arxiv1609_08688



end
