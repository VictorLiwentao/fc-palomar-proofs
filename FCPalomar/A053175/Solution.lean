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

Author of the proof: Wentao Li. The definitions `a` and `hankelMatrix` and the statement of
`conjecture` are copied verbatim from `FormalConjectures/OEIS/53175.lean`
(The Formal Conjectures Authors).
-/
module

public import Mathlib
import all Init.Data.Nat.Power2.Basic

/-!
# OEIS A053175: Hankel determinants of the Catalan–Larcombe–French numbers

We prove `OeisA53175.conjecture`: for every $n$, $2^{n(n+3)}$ divides
$P(n) = \det[a(i+j)]_{0 \le i,j \le n}$, and $P(n)/2^{n(n+3)}$ is a positive odd integer.
This is Zhi-Wei Sun's conjecture (2013), proved by Zhu and Sun.

The proof follows Zhu–Sun in outline. Steps 4 and 5 use different arguments from theirs.

1. `a_eq`: $a(n) = 2^n D(n)$ with $D(n) = \sum_k \binom{n}{2k}\binom{2k}{k}^2 4^{n-2k}$.
   The recurrence for $D$ is proved by a creative-telescoping certificate. In particular the
   natural-number subtraction and division in `a` are exact.
2. `d_mod_eight`: $D(0) = 1$, $4 \mid D(m)$ for $m \ge 1$, and $8 \mid D(m)$ iff $m$ is not a
   power of two.
3. `det_hankelMatrix`: $P(n) = 2^{n(n+3)} \det N$ for an explicit integer matrix $N$.
4. `det_modTwoMatrix`: $\det N \equiv 1 \pmod 2$. Modulo $2$, the determinant counts the
   permutations $\sigma$ of $\{1,\dots,n\}$ with every $i + \sigma(i)$ a power of two, and
   there is exactly one (`eq_partner`).
5. `det_hankelD_nonneg`: $\det[D(i+j)] \ge 0$, since $D(m)$ is a moment of a discrete measure
   on the nodes $4 + 4\cos(2\pi l/N)\cos(2\pi l'/N)$, so the Hankel matrix is a Gram matrix.

*References:*
- [A053175](https://oeis.org/A053175)
- [ZS18] B.-X. Zhu and Z.-W. Sun, *Hankel-type determinants for some combinatorial sequences*,
  Int. J. Number Theory **14** (2018), 1265–1277, Theorem 1.2.
  [arXiv:1609.06810](https://arxiv.org/abs/1609.06810)
-/

@[expose] public section


open Finset
open scoped Matrix

namespace OeisA53175

/-- Catalan-Larcombe-French sequence. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 8
  | n + 2 =>
    let n' := n + 2
    let an1 := a (n + 1)
    let an2 := a n
    let term1 := 8 * (3 * n' ^ 2 - 3 * n' + 1) * an1
    let term2 := 128 * (n' - 1) ^ 2 * an2
    (term1 - term2) / (n' ^ 2)

/-- The $(n+1) \times (n+1)$ Hankel-type matrix with $(i,j)$-entry $a(i+j)$. -/
def hankelMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦ (a (i.val + j.val) : ℤ)

/-! ### The closed form $a(n) = 2^n D(n)$ -/

/-- $D(n) = \sum_k \binom{n}{2k}\binom{2k}{k}^2 4^{n-2k}$, so that $a(n) = 2^n D(n)$. -/
def d (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), n.choose (2 * k) * (2 * k).choose k ^ 2 * 4 ^ (n - 2 * k)

/-- Normalized summand $\binom{n}{2k}\binom{2k}{k}^2 / 16^k$. -/
noncomputable def summand (n k : ℕ) : ℚ :=
  (n.choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ) ^ 2 / 16 ^ k

/-- The telescoping certificate, normalized by $4^n$. -/
noncomputable def cert (n k : ℕ) : ℚ :=
  16 * (2 * k + 1) ^ 2 * ((n + 1).choose (2 * k + 1) : ℚ) * ((2 * k).choose k : ℚ) ^ 2 / 16 ^ k

/-- The recurrence operator applied to the normalized summand. -/
noncomputable def recTerm (n k : ℕ) : ℚ :=
  16 * (n + 2) ^ 2 * summand (n + 2) k - 16 * (3 * n ^ 2 + 9 * n + 7) * summand (n + 1) k +
    32 * (n + 1) ^ 2 * summand n k

lemma choose_succ_right_rat (n k : ℕ) :
    (n.choose (k + 1) : ℚ) * (k + 1) = (n.choose k : ℚ) * ((n : ℚ) - k) := by
  rcases le_or_gt k n with hk | hk
  · have := Nat.choose_succ_right_eq n k
    rw [← Nat.cast_sub hk]
    exact_mod_cast this
  · rw [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma add_one_choose_rat (n k : ℕ) :
    ((n + 1).choose (k + 1) : ℚ) * (k + 1) = (n.choose k : ℚ) * (n + 1) := by
  have := Nat.add_one_mul_choose_eq n k
  have h' : (((n + 1) * n.choose k : ℕ) : ℚ) = (((n + 1).choose (k + 1) * (k + 1) : ℕ) : ℚ) := by
    rw [this]
  push_cast at h'
  linarith

lemma centralBinom_succ_rat (k : ℕ) :
    ((2 * (k + 1)).choose (k + 1) : ℚ) * (k + 1) = 2 * (2 * k + 1) * ((2 * k).choose k : ℚ) := by
  have := Nat.succ_mul_centralBinom_succ k
  simp only [Nat.centralBinom] at this
  have h' : (((k + 1) * (2 * (k + 1)).choose (k + 1) : ℕ) : ℚ) =
      ((2 * (2 * k + 1) * (2 * k).choose k : ℕ) : ℚ) := by rw [this]
  push_cast at h'
  linarith

lemma recTerm_zero_add_cert_zero (n : ℕ) : recTerm n 0 + cert n 0 = 0 := by
  simp [recTerm, cert, summand]
  ring

lemma recTerm_succ_add_cert_succ (n k : ℕ) : recTerm n (k + 1) + cert n (k + 1) = cert n k := by
  set B : ℚ := (n.choose (2 * k) : ℚ)
  set c : ℚ := ((2 * k).choose k : ℚ)
  have e1 : ((n + 1).choose (2 * k + 1) : ℚ) = B * (n + 1) / (2 * k + 1) := by
    have := add_one_choose_rat n (2 * k)
    push_cast at this
    field_simp
    linarith
  have e2 : ((n + 2).choose (2 * k + 2) : ℚ) = ((n + 1).choose (2 * k + 1) : ℚ) * (n + 2) /
      (2 * k + 2) := by
    have := add_one_choose_rat (n + 1) (2 * k + 1)
    push_cast at this
    field_simp
    linarith
  have e3 : (n.choose (2 * k + 1) : ℚ) = B * ((n : ℚ) - 2 * k) / (2 * k + 1) := by
    have := choose_succ_right_rat n (2 * k)
    push_cast at this
    field_simp
    linarith
  have e4 : (n.choose (2 * k + 2) : ℚ) = (n.choose (2 * k + 1) : ℚ) * ((n : ℚ) - 2 * k - 1) /
      (2 * k + 2) := by
    have := choose_succ_right_rat n (2 * k + 1)
    push_cast at this
    field_simp
    linarith
  have e5 : ((n + 1).choose (2 * k + 2) : ℚ) = (n.choose (2 * k + 1) : ℚ) * (n + 1) /
      (2 * k + 2) := by
    have := add_one_choose_rat n (2 * k + 1)
    push_cast at this
    field_simp
    linarith
  have e6 : ((n + 1).choose (2 * k + 3) : ℚ) = (n.choose (2 * k + 2) : ℚ) * (n + 1) /
      (2 * k + 3) := by
    have := add_one_choose_rat n (2 * k + 2)
    push_cast at this
    field_simp
    linarith
  have e7 : ((2 * (k + 1)).choose (k + 1) : ℚ) = 2 * (2 * k + 1) * c / (k + 1) := by
    have := centralBinom_succ_rat k
    field_simp
    linarith
  have hk : 2 * (k + 1) = 2 * k + 2 := by ring
  have hk3 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
  simp only [recTerm, cert, summand]
  rw [hk3, e7, hk, e2, e5, e6, e4, e3, e1]
  push_cast
  field_simp
  ring

lemma sum_recTerm (n K : ℕ) : ∑ k ∈ range (K + 1), recTerm n k = - cert n K := by
  induction K with
  | zero => simp; linarith [recTerm_zero_add_cert_zero n]
  | succ K ih =>
    rw [sum_range_succ, ih]
    linarith [recTerm_succ_add_cert_succ n K]

lemma cert_eq_zero (n : ℕ) : cert n (n + 2) = 0 := by
  simp [cert, Nat.choose_eq_zero_of_lt (show n + 1 < 2 * (n + 2) + 1 by omega)]

lemma cast_d (m K : ℕ) (hK : m + 1 ≤ K) : (d m : ℚ) = 4 ^ m * ∑ k ∈ range K, summand m k := by
  have hsplit : ∑ k ∈ range K, summand m k = ∑ k ∈ range (m + 1), summand m k := by
    rw [← sum_range_add_sum_Ico _ hK]
    rw [sum_eq_zero (s := Ico (m + 1) K), add_zero]
    intro k hk
    rw [mem_Ico] at hk
    simp [summand, Nat.choose_eq_zero_of_lt (show m < 2 * k by omega)]
  rw [hsplit, d, mul_sum]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  rcases le_or_gt (2 * k) m with hk | hk
  · have : (4 : ℚ) ^ m = 4 ^ (m - 2 * k) * 16 ^ k := by
      rw [show (16 : ℚ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_add, Nat.sub_add_cancel hk]
    rw [this, summand]
    field_simp
  · simp [summand, Nat.choose_eq_zero_of_lt hk]

theorem d_recurrence (n : ℕ) :
    ((n + 2) ^ 2 * d (n + 2) + 32 * (n + 1) ^ 2 * d n : ℕ) =
      4 * (3 * n ^ 2 + 9 * n + 7) * d (n + 1) := by
  have h0 := cast_d n (n + 3) (by omega)
  have h1 := cast_d (n + 1) (n + 3) (by omega)
  have h2 := cast_d (n + 2) (n + 3) (by omega)
  have hT := sum_recTerm n (n + 2)
  rw [cert_eq_zero, neg_zero] at hT
  simp only [recTerm, sum_add_distrib, sum_sub_distrib, ← mul_sum] at hT
  have key : (((n + 2) ^ 2 * d (n + 2) + 32 * (n + 1) ^ 2 * d n : ℕ) : ℚ) =
      ((4 * (3 * n ^ 2 + 9 * n + 7) * d (n + 1) : ℕ) : ℚ) := by
    push_cast
    rw [h0, h1, h2]
    have : (4 : ℚ) ^ (n + 2) = 16 * 4 ^ n := by ring
    have h' : (4 : ℚ) ^ (n + 1) = 4 * 4 ^ n := by ring
    rw [this, h']
    linear_combination (4 : ℚ) ^ n * hT
  exact_mod_cast key

theorem d_zero : d 0 = 1 := by simp [d]

theorem d_one : d 1 = 4 := by simp [d, sum_range_succ]

theorem a_eq (n : ℕ) : a n = 2 ^ n * d n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [a, d_zero]
    | 1, _ => simp [a, d_one]
    | n + 2, ih =>
      rw [a]
      rw [ih (n + 1) (by omega), ih n (by omega)]
      have hs : 3 * (n + 2) ^ 2 - 3 * (n + 2) + 1 = 3 * n ^ 2 + 9 * n + 7 := by
        have : 3 * (n + 2) ^ 2 = (3 * n ^ 2 + 9 * n + 6) + 3 * (n + 2) := by ring
        rw [this, Nat.add_sub_cancel]
      have hs' : n + 2 - 1 = n + 1 := by omega
      rw [hs, hs']
      have hrec := d_recurrence n
      have hterm : 8 * (3 * n ^ 2 + 9 * n + 7) * (2 ^ (n + 1) * d (n + 1)) =
          (n + 2) ^ 2 * (2 ^ (n + 2) * d (n + 2)) + 128 * (n + 1) ^ 2 * (2 ^ n * d n) := by
        have : 8 * (3 * n ^ 2 + 9 * n + 7) * (2 ^ (n + 1) * d (n + 1)) =
            2 ^ n * 4 * (4 * (3 * n ^ 2 + 9 * n + 7) * d (n + 1)) := by ring
        rw [this, ← hrec]
        ring
      rw [hterm, Nat.add_sub_cancel]
      exact Nat.mul_div_cancel_left _ (by positivity)

/-! ### Powers of two -/

lemma isPowerOfTwo_two_mul_iff {q : ℕ} (hq : 0 < q) :
    (2 * q).isPowerOfTwo ↔ q.isPowerOfTwo := by
  constructor
  · rintro ⟨j, hj⟩
    rcases j with _ | j
    · omega
    · exact ⟨j, by rw [pow_succ] at hj; omega⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j + 1, by ring⟩

lemma isPowerOfTwo_two_mul_add_one_iff (q : ℕ) :
    (2 * q + 1).isPowerOfTwo ↔ q = 0 := by
  constructor
  · rintro ⟨j, hj⟩
    rcases j with _ | j
    · simpa using hj
    · rw [pow_succ] at hj; omega
  · rintro rfl
    exact Nat.isPowerOfTwo_one

/-! ### The 2-adic valuation of the central binomial coefficient -/

/-- The binary digit sum. -/
def digitSum (k : ℕ) : ℕ := (Nat.digits 2 k).sum

lemma digitSum_two_mul (k : ℕ) : digitSum (2 * k) = digitSum k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · rw [digitSum, Nat.digits_def' (by norm_num) (by omega)]
    simp [digitSum, Nat.mul_mod_right, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]

lemma digitSum_two_mul_add_one (k : ℕ) : digitSum (2 * k + 1) = digitSum k + 1 := by
  rw [digitSum, Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2, List.sum_cons, digitSum, add_comm]

lemma digitSum_pos_and_eq_one_iff (k : ℕ) (hk : 0 < k) :
    0 < digitSum k ∧ (digitSum k = 1 ↔ k.isPowerOfTwo) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' k
    · have hq : 0 < q := by omega
      obtain ⟨h1, h2⟩ := ih q (by omega) hq
      rw [digitSum_two_mul, isPowerOfTwo_two_mul_iff hq]
      exact ⟨h1, h2⟩
    · rw [digitSum_two_mul_add_one, isPowerOfTwo_two_mul_add_one_iff]
      refine ⟨by omega, ?_⟩
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp [digitSum]
      · have := (ih q (by omega) hq).1
        omega

lemma padicValNat_factorial_two (n : ℕ) : padicValNat 2 n.factorial = n - digitSum n := by
  have := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [digitSum] using this

lemma padicValNat_centralBinom (k : ℕ) :
    padicValNat 2 ((2 * k).choose k) = digitSum k := by
  have hfac : (2 * k).choose k * k.factorial * k.factorial = (2 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rwa [show 2 * k - k = k by omega] at this
  have hC : (2 * k).choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hF : k.factorial ≠ 0 := Nat.factorial_ne_zero k
  have hv := congrArg (padicValNat 2) hfac
  rw [padicValNat.mul (mul_ne_zero hC hF) hF, padicValNat.mul hC hF,
    padicValNat_factorial_two, padicValNat_factorial_two, digitSum_two_mul] at hv
  have hle : digitSum k ≤ k := Nat.digit_sum_le 2 k
  omega

lemma four_dvd_centralBinom_iff {k : ℕ} (hk : 0 < k) :
    4 ∣ (2 * k).choose k ↔ ¬ k.isPowerOfTwo := by
  have hC : (2 * k).choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat_dvd_iff_le hC, padicValNat_centralBinom]
  obtain ⟨h1, h2⟩ := digitSum_pos_and_eq_one_iff k hk
  rw [← h2]
  omega

lemma two_dvd_centralBinom {k : ℕ} (hk : 0 < k) : 2 ∣ (2 * k).choose k := by
  have := Nat.two_dvd_centralBinom_of_one_le hk
  rwa [Nat.centralBinom_eq_two_mul_choose] at this

/-! ### $D(m)$ modulo $8$ -/

lemma sixteen_dvd_term {m k : ℕ} (hm : 2 ≤ m) (hk : 2 * k ≠ m) :
    16 ∣ m.choose (2 * k) * (2 * k).choose k ^ 2 * 4 ^ (m - 2 * k) := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [mul_zero, Nat.choose_zero_right, one_mul, Nat.sub_zero, one_pow]
      exact (show 16 ∣ 4 ^ 2 by norm_num).trans (pow_dvd_pow 4 hm)
    · have h1 : 4 ∣ (2 * k).choose k ^ 2 := by
        have := pow_dvd_pow_of_dvd (two_dvd_centralBinom hk0) 2
        simpa using this
      have h2 : 4 ∣ 4 ^ (m - 2 * k) := dvd_pow_self 4 (by omega)
      have := mul_dvd_mul h1 h2
      rw [show (16 : ℕ) = 4 * 4 by norm_num, mul_assoc]
      exact Dvd.dvd.mul_left this _
  · simp [Nat.choose_eq_zero_of_lt hk]

theorem d_mod_eight {m : ℕ} (hm : 0 < m) : 4 ∣ d m ∧ (8 ∣ d m ↔ ¬ m.isPowerOfTwo) := by
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    rw [d_one]
    exact ⟨dvd_refl 4, by simp [Nat.isPowerOfTwo_one]⟩
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · -- even case: the middle term is $\binom{2j}{j}^2$
    have hj : 0 < j := by omega
    have hmem : j ∈ range (2 * j + 1) := mem_range.mpr (by omega)
    obtain ⟨X, hX⟩ : 16 ∣ ∑ k ∈ (range (2 * j + 1)).erase j,
        (2 * j).choose (2 * k) * (2 * k).choose k ^ 2 * 4 ^ (2 * j - 2 * k) := by
      refine dvd_sum fun k hk => sixteen_dvd_term hm2 ?_
      have := ne_of_mem_erase hk
      omega
    have hd : d (2 * j) = (2 * j).choose j ^ 2 + 16 * X := by
      rw [d, ← add_sum_erase _ _ hmem, hX]
      simp
    obtain ⟨u, hu⟩ := two_dvd_centralBinom hj
    have h4 := four_dvd_centralBinom_iff hj
    rw [isPowerOfTwo_two_mul_iff hj, hd, hu]
    rw [hu] at h4
    have hsq : (2 * u) ^ 2 = 4 * u ^ 2 := by ring
    rw [hsq]
    have hu2 : 2 ∣ u ^ 2 ↔ 2 ∣ u :=
      ⟨fun h => Nat.prime_two.dvd_of_dvd_pow h, fun h => dvd_pow h two_ne_zero⟩
    refine ⟨⟨u ^ 2 + 4 * X, by ring⟩, ?_⟩
    rw [← h4]
    constructor
    · intro h8
      have : 2 ∣ u ^ 2 := by omega
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mpr (hu2.mp this)
    · intro h
      have : 2 ∣ u := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h
      have := hu2.mpr this
      omega
  · -- odd case: every term is divisible by 16
    have h16 : 16 ∣ d (2 * j + 1) := by
      refine dvd_sum fun k _ => sixteen_dvd_term hm2 ?_
      omega
    rw [isPowerOfTwo_two_mul_add_one_iff]
    refine ⟨(show 4 ∣ 16 by norm_num).trans h16, ?_⟩
    simp only [show j ≠ 0 by omega, not_false_eq_true, iff_true]
    exact (show 8 ∣ 16 by norm_num).trans h16

/-- The Hankel matrix of $D$. -/
def hankelD (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j => (d (i + j) : ℤ)

/-! ### The unique perfect matching with power-of-two sums -/

/-- The partner of `I` in the unique perfect matching of `{1, …, N}` whose pair sums are
powers of two. The top block `[M - N, N]`, with `M = 2^(⌊log₂ N⌋ + 1)`, is paired by
`I ↦ M - I`; the rest is the matching of `{1, …, M - N - 1}`. -/
def partner (N I : ℕ) : ℕ :=
  if h : N = 0 then 0 else
    if 2 ^ (Nat.log 2 N + 1) - N ≤ I then 2 ^ (Nat.log 2 N + 1) - I
    else partner (2 ^ (Nat.log 2 N + 1) - N - 1) I
termination_by N
decreasing_by
  have h1 := Nat.pow_log_le_self 2 h
  rw [pow_succ]
  generalize 2 ^ Nat.log 2 N = P at *
  omega

lemma partner_of_ne_zero {N : ℕ} (hN : N ≠ 0) (I : ℕ) :
    partner N I = if 2 ^ (Nat.log 2 N + 1) - N ≤ I then 2 ^ (Nat.log 2 N + 1) - I
      else partner (2 ^ (Nat.log 2 N + 1) - N - 1) I := by
  rw [partner, dite_eq_right hN]

/-- A power of two strictly between `2^L` and `2^(L+2)` equals `2^(L+1)`. -/
lemma eq_of_isPowerOfTwo {L s : ℕ} (hs : s.isPowerOfTwo) (h1 : 2 ^ L < s)
    (h2 : s < 2 ^ (L + 2)) : s = 2 ^ (L + 1) := by
  obtain ⟨e, rfl⟩ := hs
  have he1 : L < e := by
    by_contra h
    exact absurd (Nat.pow_le_pow_right (by norm_num) (not_lt.mp h)) (not_le.mpr h1)
  have he2 : e < L + 2 := by
    by_contra h
    exact absurd (Nat.pow_le_pow_right (by norm_num) (not_lt.mp h)) (not_le.mpr h2)
  rw [show e = L + 1 by omega]

/-- In `{1, …, N}`, a pair with a power-of-two sum and an entry at least `2^⌊log₂ N⌋`
has sum `2^(⌊log₂ N⌋ + 1)`. -/
lemma sum_eq_top {N I J : ℕ} (hI : 1 ≤ I) (hJ : 1 ≤ J) (hIN : I ≤ N)
    (hJN : J ≤ N) (hbig : 2 ^ Nat.log 2 N ≤ I ∨ 2 ^ Nat.log 2 N ≤ J)
    (hp : (I + J).isPowerOfTwo) : I + J = 2 ^ (Nat.log 2 N + 1) := by
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  refine eq_of_isPowerOfTwo hp ?_ ?_
  · omega
  · rw [Nat.succ_eq_add_one, pow_succ] at h2
    rw [pow_succ, pow_succ]
    omega

theorem partner_spec (N : ℕ) : ∀ I, 1 ≤ I → I ≤ N →
    (1 ≤ partner N I ∧ partner N I ≤ N) ∧ partner N (partner N I) = I ∧
      (I + partner N I).isPowerOfTwo := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro I hI hIN
    have hN : N ≠ 0 := by omega
    have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
    rw [Nat.succ_eq_add_one] at hlt
    rw [partner_of_ne_zero hN I]
    split_ifs with hc
    · refine ⟨⟨by omega, by omega⟩, ?_, ⟨Nat.log 2 N + 1, by omega⟩⟩
      rw [partner_of_ne_zero hN, ite_eq_left (by omega)]
      omega
    · have hle := Nat.pow_log_le_self 2 hN
      have hN' : 2 ^ (Nat.log 2 N + 1) - N - 1 < N := by
        rw [pow_succ] at hlt ⊢
        omega
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ih _ hN' I hI (by omega)
      refine ⟨⟨h1, by omega⟩, ?_, h4⟩
      rw [partner_of_ne_zero hN, ite_eq_right (by omega), h3]

theorem eq_partner (N : ℕ) : ∀ σ : ℕ → ℕ,
    (∀ I, 1 ≤ I → I ≤ N → 1 ≤ σ I ∧ σ I ≤ N) →
    (∀ I J, 1 ≤ I → I ≤ N → 1 ≤ J → J ≤ N → σ I = σ J → I = J) →
    (∀ J, 1 ≤ J → J ≤ N → ∃ I, 1 ≤ I ∧ I ≤ N ∧ σ I = J) →
    (∀ I, 1 ≤ I → I ≤ N → (I + σ I).isPowerOfTwo) →
    ∀ I, 1 ≤ I → I ≤ N → σ I = partner N I := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro σ hb hinj hsurj hp I hI hIN
    have hN : N ≠ 0 := by omega
    have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
    rw [Nat.succ_eq_add_one] at hlt
    have hle := Nat.pow_log_le_self 2 hN
    set M := 2 ^ (Nat.log 2 N + 1) with hM
    have hMP : M = 2 * 2 ^ Nat.log 2 N := by rw [hM, pow_succ, mul_comm]
    -- the top block is forced
    have top : ∀ I, M - N ≤ I → I ≤ N → σ I = M - I := by
      intro I hI1 hI2
      rcases le_or_gt (2 ^ Nat.log 2 N) I with hbig | hsmall
      · have := sum_eq_top (by omega) (hb I (by omega) hI2).1 hI2 (hb I (by omega) hI2).2
          (Or.inl hbig) (hp I (by omega) hI2)
        omega
      · obtain ⟨I', hI'1, hI'2, hI'3⟩ := hsurj (M - I) (by omega) (by omega)
        have := sum_eq_top hI'1 (by omega) hI'2 (by omega) (Or.inr (by omega))
          (hI'3 ▸ hp I' hI'1 hI'2)
        have : I' = I := by omega
        subst this
        exact hI'3
    set N' := M - N - 1 with hN'
    have hN'lt : N' < N := by omega
    -- the rest stays in `{1, …, N'}`
    have low : ∀ I, 1 ≤ I → I ≤ N' → σ I ≤ N' := by
      intro I hI1 hI2
      by_contra hc
      have hσ := hb I hI1 (by omega)
      have h1 := top (M - σ I) (by omega) (by omega)
      have h2 : σ (M - σ I) = σ I := by omega
      have := hinj _ _ (by omega) (by omega) hI1 (by omega) h2
      omega
    have hrest := ih N' hN'lt σ
      (fun I h1 h2 => ⟨(hb I h1 (by omega)).1, low I h1 h2⟩)
      (fun I J h1 h2 h3 h4 => hinj I J h1 (by omega) h3 (by omega))
      (fun J h1 h2 => by
        obtain ⟨I, hI1, hI2, hI3⟩ := hsurj J h1 (by omega)
        refine ⟨I, hI1, ?_, hI3⟩
        by_contra hc
        have := top I (by omega) hI2
        omega)
      (fun I h1 h2 => hp I h1 (by omega))
    rw [partner_of_ne_zero hN I]
    split_ifs with hc
    · exact top I hc hIN
    · exact hrest I hI (by omega)

/-! ### The matrix modulo two -/

/-- The `(0,1)`-matrix `[i + j + 2 is a power of two]` on `Fin n`. -/
def powTwoMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if ((i : ℕ) + 1 + ((j : ℕ) + 1)).isPowerOfTwo then 1 else 0

/-- The matching as a permutation of `Fin n`. -/
def matchingPerm (n : ℕ) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm
    (fun i => ⟨partner n (i + 1) - 1, by
      have := (partner_spec n (i + 1) (by omega) i.isLt).1.2
      have := i.isLt
      omega⟩)
    (by
      intro i
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := partner_spec n (i + 1) (by omega) i.isLt
      ext
      simp only [Nat.sub_add_cancel h1, h3]
      omega)

lemma matchingPerm_val (n : ℕ) (i : Fin n) :
    ((matchingPerm n i : Fin n) : ℕ) = partner n (i + 1) - 1 := rfl

lemma eq_matchingPerm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, ((σ i : ℕ) + 1 + ((i : ℕ) + 1)).isPowerOfTwo) : σ = matchingPerm n := by
  let τ : ℕ → ℕ := fun I => if h : 1 ≤ I ∧ I ≤ n then (σ ⟨I - 1, by omega⟩ : ℕ) + 1 else 0
  have hτ : ∀ I (h : 1 ≤ I ∧ I ≤ n), τ I = (σ ⟨I - 1, by omega⟩ : ℕ) + 1 := fun I h => dite_eq_left h
  have key := eq_partner n τ
    (fun I h1 h2 => by
      rw [hτ I ⟨h1, h2⟩]
      have := (σ ⟨I - 1, by omega⟩).isLt
      omega)
    (fun I J h1 h2 h3 h4 hIJ => by
      rw [hτ I ⟨h1, h2⟩, hτ J ⟨h3, h4⟩] at hIJ
      have := σ.injective (Fin.ext (by omega) : σ ⟨I - 1, by omega⟩ = σ ⟨J - 1, by omega⟩)
      have := congrArg Fin.val this
      simp only at this
      omega)
    (fun J h1 h2 => by
      refine ⟨(σ.symm ⟨J - 1, by omega⟩ : ℕ) + 1, by omega, by omega, ?_⟩
      rw [hτ _ ⟨by omega, by omega⟩]
      simp only [Nat.add_sub_cancel, Fin.eta, Equiv.apply_symm_apply]
      omega)
    (fun I h1 h2 => by
      rw [hτ I ⟨h1, h2⟩]
      have := hσ ⟨I - 1, by omega⟩
      simp only at this
      rwa [Nat.sub_add_cancel h1, add_comm] at this)
  ext i
  have := key (i + 1) (by omega) (by omega)
  rw [hτ _ ⟨by omega, by omega⟩] at this
  simp only [Nat.add_sub_cancel, Fin.eta] at this
  rw [matchingPerm_val]
  omega

lemma matchingPerm_valid (n : ℕ) (i : Fin n) :
    ((matchingPerm n i : ℕ) + 1 + ((i : ℕ) + 1)).isPowerOfTwo := by
  obtain ⟨⟨h1, _⟩, _, h4⟩ := partner_spec n (i + 1) (by omega) (by omega)
  rw [matchingPerm_val, Nat.sub_add_cancel h1, add_comm]
  exact h4

lemma intCast_sign_zmod_two {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ZMod 2) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · simp
  · rfl

theorem det_powTwoMatrix (n : ℕ) : (powTwoMatrix n).det = 1 := by
  rw [Matrix.det_apply']
  rw [sum_eq_single (matchingPerm n)]
  · rw [intCast_sign_zmod_two, one_mul]
    simp only [powTwoMatrix, Matrix.of_apply]
    rw [Fintype.prod_boole, ite_eq_left (matchingPerm_valid n)]
  · intro σ _ hσ
    simp only [powTwoMatrix, Matrix.of_apply]
    rw [Fintype.prod_boole, ite_eq_right (fun h => hσ (eq_matchingPerm σ h)), mul_zero]
  · intro h
    exact absurd (mem_univ _) h

/-- The reduction modulo two of the normalized Hankel matrix. -/
def modTwoMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then 1 else if i = 0 ∨ j = 0 then 0
    else if ((i : ℕ) + j).isPowerOfTwo then 1 else 0

theorem det_modTwoMatrix (n : ℕ) : (modTwoMatrix n).det = 1 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hrest : ∀ j : Fin n, (-1 : ZMod 2) ^ ((j.succ : Fin (n + 1)) : ℕ) *
      modTwoMatrix n 0 j.succ *
      ((modTwoMatrix n).submatrix Fin.succ (j.succ).succAbove).det = 0 := by
    intro j
    simp [modTwoMatrix, Fin.succ_ne_zero]
  rw [sum_eq_zero fun j _ => hrest j, add_zero]
  have hsub : (modTwoMatrix n).submatrix Fin.succ (0 : Fin (n + 1)).succAbove = powTwoMatrix n := by
    ext i j
    simp [modTwoMatrix, powTwoMatrix, Fin.succ_ne_zero]
  rw [hsub, det_powTwoMatrix]
  simp [modTwoMatrix]

/-! ### $D(m)$ as a moment of a discrete measure -/

/-- $\mu_j = \binom{j}{j/2}^2$ for even $j$ and $0$ for odd $j$. -/
def mu (j : ℕ) : ℕ := if Even j then j.choose (j / 2) ^ 2 else 0

lemma sum_range_two_mul (g : ℕ → ℕ) (K : ℕ) :
    ∑ j ∈ range (2 * K), g j = ∑ k ∈ range K, (g (2 * k) + g (2 * k + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

lemma d_eq_moment (m : ℕ) :
    d m = ∑ j ∈ range (m + 1), m.choose j * 4 ^ (m - j) * mu j := by
  set g : ℕ → ℕ := fun j => m.choose j * 4 ^ (m - j) * mu j with hg
  have hext : ∑ j ∈ range (m + 1), g j = ∑ j ∈ range (2 * (m + 1)), g j := by
    rw [← sum_range_add_sum_Ico _ (show m + 1 ≤ 2 * (m + 1) by omega)]
    rw [sum_eq_zero (s := Ico (m + 1) (2 * (m + 1))), add_zero]
    intro j hj
    rw [mem_Ico] at hj
    simp [hg, Nat.choose_eq_zero_of_lt (show m < j by omega)]
  change d m = ∑ j ∈ range (m + 1), g j
  rw [hext, sum_range_two_mul, d]
  refine sum_congr rfl fun k _ => ?_
  have h1 : mu (2 * k) = (2 * k).choose k ^ 2 := by
    simp [mu, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  have h2 : mu (2 * k + 1) = 0 := by
    simp [mu]
  simp only [hg, h1, h2, mul_zero, add_zero]
  ring

/-! ### Power sums over roots of unity -/

/-- The node $2\cos(2\pi l/N)$. -/
noncomputable def node (N l : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * l / N)

lemma node_eq (N l : ℕ) :
    ((node N l : ℝ) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N) ^ l +
      (Complex.exp (2 * Real.pi * Complex.I / N) ^ l)⁻¹ := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg, node]
  push_cast
  rw [Complex.two_cos]
  congr 2 <;> ring

lemma geom_sum_root {N : ℕ} {q : ℂ} (hq : q ^ N = 1) :
    ∑ l ∈ range N, q ^ l = if q = 1 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · rw [geom_sum_eq h, hq, sub_self, zero_div]

lemma sum_node_pow {N j : ℕ} (hj : j < N) :
    ∑ l ∈ range N, node N l ^ j = if Even j then (N : ℝ) * (j.choose (j / 2) : ℝ) else 0 := by
  have hN : N ≠ 0 := by omega
  set ζ := Complex.exp (2 * Real.pi * Complex.I / N) with hζ
  have hprim : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN
  have hζ0 : ζ ≠ 0 := hprim.ne_zero hN
  apply Complex.ofReal_injective
  push_cast
  simp only [node_eq, ← hζ]
  have hterm : ∀ l a, (ζ ^ l) ^ a * ((ζ ^ l)⁻¹) ^ (j - a) * (j.choose a : ℂ) =
      (j.choose a : ℂ) * (ζ ^ a * (ζ ^ (j - a))⁻¹) ^ l := by
    intro l a
    rw [mul_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm l a,
      mul_comm l (j - a)]
    ring
  simp only [add_pow, hterm]
  rw [sum_comm]
  simp only [← mul_sum]
  have hgeom : ∀ a ∈ range (j + 1), ∑ l ∈ range N, (ζ ^ a * (ζ ^ (j - a))⁻¹) ^ l =
      if a = j - a then (N : ℂ) else 0 := by
    intro a ha
    rw [mem_range] at ha
    rw [geom_sum_root]
    · congr 1
      rw [mul_inv_eq_one₀ (pow_ne_zero _ hζ0)]
      exact propext ⟨fun h => hprim.pow_inj (by omega) (by omega) h, fun h => by rw [← h]⟩
    · rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm (j - a), pow_mul,
        pow_mul, hprim.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
  rw [sum_congr rfl fun a ha => by rw [hgeom a ha]]
  split_ifs with he
  · obtain ⟨r, rfl⟩ := he
    rw [sum_eq_single r]
    · rw [ite_eq_left (by omega), show (r + r) / 2 = r by omega]
      push_cast
      ring
    · intro b _ hb
      rw [ite_eq_right (by omega), mul_zero]
    · intro h
      exact absurd (mem_range.mpr (by omega)) h
  · refine sum_eq_zero fun a ha => ?_
    rw [ite_eq_right, mul_zero]
    intro h
    exact he ⟨a, by rw [mem_range] at ha; omega⟩

lemma sum_sum_node_pow {N j : ℕ} (hj : j < N) :
    ∑ l ∈ range N, ∑ l' ∈ range N, (node N l * node N l') ^ j = (N : ℝ) ^ 2 * (mu j : ℝ) := by
  simp only [mul_pow]
  rw [← sum_mul_sum, sum_node_pow hj, mu]
  split_ifs <;> push_cast <;> ring

lemma d_eq_sum_nodes {N m : ℕ} (hm : m < N) :
    (N : ℝ) ^ 2 * (d m : ℝ) = ∑ l ∈ range N, ∑ l' ∈ range N, (4 + node N l * node N l') ^ m := by
  simp only [add_comm (4 : ℝ), add_pow]
  rw [d_eq_moment]
  push_cast
  rw [mul_sum]
  simp only [sum_comm (s := range N) (t := range (m + 1))]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  simp only [← sum_mul]
  rw [sum_sum_node_pow (by omega)]
  ring

/-! ### The Hankel matrix of $D$ is positive semidefinite -/

theorem det_hankelD_nonneg (n : ℕ) : 0 ≤ (hankelD n).det := by
  set N := 2 * n + 1 with hN
  let A : Matrix (Fin N × Fin N) (Fin (n + 1)) ℝ :=
    Matrix.of fun p i => (4 + node N p.1 * node N p.2) ^ (i : ℕ) / N
  have hgram : (Int.castRingHom ℝ).mapMatrix (hankelD n) = Aᴴ * A := by
    ext i j
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_apply]
    simp only [hankelD, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eq_intCast,
      Int.cast_natCast, Matrix.transpose_apply, A]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have key : (N : ℝ) ^ 2 * (d (i + j) : ℝ) = ∑ x : Fin N, ∑ y : Fin N,
        (4 + node N x * node N y) ^ ((i : ℕ) + j) := by
      rw [d_eq_sum_nodes (by omega)]
      simp only [Finset.sum_range]
    rw [Fintype.sum_prod_type]
    have : ∀ x : ℝ, x ^ (i : ℕ) / N * (x ^ (j : ℕ) / N) = x ^ ((i : ℕ) + j) / N ^ 2 := by
      intro x
      rw [pow_add]
      ring
    simp only [this, ← sum_div]
    rw [← key]
    field_simp
  have hpsd : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have := hpsd.det_nonneg
  rw [← hgram, ← RingHom.map_det, eq_intCast] at this
  exact_mod_cast this

/-! ### Factoring out the power of two -/

/-- The weights $t_0 = 1$ and $t_i = 2$ for $i \ge 1$. -/
def weight (i : ℕ) : ℤ := if i = 0 then 1 else 2

/-- The entries of the normalized Hankel matrix. -/
def normEntry (i j : ℕ) : ℕ :=
  if i = 0 ∧ j = 0 then 1 else if i = 0 ∨ j = 0 then d (i + j) / 2 else d (i + j) / 4

/-- The normalized Hankel matrix. Its determinant is $P(n) / 2^{n(n+3)}$. -/
def normMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j => (normEntry i j : ℤ)

lemma weight_mul_normEntry (i j : ℕ) :
    weight i * normEntry i j * weight j = (d (i + j) : ℤ) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi <;> rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [weight, normEntry, d_zero]
  · obtain ⟨c, hc⟩ := (d_mod_eight hj).1
    simp only [weight, normEntry, hj.ne', zero_add, ite_true, true_and, true_or, ite_false]
    rw [hc]
    omega
  · obtain ⟨c, hc⟩ := (d_mod_eight hi).1
    simp only [weight, normEntry, hi.ne', add_zero, ite_true, and_true, or_true, ite_false]
    rw [hc]
    omega
  · obtain ⟨c, hc⟩ := (d_mod_eight (show 0 < i + j by omega)).1
    simp only [weight, normEntry, hi.ne', hj.ne', and_self, or_self, ite_false]
    rw [hc]
    omega

lemma hankelD_eq (n : ℕ) :
    hankelD n = Matrix.diagonal (fun i : Fin (n + 1) => weight i) * normMatrix n *
      Matrix.diagonal (fun i : Fin (n + 1) => weight i) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [hankelD, normMatrix, Matrix.of_apply]
  rw [weight_mul_normEntry]

lemma prod_weight (n : ℕ) : ∏ i : Fin (n + 1), weight i = 2 ^ n := by
  rw [Fin.prod_univ_succ]
  simp [weight]

lemma det_hankelD (n : ℕ) : (hankelD n).det = 4 ^ n * (normMatrix n).det := by
  rw [hankelD_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_weight,
    show (4 : ℤ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
  ring

lemma hankelMatrix_eq (n : ℕ) :
    hankelMatrix n = Matrix.diagonal (fun i : Fin (n + 1) => (2 : ℤ) ^ (i : ℕ)) * hankelD n *
      Matrix.diagonal (fun i : Fin (n + 1) => (2 : ℤ) ^ (i : ℕ)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [hankelMatrix, hankelD, Matrix.of_apply, a_eq]
  push_cast
  ring

lemma prod_two_pow_sq (n : ℕ) :
    (∏ i : Fin (n + 1), (2 : ℤ) ^ (i : ℕ)) ^ 2 = 2 ^ (n * (n + 1)) := by
  have hsum : ∑ i : Fin (n + 1), (i : ℕ) = ∑ i ∈ range (n + 1), i :=
    Fin.sum_univ_eq_sum_range (fun i => i) (n + 1)
  rw [prod_pow_eq_pow_sum, ← pow_mul, hsum, sum_range_id_mul_two, Nat.add_sub_cancel,
    mul_comm]

theorem det_hankelMatrix (n : ℕ) :
    (hankelMatrix n).det = 2 ^ (n * (n + 3)) * (normMatrix n).det := by
  rw [hankelMatrix_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_hankelD,
    show n * (n + 3) = n * (n + 1) + 2 * n by ring, pow_add, ← prod_two_pow_sq n, pow_mul]
  norm_num
  ring

/-! ### The normalized determinant is odd -/

lemma normMatrix_mod_two (n : ℕ) :
    (Int.castRingHom (ZMod 2)).mapMatrix (normMatrix n) = modTwoMatrix n := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, normMatrix, modTwoMatrix,
    Matrix.of_apply, eq_intCast, Int.cast_natCast, normEntry, Fin.ext_iff, Fin.val_zero]
  split_ifs with h1 h2 h3
  · simp
  · obtain ⟨c, hc⟩ := (d_mod_eight (show 0 < (i : ℕ) + j by omega)).1
    rw [ZMod.natCast_eq_zero_iff_even, hc]
    exact ⟨c, by omega⟩
  · obtain ⟨⟨c, hc⟩, h8⟩ := d_mod_eight (show 0 < (i : ℕ) + j by omega)
    have hn8 : ¬ 8 ∣ d (i + j) := fun h => h8.mp h h3
    rw [ZMod.natCast_eq_one_iff_odd, hc]
    rw [hc] at hn8
    exact ⟨c / 2, by omega⟩
  · obtain ⟨⟨c, hc⟩, h8⟩ := d_mod_eight (show 0 < (i : ℕ) + j by omega)
    have hy8 : 8 ∣ d (i + j) := h8.mpr h3
    rw [ZMod.natCast_eq_zero_iff_even, hc]
    rw [hc] at hy8
    exact ⟨c / 2, by omega⟩

theorem normMatrix_det_mod_two (n : ℕ) : (normMatrix n).det % 2 = 1 := by
  have h := RingHom.map_det (Int.castRingHom (ZMod 2)) (normMatrix n)
  rw [normMatrix_mod_two, det_modTwoMatrix, eq_intCast, ZMod.intCast_eq_one_iff_odd] at h
  exact Int.odd_iff.mp h

theorem normMatrix_det_nonneg (n : ℕ) : 0 ≤ (normMatrix n).det := by
  have h := det_hankelD_nonneg n
  rw [det_hankelD] at h
  by_contra hneg
  have : 4 ^ n * (normMatrix n).det < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (not_le.mp hneg)
  linarith

/-! ### The statement -/

/--
Conjecture: let $P(n)$ be the $(n+1) \times (n+1)$ Hankel-type determinant with $(i,j)$-entry
equal to $a(i+j)$ for all $i,j = 0, \ldots, n$. Then $P(n)/2^{n(n+3)}$ is a positive odd integer.
- Zhi-Wei Sun, Aug 14 2013

Proved by [ZS18], Theorem 1.2: $2^{-n(n+3)} |P_{i+j}|_{0 \le i,j \le n}$ is a positive odd
integer for every $n \in \mathbb{N}$, where $P_n$ are the Catalan-Larcombe-French numbers.
-/
theorem conjecture (n : ℕ) :
    let detP := (hankelMatrix n).det
    let pow2 := (2 : ℤ) ^ (n * (n + 3))
    pow2 ∣ detP ∧ 0 < detP / pow2 ∧ (detP / pow2) % 2 = 1 := by
  intro detP pow2
  have hdet : detP = pow2 * (normMatrix n).det := det_hankelMatrix n
  have hpow : pow2 ≠ 0 := by positivity
  have hq : detP / pow2 = (normMatrix n).det := by
    rw [hdet, Int.mul_ediv_cancel_left _ hpow]
  have hodd := normMatrix_det_mod_two n
  have hnonneg := normMatrix_det_nonneg n
  refine ⟨⟨(normMatrix n).det, hdet⟩, ?_, ?_⟩ <;> rw [hq]
  · omega
  · exact hodd
end OeisA53175

end
