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
# Catalan numbers divisible by $3$ (OEIS A265100)

Let $C(n)$ be the $n$-th Catalan number. Then $3 \mid C(n)$ if and only if the base-$3$
representations of $n$ and $n + 1$ both contain the digit $2$ (Conjecture 5 of A265100). A block
number is an $n \ge 1$ with $3 \mid C(n)$ and $3 \nmid C(n - 1)$. The block numbers are exactly
the numbers $9m + 5$ where $m$ has no base-$3$ digit $2$, that is, the terms of A265100
(Conjecture 1 and its converse). Conjectures 2 and 3 follow.

Proof: write $S(n)$ for the base-$3$ digit sum. Legendre's formula gives
$2 v_3(C(n)) = S(n) + S(n + 1) - S(2n) - 1$. This quantity satisfies a recursion in the last
base-$3$ digit of $n$, which gives the digit criterion.

*References:*
- L. Edson Jeffery, [A265100](https://oeis.org/A265100), December 1, 2015.
- Robert Israel, A000108(n) == 1 (mod 6), Sequence Fans Mailing List, December 2015 (proof of
  Conjecture 5).
-/

@[expose] public section

namespace OeisA265100

/-- A005836 with offset 1: the `i`-th number whose base-3 expansion has no digit 2. -/
noncomputable def A005836 (i : ℕ) : ℕ := Nat.nth (fun m => ∀ k : ℕ, m / 3 ^ k % 3 ≠ 2) (i - 1)

/-- A265100 with offset 1: $a(n) = 9\,\mathrm{A005836}(n) + 5$. -/
noncomputable def a (n : ℕ) : ℕ := 9 * A005836 n + 5

/-- A block number: $n \ge 1$ with $C(n) \equiv 0$ and $C(n - 1) \not\equiv 0 \pmod 3$. -/
def IsBlockNumber (n : ℕ) : Prop := 1 ≤ n ∧ catalan n % 3 = 0 ∧ catalan (n - 1) % 3 ≠ 0

end OeisA265100

namespace OeisA265100Proof

open Nat

/-- The base-$3$ digit sum of `n`, as an integer. -/
def S (n : ℕ) : ℤ := ((Nat.digits 3 n).sum : ℤ)

lemma S_eq (n : ℕ) : S n = (n % 3 : ℕ) + S (n / 3) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [S]
  · simp only [S]
    rw [Nat.digits_def' (by norm_num : 1 < 3) hn, List.sum_cons, Nat.cast_add]

lemma S_three_mul (t : ℕ) : S (3 * t) = S t := by
  rw [S_eq (3 * t), show 3 * t % 3 = 0 by omega, show 3 * t / 3 = t by omega]
  simp

lemma S_three_mul_add_one (t : ℕ) : S (3 * t + 1) = S t + 1 := by
  rw [S_eq (3 * t + 1), show (3 * t + 1) % 3 = 1 by omega, show (3 * t + 1) / 3 = t by omega]
  push_cast
  ring

lemma S_three_mul_add_two (t : ℕ) : S (3 * t + 2) = S t + 2 := by
  rw [S_eq (3 * t + 2), show (3 * t + 2) % 3 = 2 by omega, show (3 * t + 2) / 3 = t by omega]
  push_cast
  ring

lemma S_one : S 1 = 1 := by
  have h := S_three_mul_add_one 0
  rw [show S 0 = 0 by simp [S]] at h
  simpa using h

lemma two_mem_digits (n : ℕ) :
    2 ∈ Nat.digits 3 n ↔ n % 3 = 2 ∨ 2 ∈ Nat.digits 3 (n / 3) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.digits_def' (by norm_num : 1 < 3) hn, List.mem_cons]
    exact or_congr_left eq_comm

lemma two_mem_digits_three_mul (t : ℕ) : 2 ∈ Nat.digits 3 (3 * t) ↔ 2 ∈ Nat.digits 3 t := by
  rw [two_mem_digits (3 * t), show 3 * t % 3 = 0 by omega, show 3 * t / 3 = t by omega]
  simp

lemma two_mem_digits_three_mul_add_one (t : ℕ) :
    2 ∈ Nat.digits 3 (3 * t + 1) ↔ 2 ∈ Nat.digits 3 t := by
  rw [two_mem_digits (3 * t + 1), show (3 * t + 1) % 3 = 1 by omega, show (3 * t + 1) / 3 = t by omega]
  simp

lemma two_mem_digits_three_mul_add_two (t : ℕ) : 2 ∈ Nat.digits 3 (3 * t + 2) := by
  rw [two_mem_digits]
  left
  omega

/-- Legendre's formula for $p = 3$: $2 v_3(n!) = n - S(n)$. -/
lemma two_mul_padicValNat_factorial (n : ℕ) : (2 * padicValNat 3 n ! : ℤ) = n - S n := by
  have h := sub_one_mul_padicValNat_factorial (p := 3) n
  have hle := Nat.digit_sum_le 3 n
  rw [show (3 : ℕ) - 1 = 2 by norm_num] at h
  simp only [S]
  omega

/-- $2 v_3\binom{a + b}{a} = S(a) + S(b) - S(a + b)$. -/
lemma two_mul_padicValNat_choose (a b : ℕ) :
    (2 * padicValNat 3 ((a + b).choose a) : ℤ) = S a + S b - S (a + b) := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at h
  have hc : (a + b).choose a ≠ 0 := (Nat.choose_pos (Nat.le_add_right a b)).ne'
  have hv : padicValNat 3 (a + b)! =
      padicValNat 3 ((a + b).choose a) + padicValNat 3 a ! + padicValNat 3 b ! := by
    rw [← h, padicValNat.mul (p := 3) (mul_ne_zero hc (Nat.factorial_ne_zero a))
      (Nat.factorial_ne_zero b), padicValNat.mul (p := 3) hc (Nat.factorial_ne_zero a)]
  have e1 := two_mul_padicValNat_factorial a
  have e2 := two_mul_padicValNat_factorial b
  have e3 := two_mul_padicValNat_factorial (a + b)
  rw [Nat.cast_add] at e3
  have hv' := congrArg (fun x : ℕ => (x : ℤ)) hv
  simp only [Nat.cast_add] at hv'
  linarith

lemma S_add_le (a b : ℕ) : S (a + b) ≤ S a + S b := by
  have h := two_mul_padicValNat_choose a b
  have : (0 : ℤ) ≤ 2 * padicValNat 3 ((a + b).choose a) := by positivity
  linarith

/-- $F(n) = S(n) + S(n + 1) - S(2n) - 1 = 2 v_3(C(n))$. -/
def F (n : ℕ) : ℤ := S n + S (n + 1) - S (2 * n) - 1

/-- $K(q) = 2 S(q) - S(2q)$. -/
def K (q : ℕ) : ℤ := 2 * S q - S (2 * q)

/-- $G(q) = S(q) + S(q + 1) - S(2q + 1)$. -/
def G (q : ℕ) : ℤ := S q + S (q + 1) - S (2 * q + 1)

/-- $M(q) = 2 S(q) + 3 - S(2q + 1)$. -/
def M (q : ℕ) : ℤ := 2 * S q + 3 - S (2 * q + 1)

lemma catalan_ne_zero (n : ℕ) : catalan n ≠ 0 := by
  intro h0
  have h := succ_mul_catalan_eq_centralBinom n
  rw [h0, mul_zero] at h
  exact Nat.centralBinom_ne_zero n h.symm

lemma two_mul_padicValNat_catalan (n : ℕ) : (2 * padicValNat 3 (catalan n) : ℤ) = F n := by
  have h := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * n = n + n by ring] at h
  have hv : padicValNat 3 ((n + n).choose n) =
      padicValNat 3 (n + 1) + padicValNat 3 (catalan n) := by
    rw [← h, padicValNat.mul (p := 3) (show n + 1 ≠ 0 by omega) (catalan_ne_zero n)]
  have hf : padicValNat 3 (n + 1)! = padicValNat 3 (n + 1) + padicValNat 3 n ! := by
    rw [Nat.factorial_succ,
      padicValNat.mul (p := 3) (show n + 1 ≠ 0 by omega) (Nat.factorial_ne_zero n)]
  have e1 := two_mul_padicValNat_choose n n
  have e2 := two_mul_padicValNat_factorial n
  have e3 := two_mul_padicValNat_factorial (n + 1)
  rw [Nat.cast_add, Nat.cast_one] at e3
  have hv' := congrArg (fun x : ℕ => (x : ℤ)) hv
  have hf' := congrArg (fun x : ℕ => (x : ℤ)) hf
  simp only [Nat.cast_add] at hv' hf'
  rw [F, show 2 * n = n + n by ring]
  linarith

lemma three_dvd_catalan_iff (n : ℕ) : 3 ∣ catalan n ↔ 0 < F n := by
  rw [← two_mul_padicValNat_catalan]
  constructor
  · intro h
    have := one_le_padicValNat_of_dvd (catalan_ne_zero n) h
    omega
  · intro h
    exact dvd_of_one_le_padicValNat (by omega)

lemma two_le_M (q : ℕ) : 2 ≤ M q := by
  have h1 := S_add_le q (q + 1)
  have h2 := S_add_le q 1
  rw [S_one] at h2
  rw [M, show 2 * q + 1 = q + (q + 1) by ring]
  linarith

lemma K_three_mul (t : ℕ) : K (3 * t) = K t := by
  rw [K, K, show 2 * (3 * t) = 3 * (2 * t) by ring, S_three_mul, S_three_mul]

lemma K_three_mul_add_one (t : ℕ) : K (3 * t + 1) = K t := by
  rw [K, K, show 2 * (3 * t + 1) = 3 * (2 * t) + 2 by ring, S_three_mul_add_one,
    S_three_mul_add_two]
  ring

lemma K_three_mul_add_two (t : ℕ) : K (3 * t + 2) = M t := by
  rw [K, M, show 2 * (3 * t + 2) = 3 * (2 * t + 1) + 1 by ring, S_three_mul_add_two,
    S_three_mul_add_one]
  ring

lemma G_three_mul (t : ℕ) : G (3 * t) = K t := by
  rw [G, K, show 2 * (3 * t) + 1 = 3 * (2 * t) + 1 by ring, S_three_mul, S_three_mul_add_one,
    S_three_mul_add_one]
  ring

lemma G_three_mul_add_one (t : ℕ) : G (3 * t + 1) = M t := by
  rw [G, M, show 3 * t + 1 + 1 = 3 * t + 2 by ring,
    show 2 * (3 * t + 1) + 1 = 3 * (2 * t + 1) by ring, S_three_mul_add_one, S_three_mul_add_two,
    S_three_mul]
  ring

lemma G_three_mul_add_two (t : ℕ) : G (3 * t + 2) = G t := by
  rw [G, G, show 3 * t + 2 + 1 = 3 * (t + 1) by ring,
    show 2 * (3 * t + 2) + 1 = 3 * (2 * t + 1) + 2 by ring, S_three_mul_add_two, S_three_mul,
    S_three_mul_add_two]
  ring

lemma F_three_mul (t : ℕ) : F (3 * t) = K t := by
  rw [F, K, show 2 * (3 * t) = 3 * (2 * t) by ring, S_three_mul, S_three_mul_add_one,
    S_three_mul]
  ring

lemma F_three_mul_add_one (t : ℕ) : F (3 * t + 1) = K t := by
  rw [F, K, show 3 * t + 1 + 1 = 3 * t + 2 by ring,
    show 2 * (3 * t + 1) = 3 * (2 * t) + 2 by ring, S_three_mul_add_one, S_three_mul_add_two,
    S_three_mul_add_two]
  ring

lemma F_three_mul_add_two (t : ℕ) : F (3 * t + 2) = G t := by
  rw [F, G, show 3 * t + 2 + 1 = 3 * (t + 1) by ring,
    show 2 * (3 * t + 2) = 3 * (2 * t + 1) + 1 by ring, S_three_mul_add_two, S_three_mul,
    S_three_mul_add_one]
  ring

lemma K_pos_iff (q : ℕ) : 0 < K q ↔ 2 ∈ Nat.digits 3 q := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    obtain ⟨t, rfl | rfl | rfl⟩ : ∃ t, q = 3 * t ∨ q = 3 * t + 1 ∨ q = 3 * t + 2 :=
      ⟨q / 3, by omega⟩
    · rw [K_three_mul, two_mem_digits_three_mul]
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp [K, S]
      · exact ih t (by omega)
    · rw [K_three_mul_add_one, two_mem_digits_three_mul_add_one]
      exact ih t (by omega)
    · rw [K_three_mul_add_two]
      simp only [two_mem_digits_three_mul_add_two, iff_true]
      linarith [two_le_M t]

lemma G_pos_iff (q : ℕ) : 0 < G q ↔ 2 ∈ Nat.digits 3 (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    obtain ⟨t, rfl | rfl | rfl⟩ : ∃ t, q = 3 * t ∨ q = 3 * t + 1 ∨ q = 3 * t + 2 :=
      ⟨q / 3, by omega⟩
    · rw [G_three_mul, K_pos_iff, two_mem_digits_three_mul_add_one]
    · rw [G_three_mul_add_one, show 3 * t + 1 + 1 = 3 * t + 2 by ring]
      simp only [two_mem_digits_three_mul_add_two, iff_true]
      linarith [two_le_M t]
    · rw [G_three_mul_add_two, show 3 * t + 2 + 1 = 3 * (t + 1) by ring,
        two_mem_digits_three_mul]
      exact ih t (by omega)

lemma F_pos_iff (n : ℕ) : 0 < F n ↔ 2 ∈ Nat.digits 3 n ∧ 2 ∈ Nat.digits 3 (n + 1) := by
  obtain ⟨t, rfl | rfl | rfl⟩ : ∃ t, n = 3 * t ∨ n = 3 * t + 1 ∨ n = 3 * t + 2 :=
    ⟨n / 3, by omega⟩
  · rw [F_three_mul, K_pos_iff, two_mem_digits_three_mul, two_mem_digits_three_mul_add_one,
      and_self]
  · rw [F_three_mul_add_one, K_pos_iff, show 3 * t + 1 + 1 = 3 * t + 2 by ring,
      two_mem_digits_three_mul_add_one]
    simp only [two_mem_digits_three_mul_add_two, and_true]
  · rw [F_three_mul_add_two, G_pos_iff, show 3 * t + 2 + 1 = 3 * (t + 1) by ring,
      two_mem_digits_three_mul]
    simp only [two_mem_digits_three_mul_add_two, true_and]

/-- **A265100, Conjecture 5** (Robert Israel). $3 \mid C(n)$ if and only if the base-$3$
representations of $n$ and $n + 1$ both contain the digit $2$. -/
theorem conjecture5 (n : ℕ) :
    3 ∣ catalan n ↔ 2 ∈ Nat.digits 3 n ∧ 2 ∈ Nat.digits 3 (n + 1) := by
  rw [three_dvd_catalan_iff, F_pos_iff]

/-- A block number of A265100: $n \ge 1$, $3 \mid C(n)$ and $3 \nmid C(n - 1)$. -/
def IsBlockNumber (n : ℕ) : Prop := 1 ≤ n ∧ 3 ∣ catalan n ∧ ¬ 3 ∣ catalan (n - 1)

/-- The block numbers are exactly the numbers $9m + 5$ where $m$ has no base-$3$ digit $2$. -/
theorem isBlockNumber_iff (n : ℕ) :
    IsBlockNumber n ↔ ∃ m, 2 ∉ Nat.digits 3 m ∧ n = 9 * m + 5 := by
  constructor
  · rintro ⟨hn, h1, h2⟩
    rw [conjecture5] at h1 h2
    obtain ⟨hd, hd1⟩ := h1
    have h3 : 2 ∉ Nat.digits 3 (n - 1) := fun h => h2 ⟨h, by rwa [Nat.sub_add_cancel hn]⟩
    obtain ⟨q, rfl | rfl | rfl⟩ : ∃ q, n = 3 * q ∨ n = 3 * q + 1 ∨ n = 3 * q + 2 :=
      ⟨n / 3, by omega⟩
    · rw [show 3 * q - 1 = 3 * (q - 1) + 2 by omega] at h3
      exact absurd (two_mem_digits_three_mul_add_two _) h3
    · rw [show 3 * q + 1 - 1 = 3 * q by omega, two_mem_digits_three_mul] at h3
      rw [two_mem_digits_three_mul_add_one] at hd
      exact absurd hd h3
    · rw [show 3 * q + 2 - 1 = 3 * q + 1 by omega, two_mem_digits_three_mul_add_one] at h3
      rw [show 3 * q + 2 + 1 = 3 * (q + 1) by ring, two_mem_digits_three_mul] at hd1
      obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, q = 3 * m ∨ q = 3 * m + 1 ∨ q = 3 * m + 2 :=
        ⟨q / 3, by omega⟩
      · rw [two_mem_digits_three_mul] at h3
        rw [two_mem_digits_three_mul_add_one] at hd1
        exact absurd hd1 h3
      · rw [two_mem_digits_three_mul_add_one] at h3
        exact ⟨m, h3, by ring⟩
      · exact absurd (two_mem_digits_three_mul_add_two m) h3
  · rintro ⟨m, hm, rfl⟩
    refine ⟨by omega, ?_, ?_⟩
    · rw [conjecture5, show 9 * m + 5 = 3 * (3 * m + 1) + 2 by ring,
        show 3 * (3 * m + 1) + 2 + 1 = 3 * (3 * m + 2) by ring, two_mem_digits_three_mul]
      exact ⟨two_mem_digits_three_mul_add_two _, two_mem_digits_three_mul_add_two _⟩
    · rw [conjecture5, show 9 * m + 5 - 1 = 3 * (3 * m + 1) + 1 by omega,
        two_mem_digits_three_mul_add_one, two_mem_digits_three_mul_add_one]
      exact fun h => hm h.1

/-- **A265100, Conjecture 1.** Every block number is a term $9m + 5$ of the sequence, where $m$
has no base-$3$ digit $2$ (so $m$ is a term of A005836). -/
theorem conjecture1 {n : ℕ} (h : IsBlockNumber n) : ∃ m, 2 ∉ Nat.digits 3 m ∧ n = 9 * m + 5 :=
  (isBlockNumber_iff n).1 h

/-- **A265100, Conjecture 2.** If $m$ is a block number, then so is $3m - 1$. -/
theorem conjecture2 {m : ℕ} (h : IsBlockNumber m) : IsBlockNumber (3 * m - 1) := by
  obtain ⟨k, hk, rfl⟩ := (isBlockNumber_iff m).1 h
  refine (isBlockNumber_iff _).2 ⟨3 * k + 1, ?_, by omega⟩
  rwa [two_mem_digits_three_mul_add_one]

/-- **A265100, Conjecture 3.** If $3 \mid C(n)$, then $3 \mid C(3n - 1)$. -/
theorem conjecture3 {n : ℕ} (h : 3 ∣ catalan n) : 3 ∣ catalan (3 * n - 1) := by
  rw [conjecture5] at h ⊢
  obtain ⟨hn, -⟩ := h
  have hpos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hn
    · exact h
  rw [show 3 * n - 1 = 3 * (n - 1) + 2 by omega, show 3 * (n - 1) + 2 + 1 = 3 * n by omega,
    two_mem_digits_three_mul]
  exact ⟨two_mem_digits_three_mul_add_two _, hn⟩

end OeisA265100Proof

/-! Separately written source statements for OEIS A265100, Conjectures 1, 2, 3 and 5. They assert
no theorem.

Source: A265100 (L. Edson Jeffery, Dec 01 2015; revision #31, Dec 23 2024), retrieved 2026-11-03.
- Name: "a(n) = 9*A005836(n) + 5, n >= 1". A005836 lists the numbers whose base-3 expansion has
  no digit 2, from A005836(1) = 0.
- "If n is an integer such that the congruences C(n) == 0 (mod 3) and C(n-1) =!= 0 (mod 3) hold
  simultaneously, then we call n a "block number."" Here $C(n - 1)$ requires $n \ge 1$.
- Conjecture 1: "The sequence contains all possible block numbers."
- Conjecture 2: "If m is a block number, then 3*m - 1 is a block number."
- Conjecture 3: "If C(n) == 0 (mod 3), then C(3*n-1) == 0 (mod 3)".
- Conjecture 5: "C(n) == 0 (mod 3) if and only if the base 3 representations of n and n + 1 both
  contain at least one 2."

The base-3 digit of $n$ at position $k$ is written `n / 3 ^ k % 3`. -/
namespace A265100Frozen

/-- A005836 with offset 1: the `i`-th number whose base-3 expansion has no digit 2. -/
noncomputable def A005836 (i : ℕ) : ℕ := Nat.nth (fun m => ∀ k : ℕ, m / 3 ^ k % 3 ≠ 2) (i - 1)

/-- A265100 with offset 1. -/
noncomputable def a (n : ℕ) : ℕ := 9 * A005836 n + 5

/-- A block number: $n \ge 1$, $C(n) \equiv 0$ and $C(n - 1) \not\equiv 0 \pmod 3$. -/
def IsBlockNumber (n : ℕ) : Prop := 1 ≤ n ∧ catalan n % 3 = 0 ∧ catalan (n - 1) % 3 ≠ 0

/-- Conjecture 5, for every $n \ge 0$. -/
def conjecture5 : Prop :=
  ∀ n : ℕ, catalan n % 3 = 0 ↔ (∃ k : ℕ, n / 3 ^ k % 3 = 2) ∧ ∃ k : ℕ, (n + 1) / 3 ^ k % 3 = 2

/-- Conjecture 1: every block number is a term `a i`, `i ≥ 1`. -/
def conjecture1 : Prop := ∀ n : ℕ, IsBlockNumber n → ∃ i ≥ 1, a i = n

/-- Conjecture 2. -/
def conjecture2 : Prop := ∀ m : ℕ, IsBlockNumber m → IsBlockNumber (3 * m - 1)

/-- Conjecture 3, for every $n \ge 0$. -/
def conjecture3 : Prop := ∀ n : ℕ, catalan n % 3 = 0 → catalan (3 * n - 1) % 3 = 0

/-- The converse of Conjecture 1, which the source does not state: every term is a block
number. -/
def conjecture1Converse : Prop := ∀ i ≥ 1, IsBlockNumber (a i)

end A265100Frozen

/-! Kernel checks for the OEIS A265100 candidate: the separately frozen statements and transitive
axioms. This file is not Comparator. -/

open OeisA265100Proof

lemma exists_digit_iff (n : ℕ) : (∃ k : ℕ, n / 3 ^ k % 3 = 2) ↔ 2 ∈ Nat.digits 3 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have step : (∃ k : ℕ, n / 3 ^ k % 3 = 2) ↔ n % 3 = 2 ∨ ∃ k : ℕ, n / 3 / 3 ^ k % 3 = 2 := by
      constructor
      · rintro ⟨k, hk⟩
        cases k with
        | zero => exact Or.inl (by simpa using hk)
        | succ k => exact Or.inr ⟨k, by rwa [pow_succ', ← Nat.div_div_eq_div_mul] at hk⟩
      · rintro (h | ⟨k, hk⟩)
        · exact ⟨0, by simpa using h⟩
        · exact ⟨k + 1, by rwa [pow_succ', ← Nat.div_div_eq_div_mul]⟩
    rw [step, two_mem_digits n]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [ih (n / 3) (by omega)]

lemma noTwo_iff (m : ℕ) : (∀ k : ℕ, m / 3 ^ k % 3 ≠ 2) ↔ 2 ∉ Nat.digits 3 m := by
  rw [← exists_digit_iff]
  exact ⟨fun h ⟨k, hk⟩ => h k hk, fun h k hk => h ⟨k, hk⟩⟩

lemma isBlockNumber_frozen_iff (n : ℕ) :
    A265100Frozen.IsBlockNumber n ↔ IsBlockNumber n := by
  unfold A265100Frozen.IsBlockNumber IsBlockNumber
  omega

lemma infinite_noTwo : (Set.ofPred fun m : ℕ => ∀ k : ℕ, m / 3 ^ k % 3 ≠ 2).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ⟨3 ^ a, ?_, Nat.lt_pow_self (by norm_num)⟩
  show ∀ k : ℕ, 3 ^ a / 3 ^ k % 3 ≠ 2
  intro k
  rcases le_or_gt k a with hk | hk
  · rw [Nat.pow_div hk (by norm_num)]
    rcases Nat.eq_zero_or_pos (a - k) with h | h
    · rw [h]
      norm_num
    · rw [show a - k = a - k - 1 + 1 by omega, pow_succ]
      omega
  · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk)]
    norm_num

theorem frozen_conjecture5 : A265100Frozen.conjecture5 := by
  intro n
  rw [exists_digit_iff n, exists_digit_iff (n + 1), ← conjecture5 n]
  omega

theorem frozen_conjecture1 : A265100Frozen.conjecture1 := by
  intro n hn
  obtain ⟨m, hm, rfl⟩ := conjecture1 ((isBlockNumber_frozen_iff n).1 hn)
  obtain ⟨i, -, hi⟩ := Nat.exists_lt_card_nth_eq
    (p := fun m : ℕ => ∀ k : ℕ, m / 3 ^ k % 3 ≠ 2) ((noTwo_iff m).2 hm)
  refine ⟨i + 1, by omega, ?_⟩
  rw [A265100Frozen.a, A265100Frozen.A005836, Nat.add_sub_cancel, hi]

theorem frozen_conjecture2 : A265100Frozen.conjecture2 := fun m hm =>
  (isBlockNumber_frozen_iff _).2 (conjecture2 ((isBlockNumber_frozen_iff m).1 hm))

theorem frozen_conjecture3 : A265100Frozen.conjecture3 := by
  intro n hn
  have := conjecture3 (n := n) (by omega)
  omega

theorem frozen_conjecture1Converse : A265100Frozen.conjecture1Converse := by
  intro i _
  refine (isBlockNumber_frozen_iff _).2 ((isBlockNumber_iff _).2
    ⟨Nat.nth (fun m : ℕ => ∀ k : ℕ, m / 3 ^ k % 3 ≠ 2) (i - 1), ?_, rfl⟩)
  exact (noTwo_iff _).1 (Nat.nth_mem_of_infinite infinite_noTwo _)

namespace OeisA265100

theorem conjecture5 :
    ∀ n : ℕ, catalan n % 3 = 0 ↔ (∃ k : ℕ, n / 3 ^ k % 3 = 2) ∧ ∃ k : ℕ, (n + 1) / 3 ^ k % 3 = 2 :=
  _root_.frozen_conjecture5

theorem conjecture1 :
    ∀ n : ℕ, IsBlockNumber n → ∃ i ≥ 1, a i = n :=
  _root_.frozen_conjecture1

theorem conjecture2 :
    ∀ m : ℕ, IsBlockNumber m → IsBlockNumber (3 * m - 1) :=
  _root_.frozen_conjecture2

theorem conjecture3 :
    ∀ n : ℕ, catalan n % 3 = 0 → catalan (3 * n - 1) % 3 = 0 :=
  _root_.frozen_conjecture3

end OeisA265100

end
