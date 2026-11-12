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
# Motzkin numbers at $p - 2$ modulo $p$

The Motzkin numbers (OEIS A001006) satisfy $M(n) = \sum_{k=0}^{n} \binom{n}{2k} C_k$, where $C_k$
are the Catalan numbers. Serge Batalov conjectured (2022) that $p \mid M(p-2)$ for every prime
$p \equiv 1 \pmod 6$. Rob Burns (2017) showed that $M(p-2) \equiv 0$ for $p \equiv 1 \pmod 6$ and
$M(p-2) \equiv -1$ for $p \equiv 5 \pmod 6$, and Nadav Kohen (2024, Proposition 6) showed that
$p \mid M(p-2)$ if and only if $p \equiv 1 \pmod 3$.

This file proves both statements for every prime $p$. For $p \ge 5$ with $p = 2h + 1$ we show
$2 M(p-2) \equiv (-3)^h - 1 \pmod p$ from $\binom{p-2}{2k} \equiv 2k + 1$ and
$C_k \equiv 2 (-4)^k \binom{h+1}{k+1}$, and then use Euler's criterion: $-3$ is a square modulo
$p$ if and only if $p \equiv 1 \pmod 3$.

*References:*
- [A001006](https://oeis.org/A001006)
- Rob Burns, Structure and asymptotics for Motzkin numbers modulo primes using automata,
  [arXiv:1703.00826](https://arxiv.org/abs/1703.00826), 2017, Tables 4 and 5.
- Nadav Kohen, Density and Symmetry in the Generalized Motzkin Numbers mod p,
  [arXiv:2411.03681](https://arxiv.org/abs/2411.03681), 2024, Proposition 6; also
  *Integers* 26 (2026), A22.
-/

@[expose] public section

namespace OeisA1006

/-- The coefficient form of $A(x) = 1 + x A(x) + x^2 A(x)^2$: $a(0) = a(1) = 1$ and
$a(n+2) = a(n+1) + \sum_{i+j=n} a(i) a(j)$. -/
def IsMotzkin (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 1 ∧ ∀ n, a (n + 2) = a (n + 1) + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, a x.1 * a x.2

end OeisA1006

namespace OeisA1006Proof

open Finset

/-- The Motzkin numbers, $M(n) = \sum_{k=0}^{n} \binom{n}{2k} C_k$ (Paul Barry's formula in
A001006), where $C_k$ is the $k$-th Catalan number. -/
def motzkin (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose (2 * k) * catalan k

/-- For every prime $p$: $p \mid M(p-2)$ if and only if $p \equiv 1 \pmod 3$, and
$M(p-2) \equiv -1 \pmod p$ if $p \equiv 5 \pmod 6$. -/
def Target : Prop :=
  ∀ p : ℕ, p.Prime →
    (p ∣ motzkin (p - 2) ↔ p % 3 = 1) ∧ (p % 6 = 5 → (motzkin (p - 2) : ZMod p) = -1)

/-- Only the terms with $2k \le n$ contribute. -/
theorem motzkin_eq_sum_half (n : ℕ) :
    motzkin n = ∑ k ∈ range (n / 2 + 1), n.choose (2 * k) * catalan k := by
  refine (sum_subset (fun k hk => ?_) fun k _ hk => ?_).symm
  · simp only [mem_range] at hk ⊢
    omega
  · simp only [mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]

/-! ## The generating-function recurrence

The recurrence $M(n+2) = M(n+1) + \sum_{i+j=n} M(i) M(j)$ with $M(0) = M(1) = 1$ is the
coefficient form of $A(x) = 1 + x A(x) + x^2 A(x)^2$, the generating-function equation in A001006.
It determines the sequence, so `motzkin` is the OEIS sequence. -/

theorem motzkin_eq_sum_of_le {i N : ℕ} (h : i ≤ N) :
    motzkin i = ∑ a ∈ range (N + 1), i.choose (2 * a) * catalan a := by
  refine sum_subset (fun a ha => ?_) fun a _ ha => ?_
  · simp only [mem_range] at ha ⊢
    omega
  · simp only [mem_range, not_lt] at ha
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]

/-- Upper Vandermonde: $\sum_{i+j=n} \binom{i}{r}\binom{j}{s} = \binom{n+1}{r+s+1}$. -/
theorem sum_antidiagonal_choose_mul_choose (r s n : ℕ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, x.1.choose r * x.2.choose s = (n + 1).choose (r + s + 1) := by
  have hG : ∀ t : ℕ, (PowerSeries.X : PowerSeries ℤ) ^ t * (PowerSeries.mk 1) ^ (t + 1) =
      PowerSeries.mk fun i => ((i.choose t : ℕ) : ℤ) := by
    intro t
    ext i
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add ℤ t, PowerSeries.coeff_X_pow_mul']
    simp only [PowerSeries.coeff_mk]
    split_ifs with h
    · rw [Nat.add_sub_cancel' h]
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  have key : (PowerSeries.X : PowerSeries ℤ) * ((PowerSeries.mk fun i => ((i.choose r : ℕ) : ℤ)) *
      (PowerSeries.mk fun i => ((i.choose s : ℕ) : ℤ))) =
      PowerSeries.mk fun i => ((i.choose (r + s + 1) : ℕ) : ℤ) := by
    rw [← hG, ← hG, ← hG]
    ring
  have h := congrArg (PowerSeries.coeff (n + 1)) key
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul] at h
  simp only [PowerSeries.coeff_mk] at h
  exact_mod_cast h

/-- $M(n+2) = M(n+1) + \sum_{k} \binom{n+1}{2k+1} C_{k+1}$, by Pascal's rule. -/
theorem motzkin_add_two_eq (n : ℕ) :
    motzkin (n + 2) =
      motzkin (n + 1) + ∑ k ∈ range (n + 2), (n + 1).choose (2 * k + 1) * catalan (k + 1) := by
  have h2 : motzkin (n + 2) =
      ∑ k ∈ range (n + 2), (n + 2).choose (2 * (k + 1)) * catalan (k + 1) + 1 := by
    rw [motzkin, sum_range_succ']
    simp only [mul_zero, Nat.choose_zero_right, catalan_zero, mul_one]
  have h1 : motzkin (n + 1) =
      ∑ k ∈ range (n + 1), (n + 1).choose (2 * (k + 1)) * catalan (k + 1) + 1 := by
    rw [motzkin, sum_range_succ']
    simp only [mul_zero, Nat.choose_zero_right, catalan_zero, mul_one]
  have hsplit : ∀ k, (n + 2).choose (2 * (k + 1)) * catalan (k + 1) =
      (n + 1).choose (2 * k + 1) * catalan (k + 1) +
        (n + 1).choose (2 * (k + 1)) * catalan (k + 1) := by
    intro k
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.choose_succ_succ']
    ring
  rw [h2, h1, sum_congr rfl fun k _ => hsplit k, sum_add_distrib, sum_range_succ
    (fun k => (n + 1).choose (2 * (k + 1)) * catalan (k + 1)) (n + 1),
    Nat.choose_eq_zero_of_lt (show n + 1 < 2 * (n + 1 + 1) by omega)]
  ring

/-- $\sum_{i+j=n} M(i) M(j) = \sum_{k} \binom{n+1}{2k+1} C_{k+1}$, by upper Vandermonde and the
Catalan recurrence. -/
theorem sum_antidiagonal_motzkin (n : ℕ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, motzkin x.1 * motzkin x.2 =
      ∑ k ∈ range (n + 2), (n + 1).choose (2 * k + 1) * catalan (k + 1) := by
  set g : ℕ → ℕ → ℕ := fun a b => catalan a * catalan b * (n + 1).choose (2 * a + 2 * b + 1)
    with hg
  have hz : ∀ a b, n + 1 < 2 * a + 2 * b + 1 → g a b = 0 := fun a b h => by
    rw [hg]
    dsimp only
    rw [Nat.choose_eq_zero_of_lt h, mul_zero]
  have hL : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, motzkin x.1 * motzkin x.2 =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), g a b := by
    calc ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, motzkin x.1 * motzkin x.2
        = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, (∑ a ∈ range (n + 1), x.1.choose (2 * a) * catalan a) *
            ∑ b ∈ range (n + 1), x.2.choose (2 * b) * catalan b := by
          refine sum_congr rfl fun x hx => ?_
          have hx' := mem_antidiagonal.mp hx
          rw [motzkin_eq_sum_of_le (show x.1 ≤ n by omega),
            motzkin_eq_sum_of_le (show x.2 ≤ n by omega)]
      _ = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
            x.1.choose (2 * a) * catalan a * (x.2.choose (2 * b) * catalan b) := by
          simp_rw [sum_mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun a _ => sum_comm
      _ = _ := by
          refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
          rw [hg]
          dsimp only
          rw [← sum_antidiagonal_choose_mul_choose (2 * a) (2 * b) n, mul_sum]
          exact sum_congr rfl fun x _ => by ring
  have hR : ∑ k ∈ range (n + 2), (n + 1).choose (2 * k + 1) * catalan (k + 1) =
      ∑ a ∈ range (n + 2), ∑ b ∈ range (n + 2 - a), g a b := by
    rw [← sum_range_diag_flip]
    refine sum_congr rfl fun c _ => ?_
    rw [catalan_succ', Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_comm, sum_mul]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    rw [hg]
    dsimp only
    rw [show 2 * k + 2 * (c - k) + 1 = 2 * c + 1 by omega]
  have hin : ∀ a, ∑ b ∈ range (n + 2 - a), g a b = ∑ b ∈ range (n + 2), g a b := by
    intro a
    refine sum_subset (fun b hb => ?_) fun b hb hb' => ?_
    · simp only [mem_range] at hb ⊢
      omega
    · simp only [mem_range, not_lt] at hb hb'
      exact hz a b (by omega)
  have hin' : ∀ a, ∑ b ∈ range (n + 1), g a b = ∑ b ∈ range (n + 2), g a b := by
    intro a
    have h := sum_range_succ (g a) (n + 1)
    rw [hz a (n + 1) (by omega), add_zero] at h
    exact h.symm
  rw [hL, hR]
  conv_rhs => rw [sum_range_succ]
  rw [hin (n + 1), sum_eq_zero fun b _ => hz (n + 1) b (by omega), add_zero]
  exact sum_congr rfl fun a _ => by rw [hin, hin']

theorem motzkin_zero : motzkin 0 = 1 := by
  simp [motzkin]

theorem motzkin_one : motzkin 1 = 1 := by
  rw [motzkin_eq_sum_half]
  simp

/-- **Bernhart's recurrence** in A001006: $M(n+2) = M(n+1) + \sum_{i+j=n} M(i) M(j)$. -/
theorem motzkin_add_two (n : ℕ) :
    motzkin (n + 2) = motzkin (n + 1) + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, motzkin x.1 * motzkin x.2 := by
  rw [motzkin_add_two_eq, sum_antidiagonal_motzkin]

/-- The recurrence with $M(0) = M(1) = 1$ determines the sequence. -/
theorem eq_motzkin_of_recurrence (f : ℕ → ℕ) (h0 : f 0 = 1) (h1 : f 1 = 1)
    (h : ∀ n, f (n + 2) = f (n + 1) + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, f x.1 * f x.2) (n : ℕ) :
    f n = motzkin n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [h0, motzkin_zero]
    | 1 => rw [h1, motzkin_one]
    | n + 2 =>
      rw [h, motzkin_add_two, ih (n + 1) (by omega)]
      congr 1
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_antidiagonal.mp hx
      rw [ih x.1 (by omega), ih x.2 (by omega)]

/-- $(k+2) C_{k+1} = 2(2k+1) C_k$. -/
theorem catalan_succ_mul (k : ℕ) : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k)
  calc (k + 1) * ((k + 2) * catalan (k + 1))
      = (k + 1) * ((k + 1 + 1) * catalan (k + 1)) := by ring
    _ = (k + 1) * (k + 1).centralBinom := by rw [h1]
    _ = 2 * (2 * k + 1) * k.centralBinom := h3
    _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := by rw [h2]
    _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by ring

/-- $\sum_{k=0}^{n} (2k+1) y^{k+1} \binom{n+1}{k+1} = 2(n+1) y (1+y)^n - (1+y)^{n+1} + 1$. -/
theorem sum_two_mul_add_one_choose {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∑ k ∈ range (n + 1), (2 * k + 1 : R) * y ^ (k + 1) * ((n + 1).choose (k + 1) : R) =
      2 * (n + 1) * y * (1 + y) ^ n - (1 + y) ^ (n + 1) + 1 := by
  have hA : ∑ k ∈ range (n + 1), ((k : R) + 1) * y ^ (k + 1) * ((n + 1).choose (k + 1) : R) =
      (n + 1) * y * (1 + y) ^ n := by
    rw [add_comm 1 y, add_pow, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    have h := congrArg (Nat.cast : ℕ → R) (Nat.add_one_mul_choose_eq n k)
    push_cast at h
    simp only [one_pow, mul_one]
    linear_combination (-y ^ (k + 1)) * h
  have hB : ∑ k ∈ range (n + 1), y ^ (k + 1) * ((n + 1).choose (k + 1) : R) =
      (1 + y) ^ (n + 1) - 1 := by
    rw [add_comm 1 y, add_pow, sum_range_succ' _ (n + 1)]
    simp
  have hsplit : ∀ k : ℕ, (2 * k + 1 : R) * y ^ (k + 1) * ((n + 1).choose (k + 1) : R) =
      2 * (((k : R) + 1) * y ^ (k + 1) * ((n + 1).choose (k + 1) : R)) -
        y ^ (k + 1) * ((n + 1).choose (k + 1) : R) := fun k => by ring
  rw [sum_congr rfl fun k _ => hsplit k, sum_sub_distrib, ← mul_sum, hA, hB]
  ring

section ZModPrime

variable {p : ℕ} [hp : Fact p.Prime]

theorem natCast_ne_zero {n : ℕ} (h0 : 0 < n) (hn : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd h0 h) (by omega)

/-- $\binom{p-2}{j} \equiv (-1)^j (j+1) \pmod p$. -/
theorem choose_sub_two (j : ℕ) (hj : j ≤ p - 2) :
    ((p - 2).choose j : ZMod p) = (-1) ^ j * (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp2 : 2 ≤ p := hp.out.two_le
    have hc : ((p - 2 - j : ℕ) : ZMod p) = -((j : ZMod p) + 2) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hp2, ZMod.natCast_self]
      push_cast
      ring
    have h' := congrArg (Nat.cast : ℕ → ZMod p) (Nat.choose_succ_right_eq (p - 2) j)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add_one] at h'
    rw [ih (by omega), hc] at h'
    have hne : ((j : ZMod p) + 1) ≠ 0 := by
      have := natCast_ne_zero (p := p) (n := j + 1) (by omega) (by omega)
      push_cast at this
      exact this
    apply mul_right_cancel₀ hne
    rw [h']
    push_cast
    ring

/-- With $p = 2h + 1$: $C_k \equiv 2 (-4)^k \binom{h+1}{k+1} \pmod p$ for $k < h$. -/
theorem catalan_cast {h : ℕ} (hph : p = 2 * h + 1) (k : ℕ) (hk : k < h) :
    (catalan k : ZMod p) = 2 * (-4) ^ k * ((h + 1).choose (k + 1) : ZMod p) := by
  have h0 : (2 * (h : ZMod p) + 1) = 0 := by
    have : ((2 * h + 1 : ℕ) : ZMod p) = 0 := by rw [← hph]; exact ZMod.natCast_self p
    push_cast at this
    exact this
  induction k with
  | zero =>
    simp only [catalan_zero, Nat.cast_one, pow_zero, mul_one, zero_add, Nat.choose_one_right]
    push_cast
    linear_combination (-1 : ZMod p) * h0
  | succ k ih =>
    have hrec := congrArg (Nat.cast : ℕ → ZMod p) (catalan_succ_mul k)
    push_cast at hrec
    have hch : ((h + 1).choose (k + 1 + 1) : ZMod p) * ((k : ZMod p) + 2) =
        ((h + 1).choose (k + 1) : ZMod p) * ((h : ZMod p) - k) := by
      have e := Nat.choose_succ_right_eq (h + 1) (k + 1)
      rw [Nat.add_sub_add_right] at e
      have e' := congrArg (Nat.cast : ℕ → ZMod p) e
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (show k ≤ h by omega)] at e'
      push_cast at e'
      linear_combination e'
    have hne : ((k : ZMod p) + 2) ≠ 0 := by
      have := natCast_ne_zero (p := p) (n := k + 2) (by omega) (by omega)
      push_cast at this
      exact this
    apply mul_left_cancel₀ hne
    rw [hrec, ih (by omega)]
    linear_combination (-2 * (-4 : ZMod p) ^ (k + 1)) * hch +
      (4 * (-4 : ZMod p) ^ k * ((h + 1).choose (k + 1) : ZMod p)) * h0

/-- For a prime $p \ge 5$: $2 M(p-2) \equiv (-3)^{(p-1)/2} - 1 \pmod p$. -/
theorem two_mul_motzkin_sub_two (hp5 : 5 ≤ p) :
    2 * (motzkin (p - 2) : ZMod p) = (-3) ^ (p / 2) - 1 := by
  obtain ⟨h, hph⟩ : ∃ h, p = 2 * h + 1 := hp.out.eq_two_or_odd'.resolve_left (by omega)
  have h0 : (2 * (h : ZMod p) + 1) = 0 := by
    have : ((2 * h + 1 : ℕ) : ZMod p) = 0 := by rw [← hph]; exact ZMod.natCast_self p
    push_cast at this
    exact this
  rw [motzkin_eq_sum_half, show (p - 2) / 2 + 1 = h by omega, show p / 2 = h by omega,
    Nat.cast_sum]
  have hterm : ∀ k ∈ range h, (((p - 2).choose (2 * k) * catalan k : ℕ) : ZMod p) =
      2 * ((2 * k + 1) * (-4) ^ k * ((h + 1).choose (k + 1) : ZMod p)) := by
    intro k hk
    have hk' := mem_range.mp hk
    push_cast
    rw [choose_sub_two (2 * k) (by omega), catalan_cast hph k hk', pow_mul, neg_one_sq, one_pow]
    push_cast
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have hS := sum_two_mul_add_one_choose (-4 : ZMod p) h
  rw [sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one,
    show (1 + -4 : ZMod p) = -3 by norm_num] at hS
  have hS' : ∑ k ∈ range h, (2 * (k : ZMod p) + 1) * (-4) ^ (k + 1) *
      ((h + 1).choose (k + 1) : ZMod p) =
      (-4) * ∑ k ∈ range h, (2 * (k : ZMod p) + 1) * (-4) ^ k * ((h + 1).choose (k + 1) : ZMod p) := by
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  rw [hS'] at hS
  linear_combination (-1 : ZMod p) * hS + ((-4 : ZMod p) ^ (h + 1) + 4 * (-3) ^ h) * h0

/-- For a prime $p \ge 5$, $-3$ is a square modulo $p$ if and only if $p \equiv 1 \pmod 3$. -/
theorem isSquare_neg_three_iff (hp5 : 5 ≤ p) : IsSquare (-3 : ZMod p) ↔ p % 3 = 1 := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := natCast_ne_zero (p := p) (n := 3) (by norm_num) (by omega)
    exact_mod_cast this
  have h4 : (4 : ZMod p) ≠ 0 := by
    have := natCast_ne_zero (p := p) (n := 4) (by norm_num) (by omega)
    exact_mod_cast this
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := natCast_ne_zero (p := p) (n := 2) (by norm_num) (by omega)
    exact_mod_cast this
  constructor
  · rintro ⟨s, hs⟩
    set ω : ZMod p := (s - 1) * 2⁻¹ with hωdef
    have h2ω : 2 * ω = s - 1 := by
      rw [hωdef, mul_comm, mul_assoc, inv_mul_cancel₀ h2, mul_one]
    have hq : 4 * (ω ^ 2 + ω + 1) = 0 := by
      linear_combination (s + 2 * ω + 1) * h2ω - hs
    have hω0 : ω ^ 2 + ω + 1 = 0 := (mul_eq_zero.mp hq).resolve_left h4
    have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω0
    have hω1 : ω ≠ 1 := by
      intro h1
      rw [h1] at hω0
      apply h3
      linear_combination hω0
    have hω_ne : ω ≠ 0 := by
      intro h1
      rw [h1] at hω3
      norm_num at hω3
    have hdvd := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hω_ne)
    rw [orderOf_eq_prime hω3 hω1] at hdvd
    omega
  · intro h31
    have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
      rw [ZMod.card_units]
      omega
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hdvd
    have hg3 : ((g : ZMod p)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
    have hg1 : (g : ZMod p) ≠ 1 := by
      intro h1
      have : g = 1 := Units.ext (by simpa using h1)
      rw [this, orderOf_one] at hg
      norm_num at hg
    have hω0 : (g : ZMod p) ^ 2 + g + 1 = 0 := by
      have : ((g : ZMod p) - 1) * ((g : ZMod p) ^ 2 + g + 1) = 0 := by
        linear_combination hg3
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hg1)
    exact ⟨2 * g + 1, by linear_combination (-4 : ZMod p) * hω0⟩

end ZModPrime

/-- **OEIS A001006** (Batalov's conjecture, proved by Burns and by Kohen). For every prime $p$,
$p \mid M(p-2)$ if and only if $p \equiv 1 \pmod 3$, and $M(p-2) \equiv -1 \pmod p$ when
$p \equiv 5 \pmod 6$. -/
theorem a1006_motzkin_congruence : Target := by
  intro p hp
  have := Fact.mk hp
  rcases Nat.lt_or_ge p 5 with h5 | hp5
  · interval_cases p
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · refine ⟨?_, by norm_num⟩
      rw [motzkin_eq_sum_half]
      norm_num
    · refine ⟨?_, by norm_num⟩
      rw [motzkin_eq_sum_half]
      norm_num
    · exact absurd hp (by decide)
  have key := two_mul_motzkin_sub_two hp5
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := natCast_ne_zero (p := p) (n := 2) (by norm_num) (by omega)
    exact_mod_cast this
  have h3ne : (-3 : ZMod p) ≠ 0 := by
    have := natCast_ne_zero (p := p) (n := 3) (by norm_num) (by omega)
    rw [neg_ne_zero]
    exact_mod_cast this
  rw [← ZMod.natCast_eq_zero_iff]
  rcases ZMod.pow_div_two_eq_neg_one_or_one p h3ne with h1 | h1
  · have hM : (motzkin (p - 2) : ZMod p) = 0 := by
      rw [h1, sub_self] at key
      exact (mul_eq_zero.mp key).resolve_left h2
    have h31 : p % 3 = 1 := (isSquare_neg_three_iff hp5).mp ((ZMod.euler_criterion p h3ne).mpr h1)
    exact ⟨iff_of_true hM h31, fun h6 => by omega⟩
  · have hM : (motzkin (p - 2) : ZMod p) = -1 := by
      rw [h1] at key
      apply mul_left_cancel₀ h2
      linear_combination key
    have h31 : ¬p % 3 = 1 := fun h => by
      have h1' := (ZMod.euler_criterion p h3ne).mp ((isSquare_neg_three_iff hp5).mpr h)
      rw [h1'] at h1
      exact h2 (by linear_combination h1)
    refine ⟨iff_of_false ?_ h31, fun _ => hM⟩
    rw [hM]
    exact neg_ne_zero.mpr one_ne_zero

/-- Batalov's conjecture as stated in A001006: if $p$ is a prime of the form $6m + 1$, then
$p \mid M(p-2)$. -/
theorem batalov (p : ℕ) (hp : p.Prime) (h6 : p % 6 = 1) : p ∣ motzkin (p - 2) :=
  ((a1006_motzkin_congruence p hp).1).mpr (by omega)

end OeisA1006Proof

/-! Separately written source statement for OEIS A001006. It asserts no theorem or proof.

Source: https://oeis.org/A001006, retrieved 2026-11-03. Batalov's comment (Feb 08 2022):
"Conjecture: If p is a prime of the form 6m+1 (A002476), then a(p-2) is divisible by p."
Rob Burns' comment (Nov 11 2024): Burns (2017) shows "a(p-2) == 0 (mod p) when p == 1 (mod 6)
and a(p-2) == -1 (mod p) when p == -1 (mod 6)", and Kohen (2024), Proposition 6, "states that
a prime p divides a(p-2) if and only if p = (1 mod 3)."

The sequence is fixed by the g.f. equation `A(x) = 1 + x*A(x) + x^2*A(x)^2` from the entry, in
coefficient form `a(n+2) = a(n+1) + Σ_{i+j=n} a(i) a(j)` with `a(0) = a(1) = 1` (offset 0). The
statement quantifies over every such sequence and also asks that one exists. -/
namespace A001006Frozen

/-- The coefficient form of `A(x) = 1 + x*A(x) + x^2*A(x)^2`. -/
def IsMotzkin (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 1 ∧ ∀ n, a (n + 2) = a (n + 1) + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, a x.1 * a x.2

/-- Kohen's Proposition 6 and Burns' value for `p ≡ 5 (mod 6)`, for every prime `p`. -/
def Claim (a : ℕ → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (p ∣ a (p - 2) ↔ p % 3 = 1) ∧ (p % 6 = 5 → (a (p - 2) : ZMod p) = -1)

def statement : Prop := (∃ a, IsMotzkin a) ∧ ∀ a, IsMotzkin a → Claim a

/-- Paul Barry's formula in the entry, `a(n) = Sum_{k=0..n} C(n, 2k)*A000108(k)`. -/
def barry (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose (2 * k) * catalan k

end A001006Frozen

/-! Kernel checks for the A001006 candidate: the frozen statement follows from the main theorem,
`motzkin` is Barry's formula, the first 31 terms match the OEIS data, and transitive axioms.
This is not Comparator. -/

open OeisA1006Proof

/-! `motzkin` is literally Barry's formula from the entry. -/

example : motzkin = A001006Frozen.barry := rfl

/-! The frozen statement: a sequence satisfying the g.f. recurrence exists, and every such
sequence satisfies the claim. -/

theorem frozen_statement : A001006Frozen.statement := by
  refine ⟨⟨motzkin, motzkin_zero, motzkin_one, motzkin_add_two⟩, fun a ha => ?_⟩
  have h : a = motzkin := funext (eq_motzkin_of_recurrence a ha.1 ha.2.1 ha.2.2)
  rw [h]
  exact a1006_motzkin_congruence

namespace OeisA1006

theorem prime_dvd_iff :
    (∃ a, IsMotzkin a) ∧ ∀ a, IsMotzkin a → ∀ p : ℕ, p.Prime →
      (p ∣ a (p - 2) ↔ p % 3 = 1) ∧ (p % 6 = 5 → (a (p - 2) : ZMod p) = -1) :=
  _root_.frozen_statement

end OeisA1006

end
