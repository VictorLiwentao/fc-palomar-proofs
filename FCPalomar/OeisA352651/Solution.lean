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
# Integrality of Bala's $u_N$ for $N \le -1$ (OEIS A352651)

This file proves `OeisA352651.u_integral`: for every integer $N \le -1$ and every $n \ge 0$,
$$u_N(n) = \frac{\binom{Nn}{2n}\binom{Nn/2}{2n}\binom{2n}{n}^2}{\binom{Nn/2}{n}^2} \in \mathbb{Z},$$
with $\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$ (`gbinom`). It also proves
`OeisA352651.denominator_ne_zero`: the denominator is nonzero. The sanity checks show
`gbinom = Ring.choose` on `ℚ`, $u_{-1}(1) = 6$, $u_{-3}(1) = 20$, and Bala's formulas
$\mathrm{A275652}(n) = \frac53 u_{-1}(n)$ and $\mathrm{A275654}(n) = \frac75 u_{-3}(n)$ for
$n = 1, 2, 3$.

The proof is elementary. Write $N = -M$ with $M \ge 1$ and $a = Mn$.

1. **Signs** (`gbinom_neg`, `gbinom_neg_half`, `gbinom_natCast`). From the definition,
   $\binom{-a}{2n} = \prod_{i<2n}(a+i)/(2n)!$, $\binom{-a/2}{k} = (-\frac12)^k \prod_{i<k}(a+2i)/k!$
   and $\binom{2n}{n} = (2n)!/n!^2$.
2. **Denominator** (`denom_prod_ne_zero`). Put $D = \prod_{i<n}(a+2i)$. Each factor is positive,
   because $a = Mn > i$ for $i < n$. So $D \ne 0$, and $\binom{-a/2}{n} = (-\frac12)^n D/n! \ne 0$.
3. **Closed form** (`u_neg_eq`). Split $\prod_{i<2n}(a+i)$ into even and odd $i$, and
   $\prod_{i<2n}(a+2i)$ into $i < n$ and $i \ge n$ (`prod_range_two_mul`, `prod_range_add`).
   Each product contains $D$ once, and the powers of $2$ and the factorials cancel:
   $$u_{-M}(n) = \frac{\prod_{j<n}(a+1+2j)\,\prod_{j<n}(a+2n+2j)}{n!^2}.$$
4. **Integrality** (`factorial_mul_factorial_dvd`). Exactly one of $a+1$ and $a+2n$ is even.
   The product that starts at the even number $2b$ equals $2^n \prod_{j<n}(b+j)$, and $n!$
   divides the ascending factorial $\prod_{j<n}(b+j)$. The other product satisfies
   $n! \mid 2^n \prod_{j<n}(c+2j)$ (`factorial_dvd_two_pow_mul_prod`, valid for every $c$).
   So $n!^2$ divides the numerator in `ℕ`, and the quotient is $u_{-M}(n)$.
5. **The lemma** $n! \mid 2^n g(c, n)$ with $g(c,n) = \prod_{j<n}(c+2j)$, by induction on $c$
   and $n$. For $c = 0$ and $n \ge 1$ the product is $0$. For $c = 1$,
   $2^n n!\, g(1,n) = (2n)!$ and $n!^2 \mid (2n)!$. For the step,
   $g(c+2, n+1) = g(c, n+1) + 2(n+1)\, g(c+2, n)$.

Equivalently, $u_{-M}(n) = 4^n \binom{(a+1)/2+n-1}{n}\binom{a/2+2n-1}{n}$: one binomial has an
integer top and the other a half-integer top. This argument does not use the informal proof's
rewriting $u_{-M}(n) = \frac{K}{K+2}\,w(n)$ with $K = M + 2$ or its step-function bounds.
-/

@[expose] public section

namespace OeisA352651

open Finset

/-- The generalized binomial coefficient $\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$ for rational
$x$ and an integer $k \ge 0$. -/
def gbinom (x : ℚ) (k : ℕ) : ℚ := (∏ i ∈ range k, (x - i)) / k.factorial

/-- Bala's $u_N(n) = \binom{Nn}{2n}\binom{Nn/2}{2n}\binom{2n}{n}^2 / \binom{Nn/2}{n}^2$, with the
binomials read as `gbinom`. -/
def u (N : ℤ) (n : ℕ) : ℚ :=
  gbinom (N * n) (2 * n) * gbinom (N * n / 2) (2 * n) * gbinom (2 * n) n ^ 2 /
    gbinom (N * n / 2) n ^ 2

/-- `gbinom` agrees with Mathlib's `Ring.choose` on `ℚ`. -/
theorem gbinom_eq_ringChoose (x : ℚ) (k : ℕ) : gbinom x k = Ring.choose x k := by
  rw [Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def,
    Polynomial.eval₂_eq_eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range,
    smul_eq_mul, gbinom, div_eq_inv_mul]

/-- On natural numbers `gbinom` is the usual binomial coefficient. -/
theorem gbinom_natCast (m k : ℕ) : gbinom m k = m.choose k := by
  rw [gbinom_eq_ringChoose, Ring.choose_natCast]

/-- $u_{-1}(1) = 6$. -/
theorem u_neg_one_one : u (-1) 1 = 6 := by
  norm_num [u, gbinom, Finset.prod_range_succ]

/-- $u_{-3}(1) = 20$. -/
theorem u_neg_three_one : u (-3) 1 = 20 := by
  norm_num [u, gbinom, Finset.prod_range_succ]

/-- Bala's formula $\mathrm{A275652}(n) = \frac53 u_{-1}(n)$ for $n = 1, 2, 3$, with the OEIS
terms $10, 300, 11440$. -/
theorem a275652_check :
    5 / 3 * u (-1) 1 = 10 ∧ 5 / 3 * u (-1) 2 = 300 ∧ 5 / 3 * u (-1) 3 = 11440 := by
  norm_num [u, gbinom, Finset.prod_range_succ, Nat.factorial]

/-- Bala's formula $\mathrm{A275654}(n) = \frac75 u_{-3}(n)$ for $n = 1, 2, 3$, with the OEIS
terms $28, 2646, 316540$. -/
theorem a275654_check :
    7 / 5 * u (-3) 1 = 28 ∧ 7 / 5 * u (-3) 2 = 2646 ∧ 7 / 5 * u (-3) 3 = 316540 := by
  norm_num [u, gbinom, Finset.prod_range_succ, Nat.factorial]

/-- $n! \mid 2^n\, c(c+2)\cdots(c+2n-2)$ for every $c \ge 0$. -/
theorem factorial_dvd_two_pow_mul_prod :
    ∀ c n : ℕ, n.factorial ∣ 2 ^ n * ∏ j ∈ range n, (c + 2 * j)
  | 0, 0 => by simp
  | 0, n + 1 => by
    rw [prod_eq_zero (mem_range.2 n.succ_pos) (by simp)]
    simp
  | 1, n => by
    have key : ∀ n : ℕ, 2 ^ n * n.factorial * ∏ j ∈ range n, (1 + 2 * j) = (2 * n).factorial := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ (2 * n + 1),
          Nat.factorial_succ (2 * n), ← ih, prod_range_succ, Nat.factorial_succ n]
        ring
    have h := Nat.factorial_mul_factorial_dvd_factorial_add n n
    rw [← two_mul, ← key, mul_comm (2 ^ n), mul_assoc] at h
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.factorial_pos n) h
  | c + 2, 0 => by simp
  | c + 2, n + 1 => by
    have h1 := factorial_dvd_two_pow_mul_prod c (n + 1)
    have h2 := factorial_dvd_two_pow_mul_prod (c + 2) n
    have e1 : ∏ j ∈ range (n + 1), (c + 2 * j) = (∏ j ∈ range n, (c + 2 + 2 * j)) * c := by
      rw [prod_range_succ']
      simp only [mul_zero, add_zero]
      congr 1
      exact prod_congr rfl fun j _ => by ring
    rw [prod_range_succ]
    have e2 : 2 ^ (n + 1) * ((∏ j ∈ range n, (c + 2 + 2 * j)) * (c + 2 + 2 * n)) =
        2 ^ (n + 1) * ∏ j ∈ range (n + 1), (c + 2 * j) +
          (n + 1) * (4 * (2 ^ n * ∏ j ∈ range n, (c + 2 + 2 * j))) := by
      rw [e1]; ring
    rw [e2, Nat.factorial_succ]
    exact dvd_add (dvd_trans (by rw [Nat.factorial_succ]) h1)
      (mul_dvd_mul_left _ (dvd_mul_of_dvd_right h2 _))

/-- $\binom{-x}{k} = (-1)^k\, x(x+1)\cdots(x+k-1)/k!$. -/
theorem gbinom_neg (x : ℚ) (k : ℕ) :
    gbinom (-x) k = (-1) ^ k * (∏ i ∈ range k, (x + i)) / k.factorial := by
  unfold gbinom
  congr 1
  rw [show ((-1 : ℚ)) ^ k = ∏ _i ∈ range k, (-1 : ℚ) by simp, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by ring

/-- $\binom{-x/2}{k} = (-\frac12)^k\, x(x+2)\cdots(x+2k-2)/k!$. -/
theorem gbinom_neg_half (x : ℚ) (k : ℕ) :
    gbinom (-x / 2) k = (-1 / 2) ^ k * (∏ i ∈ range k, (x + 2 * i)) / k.factorial := by
  unfold gbinom
  congr 1
  rw [show ((-1 / 2 : ℚ)) ^ k = ∏ _i ∈ range k, (-1 / 2 : ℚ) by rw [prod_const, card_range],
    ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by ring

/-- A product over $i < 2n$ splits into even and odd $i$. -/
theorem prod_range_two_mul {β : Type*} [CommMonoid β] (f : ℕ → β) (n : ℕ) :
    ∏ i ∈ range (2 * n), f i = (∏ i ∈ range n, f (2 * i)) * ∏ i ∈ range n, f (2 * i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ, prod_range_succ]
    ac_rfl

/-- For $M \ge 1$, the product $\prod_{i<n} (Mn + 2i)$ is nonzero. -/
theorem denom_prod_ne_zero (M n : ℕ) (hM : 0 < M) : ∏ i ∈ range n, ((M : ℚ) * n + 2 * i) ≠ 0 := by
  refine prod_ne_zero_iff.2 fun i hi => ne_of_gt ?_
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i) (mem_range.1 hi)
  have : (0 : ℚ) < M * n := mul_pos (by exact_mod_cast hM) (by exact_mod_cast hn)
  positivity

/-- The closed form $u_{-M}(n) = \prod_{j<n} (Mn + 1 + 2j) \prod_{j<n} (Mn + 2n + 2j) / n!^2$. -/
theorem u_neg_eq (M n : ℕ) (hM : 0 < M) :
    u (-M) n = ((∏ j ∈ range n, (M * n + 1 + 2 * j) : ℕ) : ℚ) *
      ((∏ j ∈ range n, (M * n + 2 * n + 2 * j) : ℕ) : ℚ) / (n.factorial : ℚ) ^ 2 := by
  have hD := denom_prod_ne_zero M n hM
  have hA : ∏ i ∈ range (2 * n), ((M : ℚ) * n + i) =
      (∏ i ∈ range n, ((M : ℚ) * n + 2 * i)) * ∏ i ∈ range n, ((M : ℚ) * n + 1 + 2 * i) := by
    rw [prod_range_two_mul]
    push_cast
    congr 1
    exact prod_congr rfl fun i _ => by ring
  have hB : ∏ i ∈ range (2 * n), ((M : ℚ) * n + 2 * i) =
      (∏ i ∈ range n, ((M : ℚ) * n + 2 * i)) * ∏ i ∈ range n, ((M : ℚ) * n + 2 * n + 2 * i) := by
    rw [two_mul, prod_range_add]
    push_cast
    congr 1
    exact prod_congr rfl fun i _ => by ring
  have hC : gbinom (2 * n) n = (2 * n).factorial / (n.factorial * n.factorial) := by
    rw [show (2 * n : ℚ) = ((2 * n : ℕ) : ℚ) by push_cast; ring, gbinom_natCast,
      Nat.cast_choose ℚ (by omega : n ≤ 2 * n), show 2 * n - n = n by omega]
  unfold u
  rw [show ((-(M : ℤ) : ℤ) : ℚ) * n = -((M : ℚ) * n) by push_cast; ring,
    gbinom_neg, gbinom_neg_half, gbinom_neg_half, hA, hB, hC, pow_mul, neg_one_sq, one_pow]
  push_cast
  have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- The numerator of the closed form is divisible by $n!^2$:
$n!^2 \mid \prod_{j<n} (a + 1 + 2j) \prod_{j<n} (a + 2n + 2j)$. -/
theorem factorial_mul_factorial_dvd (a n : ℕ) :
    n.factorial * n.factorial ∣
      (∏ j ∈ range n, (a + 1 + 2 * j)) * ∏ j ∈ range n, (a + 2 * n + 2 * j) := by
  have even_prod : ∀ b, ∏ j ∈ range n, (2 * b + 2 * j) = 2 ^ n * ∏ j ∈ range n, (b + j) := by
    intro b
    rw [show 2 ^ n = ∏ _j ∈ range n, 2 by simp, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ => by ring
  have hasc : ∀ b, n.factorial ∣ ∏ j ∈ range n, (b + j) := fun b => by
    rw [← Nat.ascFactorial_eq_prod_range]; exact Nat.factorial_dvd_ascFactorial b n
  rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  · have e : ∏ j ∈ range n, (a + 2 * n + 2 * j) = 2 ^ n * ∏ j ∈ range n, (b + n + j) := by
      rw [← even_prod]; exact prod_congr rfl fun j _ => by omega
    rw [e]
    convert mul_dvd_mul (factorial_dvd_two_pow_mul_prod (a + 1) n) (hasc (b + n)) using 1
    ring
  · have e : ∏ j ∈ range n, (a + 1 + 2 * j) = 2 ^ n * ∏ j ∈ range n, (b + 1 + j) := by
      rw [← even_prod]; exact prod_congr rfl fun j _ => by omega
    rw [e]
    convert mul_dvd_mul (hasc (b + 1)) (factorial_dvd_two_pow_mul_prod (a + 2 * n) n) using 1
    ring

/-- For $N \le -1$ and $n \ge 0$, the binomial $\binom{Nn/2}{n}$ in the denominator of $u_N(n)$
is nonzero. -/
theorem denominator_ne_zero (N : ℤ) (hN : N ≤ -1) (n : ℕ) : gbinom (N * n / 2) n ≠ 0 := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = -M := ⟨N.natAbs, by omega⟩
  rw [show ((-(M : ℤ) : ℤ) : ℚ) * n / 2 = -((M : ℚ) * n) / 2 by push_cast; ring, gbinom_neg_half]
  have hD := denom_prod_ne_zero M n (by omega)
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hD) h1

/-- **Bala's conjecture for $N \le -1$, integrality.** For every integer $N \le -1$ and every
$n \ge 0$, $u_N(n)$ is an integer. -/
theorem u_integral (N : ℤ) (hN : N ≤ -1) (n : ℕ) : ∃ m : ℤ, u N n = m := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = -M := ⟨N.natAbs, by omega⟩
  obtain ⟨q, hq⟩ := factorial_mul_factorial_dvd (M * n) n
  refine ⟨q, ?_⟩
  rw [u_neg_eq M n (by omega), ← Nat.cast_mul, hq]
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

end OeisA352651

end
