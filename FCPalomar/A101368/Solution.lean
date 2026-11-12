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
# Pairs with $i \mid 1 + j + j^2$ and $j \mid 1 + i + i^2$

OEIS A101368 is $1, 1, 3, 13, 61, 291, \dots$: the pairs $(a(n), a(n+1))$, $n \ge 1$, solve the
problem of W. W. Chao (Crux Mathematicorum Problem 2981, 2004): find all pairs of positive integers
$(i, j)$ with $i \mid 1 + j + j^2$ and $j \mid 1 + i + i^2$. Ralf Stephan conjectured (2005) the
generating function $x(1 - 5x + 3x^2)/((1-x)(1 - 5x + x^2))$, and Max Alekseyev proved it
(2006).

This file proves that the positive solutions are exactly the pairs $(a(n), a(n+1))$, $n \ge 1$,
in either order (the pair $(3, 1)$ is a solution, so the order matters), where $a(1) = a(2) = 1$
and $a(n+2) = 5a(n+1) - a(n) - 1$. It also proves that $a(n)$, $n \ge 1$, are the coefficients of
Stephan's generating function.

The proof is Vieta jumping. A solution with $i > j$ gives the smaller solution $(j, i')$ with
$i' = (j^2 + j + 1)/i \le j$, and the descent ends at $(1, 1)$. Along the way
$i^2 + j^2 + i + j + 1 = 5ij$, so $i = 5j - i' - 1$, which is the recurrence.

*References:*
- [A101368](https://oeis.org/A101368)
- W. W. Chao, Problem 2981, *Crux Mathematicorum* 30 (2004), p. 430.
- M. A. Alekseyev and D. I. Khomovsky, Congruence Jumping in Polynomial Divisibility Systems,
  [arXiv:2610.00808](https://arxiv.org/abs/2610.00808), 2026, Example 7.1.
-/

@[expose] public section

namespace OeisA101368

open PowerSeries

/-- The coefficient of $x^n$ in Stephan's generating function
$x(1 - 5x + 3x^2)/((1 - x)(1 - 5x + x^2))$. -/
noncomputable def c (n : ℕ) : ℚ :=
  coeff n (X * (1 - 5 * X + 3 * X ^ 2) * ((1 - X) * (1 - 5 * X + X ^ 2))⁻¹ : ℚ⟦X⟧)

end OeisA101368

namespace OeisA101368

/-- $a(n)$ with $a(1) = a(2) = 1$ and $a(n+2) = 5a(n+1) - a(n) - 1$. The value $a(0) = 3$ extends
the recurrence backwards; the OEIS offset is $1$. -/
def a : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | n + 2 => 5 * a (n + 1) - a n - 1

/-- Consecutive terms, in either order. -/
def Consec (i j : ℕ) : Prop :=
  ∃ n, 1 ≤ n ∧ (((i : ℤ) = a n ∧ (j : ℤ) = a (n + 1)) ∨ ((j : ℤ) = a n ∧ (i : ℤ) = a (n + 1)))

/-- The positive solutions of $i \mid 1 + j + j^2$, $j \mid 1 + i + i^2$ are the pairs of
consecutive terms $(a(n), a(n+1))$, $n \ge 1$, in either order. -/
def Target : Prop :=
  ∀ i j : ℕ, (0 < i ∧ 0 < j ∧ i ∣ 1 + j + j ^ 2 ∧ j ∣ 1 + i + i ^ 2) ↔ Consec i j

theorem a_add_two (n : ℕ) : a (n + 2) = 5 * a (n + 1) - a n - 1 := rfl

theorem a_add_three (n : ℕ) : a (n + 3) = 6 * a (n + 2) - 6 * a (n + 1) + a n := by
  have h1 : a (n + 3) = 5 * a (n + 2) - a (n + 1) - 1 := rfl
  have h2 := a_add_two n
  linarith

/-- The Markov-type invariant $a(n)^2 + a(n+1)^2 + a(n) + a(n+1) + 1 = 5 a(n) a(n+1)$. -/
theorem a_invariant (n : ℕ) :
    a n ^ 2 + a (n + 1) ^ 2 + a n + a (n + 1) + 1 = 5 * a n * a (n + 1) := by
  induction n with
  | zero => norm_num [a]
  | succ n ih =>
    rw [show a (n + 1 + 1) = 5 * a (n + 1) - a n - 1 from rfl]
    linear_combination ih

/-- For $n \ge 1$: $1 \le a(n) \le a(n+1)$. -/
theorem one_le_a_and_le (n : ℕ) : 1 ≤ a (n + 1) ∧ a (n + 1) ≤ a (n + 2) := by
  induction n with
  | zero => norm_num [a]
  | succ n ih =>
    refine ⟨ih.1.trans ih.2, ?_⟩
    show a (n + 2) ≤ 5 * a (n + 2) - a (n + 1) - 1
    linarith [ih.1, ih.2]

theorem consec_comm {i j : ℕ} : Consec i j ↔ Consec j i := by
  constructor <;> rintro ⟨n, hn, h | h⟩ <;> exact ⟨n, hn, by tauto⟩

/-- Consecutive terms solve the problem. -/
theorem solution_of_consec {i j : ℕ} (h : Consec i j) :
    0 < i ∧ 0 < j ∧ i ∣ 1 + j + j ^ 2 ∧ j ∣ 1 + i + i ^ 2 := by
  have key : ∀ x y : ℕ, ∀ n, 1 ≤ n → (x : ℤ) = a n → (y : ℤ) = a (n + 1) →
      0 < x ∧ 0 < y ∧ x ∣ 1 + y + y ^ 2 ∧ y ∣ 1 + x + x ^ 2 := by
    intro x y n hn hx hy
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hpos := one_le_a_and_le m
    have hpos' := one_le_a_and_le (m + 1)
    have hinv := a_invariant (m + 1)
    rw [← hx, ← hy] at hinv
    have hx1 : (1 : ℤ) ≤ x := by rw [hx]; exact hpos.1
    have hy1 : (1 : ℤ) ≤ y := by rw [hy]; exact hpos'.1
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [← Int.natCast_dvd_natCast]
      push_cast
      exact ⟨5 * (y : ℤ) - x - 1, by linear_combination hinv⟩
    · rw [← Int.natCast_dvd_natCast]
      push_cast
      exact ⟨5 * (x : ℤ) - y - 1, by linear_combination hinv⟩
  obtain ⟨n, hn, ⟨hi, hj⟩ | ⟨hj, hi⟩⟩ := h
  · exact key i j n hn hi hj
  · obtain ⟨h1, h2, h3, h4⟩ := key j i n hn hj hi
    exact ⟨h2, h1, h4, h3⟩

/-- A common divisor of $i$ and $j$ divides $1$. -/
theorem coprime_of_dvd {i j : ℕ} (hi : i ∣ 1 + j + j ^ 2) : Nat.Coprime i j := by
  have hg : Nat.gcd i j ∣ 1 + j + j ^ 2 := (Nat.gcd_dvd_left i j).trans hi
  have hg' : Nat.gcd i j ∣ j + j ^ 2 := (Nat.gcd_dvd_right i j).trans ⟨1 + j, by ring⟩
  rw [show 1 + j + j ^ 2 = j + j ^ 2 + 1 by ring] at hg
  exact Nat.dvd_one.mp ((Nat.dvd_add_right hg').mp hg)

/-- Vieta jumping: every solution satisfies $i^2 + j^2 + i + j + 1 = 5ij$ and consists of
consecutive terms. -/
theorem descent (s : ℕ) : ∀ i j : ℕ, i + j = s → i ∣ 1 + j + j ^ 2 → j ∣ 1 + i + i ^ 2 →
    ((i : ℤ) ^ 2 + j ^ 2 + i + j + 1 = 5 * i * j ∧ Consec i j) := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro i j hs hi hj
  wlog hji : j ≤ i generalizing i j with H
  · obtain ⟨h1, h2⟩ := H j i (by omega) hj hi (by omega)
    exact ⟨by linear_combination h1, consec_comm.mp h2⟩
  rcases Nat.lt_or_ge j i with hlt | hge
  · -- descent step
    have hj0 : 0 < j := Nat.pos_of_ne_zero fun h0 => by
      subst h0
      exact absurd (Nat.eq_zero_of_zero_dvd hj) (by positivity)
    obtain ⟨i', hii'⟩ := hi
    have hi'0 : 0 < i' := Nat.pos_of_ne_zero fun h0 => by
      have h : 0 < 1 + j + j ^ 2 := by positivity
      rw [hii', h0, mul_zero] at h
      exact lt_irrefl 0 h
    have hi'j : i' ≤ j := by
      by_contra hc
      have h := Nat.mul_le_mul (show j + 1 ≤ i by omega) (show j + 1 ≤ i' by omega)
      nlinarith
    have hcop := coprime_of_dvd ⟨i', hii'⟩
    -- `j ∣ 1 + i' + i'^2`
    have hj' : j ∣ 1 + i' + i' ^ 2 := by
      have hz : ((i ^ 2 * (1 + i' + i' ^ 2) : ℕ) : ℤ) =
          ((1 + i + i ^ 2 + j * ((j + 1) * (j ^ 2 + j + 2) + (j + 1) * i) : ℕ) : ℤ) := by
        have hii'z : ((1 + j + j ^ 2 : ℕ) : ℤ) = ((i * i' : ℕ) : ℤ) := by rw [hii']
        push_cast at hii'z ⊢
        linear_combination (-(i : ℤ) * i' - (1 + j + j ^ 2) - i) * hii'z
      have hnat := Nat.cast_injective hz
      have hdvd : j ∣ (1 + i' + i' ^ 2) * i ^ 2 := by
        rw [mul_comm, hnat]
        exact dvd_add hj (dvd_mul_right j _)
      exact (Nat.Coprime.pow_right 2 hcop.symm).dvd_of_dvd_mul_right hdvd
    obtain ⟨heq, hcon⟩ := ih (j + i') (by omega) j i' rfl hj' ⟨i, by rw [hii']; ring⟩
    -- `i = 5 j - i' - 1`
    have hii'z : ((1 + j + j ^ 2 : ℕ) : ℤ) = ((i * i' : ℕ) : ℤ) := by rw [hii']
    push_cast at hii'z
    have hival : (i : ℤ) = 5 * j - i' - 1 := by
      have hne : (i' : ℤ) ≠ 0 := by exact_mod_cast hi'0.ne'
      apply mul_right_cancel₀ hne
      linear_combination heq - hii'z
    refine ⟨by rw [hival]; linear_combination heq, ?_⟩
    -- consecutive terms
    obtain ⟨m, hm, h | h⟩ := hcon
    · -- `(j, i') = (a m, a (m + 1))`: then `j = i'`
      have hle : a m ≤ a (m + 1) := by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        exact (one_le_a_and_le k).2
      have hjeq : (j : ℤ) = i' := le_antisymm (by rw [h.1, h.2]; exact hle) (by exact_mod_cast hi'j)
      refine ⟨m + 1, by omega, Or.inr ⟨?_, ?_⟩⟩
      · rw [hjeq]
        exact h.2
      · rw [hival, show a (m + 1 + 1) = 5 * a (m + 1) - a m - 1 from rfl, ← h.1, ← h.2]
        linarith [hjeq]
    · -- `(i', j) = (a m, a (m + 1))`
      refine ⟨m + 1, by omega, Or.inr ⟨h.2, ?_⟩⟩
      rw [hival, show a (m + 1 + 1) = 5 * a (m + 1) - a m - 1 from rfl, ← h.1, ← h.2]
  · -- `i = j` forces `i = j = 1`
    obtain rfl : i = j := le_antisymm hge hji
    obtain rfl := (Nat.coprime_self _).mp (coprime_of_dvd hi)
    exact ⟨by norm_num, 1, le_rfl, Or.inl ⟨by simp [a], by simp [a]⟩⟩

/-- **OEIS A101368** (Chao's problem; Stephan's conjecture proved by Alekseyev). -/
theorem a101368_solutions : Target := by
  intro i j
  constructor
  · rintro ⟨-, -, hi, hj⟩
    exact (descent (i + j) i j rfl hi hj).2
  · exact solution_of_consec

/-! ## Stephan's generating function -/

open PowerSeries in
/-- $\sum_{n \ge 1} a(n) x^n = x(1 - 5x + 3x^2)/((1-x)(1 - 5x + x^2))$: the coefficient of $x^n$
in the generating function is $a(n)$ for $n \ge 1$. -/
theorem coeff_genFun {n : ℕ} (hn : 1 ≤ n) :
    coeff n (X * (1 - 5 * X + 3 * X ^ 2) * ((1 - X) * (1 - 5 * X + X ^ 2))⁻¹ : ℚ⟦X⟧) =
      (a n : ℚ) := by
  set A : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else (a n : ℚ) with hA
  set D : ℚ⟦X⟧ := (1 - X) * (1 - 5 * X + X ^ 2) with hD
  have hAD : A * D = X * (1 - 5 * X + 3 * X ^ 2) := by
    have e : A * D = A - C (6 : ℚ) * (X ^ 1 * A) + C (6 : ℚ) * (X ^ 2 * A) - X ^ 3 * A := by
      rw [hD]
      simp only [map_ofNat]
      ring
    have e' : (X : ℚ⟦X⟧) * (1 - 5 * X + 3 * X ^ 2) =
        X ^ 1 - C (5 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e, e']
    ext k
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, hA, coeff_mk]
    rcases Nat.lt_or_ge k 4 with hk | hk
    · interval_cases k <;> norm_num [a]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
      have h := a_add_three (j + 1)
      rw [show j + 1 + 3 = j + 4 by ring, show j + 1 + 2 = j + 3 by ring,
        show j + 1 + 1 = j + 2 by ring] at h
      have hq : (a (j + 4) : ℚ) = 6 * a (j + 3) - 6 * a (j + 2) + a (j + 1) := by
        exact_mod_cast h
      rw [ite_eq_right (show j + 4 ≠ 0 by omega), ite_eq_left (show 1 ≤ j + 4 by omega),
        ite_eq_left (show 2 ≤ j + 4 by omega), ite_eq_left (show 3 ≤ j + 4 by omega),
        ite_eq_right (show j + 4 - 1 ≠ 0 by omega), ite_eq_right (show j + 4 - 2 ≠ 0 by omega),
        ite_eq_right (show j + 4 - 3 ≠ 0 by omega), ite_eq_right (show j + 4 ≠ 1 by omega),
        ite_eq_right (show j + 4 ≠ 2 by omega), ite_eq_right (show j + 4 ≠ 3 by omega),
        show j + 4 - 1 = j + 3 by omega, show j + 4 - 2 = j + 2 by omega,
        show j + 4 - 3 = j + 1 by omega]
      linarith
  have hDinv : D * D⁻¹ = 1 := PowerSeries.mul_inv_cancel D (by simp [hD])
  calc coeff n (X * (1 - 5 * X + 3 * X ^ 2) * D⁻¹) = coeff n (A * (D * D⁻¹)) := by
        rw [← hAD, mul_assoc]
    _ = (a n : ℚ) := by
        simp only [hDinv, mul_one, hA, coeff_mk, ite_eq_right (show n ≠ 0 by omega)]

end OeisA101368

/-! Separately written source statement for OEIS A101368. It asserts no theorem or proof.

Source: https://oeis.org/A101368, retrieved 2026-11-03 (revision `#48`). Name: "The sequence
solves the following problem: find all the pairs (i,j) such that i divides 1+j+j^2 and j divides
1+i+i^2. In fact, the pairs (a(n),a(n+1)), n>0, are all the solutions." Formula: "G.f.: x(1 - 5x
+ 3x^2) / [(1-x)(1 - 5x + x^2)] ... - Conjectured by Ralf Stephan, Jan 14 2005, proved by Max
Alekseyev, Aug 03 2006". Offset 1.

The pairs are of positive integers (Chao's problem; Alekseyev–Khomovsky's "positive states").
Since `(3, 1)` is a solution while `(1, 3) = (a(2), a(3))`, the pairs are taken in either order.
The terms `a(n)` are the coefficients of Stephan's generating function. -/
namespace A101368Frozen
open PowerSeries

/-- The coefficient of `x^n` in `x(1 - 5x + 3x^2) / ((1 - x)(1 - 5x + x^2))`. -/
noncomputable def c (n : ℕ) : ℚ :=
  coeff n (X * (1 - 5 * X + 3 * X ^ 2) * ((1 - X) * (1 - 5 * X + X ^ 2))⁻¹ : ℚ⟦X⟧)

/-- The positive solutions of `i ∣ 1 + j + j^2`, `j ∣ 1 + i + i^2` are exactly the pairs
`(c n, c (n + 1))`, `n ≥ 1`, in either order. -/
def statement : Prop :=
  ∀ i j : ℕ, (0 < i ∧ 0 < j ∧ i ∣ 1 + j + j ^ 2 ∧ j ∣ 1 + i + i ^ 2) ↔
    ∃ n : ℕ, 1 ≤ n ∧
      (((i : ℚ) = c n ∧ (j : ℚ) = c (n + 1)) ∨ ((j : ℚ) = c n ∧ (i : ℚ) = c (n + 1)))

end A101368Frozen

/-! Kernel checks for the A101368 candidate: the frozen statement (with Stephan's generating
function) follows from the main theorem, the first 28 terms match the OEIS data, and transitive
axioms. This is not Comparator. -/

open OeisA101368

theorem frozen_statement : A101368Frozen.statement := by
  intro i j
  rw [a101368_solutions i j]
  unfold Consec
  refine exists_congr fun n => and_congr_right fun hn => ?_
  have hc : ∀ m, 1 ≤ m → A101368Frozen.c m = (a m : ℚ) := fun m hm => coeff_genFun hm
  have e : ∀ (x : ℕ) (y : ℤ), ((x : ℚ) = (y : ℚ)) ↔ ((x : ℤ) = y) := fun x y => by
    constructor <;> intro h <;> exact_mod_cast h
  rw [hc n hn, hc (n + 1) (by omega), e, e, e, e]

namespace OeisA101368

open PowerSeries

theorem solutions_iff :
    ∀ i j : ℕ, (0 < i ∧ 0 < j ∧ i ∣ 1 + j + j ^ 2 ∧ j ∣ 1 + i + i ^ 2) ↔
      ∃ n : ℕ, 1 ≤ n ∧
        (((i : ℚ) = c n ∧ (j : ℚ) = c (n + 1)) ∨ ((j : ℚ) = c n ∧ (i : ℚ) = c (n + 1))) :=
  _root_.frozen_statement

end OeisA101368

end
