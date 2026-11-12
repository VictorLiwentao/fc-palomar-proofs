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
# Arithmetic mean of $(21k+8)\binom{2k}{k}^3$

OEIS A173774 is $a(n) = \frac{1}{n} \sum_{k=0}^{n-1} (21k+8) \binom{2k}{k}^3$ for $n \ge 1$.
Zhi-Wei Sun conjectured (2010) that every $a(n)$ is an integer divisible by
$4 \binom{2n}{n}$. Kasper Andersen confirmed it by identifying $a(n) / (4 \binom{2n}{n})$ with
OEIS A112029, $b(m) = \sum_{k=0}^{m} \binom{m+k}{k}^2$ at $m = n - 1$.

This file proves $a(n) = 4 \binom{2n}{n} b(n-1)$ for $n \ge 1$, which gives the conjecture.
The key step is the recurrence $8(2m+1) b(m) = (21m+8) \binom{2m}{m}^2 + 4m\, b(m-1)$. It
follows by summing over $k$ the telescoping identity
$$8(2m+1) F(m,k) - 4m F(m-1,k) = G(m,k+1) - G(m,k)$$
with $F(m,k) = \binom{m+k}{k}^2$ and $G(m,k) = (8k+12m) \binom{m+k-1}{k-1}^2$.

*References:*
- [A173774](https://oeis.org/A173774)
- [A112029](https://oeis.org/A112029)
- Zhi-Wei Sun, "A somewhat surprising conjecture", NMBRTHRY mailing list, February 2010.
- Kasper Andersen, "Re: A somewhat surprising conjecture", NMBRTHRY mailing list,
  February 2010.
-/

@[expose] public section

namespace OeisA173774

/-- $a(n) = \frac{1}{n} \sum_{k=0}^{n-1} (21k+8)\binom{2k}{k}^3$, for $n \ge 1$. The sum is a
natural number and the division is in $\mathbb{Q}$. -/
def a (n : ℕ) : ℚ := ((∑ k ∈ Finset.range n, (21 * k + 8) * (2 * k).choose k ^ 3 : ℕ) : ℚ) / n

end OeisA173774

namespace OeisA173774

open Finset



/-- Every $a(n)$ with $n \ge 1$ is an integer divisible by $4 \binom{2n}{n}$. -/
def Target : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, a n = z ∧ 4 * ((2 * n).choose n : ℤ) ∣ z

/-- $b(m) = \sum_{k=0}^{m} \binom{m+k}{k}^2$, OEIS A112029. -/
def b (m : ℕ) : ℕ := ∑ k ∈ range (m + 1), (m + k).choose k ^ 2

/-! ## The telescoping certificate, with $m = j + 1$ -/

/-- The summand $8(2m+1) F(m,k) - 4m F(m-1,k)$ at $m = j + 1$. -/
def term (j k : ℕ) : ℚ :=
  8 * (2 * j + 3) * ((j + 1 + k).choose k : ℚ) ^ 2 - 4 * (j + 1) * ((j + k).choose k : ℚ) ^ 2

/-- The certificate $G(m, k+1) = (8(k+1) + 12m) \binom{m+k}{k}^2$ at $m = j + 1$. -/
def cert (j k : ℕ) : ℚ := (8 * (k + 1) + 12 * (j + 1)) * ((j + 1 + k).choose k : ℚ) ^ 2

theorem term_zero (j : ℕ) : term j 0 = cert j 0 := by
  simp only [term, cert, add_zero, Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero]
  ring

theorem term_succ (j t : ℕ) : term j (t + 1) = cert j (t + 1) - cert j t := by
  unfold term cert
  obtain ⟨n, hn⟩ : ∃ n, n = j + t + 1 := ⟨_, rfl⟩
  rw [show j + 1 + (t + 1) = n + 1 by omega, show j + (t + 1) = n by omega,
    show j + 1 + t = n by omega]
  have hY : ((n + 1).choose (t + 1) : ℚ) = (n.choose t : ℚ) * (n + 1) / (t + 1) := by
    have h : (n + 1).choose (t + 1) * (t + 1) = n.choose t * (n + 1) := by
      rw [← Nat.add_one_mul_choose_eq]
      ring
    rw [eq_div_iff (by positivity)]
    exact_mod_cast h
  have hZ : (n.choose (t + 1) : ℚ) = (n.choose t : ℚ) * (j + 1) / (t + 1) := by
    have h := Nat.choose_succ_right_eq n t
    rw [show n - t = j + 1 by omega] at h
    rw [eq_div_iff (by positivity)]
    exact_mod_cast h
  rw [hY, hZ]
  subst hn
  push_cast
  field_simp
  ring

theorem sum_term (j m : ℕ) : ∑ k ∈ range (m + 1), term j k = cert j m := by
  induction m with
  | zero => simp [term_zero]
  | succ m ih => rw [sum_range_succ, ih, term_succ]; ring

/-- $\binom{2m+2}{m+1} = 2 \binom{2m+1}{m+1}$. -/
theorem choose_two_mul_succ (m : ℕ) :
    (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1).choose (m + 1) := by
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.choose_succ_succ', Nat.choose_symm_half]
  ring

/-- The recurrence $8(2m+1) b(m) = (21m+8) \binom{2m}{m}^2 + 4m\, b(m-1)$ at $m = j + 1$. -/
theorem b_succ (j : ℕ) :
    8 * (2 * j + 3) * b (j + 1) =
      (21 * (j + 1) + 8) * (2 * (j + 1)).choose (j + 1) ^ 2 + 4 * (j + 1) * b j := by
  have h := sum_term j (j + 1)
  simp only [term, sum_sub_distrib, ← mul_sum] at h
  rw [sum_range_succ (fun k => ((j + k).choose k : ℚ) ^ 2)] at h
  have hW := choose_two_mul_succ j
  have hb1 : (b (j + 1) : ℚ) = ∑ k ∈ range (j + 1 + 1), ((j + 1 + k).choose k : ℚ) ^ 2 := by
    simp [b]
  have hb0 : (b j : ℚ) = ∑ k ∈ range (j + 1), ((j + k).choose k : ℚ) ^ 2 := by
    simp [b]
  have hc : ((j + 1 + (j + 1)).choose (j + 1) : ℚ) = ((2 * (j + 1)).choose (j + 1) : ℚ) := by
    rw [show j + 1 + (j + 1) = 2 * (j + 1) by ring]
  have hd : ((j + (j + 1)).choose (j + 1) : ℚ) = ((2 * (j + 1)).choose (j + 1) : ℚ) / 2 := by
    rw [hW, show j + (j + 1) = 2 * j + 1 by ring]
    push_cast
    ring
  rw [← hb1, ← hb0, hd] at h
  rw [cert, hc] at h
  have h' : (8 * (2 * j + 3) * b (j + 1) : ℚ) =
      (21 * (j + 1) + 8) * ((2 * (j + 1)).choose (j + 1) : ℚ) ^ 2 + 4 * (j + 1) * b j := by
    push_cast at h ⊢
    linear_combination h
  exact_mod_cast h'

/-- $\sum_{k=0}^{n-1} (21k+8) \binom{2k}{k}^3 = 4 n \binom{2n}{n}\, b(n-1)$, with $n = N + 1$. -/
theorem sum_eq (N : ℕ) :
    ∑ k ∈ range (N + 1), (21 * k + 8) * (2 * k).choose k ^ 3 =
      4 * (N + 1) * (2 * (N + 1)).choose (N + 1) * b N := by
  induction N with
  | zero => simp [b]
  | succ N ih =>
    have h := Nat.succ_mul_centralBinom_succ (N + 1)
    simp only [Nat.centralBinom_eq_two_mul_choose] at h
    rw [sum_range_succ, ih]
    calc 4 * (N + 1) * (2 * (N + 1)).choose (N + 1) * b N +
          (21 * (N + 1) + 8) * (2 * (N + 1)).choose (N + 1) ^ 3
        = (2 * (N + 1)).choose (N + 1) *
            ((21 * (N + 1) + 8) * (2 * (N + 1)).choose (N + 1) ^ 2 + 4 * (N + 1) * b N) := by
          ring
      _ = (2 * (N + 1)).choose (N + 1) * (8 * (2 * N + 3) * b (N + 1)) := by rw [b_succ]
      _ = 4 * (2 * (2 * (N + 1) + 1) * (2 * (N + 1)).choose (N + 1)) * b (N + 1) := by ring
      _ = 4 * (N + 1 + 1) * (2 * (N + 1 + 1)).choose (N + 1 + 1) * b (N + 1) := by
          rw [← h]
          ring

/-- Andersen's identity $a(n) = 4 \binom{2n}{n}\, b(n-1)$ for $n \ge 1$. -/
theorem a_succ (N : ℕ) : a (N + 1) = 4 * (2 * (N + 1)).choose (N + 1) * b N := by
  rw [a, sum_eq]
  push_cast
  field_simp

/-- **OEIS A173774 conjecture** (Sun 2010; confirmed by Andersen 2010). For every $n \ge 1$,
$a(n)$ is an integer divisible by $4 \binom{2n}{n}$. -/
theorem a173774_integral_dvd : Target := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  refine ⟨4 * ((2 * (N + 1)).choose (N + 1) : ℤ) * b N, ?_, dvd_mul_right _ _⟩
  rw [a_succ]
  push_cast
  ring

end OeisA173774

namespace OeisA173774

theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, a n = z ∧ 4 * ((2 * n).choose n : ℤ) ∣ z :=
  a173774_integral_dvd n hn

end OeisA173774

end
