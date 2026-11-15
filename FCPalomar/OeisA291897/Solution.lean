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
# Shevelev's conjectures on OEIS A291897 and A292911 (Euler polynomials at $n$)

Let $E_m(x)$ be the Euler polynomials and $E_k$ the Euler numbers. For $n \ge 1$ and
$N = 2n - 1$, this file proves that $N^2$ divides the numerator $a(n)$ of $E_N(n)$
(`a291897_conjecture`, Shevelev's A291897 conjecture), and that $N^3 \mid a(n)$ if and only if
$N \mid E_{N-1}$ (`a291897_cube_dvd_iff`). With Ely's congruence for $E_{p-1} \bmod p$ this gives,
for an odd prime $p$, $p^3 \mid a((p+1)/2)$ if and only if $p \equiv 1 \pmod 4$
(`prime_cube_dvd_num_iff`, `prime_mem_a292911_iff`), and hence Shevelev's A292911 conjecture
(`a292911_conjecture`).

1. **E.g.f.s** (`egf_mul`, `eulerPoly_egf`, `eulerNum_egf`). The product of two e.g.f.s is the
   e.g.f. of the binomial convolution. So the defining recurrences are the coefficient forms of
   $\bigl(\sum_m E_m(x)\, t^m/m!\bigr)(e^t + 1) = 2e^{xt}$ and
   $S(t)\,(e^t + e^{-t}) = 2$, where $S(t) = \sum_k E_k\, t^k/k!$. Strong induction on the
   recurrence gives $E_k = 0$ for odd $k$ (`eulerNum_odd`).
2. **The sums $A_m$** (`eulerA`, `eulerAZ`). Put $A_m(y) = \sum_k \binom mk E_k y^{m-k}$. Its
   e.g.f. is $S(t)\, e^{yt}$ (`egf_eulerA`). For $a \in \mathbb{Z}$, $A_m(a)$ is an integer.
3. **Shift** (`eulerA_add_two`). $e^{(y+2)t} + e^{yt} = e^{(y+1)t}(e^t + e^{-t})$ and
   $S(t)(e^t + e^{-t}) = 2$ give $A_m(y+2) + A_m(y) = 2(y+1)^m$.
4. **Expansion about $1/2$** (`two_pow_mul_eval_eulerPoly`). $2^m E_m(x) = A_m(2x - 1)$, the
   classical expansion DLMF 24.2.10 (with $E_m = 2^m E_m(1/2)$, DLMF 24.2.9). The e.g.f. of
   $A_m(2x-1)/2^m$ is $S(t/2)\, e^{(2x-1)t/2}$. Its product with
   $e^t + 1 = e^{t/2}(e^{t/2} + e^{-t/2})$ is $2e^{xt}$. By step 1 the e.g.f. of $E_m(x)$
   satisfies the same equation. Cancel $e^t + 1$ in the domain $\mathbb{Q}[[t]]$. Hence
   $E_m((a+1)/2) = A_m(a)/2^m$ for $a \in \mathbb{Z}$ (`eval_eulerPoly_half`).
5. **A291897** (`eulerAZ_odd_self`). Let $N = 2j + 1$ and $n = j + 1$. Then
   $E_N(n) = A_N(N)/2^N$. The term $k = N$ of $A_N(N)$ vanishes and the term $k = N - 1$ is
   $N^2 E_{N-1}$. Each term $k < N - 1$ is divisible by $N^3$: $E_k = 0$ for odd $k$, and
   $N - k \ge 3$ for even $k$. So $A_N(N) \equiv N^2 E_{N-1} \pmod{N^3}$.
6. **Numerators** (`odd_dvd_num_div_two_pow_iff`). For odd $d$ and $q = A/2^s$,
   $d \mid \operatorname{num} q \iff d \mid A$. This uses $\operatorname{num} q \cdot 2^s = A
   \cdot \operatorname{den} q$ and $\operatorname{den} q \mid 2^s$. With step 5 it gives
   `a291897_conjecture` and `a291897_cube_dvd_iff`.
7. **Ely's congruence** (`eulerNum_prime_sub_one`). Let $p = 2h + 1$ be prime, $m = p - 1$ and
   $f(j) = A_m(2j) \bmod p$. By step 3 and Fermat's little theorem, $f(j+1) = 2 - f(j)$ for
   $j < h$. So $f(h)$ is $f(0) = E_m$ for even $h$ and $2 - E_m$ for odd $h$. Also
   $f(h) = A_m(-1) \bmod p$, since $2h \equiv -1$. For even $m \ge 2$, $A_m(-1) = A_m(1)$
   because $E_k = 0$ for odd $k$, and $A_m(1) + A_m(-1) = 0$ by step 3. So $A_m(-1) = 0$, and
   $E_{p-1} \equiv 0$ or $2 \pmod p$ as $p \equiv 1$ or $3 \pmod 4$ (`prime_dvd_eulerNum_iff`).
8. **A292911**. For $p = 2j + 1$ we have $(p+1)/2 = j + 1$, so steps 6 and 7 give
   `prime_cube_dvd_num_iff` and `prime_mem_a292911_iff`. For $p \equiv 1 \pmod 4$ take
   $a = (p+1)/2$, so $2a - 1 = p$ (`a292911_conjecture`).

*References:*
- Vladimir Shevelev, [A291897](https://oeis.org/A291897), September 22, 2017.
- Vladimir Shevelev, [A292911](https://oeis.org/A292911), September 26, 2017.
- NIST Digital Library of Mathematical Functions, [§24.2](https://dlmf.nist.gov/24.2),
  formulas 24.2.9 and 24.2.10.
- G. S. Ely, Some notes on the numbers of Bernoulli and Euler, Amer. J. Math. 5 (1882),
  337–341, [doi:10.2307/2369547](https://doi.org/10.2307/2369547). The congruence for
  $E_{p-1} \bmod p$ is also stated in OEIS [A000364](https://oeis.org/A000364) and
  [A122045](https://oeis.org/A122045).
-/

@[expose] public section

namespace OeisA291897

open Finset PowerSeries

/-- The Euler polynomials, by the recurrence
$E_m(x) = x^m - \frac12 \sum_{k<m} \binom mk E_k(x)$. -/
noncomputable def eulerPoly (m : ℕ) : Polynomial ℚ :=
  Polynomial.X ^ m -
    Polynomial.C (1 / 2) * ∑ k : Fin m, (m.choose k : Polynomial ℚ) * eulerPoly k

/-- The Euler numbers, by the recurrence
$E_m = [m = 0] - \sum_{k<m,\ m-k \text{ even}} \binom mk E_k$. -/
def eulerNum (m : ℕ) : ℤ :=
  (if m = 0 then 1 else 0) -
    ∑ k : Fin m, if Even (m - k) then (m.choose k : ℤ) * eulerNum k else 0

/-- OEIS A291897: the numerator of $E_{2n-1}(n)$ (offset $1$). -/
noncomputable def a291897 (n : ℕ) : ℤ := ((eulerPoly (2 * n - 1)).eval (n : ℚ)).num

/-- OEIS A292911: the numbers $n \ge 1$ such that A291897$(n)$ is divisible by $(2n-1)^3$. -/
def a292911 : Set ℕ := {n | 1 ≤ n ∧ (2 * (n : ℤ) - 1) ^ 3 ∣ a291897 n}

/-! ### Exponential generating functions -/

/-- The product of two e.g.f.s is the e.g.f. of the binomial convolution. -/
theorem egf_mul (a b : ℕ → ℚ) :
    (mk fun n => a n / n.factorial) * (mk fun n => b n / n.factorial) =
      mk fun n => (∑ k ∈ range (n + 1), (n.choose k : ℚ) * a k * b (n - k)) / n.factorial := by
  ext n
  rw [coeff_mul, coeff_mk, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hk : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  simp only [coeff_mk]
  rw [← Nat.choose_mul_factorial_mul_factorial hk]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((n - k).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  push_cast
  field_simp

theorem rescale_exp (y : ℚ) : rescale y (exp ℚ) = mk fun n => y ^ n / n.factorial := by
  ext n
  simp [coeff_rescale, coeff_exp, div_eq_mul_inv]

theorem exp_eq_mk : exp ℚ = mk fun n => (1 : ℚ) / n.factorial := by
  ext n
  simp [coeff_exp]

/-! ### Euler polynomials -/

theorem eval_eulerPoly (m : ℕ) (x : ℚ) :
    (eulerPoly m).eval x =
      x ^ m - 1 / 2 * ∑ k ∈ range m, (m.choose k : ℚ) * (eulerPoly k).eval x := by
  rw [eulerPoly.eq_1 m]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun k => (m.choose k : ℚ) * (eulerPoly k).eval x) m]

/-- The recurrence in the form $\sum_{k \le m} \binom mk E_k(x) + E_m(x) = 2x^m$. -/
theorem eulerPoly_rec (m : ℕ) (x : ℚ) :
    ∑ k ∈ range (m + 1), (m.choose k : ℚ) * (eulerPoly k).eval x + (eulerPoly m).eval x =
      2 * x ^ m := by
  rw [sum_range_succ, Nat.choose_self, eval_eulerPoly m x]
  push_cast
  ring

/-- `eulerPoly` has the e.g.f. $\sum_m E_m(x)\, t^m/m! = 2e^{xt}/(e^t + 1)$. -/
theorem eulerPoly_egf (x : ℚ) :
    (mk fun m => (eulerPoly m).eval x / m.factorial) * (exp ℚ + 1) = 2 * rescale x (exp ℚ) := by
  have h := egf_mul (fun m => (eulerPoly m).eval x) (fun _ => 1)
  rw [rescale_exp, mul_add, mul_one, exp_eq_mk, h]
  ext m
  simp only [map_add, coeff_mk, coeff_ofNat_mul, mul_one]
  have := eulerPoly_rec m x
  have hm : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linear_combination this

/-! ### Euler numbers -/

/-- The recurrence in the form $\sum_{k \le m,\ m-k \text{ even}} \binom mk E_k = [m = 0]$. -/
theorem eulerNum_rec (m : ℕ) :
    ∑ k ∈ range (m + 1), (if Even (m - k) then (m.choose k : ℤ) * eulerNum k else 0) =
      if m = 0 then 1 else 0 := by
  rw [sum_range_succ, Nat.sub_self, eulerNum.eq_1 m,
    Fin.sum_univ_eq_sum_range
      (fun k => if Even (m - k) then (m.choose k : ℤ) * eulerNum k else 0) m]
  simp

/-- The Euler numbers of odd index vanish. -/
theorem eulerNum_odd {m : ℕ} (hm : Odd m) : eulerNum m = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    rw [eulerNum.eq_1 m]
    simp only [hm0, ↓reduceIte, zero_sub, neg_eq_zero]
    refine sum_eq_zero fun k _ => ?_
    split_ifs with h
    · have hk : Odd (k : ℕ) := by
        rw [Nat.even_sub k.2.le] at h
        rw [← Nat.not_even_iff_odd] at hm ⊢
        tauto
      rw [ih k k.2 hk, mul_zero]
    · rfl

/-- `eulerNum` has the e.g.f. $\sum_k E_k\, t^k/k! = \operatorname{sech} t = 2/(e^t + e^{-t})$. -/
theorem eulerNum_egf :
    (mk fun k => (eulerNum k : ℚ) / k.factorial) * (exp ℚ + rescale (-1) (exp ℚ)) = 2 := by
  have hs : exp ℚ + rescale (-1) (exp ℚ) =
      PowerSeries.mk fun n => (1 + (-1 : ℚ) ^ n) / n.factorial := by
    rw [rescale_exp, exp_eq_mk]
    ext n
    simp [add_div]
  rw [hs, egf_mul]
  ext m
  rw [coeff_mk, show (2 : ℚ⟦X⟧) = C (2 : ℚ) from rfl, coeff_C]
  have h := congrArg (fun z : ℤ => (z : ℚ)) (eulerNum_rec m)
  simp only [Int.cast_sum] at h
  have key : ∑ k ∈ range (m + 1), (m.choose k : ℚ) * eulerNum k * (1 + (-1) ^ (m - k)) =
      2 * ∑ k ∈ range (m + 1),
        ((if Even (m - k) then (m.choose k : ℤ) * eulerNum k else 0 : ℤ) : ℚ) := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs with he
    · rw [he.neg_one_pow]; push_cast; ring
    · rw [(Nat.not_even_iff_odd.1 he).neg_one_pow]; simp
  rw [key, h]
  split_ifs with hm <;> simp [hm]

/-! ### The sums $A_m(y) = \sum_k \binom mk E_k y^{m-k}$ -/

/-- $A_m(y) = \sum_k \binom mk E_k y^{m-k}$ for $y \in \mathbb{Q}$. -/
def eulerA (m : ℕ) (y : ℚ) : ℚ := ∑ k ∈ range (m + 1), (m.choose k : ℚ) * eulerNum k * y ^ (m - k)

/-- $A_m(a) = \sum_k \binom mk E_k a^{m-k}$ for $a \in \mathbb{Z}$. -/
def eulerAZ (m : ℕ) (a : ℤ) : ℤ :=
  ∑ k ∈ range (m + 1), (m.choose k : ℤ) * eulerNum k * a ^ (m - k)

theorem cast_eulerAZ (m : ℕ) (a : ℤ) : (eulerAZ m a : ℚ) = eulerA m a := by
  simp [eulerAZ, eulerA]

/-- The e.g.f. $S(t) = \sum_k E_k\, t^k/k!$ of the Euler numbers. -/
noncomputable def sechSeries : ℚ⟦X⟧ := PowerSeries.mk fun k => (eulerNum k : ℚ) / k.factorial

theorem egf_eulerA (y : ℚ) :
    (PowerSeries.mk fun m => eulerA m y / m.factorial) = sechSeries * rescale y (exp ℚ) := by
  rw [sechSeries, rescale_exp, egf_mul]
  rfl

/-- The shift identity $A_m(y + 2) + A_m(y) = 2(y + 1)^m$. -/
theorem eulerA_add_two (m : ℕ) (y : ℚ) : eulerA m (y + 2) + eulerA m y = 2 * (y + 1) ^ m := by
  have e1 := exp_mul_exp_eq_exp_add (A := ℚ) (y + 1) 1
  have e2 := exp_mul_exp_eq_exp_add (A := ℚ) (y + 1) (-1)
  rw [show y + 1 + 1 = y + 2 by ring, rescale_one, RingHom.id_apply] at e1
  rw [show y + 1 + -1 = y by ring] at e2
  have key : sechSeries * rescale (y + 2) (exp ℚ) + sechSeries * rescale y (exp ℚ) =
      2 * rescale (y + 1) (exp ℚ) := by
    rw [← e1, ← e2]
    unfold sechSeries
    linear_combination (rescale (y + 1) (exp ℚ)) * eulerNum_egf
  have := congrArg (coeff m) key
  rw [← egf_eulerA, ← egf_eulerA, rescale_exp] at this
  simp only [map_add, coeff_mk, coeff_ofNat_mul] at this
  have hm : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp at this
  linear_combination this

theorem eulerAZ_add_two (m : ℕ) (a : ℤ) : eulerAZ m (a + 2) + eulerAZ m a = 2 * (a + 1) ^ m := by
  have h := eulerA_add_two m a
  have h1 := cast_eulerAZ m (a + 2)
  push_cast at h1
  rw [← h1, ← cast_eulerAZ] at h
  exact_mod_cast h

/-- The expansion of $E_m(x)$ about $x = 1/2$ (DLMF 24.2.10) in the form
$2^m E_m(x) = A_m(2x - 1)$. -/
theorem two_pow_mul_eval_eulerPoly (m : ℕ) (x : ℚ) :
    2 ^ m * (eulerPoly m).eval x = eulerA m (2 * x - 1) := by
  set y := 2 * x - 1 with hy
  have hU : (PowerSeries.mk fun m => eulerA m y / 2 ^ m / m.factorial) =
      rescale (1 / 2) sechSeries * rescale (y * (1 / 2)) (exp ℚ) := by
    rw [← rescale_rescale, ← map_mul, ← egf_eulerA, rescale_mk]
    ext n
    simp only [coeff_mk, one_div, inv_pow]
    ring
  have hE : exp ℚ + 1 = rescale (1 / 2) (exp ℚ) *
      rescale (1 / 2) (exp ℚ + rescale (-1) (exp ℚ)) := by
    rw [map_add, rescale_rescale, mul_add, exp_mul_exp_eq_exp_add, exp_mul_exp_eq_exp_add]
    norm_num [rescale_zero_apply]
  have h2 : rescale (1 / 2 : ℚ) (2 : ℚ⟦X⟧) = 2 := map_ofNat _ 2
  have hUe : (PowerSeries.mk fun m => eulerA m y / 2 ^ m / m.factorial) * (exp ℚ + 1) =
      2 * rescale x (exp ℚ) := by
    rw [hU, hE]
    have := congrArg (rescale (1 / 2 : ℚ)) eulerNum_egf
    rw [map_mul, h2] at this
    rw [show x = y * (1 / 2) + 1 / 2 by rw [hy]; ring, ← exp_mul_exp_eq_exp_add]
    rw [sechSeries] at *
    linear_combination (rescale (y * (1 / 2)) (exp ℚ) * rescale (1 / 2) (exp ℚ)) * this
  have hne : exp ℚ + 1 ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  have heq := mul_right_cancel₀ hne ((eulerPoly_egf x).trans hUe.symm)
  have := congrArg (coeff m) heq
  simp only [coeff_mk] at this
  have hm : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp at this
  linear_combination this

/-- $E_m((a+1)/2) = A_m(a)/2^m$ for $a \in \mathbb{Z}$. -/
theorem eval_eulerPoly_half (m : ℕ) (a : ℤ) :
    (eulerPoly m).eval (((a : ℚ) + 1) / 2) = (eulerAZ m a : ℚ) / 2 ^ m := by
  have h := two_pow_mul_eval_eulerPoly m (((a : ℚ) + 1) / 2)
  rw [show 2 * (((a : ℚ) + 1) / 2) - 1 = a by ring, ← cast_eulerAZ] at h
  rw [← h]
  field_simp

theorem eulerAZ_zero (m : ℕ) : eulerAZ m 0 = eulerNum m := by
  rw [eulerAZ, sum_range_succ, sum_eq_zero]
  · simp
  · intro k hk
    rw [zero_pow (by have := mem_range.1 hk; omega), mul_zero]

theorem eulerAZ_neg_one {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) : eulerAZ m (-1) = 0 := by
  have h1 : eulerAZ m 1 = eulerAZ m (-1) := by
    refine sum_congr rfl fun k hk => ?_
    rcases Nat.even_or_odd k with he | ho
    · rw [one_pow, ((Nat.even_sub (Nat.lt_succ_iff.1 (mem_range.1 hk))).2
        (iff_of_true hm he)).neg_one_pow]
    · rw [eulerNum_odd ho]
      simp
  have h2 := eulerAZ_add_two m (-1)
  norm_num [zero_pow hm0] at h2
  rw [h1] at h2
  omega

/-! ### Numerators of $A/2^s$ -/

/-- For odd $d$, $d$ divides the numerator of $A/2^s$ if and only if $d$ divides $A$. -/
theorem odd_dvd_num_div_two_pow_iff {d : ℤ} (hd : Odd d) (A : ℤ) (s : ℕ) :
    d ∣ ((A : ℚ) / 2 ^ s).num ↔ d ∣ A := by
  set q : ℚ := (A : ℚ) / 2 ^ s with hq
  have hd2 : IsCoprime d 2 := by
    obtain ⟨k, rfl⟩ := hd
    exact ⟨1, -k, by ring⟩
  have hden : (q.den : ℤ) ∣ 2 ^ s := by
    have := Rat.den_dvd A (2 ^ s)
    rwa [Rat.divInt_eq_div, Int.cast_pow, Int.cast_ofNat, ← hq] at this
  have hcross : q.num * 2 ^ s = A * q.den := by
    have h1 : (q.num : ℚ) / q.den = A / 2 ^ s := Rat.num_div_den q
    rw [div_eq_div_iff (by positivity) (by positivity)] at h1
    exact_mod_cast h1
  constructor
  · intro h
    have : d ∣ A * q.den := hcross ▸ dvd_mul_of_dvd_left h _
    exact (hd2.pow_right.of_isCoprime_of_dvd_right hden).dvd_of_dvd_mul_right this
  · intro h
    have : d ∣ q.num * 2 ^ s := hcross ▸ dvd_mul_of_dvd_left h _
    exact hd2.pow_right.dvd_of_dvd_mul_right this

/-! ### A291897 -/

/-- With $N = 2j + 1$: $A_N(N) \equiv N^2 E_{N-1} \pmod{N^3}$. -/
theorem eulerAZ_odd_self (j : ℕ) :
    (2 * (j : ℤ) + 1) ^ 3 ∣
      eulerAZ (2 * j + 1) (2 * j + 1) - (2 * j + 1) ^ 2 * eulerNum (2 * j) := by
  have hsplit : eulerAZ (2 * j + 1) (2 * j + 1) - (2 * j + 1) ^ 2 * eulerNum (2 * j) =
      ∑ k ∈ range (2 * j),
        ((2 * j + 1).choose k : ℤ) * eulerNum k * (2 * j + 1) ^ (2 * j + 1 - k) := by
    rw [eulerAZ, sum_range_succ, sum_range_succ, eulerNum_odd (m := 2 * j + 1) ⟨j, rfl⟩,
      Nat.choose_succ_self_right, show 2 * j + 1 - 2 * j = 1 by omega]
    push_cast
    ring
  rw [hsplit]
  refine dvd_sum fun k hk => ?_
  have hk := mem_range.1 hk
  rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ho
  · exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
  · rw [eulerNum_odd ho]
    simp

theorem a291897_succ (j : ℕ) :
    a291897 (j + 1) = ((eulerAZ (2 * j + 1) (2 * j + 1) : ℚ) / 2 ^ (2 * j + 1)).num := by
  rw [a291897, show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
    show ((j + 1 : ℕ) : ℚ) = (((2 * j + 1 : ℤ) : ℚ) + 1) / 2 by push_cast; ring,
    eval_eulerPoly_half]

theorem cube_dvd_iff (j : ℕ) :
    (2 * (j : ℤ) + 1) ^ 3 ∣ ((eulerAZ (2 * j + 1) (2 * j + 1) : ℚ) / 2 ^ (2 * j + 1)).num ↔
      2 * (j : ℤ) + 1 ∣ eulerNum (2 * j) := by
  rw [odd_dvd_num_div_two_pow_iff (Odd.pow ⟨j, rfl⟩),
    dvd_iff_dvd_of_dvd_sub (eulerAZ_odd_self j),
    show (2 * (j : ℤ) + 1) ^ 3 = (2 * j + 1) ^ 2 * (2 * j + 1) by ring,
    mul_dvd_mul_iff_left (by positivity)]

/-- OEIS A291897, Shevelev's conjecture: $(2n-1)^2$ divides $a(n)$ for $n \ge 1$. -/
theorem a291897_conjecture (n : ℕ) (hn : 1 ≤ n) : (2 * (n : ℤ) - 1) ^ 2 ∣ a291897 n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * ((j + 1 : ℕ) : ℤ) - 1 = 2 * j + 1 by push_cast; ring, a291897_succ,
    odd_dvd_num_div_two_pow_iff (Odd.pow ⟨j, rfl⟩)]
  obtain ⟨B, hB⟩ := eulerAZ_odd_self j
  rw [sub_eq_iff_eq_add] at hB
  rw [hB]
  exact dvd_add (Dvd.dvd.mul_right (pow_dvd_pow _ (by norm_num)) _) (dvd_mul_right _ _)

/-- For $n \ge 1$: $(2n-1)^3$ divides $a(n)$ if and only if $2n - 1$ divides the Euler number
$E_{2n-2}$. -/
theorem a291897_cube_dvd_iff (n : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℤ) - 1) ^ 3 ∣ a291897 n ↔ 2 * (n : ℤ) - 1 ∣ eulerNum (2 * n - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * ((j + 1 : ℕ) : ℤ) - 1 = 2 * j + 1 by push_cast; ring, a291897_succ,
    cube_dvd_iff, show 2 * (j + 1) - 2 = 2 * j by omega]

/-! ### Ely's congruence -/

/-- Ely's congruence (1882): for an odd prime $p$, $E_{p-1} \equiv 0 \pmod p$ if
$p \equiv 1 \pmod 4$ and $E_{p-1} \equiv 2 \pmod p$ if $p \equiv 3 \pmod 4$. -/
theorem eulerNum_prime_sub_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ((eulerNum (p - 1) : ℤ) : ZMod p) = if p % 4 = 1 then 0 else 2 := by
  obtain ⟨h, rfl⟩ : ∃ h, p = 2 * h + 1 :=
    ⟨p / 2, (Nat.two_mul_div_two_add_one_of_odd (hp.out.odd_of_ne_two hp2)).symm⟩
  have hh : 1 ≤ h := by have := hp.out.two_le; omega
  rw [show 2 * h + 1 - 1 = 2 * h by omega]
  set m := 2 * h with hmdef
  have hm : Even m := ⟨h, by omega⟩
  have hm0 : m ≠ 0 := by omega
  set f : ℕ → ZMod (2 * h + 1) := fun j => ((eulerAZ m (2 * j) : ℤ) : ZMod (2 * h + 1)) with hf
  have hstep : ∀ j < h, f (j + 1) = 2 - f j := by
    intro j hj
    have hne : ((2 * j + 1 : ℕ) : ZMod (2 * h + 1)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have hpow : ((2 * j + 1 : ℕ) : ZMod (2 * h + 1)) ^ m = 1 := by
      have := ZMod.pow_card_sub_one_eq_one hne
      rwa [show 2 * h + 1 - 1 = m by omega] at this
    have hs := congrArg (fun z : ℤ => (z : ZMod (2 * h + 1))) (eulerAZ_add_two m (2 * j))
    push_cast at hs hpow
    rw [hpow] at hs
    simp only [hf]
    rw [show 2 * ((j + 1 : ℕ) : ℤ) = 2 * (j : ℤ) + 2 by push_cast; ring]
    linear_combination hs
  have hpar : ∀ j ≤ h, f j = if Even j then f 0 else 2 - f 0 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [hstep j (by omega), ih (by omega)]
      by_cases he : Even j
      · have : ¬ Even (j + 1) := by simpa [Nat.even_add_one] using he
        simp [he, this]
      · have : Even (j + 1) := Nat.even_add_one.2 he
        simp [he, this]
  have hfh : f h = 0 := by
    have hc : (2 * (h : ZMod (2 * h + 1))) = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      exact_mod_cast ZMod.natCast_self (2 * h + 1)
    have : f h = ((eulerAZ m (-1) : ℤ) : ZMod (2 * h + 1)) := by
      simp only [hf, eulerAZ]
      push_cast
      rw [hc]
    rw [this, eulerAZ_neg_one hm hm0, Int.cast_zero]
  have key := hpar h le_rfl
  rw [hfh] at key
  simp only [hf, Nat.cast_zero, mul_zero, eulerAZ_zero] at key
  have h4 : (2 * h + 1) % 4 = 1 ↔ Even h := by rw [Nat.even_iff]; omega
  by_cases he : Even h
  · simp only [he, ↓reduceIte] at key
    simp only [h4.2 he, ↓reduceIte]
    exact key.symm
  · simp only [he, ↓reduceIte] at key
    simp only [mt h4.1 he, ↓reduceIte]
    linear_combination key

/-- For an odd prime $p$: $p \mid E_{p-1}$ if and only if $p \equiv 1 \pmod 4$. -/
theorem prime_dvd_eulerNum_iff (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : ℤ) ∣ eulerNum (p - 1) ↔ p % 4 = 1 := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, eulerNum_prime_sub_one p hp2]
  by_cases h : p % 4 = 1
  · simp [h]
  · simp only [h, ↓reduceIte, iff_false]
    intro h2
    have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    have := hp.two_le
    omega

/-! ### A292911 -/

/-- For an odd prime $p$: $p^3$ divides the numerator of $E_p((p+1)/2)$ if and only if
$p \equiv 1 \pmod 4$. -/
theorem prime_cube_dvd_num_iff (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : ℤ) ^ 3 ∣ ((eulerPoly p).eval (((p : ℚ) + 1) / 2)).num ↔ p % 4 = 1 := by
  rw [← prime_dvd_eulerNum_iff p hp hp2]
  obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 :=
    ⟨p / 2, (Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2)).symm⟩
  rw [show (((2 * j + 1 : ℕ) : ℚ) + 1) / 2 = (((2 * j + 1 : ℤ) : ℚ) + 1) / 2 by push_cast; ring,
    eval_eulerPoly_half, show 2 * j + 1 - 1 = 2 * j by omega]
  push_cast
  exact cube_dvd_iff j

/-- For an odd prime $p$: $(p+1)/2$ is a term of A292911 if and only if $p \equiv 1 \pmod 4$. -/
theorem prime_mem_a292911_iff (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p + 1) / 2 ∈ a292911 ↔ p % 4 = 1 := by
  rw [← prime_dvd_eulerNum_iff p hp hp2]
  obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 :=
    ⟨p / 2, (Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hp2)).symm⟩
  rw [show (2 * j + 1 + 1) / 2 = j + 1 by omega, a292911, Set.mem_ofPred_eq,
    a291897_cube_dvd_iff _ (by omega), show 2 * (j + 1) - 2 = 2 * j + 1 - 1 by omega,
    show 2 * ((j + 1 : ℕ) : ℤ) - 1 = ((2 * j + 1 : ℕ) : ℤ) by push_cast; ring]
  simp

/-- OEIS A292911, Shevelev's conjecture: every prime $p \equiv 1 \pmod 4$ is $2a - 1$ for a term
$a$ of A292911. -/
theorem a292911_conjecture (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ a ∈ a292911, 2 * a - 1 = p := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at h4
  exact ⟨(p + 1) / 2, (prime_mem_a292911_iff p hp hp2).2 h4, by omega⟩

/-! ### Sanity checks -/

theorem eulerNum_zero : eulerNum 0 = 1 := by
  rw [eulerNum.eq_1]; simp

theorem eulerNum_two : eulerNum 2 = -1 := by
  rw [eulerNum.eq_1]; simp [Fin.sum_univ_succ, eulerNum_zero]

theorem eulerNum_four : eulerNum 4 = 5 := by
  rw [eulerNum.eq_1]
  simp [Fin.sum_univ_succ, eulerNum_zero, eulerNum_two, Nat.even_iff, Nat.choose]

theorem eulerNum_six : eulerNum 6 = -61 := by
  rw [eulerNum.eq_1]
  simp [Fin.sum_univ_succ, eulerNum_zero, eulerNum_two, eulerNum_four, Nat.even_iff, Nat.choose]

/-- The first four terms of A291897: $1, 9, 125, 32977$. -/
theorem a291897_first :
    a291897 1 = 1 ∧ a291897 2 = 9 ∧ a291897 3 = 125 ∧ a291897 4 = 32977 := by
  have h1 : eulerNum 1 = 0 := eulerNum_odd ⟨0, rfl⟩
  have h3 : eulerNum 3 = 0 := eulerNum_odd ⟨1, rfl⟩
  have h5 : eulerNum 5 = 0 := eulerNum_odd ⟨2, rfl⟩
  have h7 : eulerNum 7 = 0 := eulerNum_odd ⟨3, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a291897_succ 0]
    simp [eulerAZ, sum_range_succ, eulerNum_zero, eulerNum_odd]
  · rw [a291897_succ 1]
    simp [eulerAZ, sum_range_succ, eulerNum_zero, eulerNum_two, h1, h3, Nat.choose]
    decide +kernel
  · rw [a291897_succ 2]
    simp [eulerAZ, sum_range_succ, eulerNum_zero, eulerNum_two, eulerNum_four, h1, h3, h5,
      Nat.choose]
    decide +kernel
  · rw [a291897_succ 3]
    simp [eulerAZ, sum_range_succ, eulerNum_zero, eulerNum_two, eulerNum_four, eulerNum_six,
      h1, h3, h5, h7, Nat.choose]
    decide +kernel

/-- The terms $1, 3, 7, 9$ of A292911 named in A291897, and the non-term $2$. -/
theorem a292911_examples :
    1 ∈ a292911 ∧ 3 ∈ a292911 ∧ 7 ∈ a292911 ∧ 9 ∈ a292911 ∧ 2 ∉ a292911 := by
  refine ⟨⟨le_rfl, by norm_num⟩, (prime_mem_a292911_iff 5 (by norm_num) (by norm_num)).2 rfl,
    (prime_mem_a292911_iff 13 (by norm_num) (by norm_num)).2 rfl,
    (prime_mem_a292911_iff 17 (by norm_num) (by norm_num)).2 rfl, ?_⟩
  rw [show 2 = (3 + 1) / 2 from rfl, prime_mem_a292911_iff 3 (by norm_num) (by norm_num)]
  decide

end OeisA291897

end
