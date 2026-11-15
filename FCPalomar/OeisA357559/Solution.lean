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
# Bala's divisibility conjectures on OEIS A357559

For $m, n \ge 0$ let $S_m(n) = \sum_{k=0}^{n} (-1)^{n+k} k^m \binom{n}{k}\binom{n+k}{k}^2$, so
that $S_3$ is A357559. This file proves $n^2(n+1)^2 \mid 2S_2(n)$, with $n^2(n+1)^2 \mid S_2(n)$
for odd $n$, and $n^2(n+1)^3 \mid 6S_3(n)$. At $2n$ these give Peter Bala's Conjecture 1,
$n^2(2n+1)^2 \mid S_2(2n)$, and his FORMULA conjecture, $n^2(2n+1)^3 \mid 3S_3(2n)$, each with an
extra factor $2$. Bala's Conjectures 2 and 3, for $m \ge 4$, are not treated.

1. **Difference lemma** (`sum_alt_choose`). The $d$-th forward difference of
   $x \mapsto \binom{x}{d+t}$ is $x \mapsto \binom{x}{t}$ (`fwdDiff_iter_choose`). Expanding it at
   $c$ with `fwdDiff_iter_eq_sum_shift` gives
   $\sum_{l=0}^{d} (-1)^{d+l}\binom{d}{l}\binom{c+l}{d+t} = \binom{c}{t}$.
2. **Positive form** (`alt_sum_eq`). For $a, b, r \ge 0$,
   $$\sum_{k=0}^{a} (-1)^{a+k}\binom{a}{k}\binom{b+k}{a+r}^2
     = \sum_{i=0}^{a} \binom{a}{i}\binom{b}{a+r-i}\binom{b+i}{r+i}.$$
   Expand one factor $\binom{b+k}{a+r}$ by Vandermonde's identity, cut at $i \le a$
   (`choose_add_eq_sum`), and swap the sums. In the inner sum use
   $\binom{a}{k}\binom{k}{i} = \binom{a}{i}\binom{a-i}{k-i}$, put $k = i + l$ (`inner_sum`), and
   apply step 1 with $c = b + i$ and $d = a - i$.
3. **Reductions** (`S_two_eq`, `S_three_eq`). By $k\binom{n+k}{k} = (n+1)\binom{n+k}{n+1}$
   (`mul_choose_add`) and $k\binom{n}{k} = n\binom{n-1}{k-1}$, the sum $S_2(n)$ is $(n+1)^2$
   times the left side of step 2 with $(a, b, r) = (n, n, 1)$. For $n = m + 1$, $S_3(n)$ is
   $n(n+1)^2$ times the left side with $(a, b, r) = (m, m+2, 2)$. So $S_2(n) = (n+1)^2 W$ and
   $S_3(n) = n(n+1)^2 Z$, where $W$ and $Z$ are sums of products of binomial coefficients.
4. **Theorem 1** (`term_two_dvd`, `key_two`). The term $i = 0$ of $W$ vanishes. The term
   $i = j + 1$ is $PQR$ with $P = \binom{n}{j+1}$, $Q = \binom{n}{j}$ and
   $R = \binom{n+j+1}{j+2}$. Here $n$ divides $(j+1)P$, $jQ$ and $(j+2)R$ (`dvd_mul_choose` and
   `Nat.choose_succ_right_eq`). So $n^2$ divides the three pairwise products, and the identity
   $2 = (j+1)^2(j+2) - j(j+1)^2 - 2j(j+2)$ gives $n^2 \mid 2PQR$. Hence $n^2(n+1)^2 \mid 2S_2(n)$.
   For odd $n$, $n^2$ is coprime to $2$, so $n^2 \mid W$.
5. **Theorem 2** (`term_three_dvd`, `key_six`, `key_two'`). Let $n = m + 1$. Each term of $Z$ is
   $\binom{n-1}{i} A B$ with $A = \binom{n+1}{i}$ and $B = \binom{n+1+i}{i+2}$. Then
   $i(i-1)A = n(n+1)\binom{n-1}{i-2}$ for $i \ge 2$, $iA = (n+1)\binom{n}{i-1}$, and
   $(i+1)(i+2)B = n(n+1)\binom{n+1+i}{i}$. The identity
   $6 = (5+2i)\,i(i-1) + (3-2i)(i+1)(i+2)$ gives $n \mid 6AB$. The identity
   $2 = (i+1)(i+2) - i(i+3)$ gives $(n+1) \mid 2AB$. So $n$ and $n+1$ both divide $6Z$. They are
   coprime, so $n(n+1) \mid 6Z$, and $n^2(n+1)^3 \mid n(n+1)^2 \cdot 6Z = 6S_3(n)$. For $n = 0$,
   $S_3(0) = 0$.
6. **Bala's conjectures.** Apply steps 4 and 5 at $2n$ and cancel a factor $2$:
   $4n^2(2n+1)^2 \mid 2S_2(2n)$ and $4n^2(2n+1)^3 \mid 6S_3(2n)$.

The informal proof bounds $p$-adic valuations of the terms of $W$ and $Z$ with Kummer's theorem.
The Lean proof replaces that case analysis by the polynomial identities in steps 4 and 5. The
checks at the end show that the constant $2$ in step 4 and the constant $6$ in step 5 cannot be
replaced by proper divisors: $36 \nmid S_2(2)$, $8 \nmid 3S_3(1)$ and $576 \nmid 2S_3(3)$.
The factor $3$ in the FORMULA conjecture is needed: $9 \cdot 7^3 \nmid S_3(6)$.

*References:*
- Peter Bala, [A357559](https://oeis.org/A357559). The FORMULA conjecture dates from
  October 4, 2022, and Conjecture 1 has its current form from October 6, 2022.
- [A005258](https://oeis.org/A005258), the Apéry numbers $S_0(n)$.
-/

@[expose] public section

namespace OeisA357559

open Finset

/-- Bala's sum $S_m(n) = \sum_{k=0}^{n} (-1)^{n+k} k^m \binom{n}{k}\binom{n+k}{k}^2$.
`S 3` is OEIS A357559. -/
def S (m n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (-1) ^ (n + k) * (k : ℤ) ^ m * (n.choose k : ℤ) * ((n + k).choose k : ℤ) ^ 2

/-! ### Binomial identities -/

/-- $n \mid k\binom{n}{k}$. -/
theorem dvd_mul_choose (n k : ℕ) : n ∣ k * n.choose k := by
  rcases k with _ | k
  · simp
  rcases n with _ | n
  · simp
  exact ⟨n.choose k, by rw [Nat.add_one_mul_choose_eq]; ring⟩

/-- $k\binom{n+k}{k} = (n+1)\binom{n+k}{n+1}$. -/
theorem mul_choose_add (n k : ℕ) : k * (n + k).choose k = (n + 1) * (n + k).choose (n + 1) := by
  have h := Nat.choose_succ_right_eq (n + k) n
  rw [Nat.add_sub_cancel_left, Nat.choose_symm_add] at h
  linarith

/-- The difference lemma: $\sum_{l=0}^{d} (-1)^{d+l}\binom{d}{l}\binom{c+l}{d+t} = \binom{c}{t}$. -/
theorem sum_alt_choose (c d t : ℕ) :
    ∑ l ∈ range (d + 1), (-1 : ℤ) ^ (d + l) * d.choose l * ((c + l).choose (d + t) : ℤ) =
      c.choose t := by
  have h := fwdDiff_iter_eq_sum_shift (1 : ℕ) (fun x : ℕ ↦ (x.choose (d + t) : ℤ)) d c
  rw [fwdDiff_iter_choose] at h
  simp only at h
  rw [h]
  refine sum_congr rfl fun l hl => ?_
  have hl : l ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hl)
  have hs : (-1 : ℤ) ^ (d + l) = (-1) ^ (d - l) := by
    rw [show d + l = d - l + 2 * l by omega, pow_add, pow_mul]; simp
  simp [hs, smul_eq_mul]

/-- Vandermonde's identity, with the sum cut at $a$. -/
theorem choose_add_eq_sum (b k s a : ℕ) (hk : k ≤ a) (ha : a ≤ s) :
    (b + k).choose s = ∑ i ∈ range (a + 1), k.choose i * b.choose (s - i) := by
  rw [add_comm, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  apply sum_subset
  · intro i hi
    simp only [mem_range] at hi ⊢
    omega
  · intro i _ hi
    simp only [mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]

/-- The inner sum of `alt_sum_eq`, shifted by $k = i + l$. -/
theorem inner_sum (a b s i : ℕ) (hi : i ≤ a) :
    ∑ k ∈ range (a + 1), (-1 : ℤ) ^ (a + k) * a.choose k * k.choose i * (b + k).choose s =
      a.choose i * ∑ l ∈ range (a - i + 1), (-1 : ℤ) ^ (a - i + l) * (a - i).choose l *
        ((b + i + l).choose s : ℤ) := by
  rw [show a + 1 = i + (a - i + 1) by omega, sum_range_add, sum_eq_zero, zero_add, mul_sum]
  · refine sum_congr rfl fun l _ => ?_
    have hc : (a.choose (i + l) : ℤ) * (i + l).choose i = a.choose i * (a - i).choose l := by
      have := Nat.choose_mul (n := a) (k := i + l) (s := i) (by omega)
      rw [Nat.add_sub_cancel_left] at this
      exact_mod_cast this
    have hs : (-1 : ℤ) ^ (a + (i + l)) = (-1) ^ (a - i + l) := by
      rw [show a + (i + l) = a - i + l + 2 * i by omega, pow_add, pow_mul]; simp
    rw [hs, show b + (i + l) = b + i + l by ring]
    linear_combination ((-1 : ℤ) ^ (a - i + l) * ((b + i + l).choose s : ℤ)) * hc
  · intro k hk
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hk)]
    simp

/-- The positive form: $\sum_k (-1)^{a+k}\binom{a}{k}\binom{b+k}{a+r}^2$ equals
$\sum_i \binom{a}{i}\binom{b}{a+r-i}\binom{b+i}{r+i}$. -/
theorem alt_sum_eq (a b r : ℕ) :
    ∑ k ∈ range (a + 1), (-1 : ℤ) ^ (a + k) * a.choose k * ((b + k).choose (a + r) : ℤ) ^ 2 =
      ∑ i ∈ range (a + 1), (a.choose i : ℤ) * b.choose (a + r - i) * (b + i).choose (r + i) := by
  calc _ = ∑ k ∈ range (a + 1), ∑ i ∈ range (a + 1), (b.choose (a + r - i) : ℤ) *
        ((-1 : ℤ) ^ (a + k) * a.choose k * k.choose i * (b + k).choose (a + r)) := by
        refine sum_congr rfl fun k hk => ?_
        have hk : k ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hk)
        have hv : ((b + k).choose (a + r) : ℤ) =
            ∑ i ∈ range (a + 1), (k.choose i : ℤ) * b.choose (a + r - i) := by
          exact_mod_cast choose_add_eq_sum b k (a + r) a hk (by omega)
        calc _ = (-1) ^ (a + k) * a.choose k * ((b + k).choose (a + r) : ℤ) *
              ∑ i ∈ range (a + 1), (k.choose i : ℤ) * b.choose (a + r - i) := by
              rw [← hv]; ring
          _ = _ := by
              rw [mul_sum]
              exact sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ range (a + 1), (b.choose (a + r - i) : ℤ) * ∑ k ∈ range (a + 1),
        (-1 : ℤ) ^ (a + k) * a.choose k * k.choose i * (b + k).choose (a + r) := by
        rw [sum_comm]
        simp_rw [mul_sum]
    _ = _ := by
        refine sum_congr rfl fun i hi => ?_
        have hi : i ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hi)
        have h1 := sum_alt_choose (b + i) (a - i) (r + i)
        rw [show a - i + (r + i) = a + r by omega] at h1
        rw [inner_sum a b (a + r) i hi, h1]
        ring

/-! ### Reductions and divisibility -/

/-- $S_2(n) = (n+1)^2 \sum_k (-1)^{n+k}\binom{n}{k}\binom{n+k}{n+1}^2$. -/
theorem S_two_eq (n : ℕ) : S 2 n = ((n : ℤ) + 1) ^ 2 *
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n + k) * n.choose k * ((n + k).choose (n + 1) : ℤ) ^ 2 := by
  rw [S, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have h : (k : ℤ) * (n + k).choose k = (n + 1) * (n + k).choose (n + 1) := by
    exact_mod_cast mul_choose_add n k
  linear_combination (-1 : ℤ) ^ (n + k) * n.choose k *
    ((k : ℤ) * (n + k).choose k + (n + 1) * (n + k).choose (n + 1)) * h

/-- $S_3(m+1) = (m+1)(m+2)^2 \sum_k (-1)^{m+k}\binom{m}{k}\binom{m+2+k}{m+2}^2$. -/
theorem S_three_eq (m : ℕ) : S 3 (m + 1) = ((m : ℤ) + 1) * ((m : ℤ) + 2) ^ 2 *
    ∑ k ∈ range (m + 1),
      (-1 : ℤ) ^ (m + k) * m.choose k * ((m + 2 + k).choose (m + 2) : ℤ) ^ 2 := by
  rw [S, sum_range_succ', mul_sum]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_mul, add_zero]
  refine sum_congr rfl fun i _ => ?_
  rw [show m + 1 + (i + 1) = m + 2 + i by ring]
  have h1 : ((m : ℤ) + 1) * m.choose i = (m + 1).choose (i + 1) * ((i : ℤ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq m i
  have h2 : ((i : ℤ) + 1) * (m + 2 + i).choose (i + 1) =
      (m + 2) * (m + 2 + i).choose (m + 2) := by
    have := mul_choose_add (m + 1) (i + 1)
    rw [show m + 1 + (i + 1) = m + 2 + i by ring] at this
    exact_mod_cast this
  have hs : (-1 : ℤ) ^ (m + 2 + i) = (-1) ^ (m + i) := by
    rw [show m + 2 + i = m + i + 2 by ring, pow_add]; simp
  rw [hs]
  push_cast
  linear_combination (-1 : ℤ) ^ (m + i) * ((i : ℤ) + 1) * ((m + 1).choose (i + 1) : ℤ) *
      (((i : ℤ) + 1) * (m + 2 + i).choose (i + 1) + (m + 2) * (m + 2 + i).choose (m + 2)) * h2 -
    (-1 : ℤ) ^ (m + i) * ((m : ℤ) + 2) ^ 2 * ((m + 2 + i).choose (m + 2) : ℤ) ^ 2 * h1

/-- If $N$ divides $(j+1)P$, $jQ$ and $(j+2)R$, then $N^2 \mid 2PQR$. -/
theorem key_two (N j P Q R : ℤ) (hP : N ∣ (j + 1) * P) (hQ : N ∣ j * Q) (hR : N ∣ (j + 2) * R) :
    N ^ 2 ∣ 2 * (P * Q * R) := by
  have h1 : N ^ 2 ∣ ((j + 1) * P) * ((j + 2) * R) := by rw [sq]; exact mul_dvd_mul hP hR
  have h2 : N ^ 2 ∣ (j * Q) * ((j + 1) * P) := by rw [sq]; exact mul_dvd_mul hQ hP
  have h3 : N ^ 2 ∣ (j * Q) * ((j + 2) * R) := by rw [sq]; exact mul_dvd_mul hQ hR
  have : 2 * (P * Q * R) = (j + 1) * Q * (((j + 1) * P) * ((j + 2) * R)) -
      (j + 1) * R * ((j * Q) * ((j + 1) * P)) - 2 * P * ((j * Q) * ((j + 2) * R)) := by ring
  rw [this]
  exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _))
    (dvd_mul_of_dvd_right h3 _)

/-- If $N$ divides $i(i-1)A$ and $(i+1)(i+2)B$, then $N \mid 6AB$. -/
theorem key_six (N i A B : ℤ) (hA : N ∣ i * (i - 1) * A) (hB : N ∣ (i + 1) * (i + 2) * B) :
    N ∣ 6 * (A * B) := by
  have : 6 * (A * B) = (5 + 2 * i) * B * (i * (i - 1) * A) +
      (3 - 2 * i) * A * ((i + 1) * (i + 2) * B) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hB _)

/-- If $N$ divides $iA$ and $(i+1)(i+2)B$, then $N \mid 2AB$. -/
theorem key_two' (N i A B : ℤ) (hA : N ∣ i * A) (hB : N ∣ (i + 1) * (i + 2) * B) :
    N ∣ 2 * (A * B) := by
  have : 2 * (A * B) = A * ((i + 1) * (i + 2) * B) - (i + 3) * B * (i * A) := by ring
  rw [this]
  exact dvd_sub (dvd_mul_of_dvd_right hB _) (dvd_mul_of_dvd_right hA _)

/-- Each term of the positive form of $S_2(n)/(n+1)^2$ times $2$ is divisible by $n^2$. -/
theorem term_two_dvd (n i : ℕ) (hi : i ≤ n) :
    (n : ℤ) ^ 2 ∣ 2 * ((n.choose i : ℤ) * n.choose (n + 1 - i) * (n + i).choose (1 + i)) := by
  rcases i with _ | j
  · simp
  have hQ : n.choose (n + 1 - (j + 1)) = n.choose j := by
    rw [show n + 1 - (j + 1) = n - j by omega, Nat.choose_symm (by omega)]
  rw [hQ, show n + (j + 1) = n + j + 1 by ring, show 1 + (j + 1) = j + 2 by ring]
  have hP : (n : ℤ) ∣ ((j : ℤ) + 1) * n.choose (j + 1) := by
    exact_mod_cast dvd_mul_choose n (j + 1)
  have hQ' : (n : ℤ) ∣ (j : ℤ) * n.choose j := by exact_mod_cast dvd_mul_choose n j
  have hR : (n : ℤ) ∣ ((j : ℤ) + 2) * (n + j + 1).choose (j + 2) := by
    have := Nat.choose_succ_right_eq (n + j + 1) (j + 1)
    rw [show n + j + 1 - (j + 1) = n by omega, show j + 1 + 1 = j + 2 from rfl] at this
    have h' : ((n + j + 1).choose (j + 2) : ℤ) * ((j : ℤ) + 2) =
        (n + j + 1).choose (j + 1) * n := by
      exact_mod_cast this
    exact ⟨(n + j + 1).choose (j + 1), by linear_combination h'⟩
  exact key_two _ _ _ _ _ hP hQ' hR

/-- For $n = m + 1$, each term $\tau$ of the positive form of $S_3(n)/(n(n+1)^2)$ satisfies
$n \mid 6\tau$ and $(n+1) \mid 2\tau$. -/
theorem term_three_dvd (m i : ℕ) (hi : i ≤ m) :
    ((m : ℤ) + 1) ∣
        6 * ((m.choose i : ℤ) * (m + 2).choose (m + 2 - i) * (m + 2 + i).choose (2 + i)) ∧
      ((m : ℤ) + 2) ∣
        2 * ((m.choose i : ℤ) * (m + 2).choose (m + 2 - i) * (m + 2 + i).choose (2 + i)) := by
  rw [Nat.choose_symm (by omega), show 2 + i = i + 2 by ring]
  have e1 := Nat.choose_succ_right_eq (m + 2 + i) i
  have e2 := Nat.choose_succ_right_eq (m + 2 + i) (i + 1)
  rw [show m + 2 + i - i = m + 2 by omega] at e1
  rw [show m + 2 + i - (i + 1) = m + 1 by omega, show i + 1 + 1 = i + 2 from rfl] at e2
  have e1' : ((m + 2 + i).choose (i + 1) : ℤ) * ((i : ℤ) + 1) =
      (m + 2 + i).choose i * ((m : ℤ) + 2) := by
    exact_mod_cast e1
  have e2' : ((m + 2 + i).choose (i + 2) : ℤ) * ((i : ℤ) + 2) =
      (m + 2 + i).choose (i + 1) * ((m : ℤ) + 1) := by
    exact_mod_cast e2
  have hB : ((i : ℤ) + 1) * ((i : ℤ) + 2) * (m + 2 + i).choose (i + 2) =
      ((m : ℤ) + 1) * (((m : ℤ) + 2) * (m + 2 + i).choose i) := by
    linear_combination ((i : ℤ) + 1) * e2' + ((m : ℤ) + 1) * e1'
  have hA6 : ((m : ℤ) + 1) ∣ (i : ℤ) * ((i : ℤ) - 1) * (m + 2).choose i := by
    rcases i with _ | _ | j
    · simp
    · simp
    have e3 : ((m : ℤ) + 1) * m.choose j = (m + 1).choose (j + 1) * ((j : ℤ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m j
    have e4 : ((m : ℤ) + 2) * (m + 1).choose (j + 1) =
        (m + 2).choose (j + 2) * ((j : ℤ) + 2) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (m + 1) (j + 1)
    refine ⟨((m : ℤ) + 2) * m.choose j, ?_⟩
    push_cast
    linear_combination (-((j : ℤ) + 1)) * e4 - ((m : ℤ) + 2) * e3
  have hA2 : ((m : ℤ) + 2) ∣ (i : ℤ) * (m + 2).choose i := by
    exact_mod_cast dvd_mul_choose (m + 2) i
  constructor
  · have := key_six ((m : ℤ) + 1) (i : ℤ) ((m + 2).choose i) ((m + 2 + i).choose (i + 2)) hA6
      ⟨_, hB⟩
    rw [show 6 * ((m.choose i : ℤ) * (m + 2).choose i * (m + 2 + i).choose (i + 2)) =
      m.choose i * (6 * ((m + 2).choose i * (m + 2 + i).choose (i + 2))) by ring]
    exact dvd_mul_of_dvd_right this _
  · have := key_two' ((m : ℤ) + 2) (i : ℤ) ((m + 2).choose i) ((m + 2 + i).choose (i + 2)) hA2
      ⟨((m : ℤ) + 1) * (m + 2 + i).choose i, by linear_combination hB⟩
    rw [show 2 * ((m.choose i : ℤ) * (m + 2).choose i * (m + 2 + i).choose (i + 2)) =
      m.choose i * (2 * ((m + 2).choose i * (m + 2 + i).choose (i + 2))) by ring]
    exact dvd_mul_of_dvd_right this _

/-- $n^2$ divides twice the positive form of $S_2(n)/(n+1)^2$. -/
theorem S_two_dvd' (n : ℕ) : (n : ℤ) ^ 2 ∣ 2 * ∑ i ∈ range (n + 1),
    (n.choose i : ℤ) * n.choose (n + 1 - i) * (n + i).choose (1 + i) := by
  rw [mul_sum]
  exact dvd_sum fun i hi => term_two_dvd n i (Nat.lt_succ_iff.mp (mem_range.mp hi))

/-- $n^2(n+1)^2$ divides $2S_2(n)$ for every $n \ge 0$. -/
theorem S_two_dvd (n : ℕ) : (n : ℤ) ^ 2 * (n + 1) ^ 2 ∣ 2 * S 2 n := by
  rw [S_two_eq, alt_sum_eq]
  rw [mul_left_comm, mul_comm ((n : ℤ) ^ 2)]
  exact mul_dvd_mul_left _ (S_two_dvd' n)

/-- $n^2(n+1)^2$ divides $S_2(n)$ for every odd $n$. -/
theorem S_two_dvd_of_odd (n : ℕ) (hn : Odd n) : (n : ℤ) ^ 2 * (n + 1) ^ 2 ∣ S 2 n := by
  obtain ⟨t, rfl⟩ := hn
  have hc : IsCoprime ((((2 * t + 1 : ℕ)) : ℤ) ^ 2) 2 :=
    ⟨1, -(2 * (t : ℤ) ^ 2 + 2 * t), by push_cast; ring⟩
  rw [S_two_eq, alt_sum_eq, mul_comm (_ ^ 2)]
  exact mul_dvd_mul_left _ (hc.dvd_of_dvd_mul_left (S_two_dvd' _))

/-- $n^2(n+1)^3$ divides $6S_3(n)$ for every $n \ge 0$. -/
theorem S_three_dvd (n : ℕ) : (n : ℤ) ^ 2 * (n + 1) ^ 3 ∣ 6 * S 3 n := by
  rcases n with _ | m
  · simp [S]
  rw [S_three_eq, alt_sum_eq]
  set Z := ∑ i ∈ range (m + 1),
    (m.choose i : ℤ) * (m + 2).choose (m + 2 - i) * (m + 2 + i).choose (2 + i)
  have h6 : ((m : ℤ) + 1) ∣ 6 * Z := by
    rw [mul_sum]
    exact dvd_sum fun i hi => (term_three_dvd m i (Nat.lt_succ_iff.mp (mem_range.mp hi))).1
  have h2 : ((m : ℤ) + 2) ∣ 6 * Z := by
    rw [show 6 * Z = 3 * (2 * Z) by ring, mul_sum]
    refine dvd_mul_of_dvd_right ?_ _
    exact dvd_sum fun i hi => (term_three_dvd m i (Nat.lt_succ_iff.mp (mem_range.mp hi))).2
  have hcop : IsCoprime ((m : ℤ) + 1) ((m : ℤ) + 2) := ⟨-1, 1, by ring⟩
  obtain ⟨c, hc⟩ := hcop.mul_dvd h6 h2
  refine ⟨c, ?_⟩
  push_cast
  linear_combination ((m : ℤ) + 1) * ((m : ℤ) + 2) ^ 2 * hc

/-- Conjecture 1 with an extra factor $2$: $2n^2(2n+1)^2$ divides $S_2(2n)$ for every $n \ge 0$. -/
theorem conjecture_one_two (n : ℕ) : 2 * (n : ℤ) ^ 2 * (2 * n + 1) ^ 2 ∣ S 2 (2 * n) := by
  obtain ⟨c, hc⟩ := S_two_dvd (2 * n)
  refine ⟨c, mul_left_cancel₀ (two_ne_zero' ℤ) ?_⟩
  push_cast at hc
  linear_combination hc

/-- Bala's Conjecture 1 on OEIS A357559: $n^2(2n+1)^2$ divides $S_2(2n)$ for every $n \ge 0$. -/
theorem conjecture_one (n : ℕ) : (n : ℤ) ^ 2 * (2 * n + 1) ^ 2 ∣ S 2 (2 * n) := by
  exact dvd_trans ⟨2, by ring⟩ (conjecture_one_two n)

/-- The FORMULA conjecture with an extra factor $2$: $2n^2(2n+1)^3$ divides $3S_3(2n)$ for every
$n \ge 0$. -/
theorem formula_conjecture_two (n : ℕ) :
    2 * (n : ℤ) ^ 2 * (2 * n + 1) ^ 3 ∣ 3 * S 3 (2 * n) := by
  obtain ⟨c, hc⟩ := S_three_dvd (2 * n)
  refine ⟨c, mul_left_cancel₀ (two_ne_zero' ℤ) ?_⟩
  push_cast at hc
  linear_combination hc

/-- Bala's FORMULA conjecture on OEIS A357559: $3\,a(2n) \equiv 0 \pmod{n^2(2n+1)^3}$ for every
$n \ge 0$, where $a = S_3$. -/
theorem formula_conjecture (n : ℕ) : (n : ℤ) ^ 2 * (2 * n + 1) ^ 3 ∣ 3 * S 3 (2 * n) := by
  exact dvd_trans ⟨2, by ring⟩ (formula_conjecture_two n)

/-! ### Sanity checks -/

/-- The first values of `S 3`, OEIS A357559. -/
theorem S_three_first : (List.range 5).map (S 3) = [0, 4, 270, 8448, 192000] := by decide

/-- The first values of `S 0`, the Apéry numbers A005258. -/
theorem S_zero_first : (List.range 5).map (S 0) = [1, 3, 19, 147, 1251] := by decide

/-- The factor $2$ in `S_two_dvd` is needed: $2^2 \cdot 3^2 \nmid S_2(2) = 126$. -/
theorem S_two_two : S 2 2 = 126 ∧ ¬ (2 : ℤ) ^ 2 * 3 ^ 2 ∣ S 2 2 := by decide

/-- The factor $6$ in `S_three_dvd` cannot be lowered: $1^2 \cdot 2^3 \nmid 3S_3(1)$ and
$3^2 \cdot 4^3 \nmid 2S_3(3)$. -/
theorem S_three_constant :
    ¬ (1 : ℤ) ^ 2 * 2 ^ 3 ∣ 3 * S 3 1 ∧ ¬ (3 : ℤ) ^ 2 * 4 ^ 3 ∣ 2 * S 3 3 := by
  decide

/-- The factor $3$ in the FORMULA conjecture is needed: $3^2 \cdot 7^3 \nmid S_3(6)$. -/
theorem S_three_six : ¬ (3 : ℤ) ^ 2 * 7 ^ 3 ∣ S 3 6 := by decide

end OeisA357559

end
