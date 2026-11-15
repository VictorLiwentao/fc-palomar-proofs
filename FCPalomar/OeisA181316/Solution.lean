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
# OEIS A181316 and A180606: Hanna's $q$-integer powers

Write $[n]_q = 1 + q + \dots + q^{n-1}$. Paul D. Hanna (OEIS A181316, 2010) conjectures that
$\exp\left(\sum_{n \ge 1} (q-1)\left(\frac{q^n-1}{q-1}\right)^{n-1} \frac{x^n}{n}\right)$ has
integer coefficients for every integer $q > 1$. A181316 is the case $q = 3$ and A180606 is the
case $q = 2$. This file proves the conjecture for every integer $q \ne 1$, in a sharp form. Let
the exponent $e$ satisfy
- (E1) $e(pM) \equiv e(M) \pmod{\varphi(p^k)}$ whenever $p$ is prime and $p^k \mid pM$, and
- (E2) $e(n) \ge 1$ for $n \ge 2$.

Then $\exp\left(\sum_{n \ge 1} c\,[n]_q^{e(n)} x^n/n\right)$ has integer coefficients if and only
if every prime dividing $q - 1$ divides $c$ (`integral_iff_of_exponent`). The exponents $n - 1$
(A181316, A180606) and $n$ (A155206, A155210) satisfy (E1) and (E2), because
$\varphi(p^k) = p^{k-1}(p-1)$ divides $pM - M$ (`mul_modEq_totient`).

Call $b : \mathbb{N} \to \mathbb{Z}$ a *Gauss sequence* if $p^k \mid b(pM) - b(M)$ whenever $p$
is prime and $p^k \mid pM$.

*Step 1 (Dold's criterion, sufficiency; `exists_coeff_eq_intCast_of_gauss`).* For a Gauss
sequence, pairing the divisors $p^i e$ and $p^{i+1} e$ of $n$ shows
$n \mid \sum_{d \mid n} \mu(d) b(n/d)$. Möbius inversion gives $b(n) = \sum_{d \mid n} d\,c(d)$
with integers $c(d)$. Up to degree $N$ the exponential equals the finite Euler product
$\prod_{d=1}^{N} (1 - x^d)^{-c(d)}$, which has integer coefficients: both sides have constant
term $1$ and the same logarithmic derivative below degree $N$. This step reuses the Lean of the
package `FCPalomar/A158110`.

*Step 2 (Dold's criterion at a prime, necessity; `prime_dvd_sub_of_integral`).* Let the
exponential $G$ have integer coefficients. Since $(1 - x^d)^{-c} = 1 + c x^d$ up to degree $d$,
the integers $c(1), \dots, c(N)$ can be chosen one at a time so that $G$ agrees with
$\prod_{d=1}^{N} (1 - x^d)^{-c(d)}$ up to degree $N$ (`exists_eulerProduct`). Comparing
logarithmic derivatives gives $b(n) = \sum_{d \mid n} d\,c(d)$ for $1 \le n \le N$. For $N = p$
this gives $b(p) - b(1) = p\,c(p)$.

*Step 3 (the congruences; `prime_pow_dvd_b_sub`).* Let $b(n) = c\,[n]_q^{e(n)}$, let $N = pM$
with $M \ge 1$, and let $p^k \mid N$ with $k \ge 1$. The tools are $[mn]_q = [m]_q\,[n]_{q^m}$
and $q - 1 \mid [n]_q - n$. Together they give $p^k \mid [p^k m]_q$ when $p \mid q - 1$.
- If $p \mid q - 1$, then $p \mid c$ by hypothesis, $p^k \mid [N]_q$ and $p^{k-1} \mid [M]_q$.
  With (E2), $p^k$ divides both $b(N)$ and $b(M)$.
- If $p \nmid q - 1$, then $p^k$ divides $q^N - q^M = (q - 1)([N]_q - [M]_q)$: if $p \mid q$
  because $M \ge k$, and otherwise by Euler's theorem. So $[N]_q \equiv [M]_q \pmod{p^k}$.
  - If $p \nmid [M]_q$, Euler's theorem and (E1) give
    $[N]_q^{e(N)} \equiv [M]_q^{e(M)} \pmod{p^k}$.
  - If $p \mid [M]_q$, write $M = p^{k-1} m$. Fermat's theorem gives
    $q^m \equiv q^M \equiv 1 \pmod p$, so $p \mid [m]_q$ and $p^{k-1} \mid [p^{k-1}]_{q^m}$.
    Hence $p^k$ divides $[M]_q$ and $[N]_q$, and with (E2) both powers vanish modulo $p^k$.

Steps 1 and 3 give sufficiency.

*Step 4 (necessity; `not_prime_dvd_b_sub`).* If $p \mid q - 1$ and $p \nmid c$, then
$p \mid [p]_q$, so $b(p) - b(1) \equiv -c \not\equiv 0 \pmod p$. By Step 2 the series is not
integral.

*Step 5 (Hanna's formulas).* For $q \ne 1$ the identity $(q - 1)[n]_q = q^n - 1$ turns Hanna's
coefficient into $(q - 1)[n]_q^{n-1}$ (`hannaSeries_eq`), and $c = q - 1$ meets the condition on
primes. In the same way $(m^n - 1)^n/(m - 1)^{n-1} = (m - 1)[n]_m^n$.

The file ends with the first terms $1, 1, 2, 18$ of A180606 and $1, 2, 6, 122$ of A181316,
computed from the recurrence $(n+1)\,a(n+1) = \sum_{i+j=n} b(i+1)\,a(j)$.

*References:*
- Paul D. Hanna, [A181316](https://oeis.org/A181316) and [A180606](https://oeis.org/A180606),
  2010.
- Paul D. Hanna, [A155206](https://oeis.org/A155206) and [A155210](https://oeis.org/A155210),
  2009.
- A. Dold, *Fixed point indices of iterated maps*, Invent. Math. 74 (1983), 419–435.
- R. P. Stanley, *Enumerative Combinatorics*, Vol. 2, Cambridge Univ. Press, 1999,
  Exercise 5.2(a).
-/

@[expose] public section

namespace OeisA181316

open PowerSeries Finset
open scoped ArithmeticFunction.Moebius Pointwise

/-! ## Definitions -/

/-- The $q$-integer $[n]_q = \sum_{i < n} q^i$. For $q \ne 1$ it equals $(q^n - 1)/(q - 1)$;
for $q = 1$ it is $n$. -/
def qInt (q : ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, q ^ i

/-- Hanna's series $\sum_{n \ge 1} (q-1)\left(\frac{q^n-1}{q-1}\right)^{n-1} \frac{x^n}{n}$
over $\mathbb{Q}$, written as in A181316. -/
noncomputable def hannaSeries (q : ℤ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else
    ((q : ℚ) - 1) * (((q : ℚ) ^ n - 1) / ((q : ℚ) - 1)) ^ (n - 1) / n

/-- The series $\sum_{n \ge 1} c\,[n]_q^{e(n)} x^n / n$ over $\mathbb{Q}$. -/
noncomputable def logSeries (q c : ℤ) (e : ℕ → ℕ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (c : ℚ) * (qInt q n : ℚ) ^ e n / n

/-! ## $q$-integers -/

theorem sub_one_mul_qInt (q : ℤ) (n : ℕ) : (q - 1) * qInt q n = q ^ n - 1 :=
  mul_geom_sum q n

@[simp] theorem qInt_zero (q : ℤ) : qInt q 0 = 0 := by simp [qInt]

@[simp] theorem qInt_one (q : ℤ) : qInt q 1 = 1 := by simp [qInt]

theorem qInt_add (q : ℤ) (m n : ℕ) : qInt q (m + n) = qInt q m + q ^ m * qInt q n := by
  simp [qInt, sum_range_add, pow_add, mul_sum]

/-- $[mn]_q = [m]_q [n]_{q^m}$. -/
theorem qInt_mul (q : ℤ) (m n : ℕ) : qInt q (m * n) = qInt q m * qInt (q ^ m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, qInt_add, ih, qInt_add (q ^ m) n 1, qInt_one, pow_mul]
    ring

/-- $q - 1 \mid [n]_q - n$. -/
theorem sub_one_dvd_qInt_sub (q : ℤ) (n : ℕ) : q - 1 ∣ qInt q n - n := by
  have h : qInt q n - n = ∑ i ∈ range n, (q ^ i - 1 ^ i) := by
    simp [qInt, sum_sub_distrib]
  rw [h]
  exact dvd_sum fun i _ => sub_dvd_pow_sub_pow q 1 i

/-- If $p \mid q - 1$, then $p^k \mid [p^k m]_q$. -/
theorem pow_dvd_qInt {q : ℤ} {p : ℕ} (hq : (p : ℤ) ∣ q - 1) (k m : ℕ) :
    (p : ℤ) ^ k ∣ qInt q (p ^ k * m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : p ^ (k + 1) * m = p ^ k * m * p := by ring
    rw [e, qInt_mul, pow_succ]
    refine mul_dvd_mul ih ?_
    have h1 : (p : ℤ) ∣ q ^ (p ^ k * m) - 1 := by
      simpa using hq.trans (sub_dvd_pow_sub_pow q 1 (p ^ k * m))
    have h2 := h1.trans (sub_one_dvd_qInt_sub (q ^ (p ^ k * m)) p)
    simpa using dvd_add h2 (dvd_refl (p : ℤ))

/-! ## Fermat and Euler -/

theorem prime_dvd_pow_prime_pow_sub {p : ℕ} (hp : p.Prime) (x : ℤ) (j : ℕ) :
    (p : ℤ) ∣ x ^ p ^ j - x := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card_pow, sub_self]

/-- Euler's theorem for a prime power: $p^k \mid y^{\varphi(p^k)} - 1$ when $p \nmid y$. -/
theorem prime_pow_dvd_pow_totient_sub_one {p : ℕ} (hp : p.Prime) {y : ℤ} (hy : ¬(p : ℤ) ∣ y)
    {k : ℕ} (hk : 0 < k) : (p : ℤ) ^ k ∣ y ^ Nat.totient (p ^ k) - 1 := by
  have hcop : IsCoprime y p :=
    ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hy).symm
  have hf : (p : ℤ) ∣ y ^ (p - 1) - 1 :=
    (Int.ModEq.pow_card_sub_one_eq_one hp hcop).symm.dvd
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := dvd_sub_pow_of_dvd_sub hf j
  rw [one_pow, ← pow_mul] at h
  rwa [Nat.totient_prime_pow hp (by omega : 0 < j + 1), Nat.add_sub_cancel, mul_comm]

/-! ## The three cases -/

theorem isCoprime_of_not_dvd {p : ℕ} (hp : p.Prime) {y : ℤ} (hy : ¬(p : ℤ) ∣ y) (k : ℕ) :
    IsCoprime ((p : ℤ) ^ k) y :=
  IsCoprime.pow_left ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hy)

/-- If $p \nmid q - 1$ and $p^k \mid pM$, then $[pM]_q \equiv [M]_q \pmod{p^k}$. -/
theorem prime_pow_dvd_qInt_sub {q : ℤ} {p : ℕ} (hp : p.Prime) (hq : ¬(p : ℤ) ∣ q - 1)
    {k M : ℕ} (hM : M ≠ 0) (hk : p ^ k ∣ p * M) :
    (p : ℤ) ^ k ∣ qInt q (p * M) - qInt q M := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjM : p ^ j ∣ M := by
    rw [pow_succ', ] at hk
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos hk
  have key : (p : ℤ) ^ (j + 1) ∣ q ^ (p * M) - q ^ M := by
    by_cases hpq : (p : ℤ) ∣ q
    · have hle : j + 1 ≤ M :=
        (Nat.lt_pow_self hp.one_lt).trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hjM)
      have h1 : (p : ℤ) ^ (j + 1) ∣ q ^ M :=
        (pow_dvd_pow _ hle).trans (pow_dvd_pow_of_dvd hpq M)
      have h2 : q ^ M ∣ q ^ (p * M) :=
        pow_dvd_pow q (Nat.le_mul_of_pos_left M hp.pos)
      exact dvd_sub (h1.trans h2) h1
    · obtain ⟨m, rfl⟩ := hjM
      have he := prime_pow_dvd_pow_totient_sub_one hp hpq (by omega : 0 < j + 1)
      rw [Nat.totient_prime_pow hp (by omega : 0 < j + 1), Nat.add_sub_cancel] at he
      have he' := he.trans (sub_dvd_pow_sub_pow (q ^ (p ^ j * (p - 1))) 1 m)
      rw [one_pow, ← pow_mul] at he'
      have hsplit : p * (p ^ j * m) = p ^ j * m + p ^ j * (p - 1) * m := by
        have := hp.one_lt
        zify [hp.one_lt.le]
        ring
      rw [hsplit, pow_add q]
      have : q ^ (p ^ j * m) * q ^ (p ^ j * (p - 1) * m) - q ^ (p ^ j * m) =
          q ^ (p ^ j * m) * (q ^ (p ^ j * (p - 1) * m) - 1) := by ring
      rw [this]
      exact dvd_mul_of_dvd_right he' _
  have hmul : (q - 1) * (qInt q (p * M) - qInt q M) = q ^ (p * M) - q ^ M := by
    rw [mul_sub, sub_one_mul_qInt, sub_one_mul_qInt]
    ring
  rw [← hmul] at key
  exact (isCoprime_of_not_dvd hp hq (j + 1)).dvd_of_dvd_mul_left key

/-- If $p \nmid q - 1$, $p \mid [M]_q$ and $p^j \mid M$, then $p^{j+1} \mid [M]_q$. -/
theorem prime_pow_succ_dvd_qInt {q : ℤ} {p : ℕ} (hp : p.Prime) (hq : ¬(p : ℤ) ∣ q - 1)
    {j M : ℕ} (hjM : p ^ j ∣ M) (hdvd : (p : ℤ) ∣ qInt q M) :
    (p : ℤ) ^ (j + 1) ∣ qInt q M := by
  have hpZ := Nat.prime_iff_prime_int.mp hp
  obtain ⟨m, rfl⟩ := hjM
  have h1 : (p : ℤ) ∣ q ^ (p ^ j * m) - 1 := by
    rw [← sub_one_mul_qInt]
    exact dvd_mul_of_dvd_right hdvd _
  have h2 : (p : ℤ) ∣ (q ^ m) ^ p ^ j - q ^ m := prime_dvd_pow_prime_pow_sub hp _ j
  rw [← pow_mul, mul_comm m] at h2
  have h3 : (p : ℤ) ∣ q ^ m - 1 := by
    have := dvd_sub h1 h2
    rwa [sub_sub_sub_cancel_left] at this
  have h4 : (p : ℤ) ∣ qInt q m := by
    rw [← sub_one_mul_qInt] at h3
    exact (hpZ.dvd_or_dvd h3).resolve_left hq
  rw [mul_comm, qInt_mul, pow_succ']
  refine mul_dvd_mul h4 ?_
  simpa using pow_dvd_qInt h3 j 1

/-- Unit powers: if $x \equiv y \pmod{p^k}$, $p \nmid y$ and $a \equiv b \pmod{\varphi(p^k)}$,
then $x^a \equiv y^b \pmod{p^k}$. -/
theorem prime_pow_dvd_pow_sub_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) {x y : ℤ}
    (hxy : (p : ℤ) ^ k ∣ x - y) (hy : ¬(p : ℤ) ∣ y) {a b : ℕ}
    (hab : a ≡ b [MOD Nat.totient (p ^ k)]) : (p : ℤ) ^ k ∣ x ^ a - y ^ b := by
  set T := Nat.totient (p ^ k)
  have hT := prime_pow_dvd_pow_totient_sub_one hp hy hk
  have h1 : (p : ℤ) ^ k ∣ x ^ a - y ^ a := hxy.trans (sub_dvd_pow_sub_pow x y a)
  have hpow : ∀ s, (p : ℤ) ^ k ∣ (y ^ T) ^ s - 1 := fun s => by
    simpa using hT.trans (sub_dvd_pow_sub_pow (y ^ T) 1 s)
  have h2 : (p : ℤ) ^ k ∣ y ^ a - y ^ b := by
    have ea : y ^ a = (y ^ T) ^ (a / T) * y ^ (a % T) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have eb : y ^ b = (y ^ T) ^ (b / T) * y ^ (b % T) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [ea, eb, ← hab]
    have : (y ^ T) ^ (a / T) * y ^ (a % T) - (y ^ T) ^ (b / T) * y ^ (a % T) =
        (((y ^ T) ^ (a / T) - 1) - ((y ^ T) ^ (b / T) - 1)) * y ^ (a % T) := by ring
    rw [this]
    exact dvd_mul_of_dvd_left (dvd_sub (hpow _) (hpow _)) _
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-- The Gauss congruences for $b(n) = c\,[n]_q^{e(n)}$ under the radical condition. -/
theorem prime_pow_dvd_b_sub {q c : ℤ} {e : ℕ → ℕ}
    (he1 : ∀ p k M : ℕ, p.Prime → p ^ k ∣ p * M → e (p * M) ≡ e M [MOD Nat.totient (p ^ k)])
    (he2 : ∀ n, 2 ≤ n → 1 ≤ e n)
    (hc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ q - 1 → (p : ℤ) ∣ c)
    {p k M : ℕ} (hp : p.Prime) (hk : p ^ k ∣ p * M) :
    (p : ℤ) ^ k ∣ c * qInt q (p * M) ^ e (p * M) - c * qInt q M ^ e M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM0
  · simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have hM : M ≠ 0 := hM0.ne'
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjM : p ^ j ∣ M := by
    rw [pow_succ'] at hk
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos hk
  have hN2 : 2 ≤ p * M := le_trans hp.two_le (Nat.le_mul_of_pos_right p hM0)
  have heN : e (p * M) ≠ 0 := by have := he2 _ hN2; omega
  by_cases hq : (p : ℤ) ∣ q - 1
  · -- Case C: `p ∣ q - 1`, so `p ∣ c`.
    have hN : (p : ℤ) ^ (j + 1) ∣ qInt q (p * M) ^ e (p * M) := by
      obtain ⟨t, ht⟩ := hk
      rw [ht]
      exact (pow_dvd_qInt hq (j + 1) t).trans (dvd_pow_self _ (ht ▸ heN))
    have hMd : (p : ℤ) ^ j ∣ qInt q M ^ e M := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      have hpM : p ∣ M := (dvd_pow_self p hj.ne').trans hjM
      have heM : e M ≠ 0 := by
        have := he2 M (le_trans hp.two_le (Nat.le_of_dvd hM0 hpM))
        omega
      obtain ⟨t, ht⟩ := hjM
      rw [ht]
      exact (pow_dvd_qInt hq j t).trans (dvd_pow_self _ (ht ▸ heM))
    refine dvd_sub (dvd_mul_of_dvd_right hN c) ?_
    rw [pow_succ']
    exact mul_dvd_mul (hc p hp hq) hMd
  rw [← mul_sub]
  refine dvd_mul_of_dvd_right ?_ c
  have hdiff := prime_pow_dvd_qInt_sub hp hq hM hk
  by_cases hfM : (p : ℤ) ∣ qInt q M
  · -- Case B: `p ∤ q - 1` and `p ∣ [M]_q`.
    have hMk := prime_pow_succ_dvd_qInt hp hq hjM hfM
    have hM1 : M ≠ 1 := by
      rintro rfl
      rw [qInt_one] at hfM
      exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one hfM
    have heM : e M ≠ 0 := by have := he2 M (by omega); omega
    have hNk : (p : ℤ) ^ (j + 1) ∣ qInt q (p * M) := by
      simpa using dvd_add hdiff hMk
    exact dvd_sub (hNk.trans (dvd_pow_self _ heN)) (hMk.trans (dvd_pow_self _ heM))
  · -- Case A: `p ∤ q - 1` and `p ∤ [M]_q`.
    exact prime_pow_dvd_pow_sub_pow hp (Nat.succ_pos j) hdiff hfM (he1 p (j + 1) M hp hk)

/-- The congruence fails at $N = p$, $M = 1$ when $p \mid q - 1$ and $p \nmid c$. -/
theorem not_prime_dvd_b_sub {q c : ℤ} {e : ℕ → ℕ} (he2 : ∀ n, 2 ≤ n → 1 ≤ e n) {p : ℕ}
    (hp : p.Prime) (hq : (p : ℤ) ∣ q - 1) (hc : ¬(p : ℤ) ∣ c) :
    ¬(p : ℤ) ∣ c * qInt q p ^ e p - c * qInt q 1 ^ e 1 := by
  intro h
  have hep : e p ≠ 0 := by have := he2 p hp.two_le; omega
  have h1 : (p : ℤ) ∣ qInt q p := by simpa using pow_dvd_qInt hq 1 1
  have h2 : (p : ℤ) ∣ c * qInt q p ^ e p := dvd_mul_of_dvd_right (h1.trans (dvd_pow_self _ hep)) c
  rw [qInt_one, one_pow, mul_one] at h
  exact hc (by simpa using dvd_sub h2 h)

/-! ## Logarithmic derivatives

This section and the next two are copied from the package `FCPalomar/A158110`
(Apache-2.0, Wentao Li). -/

section LogDeriv

/-- Two series with equal constant terms whose logarithmic derivatives agree below degree `N`
agree up to degree `N`. -/
theorem coeff_eq_of_derivative_eq_mul {F G f g : ℚ⟦X⟧} (hF : d⁄dX F = f * F)
    (hG : d⁄dX G = g * G) (h0 : constantCoeff F = constantCoeff G) {N : ℕ}
    (hfg : ∀ i < N, coeff i f = coeff i g) : ∀ i ≤ N, coeff i F = coeff i G := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | j
    · simpa using h0
    · have e1 := congrArg (coeff j) hF
      have e2 := congrArg (coeff j) hG
      rw [coeff_derivative, coeff_mul] at e1 e2
      have hsum : ∑ x ∈ antidiagonal j, coeff x.1 f * coeff x.2 F =
          ∑ x ∈ antidiagonal j, coeff x.1 g * coeff x.2 G := by
        refine sum_congr rfl fun x hx => ?_
        have hx' := mem_antidiagonal.mp hx
        rw [hfg x.1 (by omega), ih x.2 (by omega) (by omega)]
      have hne : (j : ℚ) + 1 ≠ 0 := by positivity
      exact mul_right_cancel₀ hne (e1.trans (hsum.trans e2.symm))

theorem derivative_mul_of {F G f g : ℚ⟦X⟧} (hF : d⁄dX F = f * F)
    (hG : d⁄dX G = g * G) : d⁄dX (F * G) = (f + g) * (F * G) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hF, hG]
  ring

theorem derivative_pow_of {F f : ℚ⟦X⟧} (hF : d⁄dX F = f * F) (n : ℕ) :
    d⁄dX (F ^ n) = (n * f) * F ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, derivative_mul_of ih hF]
    push_cast
    ring

theorem derivative_prod_of {ι : Type*} (s : Finset ι) {F f : ι → ℚ⟦X⟧}
    (hF : ∀ i ∈ s, d⁄dX (F i) = f i * F i) :
    d⁄dX (∏ i ∈ s, F i) = (∑ i ∈ s, f i) * ∏ i ∈ s, F i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact derivative_mul_of (hF a (mem_insert_self a s))
      (ih fun i hi => hF i (mem_insert_of_mem hi))

/-- The chain rule for $\exp \circ L$. -/
theorem derivative_exp_subst {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) :
    d⁄dX (subst L (exp ℚ)) = d⁄dX L * subst L (exp ℚ) := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hL), derivative_exp, mul_comm]

theorem constantCoeff_exp_subst {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) :
    constantCoeff (subst L (exp ℚ)) = 1 := by
  have ha := HasSubst.of_constantCoeff_zero' hL
  have h1 : subst L (exp ℚ) = subst L (exp ℚ - 1) + 1 := by
    rw [← coe_substAlgHom ha, map_sub, map_one, sub_add_cancel]
  have h2 : constantCoeff (subst L (exp ℚ - 1)) = 0 :=
    constantCoeff_subst_eq_zero hL _ (by simp)
  rw [h1, map_add, map_one, h2, zero_add]

end LogDeriv

/-! ## Finite Euler products -/

section EulerProduct

/-- The power series over `ℚ` with integer coefficients. -/
noncomputable abbrev intSeries : Subring ℚ⟦X⟧ := (map (Int.castRingHom ℚ)).range

/-- The series $1 / (1 - x^d) = \sum_{k \ge 0} x^{dk}$. -/
noncomputable def geom (d : ℕ) : ℚ⟦X⟧ := mk fun n => if d ∣ n then 1 else 0

/-- The logarithmic derivative $d x^{d-1} / (1 - x^d)$ of $1 / (1 - x^d)$. -/
noncomputable def geomLogDeriv (d : ℕ) : ℚ⟦X⟧ := (d : ℚ⟦X⟧) * X ^ (d - 1) * geom d

/-- The factor $(1 - x^d)^{-c}$, written with natural exponents. -/
noncomputable def factor (d : ℕ) (c : ℤ) : ℚ⟦X⟧ := geom d ^ c.toNat * (1 - X ^ d) ^ (-c).toNat

/-- The finite product $\prod_{d=1}^{N} (1 - x^d)^{-c(d)}$. -/
noncomputable def eulerProduct (c : ℕ → ℤ) (N : ℕ) : ℚ⟦X⟧ := ∏ d ∈ Icc 1 N, factor d (c d)

theorem geom_mul_one_sub {d : ℕ} (hd : 0 < d) : geom d * (1 - X ^ d) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one, geom, coeff_mk, coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.not_le.mpr hd]
  · rcases le_or_gt d n with h | h
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
      simp [Nat.dvd_add_right (dvd_refl d), hd.ne']
    · have hnd : ¬d ∣ n := fun hdn => absurd (Nat.le_of_dvd hn hdn) (by omega)
      simp [hnd, Nat.not_le.mpr h, hn.ne']

theorem derivative_one_sub_X_pow {d : ℕ} (hd : 0 < d) :
    d⁄dX (1 - X ^ d) = -geomLogDeriv d * (1 - X ^ d) := by
  have h := geom_mul_one_sub hd
  rw [map_sub, derivative_one, derivative_pow, derivative_X, geomLogDeriv]
  linear_combination ((d : ℚ⟦X⟧) * X ^ (d - 1)) * h

theorem derivative_geom {d : ℕ} (hd : 0 < d) :
    d⁄dX (geom d) = geomLogDeriv d * geom d := by
  have h := geom_mul_one_sub hd
  have h' := congrArg (d⁄dX) h
  rw [Derivation.leibniz, derivative_one_sub_X_pow hd, derivative_one, smul_eq_mul,
    smul_eq_mul] at h'
  linear_combination geom d * h' - (d⁄dX (geom d) - geomLogDeriv d * geom d) * h

theorem derivative_factor {d : ℕ} (hd : 0 < d) (c : ℤ) :
    d⁄dX (factor d c) = ((c : ℚ⟦X⟧) * geomLogDeriv d) * factor d c := by
  rw [factor, derivative_mul_of (derivative_pow_of (derivative_geom hd) _)
    (derivative_pow_of (derivative_one_sub_X_pow hd) _)]
  have key : ((c.toNat : ℤ) : ℚ⟦X⟧) - (((-c).toNat : ℤ) : ℚ⟦X⟧) = (c : ℚ⟦X⟧) := by
    rw [← Int.cast_sub, Int.toNat_sub_toNat_neg]
  simp only [Int.cast_natCast] at key
  rw [← key]
  ring

theorem derivative_eulerProduct (c : ℕ → ℤ) (N : ℕ) :
    d⁄dX (eulerProduct c N) =
      (∑ d ∈ Icc 1 N, (c d : ℚ⟦X⟧) * geomLogDeriv d) * eulerProduct c N :=
  derivative_prod_of _ fun d hd => derivative_factor (mem_Icc.mp hd).1 (c d)

theorem constantCoeff_eulerProduct (c : ℕ → ℤ) (N : ℕ) :
    constantCoeff (eulerProduct c N) = 1 := by
  rw [eulerProduct, map_prod]
  refine prod_eq_one fun d hd => ?_
  have hd0 : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
  rw [factor, map_mul, map_pow, map_pow, ← coeff_zero_eq_constantCoeff_apply, geom, coeff_mk]
  simp [hd0]

theorem geom_mem (d : ℕ) : geom d ∈ intSeries :=
  ⟨mk fun n => if d ∣ n then 1 else 0, by
    ext n
    simp only [coeff_map, coeff_mk, geom]
    split_ifs <;> simp⟩

theorem one_sub_X_pow_mem (d : ℕ) : (1 - X ^ d : ℚ⟦X⟧) ∈ intSeries :=
  Subring.sub_mem _ (Subring.one_mem _) (Subring.pow_mem _ (RingHom.mem_range.mpr ⟨X, map_X _⟩) d)

theorem eulerProduct_mem (c : ℕ → ℤ) (N : ℕ) : eulerProduct c N ∈ intSeries :=
  Subring.prod_mem _ fun d _ => Subring.mul_mem _ (Subring.pow_mem _ (geom_mem d) _)
    (Subring.pow_mem _ (one_sub_X_pow_mem d) _)

theorem coeff_geomLogDeriv {d : ℕ} (hd : 0 < d) (j : ℕ) :
    coeff j (geomLogDeriv d) = if d ∣ j + 1 then (d : ℚ) else 0 := by
  rw [geomLogDeriv, mul_assoc, ← map_natCast (C (R := ℚ)) d, coeff_C_mul, coeff_X_pow_mul',
    geom]
  rcases le_or_gt d (j + 1) with h | h
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
    have hj : j - (d - 1) = t := by omega
    rw [ite_eq_left (by omega), coeff_mk, hj, ht]
    by_cases hdt : d ∣ t
    · simp [hdt, Nat.dvd_add_right (dvd_refl d)]
    · simp [hdt, Nat.dvd_add_right (dvd_refl d)]
  · have hnd : ¬d ∣ j + 1 := fun hdj => absurd (Nat.le_of_dvd (by omega) hdj) (by omega)
    rw [ite_eq_right (by omega), ite_eq_right hnd, mul_zero]

theorem coeff_logDeriv_eulerProduct (c : ℕ → ℤ) {N j : ℕ} (hj : j < N) :
    coeff j (∑ d ∈ Icc 1 N, (c d : ℚ⟦X⟧) * geomLogDeriv d) =
      ∑ d ∈ (j + 1).divisors, (d : ℚ) * c d := by
  rw [map_sum]
  have hfilter : (Icc 1 N).filter (· ∣ j + 1) = (j + 1).divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨h, by omega⟩
    · rintro ⟨h, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hj⟩, h⟩
  rw [← hfilter, sum_filter]
  refine sum_congr rfl fun d hd => ?_
  rw [← map_intCast (C (R := ℚ)), coeff_C_mul, coeff_geomLogDeriv (mem_Icc.mp hd).1 j]
  split_ifs <;> ring

end EulerProduct

/-! ## The integrality criterion (from `FCPalomar/A158110`) -/

/-- If $n \mid \sum_{d \mid n} \mu(d) b(n/d)$ for all $n \ge 1$, then
$\exp\left(\sum_{n \ge 1} b(n) x^n / n\right)$ has integer coefficients. -/
theorem exists_coeff_eq_intCast_of_dvd (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * b x.2) (N : ℕ) :
    ∃ z : ℤ, coeff N (subst (mk fun n => if n = 0 then 0 else (b n : ℚ) / n) (exp ℚ)) = z := by
  set L : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else (b n : ℚ) / n with hLdef
  set c : ℕ → ℤ := fun n : ℕ => (∑ x ∈ n.divisorsAntidiagonal, μ x.1 * b x.2) / (n : ℤ)
    with hc
  have hinv : ∀ n : ℕ, 0 < n → ∑ i ∈ n.divisors, (i : ℤ) * c i = b n := by
    refine ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr fun n hn => ?_
    simp only [Int.cast_id, hc]
    exact (Int.mul_ediv_cancel' (hb n hn)).symm
  have hL0 : constantCoeff L = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hLdef, coeff_mk, ite_eq_left rfl]
  have heq := coeff_eq_of_derivative_eq_mul (derivative_exp_subst hL0)
    (derivative_eulerProduct c N)
    (by rw [constantCoeff_exp_subst hL0, constantCoeff_eulerProduct]) (N := N)
    (fun i hi => by
      rw [coeff_derivative, coeff_logDeriv_eulerProduct c hi, hLdef, coeff_mk,
        ite_eq_right (by omega)]
      have h := hinv (i + 1) (by omega)
      have h' : ∑ d ∈ (i + 1).divisors, (d : ℚ) * c d = b (i + 1) := by exact_mod_cast h
      rw [h']
      field_simp
      push_cast
      ring) N le_rfl
  obtain ⟨G, hG⟩ := RingHom.mem_range.mp (eulerProduct_mem c N)
  exact ⟨coeff N G, by rw [heq, ← hG, coeff_map]; simp⟩

theorem sum_divisors_prime_pow_mul {p k N : ℕ} (hp : p.Prime) (hN : ¬p ∣ N) (F : ℕ → ℤ) :
    ∑ d ∈ (p ^ k * N).divisors, F d =
      ∑ i ∈ range (k + 1), ∑ e ∈ N.divisors, F (p ^ i * e) := by
  have hcop : (p ^ k).Coprime N :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hN)
  rw [Nat.divisors_mul, Finset.mul_def, sum_image hcop.mul_injOn_divisors, sum_product]
  simp only [Nat.sum_divisors_prime_pow hp]

/-! ## Gauss sequences

The Möbius pairing is adapted from `prime_pow_dvd_sum_moebius` and `dvd_sum_moebius` in
`FCPalomar/A158110`, with a general Gauss sequence in place of $q^{n^m}$. -/

/-- The Gauss congruences $b(pM) \equiv b(M) \pmod{p^k}$ whenever $p^k \mid pM$. -/
def Gauss (b : ℕ → ℤ) : Prop :=
  ∀ p k M : ℕ, p.Prime → p ^ k ∣ p * M → (p : ℤ) ^ k ∣ b (p * M) - b M

/-- Under the Gauss congruences, $p^k$ divides the Möbius sum at $p^k N$ when $p \nmid N$. -/
theorem prime_pow_dvd_sum_moebius {b : ℕ → ℤ} (hb : Gauss b) {p : ℕ} (hp : p.Prime) {k N : ℕ}
    (hk : 0 < k) (hN : ¬p ∣ N) :
    (p : ℤ) ^ k ∣ ∑ x ∈ (p ^ k * N).divisorsAntidiagonal, μ x.1 * b x.2 := by
  rw [Nat.sum_divisorsAntidiagonal (fun a c => μ a * b c),
    sum_divisors_prime_pow_mul hp hN, sum_comm]
  refine dvd_sum fun e he => ?_
  have hed : e ∣ N := (Nat.mem_divisors.mp he).1
  have hN0 : N ≠ 0 := (Nat.mem_divisors.mp he).2
  have hce : ∀ i, (p ^ i).Coprime e := fun i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hN (h.trans hed))
  have he0 : e ≠ 0 := fun h => hN0 (Nat.eq_zero_of_zero_dvd (h ▸ hed))
  obtain ⟨M, rfl⟩ := hed
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hmu : ∀ i, μ (p ^ i * e) = μ (p ^ i) * μ e := fun i =>
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hce i)
  rw [sum_range_succ', sum_range_succ', sum_eq_zero fun i _ => ?_]
  · have q0 : p ^ (j + 1) * (e * M) / (p ^ 0 * e) = p ^ (j + 1) * M := by
      rw [pow_zero, one_mul, show p ^ (j + 1) * (e * M) = e * (p ^ (j + 1) * M) by ring,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)]
    have q1 : p ^ (j + 1) * (e * M) / (p ^ (0 + 1) * e) = p ^ j * M := by
      rw [zero_add, pow_one,
        show p ^ (j + 1) * (e * M) = (p * e) * (p ^ j * M) by ring,
        Nat.mul_div_cancel_left _ (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero he0))]
    rw [q0, q1, hmu, hmu, pow_zero, ArithmeticFunction.moebius_apply_one, zero_add, pow_one,
      ArithmeticFunction.moebius_apply_prime hp]
    have ht := hb p (j + 1) (p ^ j * M) hp ⟨M, by ring⟩
    rw [show p * (p ^ j * M) = p ^ (j + 1) * M by ring] at ht
    obtain ⟨t, ht⟩ := ht
    exact ⟨μ e * t, by linear_combination (μ e) * ht⟩
  · rw [hmu, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
    simp

/-- Dold's congruence $n \mid \sum_{d \mid n} \mu(d) b(n/d)$ for a Gauss sequence. -/
theorem dvd_sum_moebius {b : ℕ → ℤ} (hb : Gauss b) {n : ℕ} (hn : 0 < n) :
    (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * b x.2 := by
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hv : k ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn.ne').mp hpk
  have hdecomp := Nat.ordProj_mul_ordCompl_eq_self n p
  have hdiv := prime_pow_dvd_sum_moebius hb hp (k := n.factorization p) (by omega)
    (Nat.not_dvd_ordCompl hp hn.ne')
  rw [hdecomp] at hdiv
  rw [← Int.natCast_dvd]
  push_cast
  exact (pow_dvd_pow _ hv).trans hdiv

/-- The series $\sum_{n \ge 1} b(n) x^n / n$ over $\mathbb{Q}$. -/
noncomputable def ofInt (b : ℕ → ℤ) : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else (b n : ℚ) / n

/-- **Dold's criterion, (⇐).** For a Gauss sequence $b$,
$\exp\left(\sum_{n \ge 1} b(n) x^n / n\right)$ has integer coefficients. -/
theorem exists_coeff_eq_intCast_of_gauss {b : ℕ → ℤ} (hb : Gauss b) (N : ℕ) :
    ∃ z : ℤ, coeff N (subst (ofInt b) (exp ℚ)) = z :=
  exists_coeff_eq_intCast_of_dvd b (fun _ hn => dvd_sum_moebius hb hn) N

/-! ## The converse at degree `N` -/

theorem constantCoeff_ofInt (b : ℕ → ℤ) : constantCoeff (ofInt b) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ofInt, coeff_mk, ite_eq_left rfl]

theorem coeff_derivative_ofInt (b : ℕ → ℤ) (j : ℕ) :
    coeff j (d⁄dX (ofInt b)) = b (j + 1) := by
  rw [coeff_derivative, ofInt, coeff_mk, ite_eq_right (Nat.succ_ne_zero j)]
  field_simp
  push_cast
  ring

/-- Two series with constant term `1` that agree up to degree `N` have logarithmic derivatives
that agree below degree `N`. -/
theorem coeff_logDeriv_eq {F G f g : ℚ⟦X⟧} (hF : d⁄dX F = f * F) (hG : d⁄dX G = g * G)
    (hF0 : constantCoeff F = 1) (hG0 : constantCoeff G = 1) {N : ℕ}
    (hFG : ∀ i ≤ N, coeff i F = coeff i G) : ∀ j < N, coeff j f = coeff j g := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have e1 := congrArg (coeff j) hF
    have e2 := congrArg (coeff j) hG
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a f * coeff b F), sum_range_succ, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, hF0, mul_one] at e1
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a g * coeff b G), sum_range_succ, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, hG0, mul_one] at e2
    have hsum : ∑ x ∈ range j, coeff x f * coeff (j - x) F =
        ∑ x ∈ range j, coeff x g * coeff (j - x) G := by
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.mp hx
      rw [ih x hx' (by omega), hFG (j - x) (by omega)]
    rw [hFG (j + 1) hj] at e1
    linarith

/-- `X ^ (d + 1)` divides `F - 1 - a X ^ d`: the series is $1 + a x^d$ up to degree `d`. -/
def Near (d : ℕ) (a : ℤ) (F : ℚ⟦X⟧) : Prop := X ^ (d + 1) ∣ F - 1 - (a : ℚ⟦X⟧) * X ^ d

theorem Near.mul {d : ℕ} (hd : 0 < d) {a b : ℤ} {F G : ℚ⟦X⟧} (hF : Near d a F) (hG : Near d b G) :
    Near d (a + b) (F * G) := by
  obtain ⟨R, hR⟩ := hF
  obtain ⟨S, hS⟩ := hG
  have hF' : F = 1 + (a : ℚ⟦X⟧) * X ^ d + X ^ (d + 1) * R := by rw [← hR]; ring
  have hG' : G = 1 + (b : ℚ⟦X⟧) * X ^ d + X ^ (d + 1) * S := by rw [← hS]; ring
  have hXX : (X : ℚ⟦X⟧) ^ d * X ^ d = X ^ (d + 1) * X ^ (d - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  refine ⟨R + S + (a : ℚ⟦X⟧) * X ^ d * S + (b : ℚ⟦X⟧) * X ^ d * R + X ^ (d + 1) * R * S +
    (a : ℚ⟦X⟧) * (b : ℚ⟦X⟧) * X ^ (d - 1), ?_⟩
  rw [hF', hG']
  push_cast
  linear_combination (a : ℚ⟦X⟧) * (b : ℚ⟦X⟧) * hXX

theorem near_one (d : ℕ) : Near d 0 1 := ⟨0, by simp⟩

theorem Near.pow {d : ℕ} (hd : 0 < d) {a : ℤ} {F : ℚ⟦X⟧} (hF : Near d a F) (n : ℕ) :
    Near d (n * a) (F ^ n) := by
  induction n with
  | zero => simpa using near_one d
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hd hF using 1
    push_cast
    ring

theorem near_geom {d : ℕ} (hd : 0 < d) : Near d 1 (geom d) := by
  have h := geom_mul_one_sub hd
  have h1 : geom d = 1 + geom d * X ^ d := by linear_combination h
  refine ⟨X ^ (d - 1) * geom d, ?_⟩
  have hXX : (X : ℚ⟦X⟧) ^ (d + 1) * X ^ (d - 1) = X ^ d * X ^ d := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  push_cast
  linear_combination (1 + X ^ d) * h1 - geom d * hXX

theorem near_one_sub {d : ℕ} : Near d (-1) (1 - X ^ d) := ⟨0, by push_cast; ring⟩

theorem near_factor {d : ℕ} (hd : 0 < d) (c : ℤ) : Near d c (factor d c) := by
  have h := ((near_geom hd).pow hd c.toNat).mul hd (near_one_sub.pow hd (-c).toNat)
  have key : (c.toNat : ℤ) * 1 + ((-c).toNat : ℤ) * (-1) = c := by
    have := Int.toNat_sub_toNat_neg c
    linarith
  rwa [key] at h

theorem coeff_mul_of_near {d : ℕ} {a : ℤ} {F : ℚ⟦X⟧} (hF : Near d a F) (E : ℚ⟦X⟧) {i : ℕ}
    (hi : i ≤ d) : coeff i (E * F) = coeff i E + if i = d then a * coeff 0 E else 0 := by
  obtain ⟨R, hR⟩ := hF
  have hF' : E * F = E + (a : ℚ⟦X⟧) * (X ^ d * E) + X ^ (d + 1) * (E * R) := by
    rw [show F = 1 + (a : ℚ⟦X⟧) * X ^ d + X ^ (d + 1) * R by rw [← hR]; ring]
    ring
  rw [hF', map_add, map_add, ← map_intCast (C (R := ℚ)), coeff_C_mul, coeff_X_pow_mul',
    coeff_X_pow_mul', ite_eq_right (show ¬d + 1 ≤ i by omega), add_zero]
  by_cases h : i = d
  · subst h
    simp
  · rw [ite_eq_right (show ¬d ≤ i by omega), ite_eq_right h]
    simp

theorem eulerProduct_succ (c : ℕ → ℤ) (N : ℕ) :
    eulerProduct c (N + 1) = eulerProduct c N * factor (N + 1) (c (N + 1)) := by
  rw [eulerProduct, eulerProduct, prod_Icc_succ_top (by omega)]

theorem eulerProduct_congr {c c' : ℕ → ℤ} {N : ℕ} (h : ∀ d ∈ Icc 1 N, c d = c' d) :
    eulerProduct c N = eulerProduct c' N :=
  prod_congr rfl fun d hd => by rw [h d hd]

/-- A series with integer coefficients and constant term `1` agrees with a finite Euler
product up to degree `N`. -/
theorem exists_eulerProduct {G : ℚ⟦X⟧} (hG : ∀ n, ∃ z : ℤ, coeff n G = z)
    (hG0 : constantCoeff G = 1) (N : ℕ) :
    ∃ c : ℕ → ℤ, ∀ i ≤ N, coeff i G = coeff i (eulerProduct c N) := by
  induction N with
  | zero =>
    refine ⟨0, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    simp [eulerProduct, hG0]
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨z, hz⟩ := hG (N + 1)
    obtain ⟨E, hE⟩ := RingHom.mem_range.mp (eulerProduct_mem c N)
    set D : ℤ := z - coeff (N + 1) E
    set c' := Function.update c (N + 1) D
    have hcc : eulerProduct c' N = eulerProduct c N :=
      eulerProduct_congr fun d hd => by
        simp only [c']
        rw [Function.update_of_ne (by have := (mem_Icc.mp hd).2; omega)]
    have hc'N : c' (N + 1) = D := Function.update_self _ _ _
    refine ⟨c', fun i hi => ?_⟩
    rw [eulerProduct_succ, hcc, hc'N,
      coeff_mul_of_near (near_factor (Nat.succ_pos N) D) _ hi]
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · rw [ite_eq_right (by omega), add_zero]
      exact hc i (by omega)
    · rw [ite_eq_left rfl, coeff_zero_eq_constantCoeff_apply, constantCoeff_eulerProduct, hz, ← hE,
        coeff_map]
      simp [D]

/-- **Dold's criterion, (⇒), at a prime.** If $\exp\left(\sum b(n) x^n/n\right)$ has integer
coefficients, then $p \mid b(p) - b(1)$. -/
theorem prime_dvd_sub_of_integral {b : ℕ → ℤ}
    (h : ∀ n, ∃ z : ℤ, coeff n (subst (ofInt b) (exp ℚ)) = z) {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ b p - b 1 := by
  have hL0 := constantCoeff_ofInt b
  obtain ⟨c, hc⟩ := exists_eulerProduct h (constantCoeff_exp_subst hL0) p
  have key := coeff_logDeriv_eq (derivative_exp_subst hL0) (derivative_eulerProduct c p)
    (constantCoeff_exp_subst hL0) (constantCoeff_eulerProduct c p) hc
  have hb : ∀ j < p, (b (j + 1) : ℚ) = ∑ d ∈ (j + 1).divisors, (d : ℚ) * c d := fun j hj => by
    rw [← coeff_derivative_ofInt, key j hj, coeff_logDeriv_eulerProduct c hj]
  have h1 := hb 0 hp.pos
  have h2 := hb (p - 1) (by have := hp.pos; omega)
  rw [Nat.sub_add_cancel hp.pos, hp.divisors, sum_pair hp.one_lt.ne] at h2
  simp only [zero_add, Nat.divisors_one, sum_singleton, Nat.cast_one, one_mul] at h1 h2
  refine ⟨c p, ?_⟩
  exact_mod_cast (show (b p : ℚ) - b 1 = p * c p by rw [h1, h2]; ring)

/-! ## The main theorems -/

theorem logSeries_eq_ofInt (q c : ℤ) (e : ℕ → ℕ) :
    logSeries q c e = ofInt fun n => c * qInt q n ^ e n := by
  ext n
  simp [logSeries, ofInt]

/-- **General exponent.** Let $e(pM) \equiv e(M) \pmod{\varphi(p^k)}$ whenever $p$ is prime and
$p^k \mid pM$ (equivalently, $e(N) \equiv e(N/p) \pmod{\varphi(p^{v_p(N)})}$ for every prime
$p \mid N$), and let $e(n) \ge 1$ for $n \ge 2$. Then for integers $q$ and $c$,
$\exp\left(\sum_{n \ge 1} c\,[n]_q^{e(n)} x^n / n\right)$ has integer coefficients if and only
if every prime dividing $q - 1$ divides $c$. -/
theorem integral_iff_of_exponent (q c : ℤ) (e : ℕ → ℕ)
    (he1 : ∀ p k M : ℕ, p.Prime → p ^ k ∣ p * M → e (p * M) ≡ e M [MOD Nat.totient (p ^ k)])
    (he2 : ∀ n, 2 ≤ n → 1 ≤ e n) :
    (∀ n, ∃ z : ℤ, coeff n (subst (logSeries q c e) (exp ℚ)) = z) ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ q - 1 → (p : ℤ) ∣ c := by
  rw [logSeries_eq_ofInt]
  constructor
  · intro h p hp hq
    by_contra hc
    exact not_prime_dvd_b_sub he2 hp hq hc (prime_dvd_sub_of_integral h hp)
  · intro hc n
    exact exists_coeff_eq_intCast_of_gauss
      (fun p k M hp hk => prime_pow_dvd_b_sub he1 he2 hc hp hk) n

/-- $pM \equiv M \pmod{\varphi(p^k)}$ when $p^k \mid pM$. -/
theorem mul_modEq_totient {p k M : ℕ} (hp : p.Prime) (hk : p ^ k ∣ p * M) :
    p * M ≡ M [MOD Nat.totient (p ^ k)] := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [Nat.modEq_one]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjM : p ^ j ∣ M := by
    rw [pow_succ'] at hk
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos hk
  obtain ⟨t, rfl⟩ := hjM
  rw [Nat.totient_prime_pow hp (by omega : 0 < j + 1), Nat.add_sub_cancel]
  have e : p * (p ^ j * t) = p ^ j * t + p ^ j * (p - 1) * t := by
    zify [hp.one_lt.le]
    ring
  rw [e]
  exact Nat.add_mul_mod_self_left _ _ _

theorem exponent_sub_one_modEq {p k M : ℕ} (hp : p.Prime) (hk : p ^ k ∣ p * M) :
    p * M - 1 ≡ M - 1 [MOD Nat.totient (p ^ k)] := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rw [mul_zero]
  refine Nat.ModEq.add_right_cancel' 1 ?_
  rw [Nat.sub_add_cancel hM, Nat.sub_add_cancel (Nat.mul_pos hp.pos hM)]
  exact mul_modEq_totient hp hk

/-- **Sharp form.** For integers $q$ and $c$,
$\exp\left(\sum_{n \ge 1} c\,[n]_q^{n-1} x^n / n\right)$ has integer coefficients if and only
if every prime dividing $q - 1$ divides $c$. For $q = 1$ the condition means $c = 0$. -/
theorem integral_iff (q c : ℤ) :
    (∀ n, ∃ z : ℤ, coeff n (subst (logSeries q c (fun n => n - 1)) (exp ℚ)) = z) ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ q - 1 → (p : ℤ) ∣ c :=
  integral_iff_of_exponent q c _ (fun _ _ _ hp hk => exponent_sub_one_modEq hp hk)
    (fun n hn => by omega)

theorem hannaSeries_eq {q : ℤ} (hq : q ≠ 1) :
    hannaSeries q = logSeries q (q - 1) (fun n => n - 1) := by
  have hq' : (q : ℚ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq)
  ext n
  have h : ((q : ℚ) ^ n - 1) / ((q : ℚ) - 1) = qInt q n := by
    rw [div_eq_iff hq']
    have := congrArg (Int.cast : ℤ → ℚ) (sub_one_mul_qInt q n)
    push_cast at this
    linear_combination -this
  simp only [hannaSeries, logSeries, coeff_mk, h]
  push_cast
  rfl

/-- Hanna's conjecture holds for every integer $q \ne 1$. -/
theorem hannaSeries_integral (q : ℤ) (hq : q ≠ 1) (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (hannaSeries q) (exp ℚ)) = z := by
  rw [hannaSeries_eq hq]
  exact (integral_iff q (q - 1)).mpr (fun _ _ h => h) n

/-- **Hanna's conjecture (A181316).** For every integer $q > 1$,
$\exp\left(\sum_{n \ge 1} (q-1)\left(\frac{q^n-1}{q-1}\right)^{n-1} \frac{x^n}{n}\right)$ has
integer coefficients. -/
theorem conjecture (q : ℤ) (hq : 1 < q) (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (hannaSeries q) (exp ℚ)) = z :=
  hannaSeries_integral q (by omega) n

/-- **OEIS A181316** ($q = 3$): $\exp\left(\sum_{n \ge 1} 2\left(\frac{3^n-1}{2}\right)^{n-1}
\frac{x^n}{n}\right)$ has integer coefficients. -/
theorem a181316_integral (n : ℕ) : ∃ z : ℤ, coeff n (subst (hannaSeries 3) (exp ℚ)) = z :=
  conjecture 3 (by norm_num) n

/-- **OEIS A180606** ($q = 2$): $\exp\left(\sum_{n \ge 1} (2^n - 1)^{n-1} x^n / n\right)$ has
integer coefficients. -/
theorem a180606_integral (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (mk fun n : ℕ => if n = 0 then (0 : ℚ) else
      ((2 : ℚ) ^ n - 1) ^ (n - 1) / n) (exp ℚ)) = z := by
  have h : (mk fun n : ℕ => if n = 0 then (0 : ℚ) else ((2 : ℚ) ^ n - 1) ^ (n - 1) / n) =
      hannaSeries 2 := by
    ext n
    simp [hannaSeries]
    norm_num
  rw [h]
  exact conjecture 2 (by norm_num) n

/-- **Hanna's claim in A155206 and A155210.** For every integer $m \ne 1$,
$\exp\left(\sum_{n \ge 1} \frac{(m^n - 1)^n}{(m - 1)^{n-1}} \frac{x^n}{n}\right)$ has integer
coefficients. A155206 is $m = 3$ and A155210 is $m = 4$. At $m = 1$ the expression is $0/0$. -/
theorem a155206_integral (m : ℤ) (hm : m ≠ 1) (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (mk fun n : ℕ => if n = 0 then (0 : ℚ) else
      ((m : ℚ) ^ n - 1) ^ n / ((m : ℚ) - 1) ^ (n - 1) / n) (exp ℚ)) = z := by
  have hm' : (m : ℚ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hm)
  have h : (mk fun n : ℕ => if n = 0 then (0 : ℚ) else
      ((m : ℚ) ^ n - 1) ^ n / ((m : ℚ) - 1) ^ (n - 1) / n) = logSeries m (m - 1) id := by
    ext n
    simp only [logSeries, coeff_mk, id]
    split_ifs with hn
    · rfl
    have h1 : (m : ℚ) ^ n - 1 = ((m : ℚ) - 1) * qInt m n := by
      have := congrArg (Int.cast : ℤ → ℚ) (sub_one_mul_qInt m n)
      push_cast at this
      linear_combination -this
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [h1, Nat.add_sub_cancel, mul_pow, pow_succ]
    push_cast
    field_simp
  rw [h]
  exact (integral_iff_of_exponent m (m - 1) id (fun _ _ _ hp hk => mul_modEq_totient hp hk)
    (fun n hn => by simp only [id]; omega)).mpr (fun _ _ h => h) n

/-! ## Sanity checks -/

/-- The coefficients $a(n)$ satisfy $(n+1)\,a(n+1) = \sum_{i+j=n} b(i+1)\,a(j)$. -/
theorem coeff_succ_mul (b : ℕ → ℤ) (n : ℕ) :
    coeff (n + 1) (subst (ofInt b) (exp ℚ)) * (n + 1) =
      ∑ x ∈ antidiagonal n, (b (x.1 + 1) : ℚ) * coeff x.2 (subst (ofInt b) (exp ℚ)) := by
  have h := congrArg (coeff n) (derivative_exp_subst (constantCoeff_ofInt b))
  rw [coeff_derivative, coeff_mul] at h
  simpa only [coeff_derivative_ofInt] using h

theorem coeff_zero_exp_subst_ofInt (b : ℕ → ℤ) :
    coeff 0 (subst (ofInt b) (exp ℚ)) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_exp_subst (constantCoeff_ofInt b)]

theorem coeff_one_two_three (b : ℕ → ℤ) :
    coeff 1 (subst (ofInt b) (exp ℚ)) = b 1 ∧
      coeff 2 (subst (ofInt b) (exp ℚ)) * 2 = b 1 * coeff 1 (subst (ofInt b) (exp ℚ)) + b 2 ∧
      coeff 3 (subst (ofInt b) (exp ℚ)) * 3 = b 1 * coeff 2 (subst (ofInt b) (exp ℚ)) +
        b 2 * coeff 1 (subst (ofInt b) (exp ℚ)) + b 3 := by
  have h0 := coeff_zero_exp_subst_ofInt b
  have h1 := coeff_succ_mul b 0
  have h2 := coeff_succ_mul b 1
  have h3 := coeff_succ_mul b 2
  simp only [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, sum_singleton,
    h0] at h1 h2 h3
  push_cast at h1 h2 h3
  exact ⟨by linear_combination h1, by linear_combination h2, by linear_combination h3⟩

/-- The first terms $1, 1, 2, 18$ of A180606. -/
theorem a180606_first_terms :
    coeff 1 (subst (hannaSeries 2) (exp ℚ)) = 1 ∧ coeff 2 (subst (hannaSeries 2) (exp ℚ)) = 2 ∧
      coeff 3 (subst (hannaSeries 2) (exp ℚ)) = 18 := by
  rw [hannaSeries_eq (by norm_num), logSeries_eq_ofInt]
  obtain ⟨h1, h2, h3⟩ := coeff_one_two_three fun n => (2 - 1) * qInt 2 n ^ (n - 1)
  generalize subst (ofInt fun n => (2 - 1) * qInt 2 n ^ (n - 1)) (exp ℚ) = G at h1 h2 h3 ⊢
  norm_num [qInt, sum_range_succ] at h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The first terms $1, 2, 6, 122$ of A181316. -/
theorem a181316_first_terms :
    coeff 1 (subst (hannaSeries 3) (exp ℚ)) = 2 ∧ coeff 2 (subst (hannaSeries 3) (exp ℚ)) = 6 ∧
      coeff 3 (subst (hannaSeries 3) (exp ℚ)) = 122 := by
  rw [hannaSeries_eq (by norm_num), logSeries_eq_ofInt]
  obtain ⟨h1, h2, h3⟩ := coeff_one_two_three fun n => (3 - 1) * qInt 3 n ^ (n - 1)
  generalize subst (ofInt fun n => (3 - 1) * qInt 3 n ^ (n - 1)) (exp ℚ) = G at h1 h2 h3 ⊢
  norm_num [qInt, sum_range_succ] at h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith⟩

end OeisA181316

end
