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
# OEIS A339946 and A361717: Bala's prime-level supercongruences

This file proves three statements of Peter Bala.
- `am_congr`: for every $m \ge 1$ and every prime $p \ge 7$, $a_m(p) \equiv a_m(1) = 2 \pmod{p^5}$,
  where $a_m(n) = [x^{mn}]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$ (A339946, Mar 2022).
- `a339946_congr`: the case $m = 1$, $a(p) \equiv a(1) \pmod{p^5}$ (A339946, Dec 2020).
- `a361717_conj2`: $a(p-1) \equiv 1 - 2p - p^2 \pmod{p^3}$ for every prime $p \ne 3$, where
  $a(n) = \sum_{k<n} \binom{n-1}{k}^2 \binom{n+k}{k}$ (A361717, Conjecture 2).
It also proves the sharpness at $p = 5$: $a_m(5) \equiv 2 + 625m^2 \pmod{5^5}$ (`am_five`), so
$a_m(5) \equiv a_m(1) \pmod{5^5}$ exactly when $5 \mid m$ (`am_five_congr_iff`).

The same tools also give the known A357511 congruence (`a357511_congr`, not a Challenge statement):
$p^4$ divides the numerator of
$S(p-1) = \sum_{k=1}^{p-1} \frac1k \binom{p-1}{k}^2 \binom{p-1+k}{k}^2$ for every prime $p \ge 7$.
It is due to O. Kutal (2026) and to Z. Chen, Q. Wang and Y. Feng, *Mathematics* 14 (2026) 2832,
both with Lean proofs; the proof below is the same expansion.

## A339946

Put $Q_n(x) = \sum_k \binom{n}{k}^2 x^k$.
1. **Legendre bridge** (`shiftedLegendre_eq`). Rodrigues' formula
   (`Polynomial.factorial_mul_shiftedLegendre_eq`) and Leibniz' rule give
   $\tilde P_n(y) = \sum_k \binom{n}{k}^2 (-y)^k (1-y)^{n-k}$. At $y = \frac{x}{1+x}$, which is
   $\frac{1-t}{2}$ for $t = \frac{1-x}{1+x}$, this is $P_n(t) = (1+x)^{-n} Q_n(-x)$
   (`aeval_legendreP_mobius`). So $1/P_n(t) = (1+x)^n Q_n(-x)^{-1}$, the image of an integer series,
   because $Q_n(-x)$ has constant term $1$ (`inv_aeval_legendreP_mobius`). Hence
   $a_m(n) = c_m(n) \in \mathbb{Z}$ with $c_m(n) = [x^{mn}] (1+x)^n Q_n(-x)^{-1}$ (`am_eq_cz`).
2. **$n = 1$** (`cz_one`). $Q_1(-x) = 1 - x$, so $c_m(1) = [x^m] \frac{1+x}{1-x} = 2$.
3. **$n = p$, modulo $p^5$** (`cz_prime`). For odd $p$,
   $Q_p(-x) = 1 - x^p + V$ with $V = p^2 E$ and $E = \sum_{0<k<p} (-1)^k (\binom{p}{k}/p)^2 x^k$
   (`Qz_eq`). In `ZMod (p ^ 5)`, $V^3 = 0$, so with $S = (1 - x^p)^{-1}$,
   $(1 - x^p + V)^{-1} = S - V S^2 + V^2 S^3$. The powers of $S$ are supported on multiples of $p$.
   If a series $A$ vanishes at all multiples of $p$, then $[x^{pm}] A S^j = 0$
   (`coeff_mul_eq_zero`). This gives three terms.
   - $j = 0$: $(1+x)^p = 1 + x^p + W$ with $W$ vanishing at multiples of $p$, and
     $[x^{pm}] (1 + x^p) S = 2$ for $m \ge 1$ (`coeff_one_add_X_pow_mul_S`).
   - $j = 1$: $(1+x)^p V$ vanishes at all multiples of $p$, exactly in $\mathbb{Z}$ (`ann1`). At $0$
     and at $tp$ with $t \ge 2$ this is a degree count. At $p$ the coefficient is
     $\sum_{0<k<p} (-1)^k \binom{p}{k}^3 = 0$, since $k \mapsto p - k$ changes its sign (`sym_sum`).
   - $j = 2$: $(1+x)^p V^2 = p^4 (1+x)^p E^2$. Modulo $p$, $(1+x)^p = 1 + x^p$ and
     $E \equiv \sum_{0<k<p} (-1)^k k^{-2} x^k$, since $k \binom{p}{k}/p = \binom{p-1}{k-1}
     \equiv (-1)^{k-1}$ (`choose_div_cast`). So the multiples of $p$ meet $E^2$ only at $x^p$, where
     the coefficient is $-\sum_k k^{-4} = 0$ in $\mathbb{F}_p$ for $p \ge 7$
     (`FiniteField.sum_pow_lt_card_sub_one`; `Ebar_sq_p`, `ann2`).
   So $c_m(p) \equiv 2 \pmod{p^5}$, and `am_congr` follows.
4. **$p = 5$** (`cz_five`). Steps 1–3 hold for every odd $p$ except the vanishing of the $j = 2$
   term (`cz_prime_gen`). For $p = 5$, $\sum_{k<5} k^{-4} = 4 \equiv -1$, so the $x^5$
   coefficient of $E^2$ is $1$ modulo $5$ (`Ebar5_sq`). Hence $P = (1+x)^5 V^2$ has coefficient
   $625$ at $x^5$ and $x^{10}$, and $0$ at the other multiples of $5$ (`coeff_P5`). The
   coefficients $g_m = [x^{5m}] P S^3$ satisfy $g_{m+3} - 3g_{m+2} + 3g_{m+1} - g_m = 0$, from
   $(1 - x^5)^3 P S^3 = P$ (`coeff_cube_mul`), with $g_0 = 0$, $g_1 = 625$, $g_2 = 2500$. So
   $g_m = 625m^2$ and $c_m(5) \equiv 2 + 625m^2 \pmod{5^5}$.

## A361717, Conjecture 2

The case $p = 2$ is a direct check. Let $p \ge 5$, work in `ZMod (p ^ 3)` and write
$H_j = \sum_{i \le j} i^{-1}$ (`hsum`) and $H^{(2)}_j = \sum_{i \le j} i^{-2}$ (`hsum2`).
1. **Products** (`choose_A`, `choose_B`, by induction on $k$). For $1 \le k \le p - 2$:
   $\binom{p-1+k}{k} \equiv \frac{p}{k}(1 + pH_{k-1}) \pmod{p^3}$ and
   $\binom{p-2}{k} \equiv (-1)^k (k+1)(1 - p(H_{k+1} - 1)) \pmod{p^2}$. Hence (`term_C`)
   $\binom{p-2}{k}^2 \binom{p-1+k}{k} \equiv p\frac{(k+1)^2}{k} + p^2 \frac{(k+1)^2}{k}
   (H_{k-1} - 2H_{k+1} + 2) \pmod{p^3}$.
2. **Wolstenholme** (`wolst`). Pairing $i$ with $p - i$ gives $2H_{p-1} = p\sum_i i^{-1}(p-i)^{-1}$,
   and the sum is $\equiv -H^{(2)}_{p-1} \equiv 0 \pmod p$. So $pH_{p-1} \equiv 0 \pmod{p^3}$.
3. **First-order part** (`partA`). $\sum_{k=1}^{p-2} \frac{(k+1)^2}{k} = \sum (k + 2) + H_{p-2}$, and
   step 2 with $(p-1)^{-1} \equiv -1 - p \pmod{p^2}$ gives $2p \sum \equiv 3p^2 - 4p$.
4. **Second-order part** (`partB`), modulo $p$, in the field `ZMod p`. Closed forms proved by
   induction (`S0`–`S3`): $\sum_{k \le n} H_{k-1} = nH_n - n$,
   $4\sum_{k \le n} kH_{k-1} = 2n(n+1)H_n - n^2 - 3n$ and
   $2\sum_{k \le n} H_{k-1}/k = H_n^2 - H^{(2)}_n$. With $n = p - 2 \equiv -2$, $H_{p-2} \equiv 1$ and
   $H^{(2)}_{p-2} \equiv -1$ (from $H_{p-1} \equiv H^{(2)}_{p-1} \equiv 0$), the second sum is
   $\equiv -\frac52$ (`Bsum_eq`).
5. So $a(p-1) \equiv 1 + \frac12(3p^2 - 4p) - \frac52 p^2 = 1 - 2p - p^2 \pmod{p^3}$
   (`a361717_zmod`).

## A357511

Let $p \ge 7$ and work in `ZMod (p ^ 4)`.
1. **Terms** (`V_formula`, by induction on $k$ from the ratios of consecutive binomials). For
   $1 \le k \le p - 1$, $\binom{p-1}{k}^2 \binom{p-1+k}{k}^2 \equiv p^2 k^{-2}(1 - 2p/k)$. So
   $\sum_k k^{-1} \binom{p-1}{k}^2 \binom{p-1+k}{k}^2 \equiv p^2 H(3) - 2p^3 H(4)$ (`sum_V_zero`).
2. **Harmonic sums.** $H(4) \equiv 0 \pmod p$ by the power sums in $\mathbb{F}_p$ (`p_cube_H4`).
   Pairing $k$ with $p - k$ gives $2H(3) = p\sum_k (3k^2 - 3pk + p^2) k^{-3}(p-k)^{-3}$, and the sum is
   $\equiv -3H(4) \equiv 0 \pmod p$; so $H(3) \equiv 0 \pmod{p^2}$ (`p_sq_H3`).
3. **Numerator** (`a357511_congr`). $M = (p-1)!\,S(p-1)$ is an integer, and steps 1 and 2 give
   $M \equiv 0 \pmod{p^4}$. From $S = n/d$ in lowest terms, $n (p-1)! = M d$, and $p \nmid (p-1)!$,
   so $p^4 \mid n$.

Some helpers are adapted from `FCPalomar/MosN8`: `natCast_mul_inv`, `castHom_natCast_inv`,
`sum_range_natCast` and the argument of `exists_mul_of_castHom_eq_zero`. The rest is written for
this package.

*References:*
- Peter Bala, [A339946](https://oeis.org/A339946), Dec 23, 2020, and comment of Mar 10, 2022.
- Peter Bala, [A361717](https://oeis.org/A361717), Mar 26, 2023.
- Peter Bala, [A357511](https://oeis.org/A357511), Oct 1, 2022.
- O. Kutal, proof of the A357513 conjecture (2026), linked from
  [A357513](https://oeis.org/A357513).
- Z. Chen, Q. Wang, Y. Feng, *Mathematics* 14 (2026) 2832.
-/

@[expose] public section

namespace OeisA339946

open Finset PowerSeries

/-- The Legendre polynomial $P_n(t) = \tilde P_n\bigl(\frac{1-t}{2}\bigr)$ over $\mathbb{Q}$, with
$\tilde P_n$ = `Polynomial.shiftedLegendre n`. -/
noncomputable def legendreP (n : ℕ) : Polynomial ℚ :=
  (Polynomial.map (Int.castRingHom ℚ) (Polynomial.shiftedLegendre n)).comp
    (Polynomial.C (1 / 2) * (1 - Polynomial.X))

/-- The power series $\frac{1-x}{1+x}$. -/
noncomputable def mobius : ℚ⟦X⟧ := (1 - X) * (1 + X)⁻¹

/-- Bala's $a_m(n) = [x^{mn}]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$. -/
noncomputable def am (m n : ℕ) : ℚ := coeff (m * n) (Polynomial.aeval mobius (legendreP n))⁻¹

/-- OEIS A339946: $a(n) = [x^n]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$. -/
noncomputable def a339946 (n : ℕ) : ℚ := coeff n (Polynomial.aeval mobius (legendreP n))⁻¹

/-- OEIS A361717: $a(n) = \sum_{k=0}^{n-1} \binom{n-1}{k}^2 \binom{n+k}{k}$. -/
def a361717 (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (n - 1).choose k ^ 2 * (n + k).choose k

/-- $S(n) = \sum_{k=1}^{n} \frac1k \binom{n}{k}^2 \binom{n+k}{k}^2$. -/
def s357511 (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℚ) * (n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2

/-- OEIS A357511: $a(n)$ is the numerator of $S(n)$; the empty sum gives $a(0) = 0$. -/
def a357511 (n : ℕ) : ℤ := (s357511 n).num

/-! ## Part 1. Series supported on, or vanishing on, the multiples of `p` -/

section General

variable {R : Type*} [CommRing R]

/-- `B` vanishes off the multiples of `p`. -/
def PSupp (p : ℕ) (B : R⟦X⟧) : Prop := ∀ n, ¬ p ∣ n → coeff n B = 0

/-- `A` vanishes on the multiples of `p`. -/
def PAnn (p : ℕ) (A : R⟦X⟧) : Prop := ∀ t, coeff (p * t) A = 0

theorem PSupp.mul {p : ℕ} {A B : R⟦X⟧} (hA : PSupp p A) (hB : PSupp p B) :
    PSupp p (A * B) := by
  intro n hn
  rw [coeff_mul]
  refine sum_eq_zero fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : p ∣ ij.1
  · have : ¬ p ∣ ij.2 := fun h => hn (hij ▸ dvd_add hi h)
    rw [hB _ this, mul_zero]
  · rw [hA _ hi, zero_mul]

theorem PSupp.one (p : ℕ) : PSupp p (1 : R⟦X⟧) := fun n hn => by
  rw [coeff_one, ite_eq_right (fun h : n = 0 => hn (h ▸ dvd_zero p))]

theorem PSupp.pow {p : ℕ} {B : R⟦X⟧} (hB : PSupp p B) (n : ℕ) : PSupp p (B ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact PSupp.one p
  | succ n ih => rw [pow_succ]; exact ih.mul hB

theorem coeff_mul_eq_zero {p : ℕ} {A B : R⟦X⟧} (hA : PAnn p A) (hB : PSupp p B) (m : ℕ) :
    coeff (p * m) (A * B) = 0 := by
  rw [coeff_mul]
  refine sum_eq_zero fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hj : p ∣ ij.2
  · have hi : p ∣ ij.1 := by
      have h := dvd_mul_right p m
      rw [← hij] at h
      exact (Nat.dvd_add_left hj).1 h
    obtain ⟨t, ht⟩ := hi
    rw [ht, hA t, zero_mul]
  · rw [hB _ hj, mul_zero]

theorem PAnn.add {p : ℕ} {A B : R⟦X⟧} (hA : PAnn p A) (hB : PAnn p B) : PAnn p (A + B) :=
  fun t => by rw [map_add, hA t, hB t, add_zero]

theorem PAnn.X_pow_mul {p : ℕ} {A : R⟦X⟧} (hA : PAnn p A) : PAnn p (X ^ p * A) := fun t => by
  rw [coeff_X_pow_mul']
  split_ifs
  · rw [← Nat.mul_sub_one]; exact hA _
  · rfl

theorem PAnn.map {S : Type*} [CommRing S] (f : R →+* S) {p : ℕ} {A : R⟦X⟧} (hA : PAnn p A) :
    PAnn p (PowerSeries.map f A) := fun t => by rw [coeff_map, hA t, map_zero]

/-- Coefficients vanish above the sum of the degree bounds. -/
theorem coeff_mul_eq_zero_of_lt {A B : R⟦X⟧} {a b n : ℕ} (hA : ∀ i, a < i → coeff i A = 0)
    (hB : ∀ j, b < j → coeff j B = 0) (hn : a + b < n) : coeff n (A * B) = 0 := by
  rw [coeff_mul]
  refine sum_eq_zero fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : a < ij.1
  · rw [hA _ hi, zero_mul]
  · rw [hB _ (by omega), mul_zero]

/-- `S p = 1 / (1 - X ^ p)`. -/
def S (p : ℕ) : R⟦X⟧ := mk fun n => if p ∣ n then 1 else 0

theorem S_supp (p : ℕ) : PSupp p (S p : R⟦X⟧) := fun n hn => by
  rw [S, coeff_mk, ite_eq_right hn]

theorem one_sub_X_pow_mul_S {p : ℕ} (hp : 0 < p) : (1 - X ^ p) * (S p : R⟦X⟧) = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_one, S, coeff_mk, coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.not_le.2 hp]
  · rw [ite_eq_right hn.ne']
    by_cases hpn : p ≤ n
    · have hd : p ∣ n - p ↔ p ∣ n := by
        rw [Nat.dvd_sub_self_right]
        exact ⟨fun h => h.elim id fun h => le_antisymm h hpn ▸ dvd_refl p, Or.inl⟩
      rw [ite_eq_left hpn]
      simp only [hd]
      split_ifs <;> simp
    · rw [ite_eq_right hpn, ite_eq_right (Nat.not_dvd_of_pos_of_lt hn (Nat.lt_of_not_le hpn))]
      simp

theorem coeff_one_add_X_pow (n i : ℕ) : coeff i ((1 + X : R⟦X⟧) ^ n) = n.choose i := by
  have : ((1 + X : R⟦X⟧)) ^ n = (((1 + Polynomial.X) ^ n : Polynomial R) : R⟦X⟧) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem W_ann {p : ℕ} (hp : 0 < p) : PAnn p ((1 + X : R⟦X⟧) ^ p - 1 - X ^ p) := fun t => by
  rw [map_sub, map_sub, coeff_one_add_X_pow, coeff_one, coeff_X_pow]
  rcases t with _ | _ | t
  · have : (0 : ℕ) ≠ p := hp.ne
    simp [this]
  · simp [hp.ne']
  · have h1 : p < p * (t + 2) := by nlinarith
    rw [Nat.choose_eq_zero_of_lt h1, ite_eq_right (by positivity), ite_eq_right h1.ne']
    simp

theorem coeff_one_add_X_pow_mul_S {p m : ℕ} (hp : 0 < p) (hm : 1 ≤ m) :
    coeff (p * m) ((1 + X : R⟦X⟧) ^ p * S p) = 2 := by
  have e : (1 + X : R⟦X⟧) ^ p * S p = ((1 + X) ^ p - 1 - X ^ p) * S p + S p + X ^ p * S p := by
    ring
  rw [e, map_add, map_add, coeff_mul_eq_zero (W_ann hp) (S_supp p), coeff_X_pow_mul',
    ite_eq_left (Nat.le_mul_of_pos_right p hm), ← Nat.mul_sub_one, S, coeff_mk, coeff_mk,
    ite_eq_left (dvd_mul_right _ _), ite_eq_left (dvd_mul_right _ _)]
  norm_num

theorem right_inv_unique {A B C : R} (h1 : A * B = 1) (h2 : A * C = 1) : B = C := by
  calc B = B * (A * C) := by rw [h2, mul_one]
    _ = (A * B) * C := by ring
    _ = C := by rw [h1, one_mul]

end General

/-! ### The series `Q_n(-x)` and its inverse -/

/-- `Q_n(-x) = ∑ (-1)^k C(n,k)^2 x^k`. -/
def Qz (n : ℕ) : ℤ⟦X⟧ := mk fun k => (-1) ^ k * (n.choose k : ℤ) ^ 2

theorem constantCoeff_Qz (n : ℕ) : constantCoeff (Qz n) = ((1 : ℤˣ) : ℤ) := by
  rw [← coeff_zero_eq_constantCoeff_apply, Qz, coeff_mk]; simp

theorem Qz_mul_inv (n : ℕ) : Qz n * invOfUnit (Qz n) 1 = 1 :=
  mul_invOfUnit _ _ (constantCoeff_Qz n)

/-- $c_m(n) = [x^{mn}]\,(1+x)^n Q_n(-x)^{-1}$, the integer value of `am m n`. -/
noncomputable def cz (m n : ℕ) : ℤ := coeff (m * n) ((1 + X) ^ n * invOfUnit (Qz n) 1)

theorem Qz_one : Qz 1 = 1 - X ^ 1 := by
  ext k
  rw [Qz, coeff_mk, map_sub, coeff_one, coeff_X_pow]
  rcases k with _ | _ | k
  · simp
  · simp
  · simp [Nat.choose_eq_zero_of_lt (show 1 < k + 2 by omega)]

theorem cz_one (m : ℕ) (hm : 1 ≤ m) : cz m 1 = 2 := by
  have h : invOfUnit (Qz 1) 1 = S 1 := by
    refine right_inv_unique (Qz_mul_inv 1) ?_
    rw [Qz_one]; exact one_sub_X_pow_mul_S one_pos
  rw [cz, h, mul_one, ← one_mul m, coeff_one_add_X_pow_mul_S one_pos hm]

/-! ### Arithmetic modulo `p` -/

theorem sum_range_natCast {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M] (H : ZMod n → M) :
    ∑ x ∈ range n, H (x : ZMod n) = ∑ z : ZMod n, H z := by
  refine Finset.sum_nbij' (fun x => (x : ZMod n)) (fun z => z.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact mem_univ _
  · intro a _; exact mem_range.2 (ZMod.val_lt a)
  · intro a ha; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 ha)]
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro a _; rfl

section ModP

variable {p : ℕ} [hp : Fact p.Prime]

theorem sum_inv_pow {j : ℕ} (hj : j < p - 1) : ∑ k ∈ range p, ((k : ZMod p)⁻¹) ^ j = 0 := by
  rw [sum_range_natCast (fun z : ZMod p => (z⁻¹) ^ j)]
  exact (Equiv.sum_comp (Equiv.inv (ZMod p)) (fun w => w ^ j)).trans
    (FiniteField.sum_pow_lt_card_sub_one (ZMod p) j (by rwa [ZMod.card]))

theorem natCast_ne_zero {i : ℕ} (h0 : 0 < i) (hi : i < p) : (i : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt h0 hi

theorem choose_pred_cast {j : ℕ} (hj : j < p) : (((p - 1).choose j : ℕ) : ZMod p) = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := Nat.choose_succ_right_eq (p - 1) j
    have hc : ((p - 1 - j : ℕ) : ZMod p) = -((j + 1 : ℕ) : ZMod p) := by
      have : ((p - 1 - j : ℕ) : ZMod p) + ((j + 1 : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, show p - 1 - j + (j + 1) = p by omega, ZMod.natCast_self]
      linear_combination this
    have h' := congrArg (fun n : ℕ => (n : ZMod p)) h
    simp only [Nat.cast_mul, hc, ih (by omega)] at h'
    refine mul_right_cancel₀ (natCast_ne_zero (i := j + 1) (by omega) hj) ?_
    rw [h']
    push_cast
    ring

/-- `i * (C(p,i)/p) = C(p-1,i-1)`. -/
theorem choose_div_mul {i : ℕ} (h0 : 0 < i) (hi : i < p) :
    p.choose i / p * i = (p - 1).choose (i - 1) := by
  obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self hp.out h0.ne' hi
  have h := Nat.add_one_mul_choose_eq (p - 1) (i - 1)
  rw [Nat.sub_add_cancel hp.out.one_lt.le, Nat.sub_add_cancel h0, hc, mul_assoc] at h
  rw [hc, Nat.mul_div_cancel_left c hp.out.pos]
  exact (Nat.eq_of_mul_eq_mul_left hp.out.pos h).symm

theorem choose_div_cast {i : ℕ} (h0 : 0 < i) (hi : i < p) :
    ((p.choose i / p : ℕ) : ZMod p) ^ 2 = ((i : ZMod p)⁻¹) ^ 2 := by
  have h := congrArg (fun n : ℕ => (n : ZMod p)) (choose_div_mul (p := p) h0 hi)
  simp only [Nat.cast_mul, choose_pred_cast (show i - 1 < p by omega)] at h
  have hi0 := natCast_ne_zero (p := p) h0 hi
  have h2 : ((p.choose i / p : ℕ) : ZMod p) = (-1) ^ (i - 1) * (i : ZMod p)⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ hi0, mul_one]
  rw [h2, mul_pow, ← pow_mul, mul_comm (i - 1), pow_mul, neg_one_sq, one_pow, one_mul]

end ModP

/-! ### The case `n = p` -/

/-- `E = ∑_{0<k<p} (-1)^k (C(p,k)/p)^2 x^k`, so that `Q_p(-x) = 1 - x^p + p^2 E` for odd `p`. -/
def Ez (p : ℕ) : ℤ⟦X⟧ :=
  mk fun k => if 0 < k ∧ k < p then (-1) ^ k * ((p.choose k / p : ℕ) : ℤ) ^ 2 else 0

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

theorem coeff_Vz (k : ℕ) : coeff k (C ((p : ℤ) ^ 2) * Ez p) =
    if 0 < k ∧ k < p then (-1) ^ k * (p.choose k : ℤ) ^ 2 else 0 := by
  rw [coeff_C_mul, Ez, coeff_mk]
  split_ifs with h
  · obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self hp.out h.1.ne' h.2
    rw [hc, Nat.mul_div_cancel_left c hp.out.pos]
    push_cast
    ring
  · rw [mul_zero]

theorem Qz_eq (hodd : Odd p) : Qz p = 1 - X ^ p + C ((p : ℤ) ^ 2) * Ez p := by
  ext k
  rw [map_add, map_sub, coeff_Vz, Qz, coeff_mk, coeff_one, coeff_X_pow]
  rcases Nat.lt_trichotomy k p with h | rfl | h
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hp.out.ne_zero.symm]
    · simp [hk.ne', h.ne, hk, h]
  · simp [hodd.neg_one_pow, hp.out.ne_zero]
  · simp [Nat.choose_eq_zero_of_lt h, h.ne', (Nat.zero_le p).trans_lt h |>.ne', Nat.not_lt.2 h.le]

end Prime

theorem sum_eq_zero_of_antisymm (g : ℕ → ℤ) (n : ℕ)
    (h : ∀ k ∈ range (n + 1), g (n - k) = -g k) : ∑ k ∈ range (n + 1), g k = 0 := by
  have h1 := Finset.sum_range_reflect g (n + 1)
  simp only [Nat.add_sub_cancel] at h1
  rw [sum_congr rfl h, sum_neg_distrib] at h1
  linarith

theorem sym_sum {p : ℕ} (hodd : Odd p) :
    ∑ k ∈ range (p + 1), ((p.choose k : ℕ) : ℤ) *
      (if 0 < p - k ∧ p - k < p then (-1) ^ (p - k) * ((p.choose (p - k) : ℕ) : ℤ) ^ 2 else 0)
      = 0 := by
  refine sum_eq_zero_of_antisymm _ p fun k hk => ?_
  have hkp : k ≤ p := Nat.lt_succ_iff.1 (mem_range.1 hk)
  simp only [Nat.sub_sub_self hkp, Nat.choose_symm hkp]
  have hc : (0 < p - k ∧ p - k < p) ↔ (0 < k ∧ k < p) := by omega
  by_cases h : 0 < k ∧ k < p
  · rw [ite_eq_left h, ite_eq_left (hc.2 h)]
    have h1 : (-1 : ℤ) ^ (p - k) * (-1) ^ k = -1 := by
      rw [← pow_add, Nat.sub_add_cancel hkp, hodd.neg_one_pow]
    have h2 : (-1 : ℤ) ^ k * (-1) ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination ((p.choose k : ℕ) : ℤ) ^ 3 * ((-1) ^ k * h1 - (-1) ^ (p - k) * h2)
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hc.1 h'))]
    simp

section Prime2

variable {p : ℕ} [hp : Fact p.Prime]

theorem ann1 (hodd : Odd p) : PAnn p ((1 + X : ℤ⟦X⟧) ^ p * (C ((p : ℤ) ^ 2) * Ez p)) := by
  intro t
  rcases t with _ | _ | t
  · rw [mul_zero, coeff_zero_eq_constantCoeff_apply, map_mul,
      ← coeff_zero_eq_constantCoeff_apply (C _ * _), coeff_Vz]
    simp
  · rw [zero_add, mul_one, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_one_add_X_pow, coeff_Vz]
    exact sym_sum hodd
  · apply coeff_mul_eq_zero_of_lt (a := p) (b := p - 1)
    · intro i hi; rw [coeff_one_add_X_pow, Nat.choose_eq_zero_of_lt hi, Nat.cast_zero]
    · intro j hj; rw [coeff_Vz, ite_eq_right (by omega)]
    · have h2 := hp.out.two_le
      have : 2 * p ≤ p * (t + 1 + 1) := by nlinarith
      omega

end Prime2

section Prime3

variable {p : ℕ} [hp : Fact p.Prime]

/-- `(1 + X)^p = 1 + X^p` over `ZMod p`. -/
theorem one_add_X_pow_char : (1 + X : (ZMod p)⟦X⟧) ^ p = 1 + X ^ p := by
  have h : ((1 + Polynomial.X : Polynomial (ZMod p)) ^ p) = 1 + Polynomial.X ^ p := by
    rw [add_pow_char, one_pow]
  have := congrArg (fun q : Polynomial (ZMod p) => (q : (ZMod p)⟦X⟧)) h
  simpa [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X] using this

theorem coeff_Ebar (k : ℕ) : coeff k (map (Int.castRingHom (ZMod p)) (Ez p)) =
    if 0 < k ∧ k < p then (-1) ^ k * ((k : ZMod p)⁻¹) ^ 2 else 0 := by
  rw [coeff_map, Ez, coeff_mk]
  split_ifs with h
  · simp only [map_mul, map_pow, map_neg, map_one, eq_intCast, Int.cast_natCast]
    rw [choose_div_cast h.1 h.2]
  · simp

theorem Ebar_sq_coeff (hodd : Odd p) :
    coeff p (map (Int.castRingHom (ZMod p)) (Ez p) ^ 2) =
      -∑ k ∈ range p, ((k : ZMod p)⁻¹) ^ 4 := by
  rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_Ebar]
  have key : ∀ k ∈ range (p + 1),
      ((if 0 < k ∧ k < p then (-1) ^ k * ((k : ZMod p)⁻¹) ^ 2 else 0) *
      (if 0 < p - k ∧ p - k < p then (-1) ^ (p - k) * (((p - k : ℕ) : ZMod p)⁻¹) ^ 2 else 0)) =
      -((k : ZMod p)⁻¹) ^ 4 := by
    intro k hk
    have hkp : k ≤ p := Nat.lt_succ_iff.1 (mem_range.1 hk)
    by_cases h : 0 < k ∧ k < p
    · rw [ite_eq_left h, ite_eq_left (by omega)]
      have hc : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        rw [Nat.cast_sub hkp, ZMod.natCast_self, zero_sub]
      have h1 : (-1 : ZMod p) ^ k * (-1) ^ (p - k) = -1 := by
        rw [← pow_add, Nat.add_sub_cancel' hkp, hodd.neg_one_pow]
      rw [hc, inv_neg, neg_sq]
      linear_combination ((k : ZMod p)⁻¹) ^ 4 * h1
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp
      · have : k = p := by omega
        subst this
        simp
  rw [sum_congr rfl key, sum_neg_distrib, sum_range_succ, ZMod.natCast_self, inv_zero,
    zero_pow (by norm_num), add_zero]

theorem Ebar_sq_p (hodd : Odd p) (h7 : 7 ≤ p) :
    coeff p (map (Int.castRingHom (ZMod p)) (Ez p) ^ 2) = 0 := by
  rw [Ebar_sq_coeff hodd, sum_inv_pow (by omega), neg_zero]

theorem ann2 (hodd : Odd p) (h7 : 7 ≤ p) (t : ℕ) :
    (p : ℤ) ∣ coeff (p * t) ((1 + X : ℤ⟦X⟧) ^ p * Ez p ^ 2) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← eq_intCast (Int.castRingHom (ZMod p)), ← coeff_map,
    map_mul, map_pow, map_pow, map_add, map_one, map_X, one_add_X_pow_char]
  set E := map (Int.castRingHom (ZMod p)) (Ez p)
  have hE : PAnn p (E ^ 2) := by
    intro t
    rcases t with _ | _ | t
    · rw [mul_zero, coeff_zero_eq_constantCoeff_apply, map_pow,
        ← coeff_zero_eq_constantCoeff_apply, coeff_Ebar]
      simp
    · rw [zero_add, mul_one]; exact Ebar_sq_p hodd h7
    · rw [sq]
      apply coeff_mul_eq_zero_of_lt (a := p - 1) (b := p - 1)
      · intro i hi; rw [coeff_Ebar, ite_eq_right (by omega)]
      · intro i hi; rw [coeff_Ebar, ite_eq_right (by omega)]
      · have h2 := hp.out.two_le
        have : 2 * p ≤ p * (t + 1 + 1) := by nlinarith
        omega
  rw [add_mul, one_mul]
  exact (hE.add hE.X_pow_mul) t

/-- For every odd prime `p`, `c_m(p) ≡ 2 + [x^{pm}] (1+x)^p V^2 S^3 (mod p^5)`. -/
theorem cz_prime_gen (hodd : Odd p) {m : ℕ} (hm : 1 ≤ m) :
    ((cz m p : ℤ) : ZMod (p ^ 5)) = 2 + coeff (p * m)
      (((1 + X) ^ p * map (Int.castRingHom (ZMod (p ^ 5))) (C ((p : ℤ) ^ 2) * Ez p) ^ 2) *
        S p ^ 3) := by
  set f := Int.castRingHom (ZMod (p ^ 5))
  set VR : (ZMod (p ^ 5))⟦X⟧ := map f (C ((p : ℤ) ^ 2) * Ez p) with hVR
  set Zi := map f (invOfUnit (Qz p) 1) with hZi
  have hS : (1 - X ^ p) * (S p : (ZMod (p ^ 5))⟦X⟧) = 1 := one_sub_X_pow_mul_S hp.out.pos
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hVR' : VR = C ((p : ZMod (p ^ 5)) ^ 2) * map f (Ez p) := by
    rw [hVR, map_mul, map_C]; simp [f]
  have hV3 : VR ^ 3 = 0 := by
    rw [hVR', mul_pow, ← map_pow, ← pow_mul,
      show (p : ZMod (p ^ 5)) ^ (2 * 3) = (p : ZMod (p ^ 5)) ^ 5 * p by ring, hp5, zero_mul,
      map_zero, zero_mul]
  have hQ : map f (Qz p) = 1 - X ^ p + VR := by
    rw [Qz_eq hodd, map_add, map_sub, map_one, map_pow, map_X]
  have h1 : map f (Qz p) * Zi = 1 := by rw [hZi, ← map_mul, Qz_mul_inv, map_one]
  rw [hQ] at h1
  set G := S p - VR * S p ^ 2 + VR ^ 2 * S p ^ 3 with hG
  have hGinv : (1 - X ^ p + VR) * G = 1 := by
    rw [hG]
    linear_combination (1 - VR * S p + VR ^ 2 * S p ^ 2) * hS + S p ^ 3 * hV3
  have hZG : Zi = G := right_inv_unique h1 hGinv
  have hcast : ((cz m p : ℤ) : ZMod (p ^ 5)) = coeff (p * m) ((1 + X) ^ p * G) := by
    rw [cz, mul_comm m p, ← eq_intCast f, ← coeff_map, map_mul, map_pow, map_add, map_one, map_X,
      ← hZi, hZG]
  have hA1 : PAnn p ((1 + X : (ZMod (p ^ 5))⟦X⟧) ^ p * VR) := by
    have := (ann1 (p := p) hodd).map f
    rwa [map_mul, map_pow, map_add, map_one, map_X] at this
  rw [hcast, show (1 + X : (ZMod (p ^ 5))⟦X⟧) ^ p * G = (1 + X) ^ p * S p -
      ((1 + X) ^ p * VR) * S p ^ 2 + ((1 + X) ^ p * VR ^ 2) * S p ^ 3 by rw [hG]; ring,
    map_add, map_sub, coeff_one_add_X_pow_mul_S hp.out.pos hm,
    coeff_mul_eq_zero hA1 ((S_supp p).pow 2)]
  ring

theorem cz_prime (hodd : Odd p) (h7 : 7 ≤ p) {m : ℕ} (hm : 1 ≤ m) :
    ((cz m p : ℤ) : ZMod (p ^ 5)) = 2 := by
  set f := Int.castRingHom (ZMod (p ^ 5))
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hA2 : PAnn p ((1 + X : (ZMod (p ^ 5))⟦X⟧) ^ p * map f (C ((p : ℤ) ^ 2) * Ez p) ^ 2) := by
    intro t
    have e : (1 + X : (ZMod (p ^ 5))⟦X⟧) ^ p * map f (C ((p : ℤ) ^ 2) * Ez p) ^ 2 =
        map f (C ((p : ℤ) ^ 4) * ((1 + X) ^ p * Ez p ^ 2)) := by
      simp only [map_mul, map_pow, map_add, map_one, map_X, map_C]
      ring
    rw [e, coeff_map, coeff_C_mul]
    obtain ⟨z, hz⟩ := ann2 (p := p) hodd h7 t
    rw [hz, map_mul, map_mul, map_pow, map_natCast, ← mul_assoc, ← pow_succ, hp5, zero_mul]
  rw [cz_prime_gen hodd hm, coeff_mul_eq_zero hA2 ((S_supp p).pow 3), add_zero]

end Prime3

/-! ### Legendre bridge -/

theorem shiftedLegendre_eq (n : ℕ) :
    Polynomial.shiftedLegendre n = ∑ k ∈ range (n + 1),
      Polynomial.C ((n.choose k : ℤ) ^ 2) * (-Polynomial.X) ^ k * (1 - Polynomial.X) ^ (n - k) := by
  refine nat_mul_inj' ?_ (Nat.factorial_ne_zero n)
  rw [Polynomial.factorial_mul_shiftedLegendre_eq, Polynomial.iterate_derivative_mul, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  have h1 : (1 - Polynomial.X : Polynomial ℤ) ^ n = (Polynomial.X ^ n).comp (1 - Polynomial.X) := by
    rw [Polynomial.X_pow_comp]
  rw [h1, Polynomial.iterate_derivative_comp_one_sub_X, Polynomial.iterate_derivative_X_pow_eq_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_pow_comp, Nat.sub_sub_self hkn, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_symm hkn, nsmul_eq_mul]
  have h2 : (n.choose k : ℤ) * ((n - k).factorial * n.choose k : ℕ) * ((k.factorial * n.choose k : ℕ))
      = (n.factorial : ℤ) * (n.choose k : ℤ) ^ 2 := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkn]
    push_cast
    ring
  have h3 : ((n.choose k : ℕ) : Polynomial ℤ) * (Polynomial.C (((n - k).factorial * n.choose k : ℕ) : ℤ) *
      Polynomial.X ^ k * ((-1) ^ k * (Polynomial.C ((k.factorial * n.choose k : ℕ) : ℤ) *
      (1 - Polynomial.X) ^ (n - k)))) =
      Polynomial.C ((n.choose k : ℤ) * ((n - k).factorial * n.choose k : ℕ) *
        ((k.factorial * n.choose k : ℕ))) * ((-Polynomial.X) ^ k * (1 - Polynomial.X) ^ (n - k)) := by
    rw [neg_pow, Polynomial.C_mul, Polynomial.C_mul, ← Polynomial.C_eq_natCast, Polynomial.C_eq_natCast]
    simp only [map_natCast]
    ring
  rw [h3, h2, Polynomial.C_mul, Polynomial.C_eq_natCast]
  ring

theorem aeval_shiftedLegendre {A : Type*} [CommRing A] [Algebra ℤ A] (n : ℕ) (y : A) :
    Polynomial.aeval y (Polynomial.shiftedLegendre n) =
      ∑ k ∈ range (n + 1), ((n.choose k : A) ^ 2) * (-y) ^ k * (1 - y) ^ (n - k) := by
  rw [shiftedLegendre_eq, map_sum]
  refine sum_congr rfl fun k _ => ?_
  simp

theorem Qz_eq_sum (n : ℕ) : map (Int.castRingHom ℚ) (Qz n) =
    ∑ k ∈ range (n + 1), ((n.choose k : ℚ⟦X⟧) ^ 2) * (-X) ^ k := by
  ext j
  rw [coeff_map, Qz, coeff_mk, map_sum]
  have e : ∀ k ∈ range (n + 1), coeff j (((n.choose k : ℚ⟦X⟧) ^ 2) * (-X) ^ k) =
      if j = k then (-1) ^ k * ((n.choose k : ℚ)) ^ 2 else 0 := by
    intro k _
    rw [neg_pow, show ((n.choose k : ℚ⟦X⟧) ^ 2) * ((-1) ^ k * X ^ k) =
      C ((-1) ^ k * ((n.choose k : ℚ)) ^ 2) * X ^ k by simp [map_natCast]; ring, coeff_C_mul_X_pow]
  rw [sum_congr rfl e, sum_ite_eq]
  split_ifs with h
  · simp
  · rw [Nat.choose_eq_zero_of_lt (by simpa using h)]
    simp

theorem half_mul_eq {u : ℚ⟦X⟧} (hu : (1 + X) * u = 1) :
    C (1 / 2 : ℚ) * (1 - (1 - X) * u) = X * u := by
  have h2 : C (1 / 2 : ℚ) * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul]; norm_num
  linear_combination (-C (1 / 2 : ℚ)) * hu + X * u * h2

theorem aeval_legendreP_mobius (n : ℕ) :
    Polynomial.aeval mobius (legendreP n) =
      ((1 + X : ℚ⟦X⟧)⁻¹) ^ n * map (Int.castRingHom ℚ) (Qz n) := by
  set u := (1 + X : ℚ⟦X⟧)⁻¹ with hu_def
  have hu : (1 + X) * u = 1 := PowerSeries.mul_inv_cancel _ (by simp)
  have hy : Polynomial.aeval mobius (Polynomial.C (1 / 2 : ℚ) * (1 - Polynomial.X)) = X * u := by
    rw [map_mul, Polynomial.aeval_C, map_sub, map_one, Polynomial.aeval_X, mobius,
      PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← hu_def]
    exact half_mul_eq hu
  have h1y : 1 - X * u = u := by linear_combination -hu
  rw [legendreP, Polynomial.aeval_comp, hy, ← algebraMap_int_eq,
    Polynomial.aeval_map_algebraMap, aeval_shiftedLegendre, h1y, algebraMap_int_eq, Qz_eq_sum,
    mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  have e : u ^ k * u ^ (n - k) = u ^ n := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [show -(X * u) = -X * u by ring, mul_pow]
  linear_combination ((n.choose k : ℚ⟦X⟧) ^ 2 * (-X) ^ k) * e

theorem inv_aeval_legendreP_mobius (n : ℕ) :
    (Polynomial.aeval mobius (legendreP n))⁻¹ =
      map (Int.castRingHom ℚ) ((1 + X) ^ n * invOfUnit (Qz n) 1) := by
  have hu : (1 + X : ℚ⟦X⟧) * (1 + X)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp)
  have hQ : map (Int.castRingHom ℚ) (Qz n) * map (Int.castRingHom ℚ) (invOfUnit (Qz n) 1) = 1 := by
    rw [← map_mul, Qz_mul_inv, map_one]
  have hprod : map (Int.castRingHom ℚ) ((1 + X) ^ n * invOfUnit (Qz n) 1) *
      Polynomial.aeval mobius (legendreP n) = 1 := by
    rw [aeval_legendreP_mobius, map_mul, map_pow, map_add, map_one, map_X]
    calc (1 + X) ^ n * map (Int.castRingHom ℚ) (invOfUnit (Qz n) 1) *
          ((1 + X)⁻¹ ^ n * map (Int.castRingHom ℚ) (Qz n))
        = ((1 + X) ^ n * (1 + X)⁻¹ ^ n) *
          (map (Int.castRingHom ℚ) (Qz n) * map (Int.castRingHom ℚ) (invOfUnit (Qz n) 1)) := by
          ring
      _ = 1 := by rw [← mul_pow, hu, hQ, one_pow, one_mul]
  have hc : constantCoeff (Polynomial.aeval mobius (legendreP n)) ≠ 0 := by
    intro h
    have := congrArg constantCoeff hprod
    rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  exact (PowerSeries.inv_eq_iff_mul_eq_one hc).2 hprod

theorem am_eq_cz (m n : ℕ) : am m n = cz m n := by
  rw [am, inv_aeval_legendreP_mobius, coeff_map, cz, eq_intCast]

/-! ### Sharpness at `p = 5` -/

section Five

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem inv_pow_four_five {a : ZMod 5} (ha : a ≠ 0) : (a⁻¹) ^ 4 = 1 := by
  rw [inv_pow, show 4 = 5 - 1 by rfl, ZMod.pow_card_sub_one_eq_one ha, inv_one]

theorem Ebar5_sq (n : ℕ) (hn : n = 0 ∨ n = 5 ∨ 9 ≤ n) :
    coeff n (map (Int.castRingHom (ZMod 5)) (Ez 5) ^ 2) = if n = 5 then 1 else 0 := by
  rcases hn with rfl | rfl | h9
  · rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply,
      coeff_Ebar]
    simp
  · rw [Ebar_sq_coeff (by decide)]
    simp only [sum_range_succ, sum_range_zero, Nat.cast_zero, inv_zero, zero_add]
    rw [inv_pow_four_five (by decide), inv_pow_four_five (by decide), inv_pow_four_five (by decide),
      inv_pow_four_five (by decide)]
    decide
  · rw [ite_eq_right (by omega), sq]
    apply coeff_mul_eq_zero_of_lt (a := 4) (b := 4)
    · intro i hi; rw [coeff_Ebar, ite_eq_right (by omega)]
    · intro i hi; rw [coeff_Ebar, ite_eq_right (by omega)]
    · omega

theorem coeff_P5 (t : ℕ) :
    coeff (5 * t) ((1 + X : (ZMod (5 ^ 5))⟦X⟧) ^ 5 *
      map (Int.castRingHom (ZMod (5 ^ 5))) (C (((5 : ℕ) : ℤ) ^ 2) * Ez 5) ^ 2) =
      if t = 1 ∨ t = 2 then 625 else 0 := by
  set f5 := Int.castRingHom (ZMod (5 ^ 5))
  have e : (1 + X : (ZMod (5 ^ 5))⟦X⟧) ^ 5 * map f5 (C (((5 : ℕ) : ℤ) ^ 2) * Ez 5) ^ 2 =
      map f5 (C (((5 : ℕ) : ℤ) ^ 4) * ((1 + X) ^ 5 * Ez 5 ^ 2)) := by
    simp only [map_mul, map_pow, map_add, map_one, map_X, map_C]
    ring
  rw [e, coeff_map, coeff_C_mul]
  set β := coeff (5 * t) ((1 + X : ℤ⟦X⟧) ^ 5 * Ez 5 ^ 2)
  have hβ : (β : ZMod 5) = ((if t = 1 ∨ t = 2 then 1 else 0 : ℤ) : ZMod 5) := by
    rw [← eq_intCast (Int.castRingHom (ZMod 5)), ← coeff_map, map_mul, map_pow, map_pow, map_add,
      map_one, map_X, one_add_X_pow_char, add_mul, one_mul, map_add, coeff_X_pow_mul']
    rw [Ebar5_sq (5 * t) (by omega), Ebar5_sq (5 * t - 5) (by omega)]
    rcases (show t = 1 ∨ t = 2 ∨ (t ≠ 1 ∧ t ≠ 2) by omega) with rfl | rfl | ⟨h1, h2⟩
    · norm_num
    · norm_num
    · have h3 : 5 * t ≠ 5 := by omega
      have h4 : 5 * t - 5 ≠ 5 := by omega
      have h5 : ¬ (t = 1 ∨ t = 2) := by omega
      simp [h3, h4, h5]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hβ
  obtain ⟨w, hw⟩ := hβ
  have hβ' : β = (if t = 1 ∨ t = 2 then 1 else 0 : ℤ) - 5 * w := by push_cast at hw; linarith
  rw [hβ', map_mul, map_sub, map_mul, map_pow, map_natCast]
  have h55 : ((5 : ℕ) : ZMod (5 ^ 5)) ^ 4 * (f5 5 * f5 w) = 0 := by
    rw [map_ofNat, ← mul_assoc, show ((5 : ℕ) : ZMod (5 ^ 5)) ^ 4 * 5 = 0 by decide, zero_mul]
  rw [mul_sub, h55, sub_zero]
  split_ifs <;> simp; decide

/-- The coefficients of `F` and of `(1 - X^5)^3 F`. -/
theorem coeff_cube_mul {R : Type*} [CommRing R] (F : R⟦X⟧) (n : ℕ) :
    coeff n ((1 - X ^ 5) ^ 3 * F) = coeff n F - (if 5 ≤ n then 3 * coeff (n - 5) F else 0) +
      (if 10 ≤ n then 3 * coeff (n - 10) F else 0) - (if 15 ≤ n then coeff (n - 15) F else 0) := by
  have e : (1 - X ^ 5 : R⟦X⟧) ^ 3 * F = F - C 3 * (X ^ 5 * F) + C 3 * (X ^ 10 * F) - X ^ 15 * F := by
    rw [map_ofNat C 3]; ring
  rw [e, map_sub, map_add, map_sub, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul',
    coeff_X_pow_mul']
  split_ifs <;> simp

theorem cz_five {m : ℕ} (hm : 1 ≤ m) : ((cz m 5 : ℤ) : ZMod (5 ^ 5)) = 2 + 625 * m ^ 2 := by
  rw [cz_prime_gen (p := 5) (by decide) hm]
  congr 1
  set Pm := (1 + X : (ZMod (5 ^ 5))⟦X⟧) ^ 5 *
      map (Int.castRingHom (ZMod (5 ^ 5))) (C (((5 : ℕ) : ℤ) ^ 2) * Ez 5) ^ 2 with hPm
  set F := Pm * S 5 ^ 3 with hF
  have hS : (1 - X ^ 5) * (S 5 : (ZMod (5 ^ 5))⟦X⟧) = 1 := one_sub_X_pow_mul_S (by norm_num)
  have hcube : (1 - X ^ 5) ^ 3 * F = Pm := by
    calc (1 - X ^ 5) ^ 3 * F = Pm * ((1 - X ^ 5) * S 5) ^ 3 := by rw [hF]; ring
      _ = Pm := by rw [hS, one_pow, mul_one]
  have hrec : ∀ n, coeff n Pm = coeff n F - (if 5 ≤ n then 3 * coeff (n - 5) F else 0) +
      (if 10 ≤ n then 3 * coeff (n - 10) F else 0) -
      (if 15 ≤ n then coeff (n - 15) F else 0) := fun n => by rw [← hcube, coeff_cube_mul]
  have r0 := hrec (5 * 0)
  have r1 := hrec (5 * 1)
  have r2 := hrec (5 * 2)
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), coeff_P5] at r0
  rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    show 5 * 1 - 5 = 5 * 0 by omega, coeff_P5] at r1
  rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega),
    show 5 * 2 - 5 = 5 * 1 by omega, show 5 * 2 - 10 = 5 * 0 by omega, coeff_P5] at r2
  have rs : ∀ k, coeff (5 * (k + 3)) F - 3 * coeff (5 * (k + 2)) F + 3 * coeff (5 * (k + 1)) F -
      coeff (5 * k) F = 0 := by
    intro k
    have r := hrec (5 * (k + 3))
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      show 5 * (k + 3) - 5 = 5 * (k + 2) by omega, show 5 * (k + 3) - 10 = 5 * (k + 1) by omega,
      show 5 * (k + 3) - 15 = 5 * k by omega, coeff_P5, ite_eq_right (by omega)] at r
    linear_combination -r
  rw [ite_eq_right (by omega)] at r0
  rw [ite_eq_left (by omega)] at r1 r2
  have key : ∀ k : ℕ, coeff (5 * k) F = 625 * (k : ZMod (5 ^ 5)) ^ 2 ∧
      coeff (5 * (k + 1)) F = 625 * ((k + 1 : ℕ) : ZMod (5 ^ 5)) ^ 2 ∧
      coeff (5 * (k + 2)) F = 625 * ((k + 2 : ℕ) : ZMod (5 ^ 5)) ^ 2 := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add]
      refine ⟨?_, ?_, ?_⟩
      · push_cast; linear_combination -r0
      · push_cast; linear_combination -r1 - 3 * r0
      · push_cast; linear_combination -r2 - 3 * r1 - 6 * r0
    | succ k ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have r := rs k
      refine ⟨h1, by rw [show k + 1 + 1 = k + 2 by ring]; exact h2, ?_⟩
      rw [show k + 1 + 2 = k + 3 by ring]
      rw [h0, h1, h2] at r
      push_cast at r ⊢
      linear_combination r
  exact (key m).1

end Five

/-! ## Part 2. Harmonic sums and A361717 -/

/-- The harmonic number `H_j = ∑_{i < j} 1/(i+1)` in a ring with `Inv`. -/
def hsum {R : Type*} [AddCommMonoid R] [NatCast R] [Inv R] (j : ℕ) : R :=
  ∑ i ∈ range j, ((i + 1 : ℕ) : R)⁻¹

/-- `H^{(2)}_j = ∑_{i < j} 1/(i+1)^2`. -/
def hsum2 {R : Type*} [CommSemiring R] [Inv R] (j : ℕ) : R :=
  ∑ i ∈ range j, ((i + 1 : ℕ) : R)⁻¹ ^ 2

theorem hsum_succ {R : Type*} [AddCommMonoid R] [NatCast R] [Inv R] (j : ℕ) :
    (hsum (j + 1) : R) = hsum j + ((j + 1 : ℕ) : R)⁻¹ := by
  rw [hsum, sum_range_succ]; rfl

theorem hsum2_succ {R : Type*} [CommSemiring R] [Inv R] (j : ℕ) :
    (hsum2 (j + 1) : R) = hsum2 j + ((j + 1 : ℕ) : R)⁻¹ ^ 2 := by
  rw [hsum2, sum_range_succ]; rfl

theorem S0 {R : Type*} [CommRing R] (n : ℕ) :
    2 * ∑ j ∈ range n, ((j + 1 : ℕ) : R) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast; ring

section Field

variable {F : Type*} [Field F]

variable {n : ℕ} (hF : ∀ i, i < n → ((i + 1 : ℕ) : F) ≠ 0)
include hF

theorem S1 : ∑ j ∈ range n, (hsum j : F) = n * hsum n - n := by
  induction n with
  | zero => simp [hsum]
  | succ n ih =>
    rw [sum_range_succ, ih (fun i hi => hF i (by omega)), hsum_succ]
    have h := mul_inv_cancel₀ (hF n (by omega))
    push_cast at h ⊢
    linear_combination (-1 : F) * h

theorem S2 : 4 * ∑ j ∈ range n, ((j + 1 : ℕ) : F) * hsum j =
    2 * n * (n + 1) * hsum n - n ^ 2 - 3 * n := by
  induction n with
  | zero => simp [hsum]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih (fun i hi => hF i (by omega)), hsum_succ]
    have h := mul_inv_cancel₀ (hF n (by omega))
    push_cast at h ⊢
    linear_combination (-2 * ((n : F) + 1 + 1)) * h

theorem S3 : 2 * ∑ j ∈ range n, ((j + 1 : ℕ) : F)⁻¹ * hsum j = hsum n ^ 2 - hsum2 n := by
  induction n with
  | zero => simp [hsum, hsum2]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih (fun i hi => hF i (by omega)), hsum_succ, hsum2_succ]
    ring

omit hF in
theorem Bsum_eq (hF : ∀ i, i < n + 1 → ((i + 1 : ℕ) : F) ≠ 0) :
    4 * ∑ j ∈ range n, ((j + 1 + 1 : ℕ) : F) ^ 2 * ((j + 1 : ℕ) : F)⁻¹ *
        ((hsum j : F) - 2 * hsum (j + 1 + 1) + 2) =
      -(2 * (n : F) * (n + 1) * hsum n - (n : F) ^ 2 - 3 * n) - 8 * ((n : F) * hsum n - n) -
        2 * ((hsum n : F) ^ 2 - hsum2 n) + 4 * ((n : F) * (n + 1)) - 16 * (hsum n : F) -
        8 * (hsum2 n : F) := by
  have hF' : ∀ i, i < n → ((i + 1 : ℕ) : F) ≠ 0 := fun i hi => hF i (by omega)
  have e : ∀ j ∈ range n, ((j + 1 + 1 : ℕ) : F) ^ 2 * ((j + 1 : ℕ) : F)⁻¹ *
      ((hsum j : F) - 2 * hsum (j + 1 + 1) + 2) =
      -(((j + 1 : ℕ) : F) * hsum j) - 2 * (hsum j : F) - ((j + 1 : ℕ) : F)⁻¹ * hsum j +
        2 * ((j + 1 : ℕ) : F) - 4 * ((j + 1 : ℕ) : F)⁻¹ - 2 * ((j + 1 : ℕ) : F)⁻¹ ^ 2 := by
    intro j hj
    have hj' := mem_range.1 hj
    have ha := mul_inv_cancel₀ (hF j (by omega))
    have hb := mul_inv_cancel₀ (hF (j + 1) (by omega))
    rw [hsum_succ (j + 1), hsum_succ j]
    set a := ((j + 1 : ℕ) : F)
    set b := ((j + 1 + 1 : ℕ) : F)
    set h := (hsum j : F)
    have hab : b = a + 1 := by simp only [a, b]; push_cast; ring
    rw [hab] at hb ⊢
    linear_combination ((a + 2) * (-h - 2 * a⁻¹ + 2) - 4) * ha + (-2 * (a + 1) * a⁻¹) * hb
  rw [sum_congr rfl e]
  simp only [sum_add_distrib, sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  have e0 := S0 (R := F) n
  have e1 := S1 hF'
  have e2 := S2 hF'
  have e3 := S3 hF'
  simp only [hsum, hsum2] at e1 e2 e3 ⊢
  linear_combination (-1 : F) * e2 - 8 * e1 - 2 * e3 + 4 * e0

end Field

/-! ### Arithmetic in `ZMod (p ^ K)` (adapted from `FCPalomar/MosN8`) -/

section ZModPow

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

theorem natCast_mul_inv {x : ℕ} (hx : ¬ p ∣ x) :
    (x : ZMod (p ^ K)) * (x : ZMod (p ^ K))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one x (((Nat.Prime.coprime_iff_not_dvd hp.out).2 hx).symm.pow_right K)

theorem natCast_mul_inv_of_lt {x : ℕ} (h0 : 0 < x) (hx : x < p) :
    (x : ZMod (p ^ K)) * (x : ZMod (p ^ K))⁻¹ = 1 :=
  natCast_mul_inv (Nat.not_dvd_of_pos_of_lt h0 hx)

theorem castHom_natCast_inv {m n : ℕ} (h : m ∣ n) {x : ℕ} (hx : Nat.Coprime x n) :
    ZMod.castHom h (ZMod m) ((x : ZMod n)⁻¹) = (x : ZMod m)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  rw [← map_natCast (ZMod.castHom h (ZMod m)) x, ← map_mul, ZMod.coe_mul_inv_eq_one x hx, map_one]

/-- An element of `ZMod (p ^ K)` that vanishes modulo `p` is a multiple of `p`. -/
theorem exists_mul_of_castHom_eq_zero (hK : 1 ≤ K) (z : ZMod (p ^ K))
    (hz : ZMod.castHom (dvd_pow_self p (by omega : K ≠ 0)) (ZMod p) z = 0) :
    ∃ w, z = p * w := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have h1 : ((z.val : ℕ) : ZMod p) = 0 := by
    rw [← map_natCast (ZMod.castHom (dvd_pow_self p (by omega : K ≠ 0)) (ZMod p)),
      ZMod.natCast_zmod_val]
    exact hz
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨c, hc⟩ := h1
  exact ⟨(c : ZMod (p ^ K)), by rw [← ZMod.natCast_zmod_val z, hc, Nat.cast_mul]⟩

theorem castHom_hsum (hK : K ≠ 0) {j : ℕ} (hj : j < p) :
    ZMod.castHom (dvd_pow_self p hK) (ZMod p) (hsum j : ZMod (p ^ K)) = hsum j := by
  rw [hsum, hsum, map_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i + 1 < p := by have := mem_range.1 hi; omega
  exact castHom_natCast_inv _ (((Nat.Prime.coprime_iff_not_dvd hp.out).2
    (Nat.not_dvd_of_pos_of_lt (by omega) hi')).symm.pow_right K)

end ZModPow

/-! ### Product expansions modulo `p ^ 3` -/

section Cube

variable {p : ℕ} [hp : Fact p.Prime]

theorem sum_inv_pow' {j : ℕ} (hj0 : 0 < j) (hj : j < p - 1) :
    ∑ i ∈ range (p - 1), (((i + 1 : ℕ) : ZMod p)⁻¹) ^ j = 0 := by
  have h := sum_inv_pow (p := p) hj
  have hr : range p = range (p - 1 + 1) := by rw [Nat.sub_add_cancel hp.out.one_lt.le]
  rw [hr, sum_range_succ'] at h
  simpa [zero_pow hj0.ne'] using h

theorem hsum_zmod (hp5 : 5 ≤ p) : (hsum (p - 1) : ZMod p) = 0 := by
  have := sum_inv_pow' (p := p) (j := 1) one_pos (by omega)
  simpa [hsum] using this

theorem hsum2_zmod (hp5 : 5 ≤ p) : (hsum2 (p - 1) : ZMod p) = 0 :=
  sum_inv_pow' (p := p) (j := 2) two_pos (by omega)

omit hp in
theorem p_cube : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]

theorem one_inv : (1 : ZMod (p ^ 3))⁻¹ = 1 := by
  have h := natCast_mul_inv_of_lt (p := p) (K := 3) (x := 1) one_pos hp.out.one_lt
  rwa [Nat.cast_one, one_mul] at h

/-- `C(p-1+k, k) = (p/k)(1 + p H_{k-1})` modulo `p ^ 3`, written with `k = j + 1`. -/
theorem choose_A {j : ℕ} (hj : j + 1 < p) :
    (((p + j).choose (j + 1) : ℕ) : ZMod (p ^ 3)) =
      p * ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ * (1 + p * hsum j) := by
  induction j with
  | zero => simp [hsum]
  | succ j ih =>
    have hC' := congrArg (fun n : ℕ => (n : ZMod (p ^ 3))) (Nat.add_one_mul_choose_eq (p + j) (j + 1))
    simp only [Nat.cast_mul] at hC'
    rw [ih (by omega)] at hC'
    rw [show p + (j + 1) = p + j + 1 by ring, hsum_succ]
    set C' := (((p + j + 1).choose (j + 1 + 1) : ℕ) : ZMod (p ^ 3))
    set a := ((j + 1 : ℕ) : ZMod (p ^ 3))
    set b := ((j + 1 + 1 : ℕ) : ZMod (p ^ 3))
    set h := (hsum j : ZMod (p ^ 3))
    have ha : a * a⁻¹ = 1 := natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hb : b * b⁻¹ = 1 := natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hpa : ((p + j + 1 : ℕ) : ZMod (p ^ 3)) = p + a := by simp only [a]; push_cast; ring
    rw [hpa] at hC'
    linear_combination (-C') * hb - b⁻¹ * hC' + b⁻¹ * p * (1 + p * h) * ha +
      b⁻¹ * a⁻¹ * h * p_cube

/-- `C(p-2, k) ≡ (-1)^k (k+1) (1 - p (H_{k+1} - 1)) (mod p ^ 2)`, stated after multiplying
by `p`. -/
theorem choose_B {k : ℕ} (hk : k + 2 ≤ p) :
    (p : ZMod (p ^ 3)) * (((p - 2).choose k : ℕ) : ZMod (p ^ 3)) =
      p * ((-1) ^ k * ((k + 1 : ℕ) : ZMod (p ^ 3)) * (1 - p * (hsum (k + 1) - 1))) := by
  induction k with
  | zero => simp [hsum]
  | succ k ih =>
    have hr := congrArg (fun n : ℕ => (n : ZMod (p ^ 3))) (Nat.choose_succ_right_eq (p - 2) k)
    simp only [Nat.cast_mul] at hr
    have ih' := ih (by omega)
    rw [hsum_succ (k + 1), pow_succ (-1 : ZMod (p ^ 3)) k]
    set C' := (((p - 2).choose (k + 1) : ℕ) : ZMod (p ^ 3))
    set C := (((p - 2).choose k : ℕ) : ZMod (p ^ 3))
    set a := ((k + 1 : ℕ) : ZMod (p ^ 3))
    set b := ((k + 1 + 1 : ℕ) : ZMod (p ^ 3))
    set h := (hsum (k + 1) : ZMod (p ^ 3))
    set s := ((-1 : ZMod (p ^ 3)) ^ k)
    have ha : a * a⁻¹ = 1 := natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hb : b * b⁻¹ = 1 := natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hpb : ((p - 2 - k : ℕ) : ZMod (p ^ 3)) = p - b := by
      rw [show p - 2 - k = p - (k + 1 + 1) by omega, Nat.cast_sub (by omega)]
    rw [hpb] at hr
    linear_combination (-p * C' + (p - b) * p * s * (1 - p * (h - 1))) * ha + p * a⁻¹ * hr +
      a⁻¹ * (p - b) * ih' + (-p ^ 2 * s) * hb + (-s * (h - 1)) * p_cube (p := p)

/-- The `k`-th term of `a(p-1)`, for `k = j + 1`, modulo `p ^ 3`. -/
theorem term_C {j : ℕ} (hj : j + 3 ≤ p) :
    ((((p - 2).choose (j + 1)) ^ 2 * (p + j).choose (j + 1) : ℕ) : ZMod (p ^ 3)) =
      p * ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) ^ 2 * ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ +
      p ^ 2 * ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) ^ 2 * ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ *
        (hsum j - 2 * hsum (j + 1 + 1) + 2) := by
  have hA := choose_A (p := p) (j := j) (by omega)
  have hB := choose_B (p := p) (k := j + 1) (by omega)
  rw [Nat.cast_mul, Nat.cast_pow, hA]
  set C := (((p - 2).choose (j + 1) : ℕ) : ZMod (p ^ 3))
  set a := ((j + 1 : ℕ) : ZMod (p ^ 3))
  set b := ((j + 1 + 1 : ℕ) : ZMod (p ^ 3))
  set h := (hsum j : ZMod (p ^ 3))
  set H := (hsum (j + 1 + 1) : ZMod (p ^ 3))
  set s := ((-1 : ZMod (p ^ 3)) ^ (j + 1))
  have hs : s ^ 2 = 1 := by
    simp only [s]; rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  set c := s * b * (1 - p * (H - 1))
  linear_combination (C + c) * a⁻¹ * (1 + p * h) * hB +
    p * b ^ 2 * a⁻¹ * (1 - p * (H - 1)) ^ 2 * (1 + p * h) * hs +
    b ^ 2 * a⁻¹ * (-2 * (H - 1) * h + (H - 1) ^ 2 + p * (H - 1) ^ 2 * h) * p_cube (p := p)

end Cube

section Cube2

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_mul_inv_two (hp5 : 5 ≤ p) : (2 : ZMod (p ^ 3)) * (2 : ZMod (p ^ 3))⁻¹ = 1 := by
  have := natCast_mul_inv (p := p) (K := 3) (x := 2)
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  rwa [Nat.cast_ofNat] at this

theorem p_sq_mul_eq_zero (z : ZMod (p ^ 3))
    (hz : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) z = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * z = 0 := by
  obtain ⟨w, rfl⟩ := exists_mul_of_castHom_eq_zero (K := 3) (by norm_num) z hz
  rw [← mul_assoc, ← pow_succ, p_cube, zero_mul]

theorem castHom_inv {j : ℕ} (h0 : 0 < j) (hj : j < p) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) ((j : ZMod (p ^ 3))⁻¹) =
      (j : ZMod p)⁻¹ :=
  castHom_natCast_inv _ (((Nat.Prime.coprime_iff_not_dvd hp.out).2
    (Nat.not_dvd_of_pos_of_lt h0 hj)).symm.pow_right 3)

/-- Wolstenholme: `p H_{p-1} ≡ 0 (mod p^3)`. -/
theorem wolst (hp5 : 5 ≤ p) : (p : ZMod (p ^ 3)) * hsum (p - 1) = 0 := by
  set f : ℕ → ZMod (p ^ 3) := fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ with hf
  have hrefl : ∑ i ∈ range (p - 1), f (p - 1 - 1 - i) = ∑ i ∈ range (p - 1), f i :=
    sum_range_reflect f (p - 1)
  set Z := ∑ i ∈ range (p - 1), f i * f (p - 1 - 1 - i) with hZdef
  have hpair : ∀ i ∈ range (p - 1), f i + f (p - 1 - 1 - i) = p * (f i * f (p - 1 - 1 - i)) := by
    intro i hi
    have hi' := mem_range.1 hi
    have hx : ((i + 1 : ℕ) : ZMod (p ^ 3)) * f i = 1 :=
      natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hy : ((p - 1 - 1 - i + 1 : ℕ) : ZMod (p ^ 3)) * f (p - 1 - 1 - i) = 1 :=
      natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hxy : ((i + 1 : ℕ) : ZMod (p ^ 3)) + ((p - 1 - 1 - i + 1 : ℕ) : ZMod (p ^ 3)) = p := by
      rw [← Nat.cast_add]; congr 1; omega
    linear_combination (-f (p - 1 - 1 - i)) * hx + (-f i) * hy +
      (f i * f (p - 1 - 1 - i)) * hxy
  have h2 : 2 * hsum (p - 1) = (p : ZMod (p ^ 3)) * Z := by
    calc 2 * (hsum (p - 1) : ZMod (p ^ 3))
        = ∑ i ∈ range (p - 1), f i + ∑ i ∈ range (p - 1), f (p - 1 - 1 - i) := by
          rw [hrefl, two_mul]; rfl
      _ = ∑ i ∈ range (p - 1), (f i + f (p - 1 - 1 - i)) := sum_add_distrib.symm
      _ = ∑ i ∈ range (p - 1), (p : ZMod (p ^ 3)) * (f i * f (p - 1 - 1 - i)) :=
          sum_congr rfl hpair
      _ = _ := (mul_sum _ _ _).symm
  have hZ : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) Z = 0 := by
    rw [hZdef, map_sum]
    have e : ∀ i ∈ range (p - 1), ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
        (f i * f (p - 1 - 1 - i)) = -(((i + 1 : ℕ) : ZMod p)⁻¹ ^ 2) := by
      intro i hi
      have hi' := mem_range.1 hi
      rw [map_mul, hf, castHom_inv (by omega) (by omega), castHom_inv (by omega) (by omega)]
      have hc : ((p - 1 - 1 - i + 1 : ℕ) : ZMod p) = -((i + 1 : ℕ) : ZMod p) := by
        have : ((p - 1 - 1 - i + 1 : ℕ) : ZMod p) + ((i + 1 : ℕ) : ZMod p) = 0 := by
          rw [← Nat.cast_add, show p - 1 - 1 - i + 1 + (i + 1) = p by omega, ZMod.natCast_self]
        linear_combination this
      rw [hc, inv_neg]; ring
    rw [sum_congr rfl e, sum_neg_distrib]
    have := hsum2_zmod (p := p) hp5
    rw [hsum2] at this
    rw [this, neg_zero]
  have h3 : 2 * ((p : ZMod (p ^ 3)) * hsum (p - 1)) = 0 := by
    rw [mul_left_comm, h2, ← mul_assoc, ← sq, p_sq_mul_eq_zero Z hZ]
  calc (p : ZMod (p ^ 3)) * hsum (p - 1)
      = (2 : ZMod (p ^ 3))⁻¹ * (2 * ((p : ZMod (p ^ 3)) * hsum (p - 1))) := by
        rw [← mul_assoc, mul_comm _ (2 : ZMod (p ^ 3)), two_mul_inv_two hp5, one_mul]
    _ = 0 := by rw [h3, mul_zero]

theorem hsum_pm2_zmod (hp5 : 5 ≤ p) : (hsum (p - 2) : ZMod p) = 1 := by
  have h := hsum_zmod (p := p) hp5
  rw [show p - 1 = p - 2 + 1 by omega, hsum_succ] at h
  have hc : ((p - 2 + 1 : ℕ) : ZMod p) = -1 := by
    have : ((p - 2 + 1 : ℕ) : ZMod p) + 1 = 0 := by
      rw [← Nat.cast_add_one, show p - 2 + 1 + 1 = p by omega, ZMod.natCast_self]
    linear_combination this
  rw [hc, inv_neg, inv_one] at h
  linear_combination h

theorem hsum2_pm2_zmod (hp5 : 5 ≤ p) : (hsum2 (p - 2) : ZMod p) = -1 := by
  have h := hsum2_zmod (p := p) hp5
  rw [show p - 1 = p - 2 + 1 by omega, hsum2_succ] at h
  have hc : ((p - 2 + 1 : ℕ) : ZMod p) = -1 := by
    have : ((p - 2 + 1 : ℕ) : ZMod p) + 1 = 0 := by
      rw [← Nat.cast_add_one, show p - 2 + 1 + 1 = p by omega, ZMod.natCast_self]
    linear_combination this
  rw [hc, inv_neg, inv_one] at h
  linear_combination h

theorem partA (hp5 : 5 ≤ p) :
    2 * (p : ZMod (p ^ 3)) * ∑ j ∈ range (p - 2),
      ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) ^ 2 * ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ =
      3 * p ^ 2 - 4 * p := by
  have e : ∀ j ∈ range (p - 2), ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) ^ 2 *
      ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ =
      ((j + 1 : ℕ) : ZMod (p ^ 3)) + 2 + ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ := by
    intro j hj
    have hj' := mem_range.1 hj
    have ha : ((j + 1 : ℕ) : ZMod (p ^ 3)) * ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ = 1 :=
      natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    rw [show ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) = ((j + 1 : ℕ) : ZMod (p ^ 3)) + 1 by push_cast; ring]
    linear_combination (((j + 1 : ℕ) : ZMod (p ^ 3)) + 2) * ha
  have hA : 2 * ∑ j ∈ range (p - 2), ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) ^ 2 *
      ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ =
      ((p - 2 : ℕ) : ZMod (p ^ 3)) * ((p - 2 : ℕ) + 1) + 4 * ((p - 2 : ℕ) : ZMod (p ^ 3)) +
        2 * hsum (p - 2) := by
    rw [sum_congr rfl e, sum_add_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
      mul_add, mul_add, S0]
    simp only [hsum]
    ring
  have hN : ((p - 2 : ℕ) : ZMod (p ^ 3)) = p - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hH : (hsum (p - 1) : ZMod (p ^ 3)) = hsum (p - 2) + ((p - 2 + 1 : ℕ) : ZMod (p ^ 3))⁻¹ := by
    rw [← hsum_succ, show p - 2 + 1 = p - 1 by omega]
  set w := ((p - 2 + 1 : ℕ) : ZMod (p ^ 3))⁻¹ with hw_def
  have hw : ((p : ZMod (p ^ 3)) - 1) * w = 1 := by
    have := natCast_mul_inv_of_lt (p := p) (K := 3) (x := p - 2 + 1) (by omega) (by omega)
    have e : ((p - 2 + 1 : ℕ) : ZMod (p ^ 3)) = p - 1 := by
      rw [show p - 2 + 1 = p - 1 by omega, Nat.cast_sub hp.out.one_lt.le]; norm_num
    rw [← e]; exact this
  have hW := wolst (p := p) hp5
  rw [hN, show (hsum (p - 2) : ZMod (p ^ 3)) = hsum (p - 1) - w by rw [hH]; ring] at hA
  linear_combination (p : ZMod (p ^ 3)) * hA + 2 * hW + 2 * ((p : ZMod (p ^ 3)) + p ^ 2) * hw +
    (1 - 2 * w) * p_cube (p := p)

theorem partB (hp5 : 5 ≤ p) :
    2 * (p : ZMod (p ^ 3)) ^ 2 * ∑ j ∈ range (p - 2),
      ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) ^ 2 * ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ *
        (hsum j - 2 * hsum (j + 1 + 1) + 2) = -5 * p ^ 2 := by
  set B := ∑ j ∈ range (p - 2),
      ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) ^ 2 * ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ *
        (hsum j - 2 * hsum (j + 1 + 1) + 2) with hBdef
  have hφ : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) (2 * B + 5) = 0 := by
    have e : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) B =
        ∑ j ∈ range (p - 2), ((j + 1 + 1 : ℕ) : ZMod p) ^ 2 * ((j + 1 : ℕ) : ZMod p)⁻¹ *
          ((hsum j : ZMod p) - 2 * hsum (j + 1 + 1) + 2) := by
      rw [hBdef, map_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.1 hj
      rw [map_mul, map_mul, map_pow, map_natCast, castHom_inv (by omega) (by omega), map_add,
        map_sub, map_mul, castHom_hsum (by norm_num) (by omega),
        castHom_hsum (by norm_num) (by omega), map_ofNat]
    have hB := Bsum_eq (F := ZMod p) (n := p - 2)
      (fun i hi => natCast_ne_zero (p := p) (by omega) (by omega))
    have hN : ((p - 2 : ℕ) : ZMod p) = -2 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, Nat.cast_ofNat]
    rw [hsum_pm2_zmod hp5, hsum2_pm2_zmod hp5, hN] at hB
    rw [map_add, map_mul, map_ofNat, map_ofNat, e]
    have h2 : (2 : ZMod p) ≠ 0 := by
      have := natCast_ne_zero (p := p) (i := 2) (by norm_num) (by omega)
      rwa [Nat.cast_ofNat] at this
    apply mul_left_cancel₀ h2
    linear_combination hB
  have := p_sq_mul_eq_zero (2 * B + 5) hφ
  linear_combination this

theorem a361717_zmod (hp5 : 5 ≤ p) :
    ((a361717 (p - 1) : ℕ) : ZMod (p ^ 3)) = 1 - 2 * p - p ^ 2 := by
  set A := ∑ j ∈ range (p - 2),
      ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) ^ 2 * ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ with hAdef
  set B := ∑ j ∈ range (p - 2),
      ((j + 1 + 1 : ℕ) : ZMod (p ^ 3)) ^ 2 * ((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹ *
        (hsum j - 2 * hsum (j + 1 + 1) + 2) with hBdef
  have hsplit : ((a361717 (p - 1) : ℕ) : ZMod (p ^ 3)) = 1 + (p * A + p ^ 2 * B) := by
    rw [a361717, show p - 1 - 1 = p - 2 by omega,
      show range (p - 1) = range (p - 2 + 1) by congr 1; omega, sum_range_succ', Nat.cast_add,
      Nat.cast_sum, hAdef, hBdef, mul_sum, mul_sum, ← sum_add_distrib]
    simp only [Nat.choose_zero_right, one_pow, mul_one, Nat.cast_one, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [show p - 1 + (j + 1) = p + j by omega, term_C (by have := mem_range.1 hj; omega)]
    ring
  rw [hsplit]
  have hA := partA hp5
  have hB := partB hp5
  rw [← hAdef] at hA
  rw [← hBdef] at hB
  linear_combination (2 : ZMod (p ^ 3))⁻¹ * (hA + hB) -
    ((p : ZMod (p ^ 3)) * A + p ^ 2 * B + 2 * p + p ^ 2) * two_mul_inv_two hp5

end Cube2

/-! ## Part 3. A357511 modulo `p ^ 4` -/

section Quart

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem p_four : (p : ZMod (p ^ 4)) ^ 4 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]

/-- `C(p-1,k)^2 C(p-1+k,k)^2 ≡ p^2 k^{-2} (1 - 2p/k) (mod p^4)`, with `k = j + 1`. -/
theorem V_formula {j : ℕ} (hj : j + 1 < p) :
    ((((p - 1).choose (j + 1)) ^ 2 * ((p - 1 + (j + 1)).choose (j + 1)) ^ 2 : ℕ) :
      ZMod (p ^ 4)) =
      p ^ 2 * ((j + 1 : ℕ) : ZMod (p ^ 4))⁻¹ ^ 2 * (1 - 2 * p * ((j + 1 : ℕ) : ZMod (p ^ 4))⁻¹) := by
  induction j with
  | zero =>
    have h1 : ((1 : ℕ) : ZMod (p ^ 4))⁻¹ = 1 := by
      rw [Nat.cast_one]
      have h := natCast_mul_inv_of_lt (p := p) (K := 4) (x := 1) one_pos hp.out.one_lt
      rwa [Nat.cast_one, one_mul] at h
    rw [zero_add, h1, Nat.choose_one_right, Nat.choose_one_right, Nat.sub_add_cancel
      hp.out.one_lt.le, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hp.out.one_lt.le]
    push_cast
    linear_combination p_four (p := p)
  | succ j ih =>
    have ih' := ih (by omega)
    have hA := congrArg (fun n : ℕ => (n : ZMod (p ^ 4))) (Nat.choose_succ_right_eq (p - 1) (j + 1))
    have hB := congrArg (fun n : ℕ => (n : ZMod (p ^ 4)))
      (Nat.add_one_mul_choose_eq (p - 1 + (j + 1)) (j + 1))
    simp only [Nat.cast_mul] at hA hB
    rw [show p - 1 + (j + 1) + 1 = p - 1 + (j + 1 + 1) by ring] at hB
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow] at ih' ⊢
    set A := (((p - 1).choose (j + 1) : ℕ) : ZMod (p ^ 4))
    set B := (((p - 1 + (j + 1)).choose (j + 1) : ℕ) : ZMod (p ^ 4))
    set A' := (((p - 1).choose (j + 1 + 1) : ℕ) : ZMod (p ^ 4))
    set B' := (((p - 1 + (j + 1 + 1)).choose (j + 1 + 1) : ℕ) : ZMod (p ^ 4))
    set a := ((j + 1 : ℕ) : ZMod (p ^ 4))
    set b := ((j + 1 + 1 : ℕ) : ZMod (p ^ 4))
    set u := a⁻¹
    set v := b⁻¹
    have ha : a * u = 1 := natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hb : b * v = 1 := natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hab : b = a + 1 := by simp only [a, b]; push_cast; ring
    have hpb : ((p - 1 - (j + 1) : ℕ) : ZMod (p ^ 4)) = p - b := by
      rw [show p - 1 - (j + 1) = p - (j + 1 + 1) by omega, Nat.cast_sub (by omega)]
    have hpa : ((p - 1 + (j + 1 + 1) : ℕ) : ZMod (p ^ 4)) = p + a := by
      rw [show p - 1 + (j + 1 + 1) = p + (j + 1) by omega, Nat.cast_add]
    rw [hpb] at hA
    rw [hpa] at hB
    have hX : (p - b) * (p + a) * (u * v) = ((p : ZMod (p ^ 4)) ^ 2 - p) * (u * v) - 1 := by
      linear_combination (-(p : ZMod (p ^ 4)) * u * v) * hab - b * v * ha - hb
    have hv : u * v - u + v = 0 := by
      rw [hab] at hb
      linear_combination u * hb - v * ha
    have step1 : A' ^ 2 * B' ^ 2 = v ^ 4 * (A ^ 2 * B ^ 2) * ((p - b) * (p + a)) ^ 2 := by
      linear_combination (-(A' ^ 2 * B' ^ 2) * (1 + b * v + (b * v) ^ 2 + (b * v) ^ 3)) * hb +
        v ^ 4 * (A' * b + A * (p - b)) * (B' * b) ^ 2 * hA +
        -(v ^ 4 * A ^ 2 * (p - b) ^ 2 * (B' * b + B * (p + a))) * hB
    rw [step1, ih']
    have step2 : v ^ 4 * ((p : ZMod (p ^ 4)) ^ 2 * u ^ 2 * (1 - 2 * p * u)) * ((p - b) * (p + a)) ^ 2 =
        p ^ 2 * (1 - 2 * p * u) * v ^ 2 * ((p - b) * (p + a) * (u * v)) ^ 2 := by ring
    rw [step2, hX]
    linear_combination (2 * (p : ZMod (p ^ 4)) ^ 3 * v ^ 2) * hv +
      (-2 * (p : ZMod (p ^ 4)) ^ 3 * u ^ 3 * v ^ 4 + 4 * p ^ 2 * u ^ 3 * v ^ 4 + p ^ 2 * u ^ 2 * v ^ 4 -
        2 * p * u ^ 3 * v ^ 4 - 2 * p * u ^ 2 * v ^ 4 + 4 * p * u ^ 2 * v ^ 3 + u ^ 2 * v ^ 4 -
        4 * u ^ 2 * v ^ 3 - 2 * u * v ^ 3) * p_four (p := p)

theorem castHom_inv4 {j : ℕ} (h0 : 0 < j) (hj : j < p) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 4 ≠ 0)) (ZMod p) ((j : ZMod (p ^ 4))⁻¹) =
      (j : ZMod p)⁻¹ :=
  castHom_natCast_inv _ (((Nat.Prime.coprime_iff_not_dvd hp.out).2
    (Nat.not_dvd_of_pos_of_lt h0 hj)).symm.pow_right 4)

/-- `H(4) ≡ 0 (mod p)`, as `p^3 H(4) ≡ 0 (mod p^4)`, for `p ≥ 7`. -/
theorem p_cube_H4 (h7 : 7 ≤ p) :
    (p : ZMod (p ^ 4)) ^ 3 * ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 4))⁻¹ ^ 4 = 0 := by
  have hz : ZMod.castHom (dvd_pow_self p (by norm_num : 4 ≠ 0)) (ZMod p)
      (∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 4))⁻¹ ^ 4) = 0 := by
    rw [map_sum]
    have e : ∀ i ∈ range (p - 1), ZMod.castHom (dvd_pow_self p (by norm_num : 4 ≠ 0)) (ZMod p)
        (((i + 1 : ℕ) : ZMod (p ^ 4))⁻¹ ^ 4) = ((i + 1 : ℕ) : ZMod p)⁻¹ ^ 4 := by
      intro i hi
      have := mem_range.1 hi
      rw [map_pow, castHom_inv4 (by omega) (by omega)]
    rw [sum_congr rfl e]
    exact sum_inv_pow' (by norm_num) (by omega)
  obtain ⟨w, hw⟩ := exists_mul_of_castHom_eq_zero (K := 4) (by norm_num) _ hz
  rw [hw, ← mul_assoc, ← pow_succ, p_four, zero_mul]

/-- `H(3) ≡ 0 (mod p^2)`, as `p^2 H(3) ≡ 0 (mod p^4)`, for `p ≥ 7`. -/
theorem p_sq_H3 (h7 : 7 ≤ p) :
    (p : ZMod (p ^ 4)) ^ 2 * ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 4))⁻¹ ^ 3 = 0 := by
  set f : ℕ → ZMod (p ^ 4) := fun i => ((i + 1 : ℕ) : ZMod (p ^ 4))⁻¹ with hf
  set x : ℕ → ZMod (p ^ 4) := fun i => ((i + 1 : ℕ) : ZMod (p ^ 4)) with hx_def
  have hrefl : ∑ i ∈ range (p - 1), f (p - 1 - 1 - i) ^ 3 = ∑ i ∈ range (p - 1), f i ^ 3 :=
    sum_range_reflect (fun i => f i ^ 3) (p - 1)
  set Z := ∑ i ∈ range (p - 1),
    (3 * x i ^ 2 - 3 * p * x i + p ^ 2) * f i ^ 3 * f (p - 1 - 1 - i) ^ 3 with hZdef
  have hpair : ∀ i ∈ range (p - 1), f i ^ 3 + f (p - 1 - 1 - i) ^ 3 =
      p * ((3 * x i ^ 2 - 3 * p * x i + p ^ 2) * f i ^ 3 * f (p - 1 - 1 - i) ^ 3) := by
    intro i hi
    have hi' := mem_range.1 hi
    have hx : x i * f i = 1 := natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hy : ((p - 1 - 1 - i + 1 : ℕ) : ZMod (p ^ 4)) * f (p - 1 - 1 - i) = 1 :=
      natCast_mul_inv_of_lt (p := p) (by omega) (by omega)
    have hxy : x i + ((p - 1 - 1 - i + 1 : ℕ) : ZMod (p ^ 4)) = p := by
      simp only [hx_def]; rw [← Nat.cast_add]; congr 1; omega
    set y := ((p - 1 - 1 - i + 1 : ℕ) : ZMod (p ^ 4))
    set xi := f i
    set yi := f (p - 1 - 1 - i)
    linear_combination (-(yi ^ 3) * ((x i * xi) ^ 2 + x i * xi + 1)) * hx +
      (-(xi ^ 3) * ((y * yi) ^ 2 + y * yi + 1)) * hy +
      ((p : ZMod (p ^ 4)) ^ 2 - 2 * p * x i + p * y + x i ^ 2 - x i * y + y ^ 2) * xi ^ 3 * yi ^ 3 * hxy
  have h2 : 2 * ∑ i ∈ range (p - 1), f i ^ 3 = (p : ZMod (p ^ 4)) * Z := by
    calc 2 * ∑ i ∈ range (p - 1), f i ^ 3
        = ∑ i ∈ range (p - 1), f i ^ 3 + ∑ i ∈ range (p - 1), f (p - 1 - 1 - i) ^ 3 := by
          rw [hrefl, two_mul]
      _ = ∑ i ∈ range (p - 1), (f i ^ 3 + f (p - 1 - 1 - i) ^ 3) := sum_add_distrib.symm
      _ = _ := by rw [sum_congr rfl hpair, ← mul_sum]
  have hZ : ZMod.castHom (dvd_pow_self p (by norm_num : 4 ≠ 0)) (ZMod p) Z = 0 := by
    rw [hZdef, map_sum]
    have e : ∀ i ∈ range (p - 1), ZMod.castHom (dvd_pow_self p (by norm_num : 4 ≠ 0)) (ZMod p)
        ((3 * x i ^ 2 - 3 * p * x i + p ^ 2) * f i ^ 3 * f (p - 1 - 1 - i) ^ 3) =
        -3 * ((i + 1 : ℕ) : ZMod p)⁻¹ ^ 4 := by
      intro i hi
      have hi' := mem_range.1 hi
      simp only [hf, hx_def]
      simp only [map_mul, map_add, map_sub, map_pow, map_natCast, map_ofNat]
      rw [castHom_inv4 (by omega) (by omega), castHom_inv4 (by omega) (by omega),
        ZMod.natCast_self]
      have hc : ((p - 1 - 1 - i + 1 : ℕ) : ZMod p) = -((i + 1 : ℕ) : ZMod p) := by
        have : ((p - 1 - 1 - i + 1 : ℕ) : ZMod p) + ((i + 1 : ℕ) : ZMod p) = 0 := by
          rw [← Nat.cast_add, show p - 1 - 1 - i + 1 + (i + 1) = p by omega, ZMod.natCast_self]
        linear_combination this
      have hne := natCast_ne_zero (p := p) (i := i + 1) (by omega) (by omega)
      rw [hc, inv_neg]
      have hh := mul_inv_cancel₀ hne
      set t := ((i + 1 : ℕ) : ZMod p)
      linear_combination (-3 * t⁻¹ ^ 4 * (1 + t * t⁻¹)) * hh
    rw [sum_congr rfl e, ← mul_sum, sum_inv_pow' (by norm_num) (by omega), mul_zero]
  obtain ⟨w, hw⟩ := exists_mul_of_castHom_eq_zero (K := 4) (by norm_num) _ hZ
  have h3 : 2 * ((p : ZMod (p ^ 4)) ^ 2 * ∑ i ∈ range (p - 1), f i ^ 3) = 0 := by
    rw [mul_left_comm, h2, hw]
    linear_combination (w : ZMod (p ^ 4)) * p_four (p := p)
  have h22 : (2 : ZMod (p ^ 4)) * (2 : ZMod (p ^ 4))⁻¹ = 1 := by
    have := natCast_mul_inv (p := p) (K := 4) (x := 2)
      (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    rwa [Nat.cast_ofNat] at this
  linear_combination (2 : ZMod (p ^ 4))⁻¹ * h3 -
    ((p : ZMod (p ^ 4)) ^ 2 * ∑ i ∈ range (p - 1), f i ^ 3) * h22

theorem sum_V_zero (h7 : 7 ≤ p) :
    ∑ j ∈ range (p - 1), ((j + 1 : ℕ) : ZMod (p ^ 4))⁻¹ *
      ((((p - 1).choose (j + 1)) ^ 2 * ((p - 1 + (j + 1)).choose (j + 1)) ^ 2 : ℕ) :
        ZMod (p ^ 4)) = 0 := by
  have e : ∀ j ∈ range (p - 1), ((j + 1 : ℕ) : ZMod (p ^ 4))⁻¹ *
      ((((p - 1).choose (j + 1)) ^ 2 * ((p - 1 + (j + 1)).choose (j + 1)) ^ 2 : ℕ) :
        ZMod (p ^ 4)) =
      p ^ 2 * ((j + 1 : ℕ) : ZMod (p ^ 4))⁻¹ ^ 3 -
        2 * p ^ 3 * ((j + 1 : ℕ) : ZMod (p ^ 4))⁻¹ ^ 4 := by
    intro j hj
    rw [V_formula (by have := mem_range.1 hj; omega)]
    ring
  rw [sum_congr rfl e, sum_sub_distrib, ← mul_sum, ← mul_sum]
  linear_combination p_sq_H3 h7 - 2 * p_cube_H4 h7

end Quart

/-! ## Main theorems -/

/-- Bala (A339946, Mar 2022): for every $m \ge 1$ and every prime $p \ge 7$,
$a_m(p) \equiv a_m(1) \pmod{p^5}$. -/
theorem am_congr (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ z : ℤ, am m p - am m 1 = (p : ℚ) ^ 5 * z := by
  have := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h := cz_prime hodd h7 hm
  rw [show (2 : ZMod (p ^ 5)) = ((2 : ℤ) : ZMod (p ^ 5)) by simp,
    ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨z, hz⟩ := h
  refine ⟨-z, ?_⟩
  rw [am_eq_cz, am_eq_cz, cz_one m hm]
  have hz' : cz m p = 2 - (p : ℤ) ^ 5 * z := by push_cast at hz; linarith
  rw [hz']
  push_cast
  ring

/-- Bala (A339946, Dec 2020): for every prime $p \ge 7$, $a(p) \equiv a(1) \pmod{p^5}$. -/
theorem a339946_congr (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ z : ℤ, a339946 p - a339946 1 = (p : ℚ) ^ 5 * z := by
  have e : ∀ n, a339946 n = am 1 n := fun n => by rw [a339946, am, one_mul]
  rw [e, e]
  exact am_congr 1 le_rfl p hp h7

/-- Bala (A361717, Conjecture 2): for every prime $p \ne 3$,
$a(p-1) \equiv 1 - 2p - p^2 \pmod{p^3}$. -/
theorem a361717_conj2 (p : ℕ) (hp : p.Prime) (h3 : p ≠ 3) :
    (a361717 (p - 1) : ℤ) ≡ 1 - 2 * p - p ^ 2 [ZMOD p ^ 3] := by
  rcases Nat.lt_or_ge p 5 with h | hp5
  · interval_cases p
    · exact absurd hp Nat.not_prime_zero
    · exact absurd hp Nat.not_prime_one
    · decide
    · exact absurd rfl h3
    · exact absurd hp (by decide)
  · have := Fact.mk hp
    have h := a361717_zmod hp5
    have h' : ((a361717 (p - 1) : ℤ) : ZMod (p ^ 3)) = ((1 - 2 * p - p ^ 2 : ℤ) : ZMod (p ^ 3)) := by
      push_cast; exact h
    rw [ZMod.intCast_eq_intCast_iff] at h'
    simpa using h'

/-- Bala (A357511): for every prime $p \ge 7$, $a(p-1) \equiv 0 \pmod{p^4}$. This is known
(O. Kutal, 2026; Z. Chen, Q. Wang, Y. Feng, *Mathematics* 14 (2026) 2832). -/
theorem a357511_congr (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) : (p : ℤ) ^ 4 ∣ a357511 (p - 1) := by
  have := Fact.mk hp
  have hdvd : ∀ k ∈ Icc 1 (p - 1), k ∣ (p - 1).factorial :=
    fun k hk => Nat.dvd_factorial (mem_Icc.1 hk).1 (mem_Icc.1 hk).2
  set M : ℕ := ∑ k ∈ Icc 1 (p - 1),
    (p - 1).factorial / k * (p - 1).choose k ^ 2 * (p - 1 + k).choose k ^ 2 with hM
  have hMQ : (M : ℚ) = (p - 1).factorial * s357511 (p - 1) := by
    rw [hM, s357511, Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : (k : ℚ) ≠ 0 := by have := (mem_Icc.1 hk).1; positivity
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_div (hdvd k hk) hk0, Nat.cast_pow, Nat.cast_pow]
    field_simp
  have hMz : (M : ZMod (p ^ 4)) = 0 := by
    rw [hM, Nat.cast_sum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    have e : ∀ j ∈ range (p - 1), (((p - 1).factorial / (1 + j) * (p - 1).choose (1 + j) ^ 2 *
        (p - 1 + (1 + j)).choose (1 + j) ^ 2 : ℕ) : ZMod (p ^ 4)) =
        ((p - 1).factorial : ZMod (p ^ 4)) * (((j + 1 : ℕ) : ZMod (p ^ 4))⁻¹ *
          ((((p - 1).choose (j + 1)) ^ 2 * ((p - 1 + (j + 1)).choose (j + 1)) ^ 2 : ℕ) :
            ZMod (p ^ 4))) := by
      intro j hj
      rw [add_comm 1 j]
      have hj' := mem_range.1 hj
      have hd : (p - 1).factorial / (j + 1) * (j + 1) = (p - 1).factorial :=
        Nat.div_mul_cancel (Nat.dvd_factorial (by omega) (by omega))
      have hu := natCast_mul_inv_of_lt (p := p) (K := 4) (x := j + 1) (by omega) (by omega)
      have hdc := congrArg (fun n : ℕ => (n : ZMod (p ^ 4))) hd
      simp only [Nat.cast_mul] at hdc ⊢
      linear_combination
        (-(((p - 1).factorial / (j + 1) : ℕ) : ZMod (p ^ 4)) *
          ((((p - 1).choose (j + 1)) ^ 2 : ℕ) : ZMod (p ^ 4)) *
          ((((p - 1 + (j + 1)).choose (j + 1)) ^ 2 : ℕ) : ZMod (p ^ 4))) * hu +
        (((j + 1 : ℕ) : ZMod (p ^ 4))⁻¹ * ((((p - 1).choose (j + 1)) ^ 2 : ℕ) : ZMod (p ^ 4)) *
          ((((p - 1 + (j + 1)).choose (j + 1)) ^ 2 : ℕ) : ZMod (p ^ 4))) * hdc
    rw [sum_congr rfl e, ← mul_sum, sum_V_zero h7, mul_zero]
  have hpM : (p : ℤ) ^ 4 ∣ (M : ℤ) := by
    have := (ZMod.natCast_eq_zero_iff M (p ^ 4)).1 hMz
    exact_mod_cast this
  set S := s357511 (p - 1)
  have hnum : (S.num : ℚ) = S * S.den :=
    (div_eq_iff (by exact_mod_cast S.den_nz)).1 (Rat.num_div_den S)
  have hint : S.num * ((p - 1).factorial : ℤ) = (M : ℤ) * S.den := by
    have : (S.num : ℚ) * (p - 1).factorial = (M : ℚ) * S.den := by rw [hnum, hMQ]; ring
    exact_mod_cast this
  have hcop : IsCoprime ((p : ℤ) ^ 4) ((p - 1).factorial : ℤ) := by
    have : Nat.Coprime (p ^ 4) (p - 1).factorial :=
      Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd hp).2
        (fun h => by have := (Nat.Prime.dvd_factorial hp).1 h; omega))
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  have h4 : (p : ℤ) ^ 4 ∣ S.num * ((p - 1).factorial : ℤ) := by
    rw [hint]; exact dvd_mul_of_dvd_left hpM _
  exact hcop.dvd_of_dvd_mul_right h4

/-- Sharpness at $p = 5$: $a_m(5) \equiv 2 + 625 m^2 \pmod{5^5}$ for every $m \ge 1$. -/
theorem am_five (m : ℕ) (hm : 1 ≤ m) : ∃ z : ℤ, am m 5 = 2 + 625 * (m : ℚ) ^ 2 + 5 ^ 5 * z := by
  have h := cz_five hm
  have h' : ((cz m 5 : ℤ) : ZMod (5 ^ 5)) = ((2 + 625 * (m : ℤ) ^ 2 : ℤ) : ZMod (5 ^ 5)) := by
    push_cast; exact h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
  obtain ⟨z, hz⟩ := h'
  refine ⟨-z, ?_⟩
  rw [am_eq_cz]
  have : cz m 5 = 2 + 625 * (m : ℤ) ^ 2 - 5 ^ 5 * z := by push_cast at hz; linarith
  rw [this]; push_cast; ring

/-- At $p = 5$, $a_m(5) \equiv a_m(1) \pmod{5^5}$ holds exactly when $5 \mid m$. So $p \ge 7$ is
the optimal uniform range. -/
theorem am_five_congr_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ z : ℤ, am m 5 - am m 1 = (5 : ℚ) ^ 5 * z) ↔ 5 ∣ m := by
  obtain ⟨w, hw⟩ := am_five m hm
  rw [hw, am_eq_cz, cz_one m hm]
  constructor
  · rintro ⟨z, hz⟩
    have hint : (625 : ℤ) * m ^ 2 = 5 ^ 5 * (z - w) := by
      have : ((625 * (m : ℤ) ^ 2 : ℤ) : ℚ) = ((5 ^ 5 * (z - w) : ℤ) : ℚ) := by
        push_cast at hz ⊢; linarith
      exact_mod_cast this
    have hdvd : (5 : ℤ) ∣ (m : ℤ) ^ 2 := ⟨z - w, by linarith⟩
    have : 5 ∣ m ^ 2 := by exact_mod_cast hdvd
    exact Nat.prime_five.dvd_of_dvd_pow this
  · rintro ⟨k, rfl⟩
    exact ⟨w + 5 * k ^ 2, by push_cast; ring⟩

/-! ## Sanity checks of the definitions -/

theorem C_half_mul_two : Polynomial.C (2⁻¹ : ℚ) * 2 = 1 := by
  rw [← map_ofNat Polynomial.C 2, ← map_mul]; norm_num

theorem legendreP_one : legendreP 1 = Polynomial.X := by
  simp [legendreP, Polynomial.shiftedLegendre, Finset.sum_range_succ]
  linear_combination (Polynomial.X - 1) * C_half_mul_two

theorem legendreP_two : legendreP 2 = Polynomial.C (3 / 2) * Polynomial.X ^ 2 - Polynomial.C (1 / 2) := by
  have h3 : Polynomial.C (3 / 2 : ℚ) = 3 * Polynomial.C 2⁻¹ := by
    rw [← map_ofNat Polynomial.C 3, ← map_mul]; norm_num
  simp [legendreP, Polynomial.shiftedLegendre, Finset.sum_range_succ, Nat.choose, h3]
  linear_combination (3 * Polynomial.C (2⁻¹ : ℚ) * Polynomial.X ^ 2 -
    6 * Polynomial.C (2⁻¹ : ℚ) * Polynomial.X + 3 * Polynomial.C (2⁻¹ : ℚ) - 1) * C_half_mul_two

theorem am_isInt (m n : ℕ) : ∃ z : ℤ, am m n = z := ⟨cz m n, am_eq_cz m n⟩

theorem am_one (m : ℕ) (hm : 1 ≤ m) : am m 1 = 2 := by
  rw [am_eq_cz, cz_one m hm]; norm_num

theorem a339946_one : a339946 1 = 2 := by
  rw [show a339946 1 = am 1 1 by rw [a339946, am, one_mul], am_one 1 le_rfl]

theorem cz_one_two : cz 1 2 = 24 := by
  have hQ := Qz_mul_inv 2
  set I := invOfUnit (Qz 2) 1 with hI
  have e : ∀ n, coeff n (Qz 2 * I) = coeff n (1 : ℤ⟦X⟧) := fun n => by rw [hQ]
  have h0 := e 0
  have h1 := e 1
  have h2 := e 2
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, Qz, coeff_mk, coeff_one] at h0 h1 h2
  norm_num [Nat.choose] at h0 h1 h2
  rw [cz, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_one_add_X_pow]
  norm_num [Nat.choose]
  linarith

theorem a339946_two : a339946 2 = 24 := by
  rw [show a339946 2 = am 1 2 by rw [a339946, am, one_mul], am_eq_cz, cz_one_two]; norm_num

theorem a361717_first : [a361717 0, a361717 1, a361717 2, a361717 3, a361717 4, a361717 5] =
    [0, 1, 4, 27, 216, 1875] := by
  decide

theorem a357511_zero : a357511 0 = 0 := by simp [a357511, s357511]

theorem a357511_two : a357511 2 = 54 := by
  have e : s357511 2 = ((54 : ℤ) : ℚ) := by
    simp [s357511, Finset.sum_Icc_succ_top, Nat.choose]
    norm_num
  rw [a357511, e, Rat.num_intCast]

theorem s357511_three : s357511 3 = 2182 / 3 := by
  simp [s357511, Finset.sum_Icc_succ_top, Nat.choose]
  norm_num

theorem a357511_three : a357511 3 = 2182 := by
  have e : ((2182 : ℤ) : ℚ) / ((3 : ℤ) : ℚ) = 2182 / 3 := by norm_num
  rw [a357511, s357511_three, ← e]
  exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)

end OeisA339946
