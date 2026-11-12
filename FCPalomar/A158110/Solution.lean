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
# Integrality of $\exp\left(\sum_{n \ge 1} q^{n^m} x^n / n\right)$

OEIS A158110 has g.f. $\exp\left(\sum_{n \ge 1} 2^{n^3} x^n / n\right)$. Its entry states the
conjecture (Paul D. Hanna, 2009) that for all nonnegative integers $q$ and $m$ the power series
$\exp\left(\sum_{n \ge 1} q^{n^m} x^n / n\right)$ has integer coefficients. Sela Fried proved it
(2025).

This file proves the conjecture. The proof follows Fried:

1. If $n \mid \sum_{d \mid n} \mu(d) b(n/d)$ for all $n \ge 1$, then
   $\exp\left(\sum_{n \ge 1} b(n) x^n / n\right)$ has integer coefficients. We write
   $b(n) = \sum_{d \mid n} d c(d)$ with integers $c(d)$. Up to degree $N$ the series equals the
   finite product $\prod_{d=1}^{N} (1 - x^d)^{-c(d)}$, because both sides have constant term
   $1$ and the same logarithmic derivative below degree $N$.
2. For $b(n) = q^{n^m}$, write $n = p^k N$ with $p \nmid N$. Pairing the divisors $d$ and $pd$
   reduces the divisibility by $p^k$ to $q^{(p^k M)^m} \equiv q^{(p^{k-1} M)^m} \pmod{p^k}$,
   which follows from Fermat's little theorem and `dvd_sub_pow_of_dvd_sub`.

*References:*
- [A158110](https://oeis.org/A158110)
- Sela Fried, [Proof of a conjecture stated in A158110](https://oeis.org/A158110/a158110.pdf),
  2025.
- Sela Fried, Further proofs of conjectures from the OEIS,
  [arXiv:2607.24832](https://arxiv.org/abs/2607.24832), 2026, pp. 2, 42–43.
- R. P. Stanley, *Enumerative Combinatorics*, Vol. 2, Cambridge Univ. Press, 1999,
  Exercise 5.2(a).
-/

@[expose] public section

namespace OeisA158110

open PowerSeries Finset
open scoped ArithmeticFunction.Moebius Pointwise

/-- The series $\sum_{n \ge 1} q^{n^m} x^n / n$ over $\mathbb{Q}$. -/
noncomputable def logSeries (q m : ℕ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (q : ℚ) ^ (n ^ m) / n

/-- Every coefficient of $\exp\left(\sum_{n \ge 1} q^{n^m} x^n / n\right)$ is an integer. -/
def Target : Prop :=
  ∀ q m n : ℕ, ∃ z : ℤ, coeff n (subst (logSeries q m) (exp ℚ)) = z

/-! ## Logarithmic derivatives -/

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

/-! ## The integrality criterion -/

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

/-! ## The congruences for $b(n) = q^{n^m}$ -/

/-- $q^{(p^k M)^m} \equiv q^{(p^{k-1} M)^m} \pmod{p^k}$ for a prime $p$ and $k \ge 1$. -/
theorem prime_pow_dvd_pow_sub_pow (q : ℤ) {p : ℕ} (hp : p.Prime) (m : ℕ) {k : ℕ} (hk : 0 < k)
    (M : ℕ) : (p : ℤ) ^ k ∣ q ^ ((p ^ k * M) ^ m) - q ^ ((p ^ (k - 1) * M) ^ m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := Fact.mk hp
  set Q := q ^ (M ^ m) with hQ
  have hferm : (p : ℤ) ∣ Q ^ (p ^ m) - Q := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_pow, sub_self]
  have h := dvd_sub_pow_of_dvd_sub hferm (k * m)
  have e1 : q ^ ((p ^ (k + 1) * M) ^ m) = (Q ^ p ^ m) ^ p ^ (k * m) := by
    rw [hQ, ← pow_mul, ← pow_mul, mul_pow, ← pow_mul, add_mul, one_mul, pow_add]
    ring_nf
  have e2 : q ^ ((p ^ (k + 1 - 1) * M) ^ m) = Q ^ p ^ (k * m) := by
    rw [hQ, ← pow_mul, Nat.add_sub_cancel, mul_pow, ← pow_mul]
    ring_nf
  rw [e1, e2]
  exact (pow_dvd_pow _ (by nlinarith)).trans h

theorem sum_divisors_prime_pow_mul {p k N : ℕ} (hp : p.Prime) (hN : ¬p ∣ N) (F : ℕ → ℤ) :
    ∑ d ∈ (p ^ k * N).divisors, F d =
      ∑ i ∈ range (k + 1), ∑ e ∈ N.divisors, F (p ^ i * e) := by
  have hcop : (p ^ k).Coprime N :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hN)
  rw [Nat.divisors_mul, Finset.mul_def, sum_image hcop.mul_injOn_divisors, sum_product]
  simp only [Nat.sum_divisors_prime_pow hp]

/-- Fried's pairing: the Möbius sum at $p^k N$ is divisible by $p^k$ when $p \nmid N$. -/
theorem prime_pow_dvd_sum_moebius (q : ℤ) (m : ℕ) {p : ℕ} (hp : p.Prime) {k N : ℕ}
    (hk : 0 < k) (hN : ¬p ∣ N) :
    (p : ℤ) ^ k ∣ ∑ x ∈ (p ^ k * N).divisorsAntidiagonal, μ x.1 * q ^ (x.2 ^ m) := by
  rw [Nat.sum_divisorsAntidiagonal (fun a c => μ a * q ^ (c ^ m)),
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
  · have hp0 : p ≠ 0 := hp.ne_zero
    have q0 : p ^ (j + 1) * (e * M) / (p ^ 0 * e) = p ^ (j + 1) * M := by
      rw [pow_zero, one_mul, show p ^ (j + 1) * (e * M) = e * (p ^ (j + 1) * M) by ring,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)]
    have q1 : p ^ (j + 1) * (e * M) / (p ^ (0 + 1) * e) = p ^ j * M := by
      rw [zero_add, pow_one,
        show p ^ (j + 1) * (e * M) = (p * e) * (p ^ j * M) by ring,
        Nat.mul_div_cancel_left _ (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero he0))]
    rw [q0, q1, hmu, hmu, pow_zero, ArithmeticFunction.moebius_apply_one, zero_add, pow_one,
      ArithmeticFunction.moebius_apply_prime hp]
    obtain ⟨t, ht⟩ := prime_pow_dvd_pow_sub_pow q hp m (k := j + 1) (by omega) M
    rw [Nat.add_sub_cancel] at ht
    exact ⟨μ e * t, by linear_combination (μ e) * ht⟩
  · rw [hmu, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
    simp

/-- Dold's congruence $n \mid \sum_{d \mid n} \mu(d) q^{(n/d)^m}$. -/
theorem dvd_sum_moebius (q : ℤ) (m : ℕ) {n : ℕ} (hn : 0 < n) :
    (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * q ^ (x.2 ^ m) := by
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hv : k ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn.ne').mp hpk
  have hdecomp := Nat.ordProj_mul_ordCompl_eq_self n p
  have hdiv := prime_pow_dvd_sum_moebius q m hp (k := n.factorization p) (by omega)
    (Nat.not_dvd_ordCompl hp hn.ne')
  rw [hdecomp] at hdiv
  rw [← Int.natCast_dvd]
  push_cast
  exact (pow_dvd_pow _ hv).trans hdiv

/-! ## The main theorem -/

/-- **OEIS A158110 conjecture** (Hanna 2009; proved by Fried 2025). For all natural numbers
$q$ and $m$, every coefficient of $\exp\left(\sum_{n \ge 1} q^{n^m} x^n / n\right)$ is an
integer. -/
theorem a158110_integral : Target := by
  intro q m n
  have h := exists_coeff_eq_intCast_of_dvd (fun n => (q : ℤ) ^ (n ^ m))
    (fun n hn => dvd_sum_moebius q m hn) n
  have hL : (mk fun n => if n = 0 then 0 else (((q : ℤ) ^ (n ^ m) : ℤ) : ℚ) / n) =
      logSeries q m := by
    ext n
    simp [logSeries]
  rwa [hL] at h

/-- The same result as a single power series over `ℤ`. -/
theorem exists_map_eq_exp_subst_logSeries (q m : ℕ) :
    ∃ G : ℤ⟦X⟧, map (Int.castRingHom ℚ) G = subst (logSeries q m) (exp ℚ) := by
  choose a ha using a158110_integral q m
  refine ⟨mk a, ?_⟩
  ext n
  simp [ha]

/-! ## Boundary cases and the recurrence -/

theorem constantCoeff_logSeries (q m : ℕ) : constantCoeff (logSeries q m) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, logSeries, coeff_mk, ite_eq_left rfl]

theorem coeff_derivative_logSeries (q m j : ℕ) :
    coeff j (d⁄dX (logSeries q m)) = (q : ℚ) ^ ((j + 1) ^ m) := by
  rw [coeff_derivative, logSeries, coeff_mk, ite_eq_right (Nat.succ_ne_zero j)]
  field_simp
  push_cast
  ring

/-- The coefficients $a(n)$ satisfy $(n+1) a(n+1) = \sum_{i+j=n} q^{(i+1)^m} a(j)$. -/
theorem coeff_succ_mul (q m n : ℕ) :
    coeff (n + 1) (subst (logSeries q m) (exp ℚ)) * (n + 1) =
      ∑ x ∈ antidiagonal n,
        (q : ℚ) ^ ((x.1 + 1) ^ m) * coeff x.2 (subst (logSeries q m) (exp ℚ)) := by
  have h := congrArg (coeff n) (derivative_exp_subst (constantCoeff_logSeries q m))
  rw [coeff_derivative, coeff_mul] at h
  simpa only [coeff_derivative_logSeries] using h

theorem constantCoeff_exp_subst_logSeries (q m : ℕ) :
    constantCoeff (subst (logSeries q m) (exp ℚ)) = 1 :=
  constantCoeff_exp_subst (constantCoeff_logSeries q m)

/-- For $q = 0$ the series is $0$, since $n^m \ge 1$ for $n \ge 1$. -/
theorem logSeries_zero_left (m : ℕ) : logSeries 0 m = 0 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [logSeries]
  · simp [logSeries, hn, zero_pow (pow_ne_zero m hn)]

/-- For $q = 0$ the exponential is $1$. -/
theorem exp_subst_logSeries_zero_left (m : ℕ) : subst (logSeries 0 m) (exp ℚ) = 1 := by
  refine derivative.ext ?_ (by rw [constantCoeff_exp_subst_logSeries, map_one])
  rw [derivative_exp_subst (constantCoeff_logSeries 0 m), logSeries_zero_left, map_zero,
    zero_mul, derivative_one]

/-- For $m = 0$ the exponential is $(1 - x)^{-q}$, as in Fried's Lemma 1. -/
theorem exp_subst_logSeries_zero_right (q : ℕ) :
    subst (logSeries q 0) (exp ℚ) * (1 - X) ^ q = 1 := by
  have hL : d⁄dX (logSeries q 0) = (q : ℚ⟦X⟧) * geomLogDeriv 1 := by
    ext j
    rw [coeff_derivative_logSeries, ← map_natCast (C (R := ℚ)), coeff_C_mul,
      coeff_geomLogDeriv Nat.one_pos]
    simp
  have hD := derivative_mul_of (derivative_exp_subst (constantCoeff_logSeries q 0))
    (derivative_pow_of (derivative_one_sub_X_pow Nat.one_pos) q)
  rw [hL, pow_one] at hD
  refine derivative.ext ?_ ?_
  · rw [hD, derivative_one]
    ring
  · simp [constantCoeff_exp_subst_logSeries]

end OeisA158110

namespace OeisA158110

open PowerSeries

theorem conjecture (q m n : ℕ) : ∃ z : ℤ, coeff n (subst (logSeries q m) (exp ℚ)) = z :=
  a158110_integral q m n

end OeisA158110

end
