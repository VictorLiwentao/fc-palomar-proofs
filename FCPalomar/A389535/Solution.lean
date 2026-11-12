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
# The power series $A$ with $A(x A(x)^4 + x A(x)^5) = A(x)^5$

Let $A(x) = \sum_{n \ge 1} a(n) x^n$ with $a(1) = 1$ satisfy
$A(x A(x)^4 + x A(x)^5) = A(x)^5$. Let $P(x) = \prod_{k \ge 0} (1 + x^{5^k})$, the series whose
coefficient of $x^n$ is $1$ when every base-$5$ digit of $n$ is $0$ or $1$, and $0$ otherwise.

The file proves that $A$ exists, is unique, and is the series reversion of $x / P(x)$. Hence
$A$ has integer coefficients, and $A(x)^5 \equiv A(x^5) \pmod 5$ coefficientwise.

Existence uses $P(x) = (1 + x) P(x^5)$. Uniqueness: if $T$ is the reversion of a solution, the
equation gives $T(x^5) = x^4 (1 + x) T(x)$, which forces $T = x / P(x)$. The congruence holds
for every integer power series, since $f^5 = f(x^5)$ over $\mathbb{F}_5$.

*References:*
- Paul D. Hanna, [A389535](https://oeis.org/A389535), October 27, 2025.
-/

@[expose] public section

namespace OeisA389535

open PowerSeries

/-- The defining equation, normalized by $A(0) = 0$ and $a(1) = 1$. The normalization excludes
the solution $A = 0$. -/
def IsSolution (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ subst (X * A ^ 4 + X * A ^ 5) A = A ^ 5

end OeisA389535

namespace OeisA389535

open PowerSeries

/-- $1$ if every base-$5$ digit of $n$ is $0$ or $1$, and $0$ otherwise. -/
def digitInd (n : ℕ) : ℕ :=
  if h : n = 0 then 1 else if n % 5 ≤ 1 then digitInd (n / 5) else 0
decreasing_by omega

lemma digitInd_zero : digitInd 0 = 1 := by
  rw [digitInd, dite_eq_left rfl]

lemma digitInd_succ (m : ℕ) :
    digitInd (m + 1) = if (m + 1) % 5 ≤ 1 then digitInd ((m + 1) / 5) else 0 := by
  rw [digitInd, dite_eq_right (Nat.succ_ne_zero m)]

lemma hfive : (5 : ℕ) ≠ 0 := by norm_num

section Ring

variable (R : Type*) [CommRing R]

/-- The product $P(x) = \prod_{k \ge 0} (1 + x^{5^k})$, given by its coefficients. -/
noncomputable def P : R⟦X⟧ := PowerSeries.mk fun n => (digitInd n : R)

/-- The inverse of $P$. -/
noncomputable def Pinv : R⟦X⟧ := invOfUnit (P R) 1

/-- The series $S(x) = x / P(x)$. -/
noncomputable def S : R⟦X⟧ := X * Pinv R

variable {R}

lemma constantCoeff_P : constantCoeff (P R) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, P, coeff_mk, digitInd_zero, Nat.cast_one]

/-- The product identity $P(x) = (1 + x) P(x^5)$. -/
lemma P_eq : P R = (1 + X) * expand 5 hfive (P R) := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => simp [coeff_expand]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_expand, coeff_expand]
    simp only [P, coeff_mk]
    rw [digitInd_succ]
    rcases (show (m + 1) % 5 = 0 ∨ (m + 1) % 5 = 1 ∨ 2 ≤ (m + 1) % 5 by omega) with h | h | h
    · have hd : 5 ∣ m + 1 := by omega
      have hnd : ¬ 5 ∣ m := by omega
      simp [h, hd, hnd]
    · have hd : ¬ 5 ∣ m + 1 := by omega
      have hnd : 5 ∣ m := by omega
      have he : (m + 1) / 5 = m / 5 := by omega
      simp [h, hd, hnd, he]
    · have hd : ¬ 5 ∣ m + 1 := by omega
      have hnd : ¬ 5 ∣ m := by omega
      have hn : ¬ (m + 1) % 5 ≤ 1 := by omega
      simp [hn, hd, hnd]

lemma P_mul_Pinv : P R * Pinv R = 1 :=
  mul_invOfUnit _ _ (by rw [constantCoeff_P, Units.val_one])

lemma Pinv_mul_P : Pinv R * P R = 1 := by rw [mul_comm, P_mul_Pinv]

lemma constantCoeff_Pinv : constantCoeff (Pinv R) = 1 := by
  rw [Pinv, constantCoeff_invOfUnit, inv_one, Units.val_one]

lemma constantCoeff_S : constantCoeff (S R) = 0 := by simp [S]

lemma coeff_one_S : coeff 1 (S R) = 1 := by
  rw [S, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_Pinv]

lemma isUnit_coeff_one_S : IsUnit (coeff 1 (S R)) := by
  rw [coeff_one_S]
  exact isUnit_one

variable (R) in
/-- The series reversion $A$ of $S$, so that $S(A(x)) = x$ and $A(S(x)) = x$. -/
noncomputable def rev : R⟦X⟧ := (S R).substInvOfIsUnit isUnit_coeff_one_S

lemma hasSubst_of_zero {f : R⟦X⟧} (h : constantCoeff f = 0) : HasSubst f :=
  HasSubst.of_constantCoeff_zero' h

lemma subst_one' {a : R⟦X⟧} (ha : HasSubst a) : (1 : R⟦X⟧).subst a = 1 := by
  rw [← coe_substAlgHom ha]
  exact map_one _

lemma coeff_one_substInv_of_eq_one {f : R⟦X⟧} (hu : IsUnit (coeff 1 f)) (h1 : coeff 1 f = 1) :
    coeff 1 (f.substInvOfIsUnit hu) = 1 := by
  rw [coeff_one_substInvOfIsUnit]
  have h : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, h1, Units.val_one])
  rw [h, inv_one, Units.val_one]

lemma constantCoeff_rev : constantCoeff (rev R) = 0 := constantCoeff_substInvOfIsUnit _ _

lemma coeff_one_rev : coeff 1 (rev R) = 1 :=
  coeff_one_substInv_of_eq_one _ coeff_one_S

lemma Pinv_subst_mul {a : R⟦X⟧} (ha : HasSubst a) :
    (Pinv R).subst a * (P R).subst a = 1 := by
  rw [← subst_mul ha, Pinv_mul_P, subst_one' ha]

/-- The reversion satisfies $A = x P(A)$. -/
lemma rev_eq : rev R = X * (P R).subst (rev R) := by
  have ha : HasSubst (rev R) := hasSubst_of_zero constantCoeff_rev
  have h : (S R).subst (rev R) = X :=
    subst_substInvOfIsUnit_right _ constantCoeff_S isUnit_coeff_one_S
  rw [S, subst_mul ha, subst_X ha] at h
  calc rev R = rev R * ((Pinv R).subst (rev R) * (P R).subst (rev R)) := by
        rw [Pinv_subst_mul ha, mul_one]
    _ = (rev R * (Pinv R).subst (rev R)) * (P R).subst (rev R) := by ring
    _ = X * (P R).subst (rev R) := by rw [h]

/-- $P(a) = (1 + a) P(a^5)$. -/
lemma P_subst {a : R⟦X⟧} (ha : HasSubst a) : (P R).subst a = (1 + a) * (P R).subst (a ^ 5) := by
  have hX5 : HasSubst ((X : R⟦X⟧) ^ 5) := hasSubst_of_zero (by simp)
  conv_lhs => rw [P_eq]
  rw [subst_mul ha, subst_add ha, subst_one' ha, subst_X ha, expand_apply,
    subst_comp_subst_apply hX5 ha, subst_pow ha, subst_X ha]

/-- The reversion solves the source equation, over every commutative ring. -/
theorem rev_source : (rev R).subst (X * rev R ^ 4 + X * rev R ^ 5) = rev R ^ 5 := by
  set a := rev R
  have ha0 : constantCoeff a = 0 := constantCoeff_rev
  have ha : HasSubst a := hasSubst_of_zero ha0
  have ha5 : HasSubst (a ^ 5) := hasSubst_of_zero (by rw [map_pow, ha0, zero_pow (by norm_num)])
  have hS : HasSubst (S R) := hasSubst_of_zero constantCoeff_S
  have hfix : a = X * (P R).subst a := rev_eq
  have hP := P_subst ha
  have hQ := Pinv_subst_mul ha5
  have h1 : a ^ 5 = (X * a ^ 4 + X * a ^ 5) * (P R).subst (a ^ 5) := by
    calc a ^ 5 = a ^ 4 * a := by ring
      _ = a ^ 4 * (X * ((1 + a) * (P R).subst (a ^ 5))) := by rw [← hP, ← hfix]
      _ = (X * a ^ 4 + X * a ^ 5) * (P R).subst (a ^ 5) := by ring
  have hG : X * a ^ 4 + X * a ^ 5 = (S R).subst (a ^ 5) := by
    rw [S, subst_mul ha5, subst_X ha5]
    calc X * a ^ 4 + X * a ^ 5
        = (X * a ^ 4 + X * a ^ 5) * ((Pinv R).subst (a ^ 5) * (P R).subst (a ^ 5)) := by
          rw [hQ, mul_one]
      _ = ((X * a ^ 4 + X * a ^ 5) * (P R).subst (a ^ 5)) * (Pinv R).subst (a ^ 5) := by ring
      _ = a ^ 5 * (Pinv R).subst (a ^ 5) := by rw [← h1]
  have hAS : a.subst (S R) = X :=
    subst_substInvOfIsUnit_left _ constantCoeff_S isUnit_coeff_one_S
  rw [hG, ← subst_comp_subst_apply hS ha5, hAS, subst_X ha5]

end Ring

/-! ### The congruence modulo 5 -/

/-- Over $\mathbb{F}_5$, $f(x)^5 = f(x^5)$. -/
lemma pow_five_eq_expand (f : (ZMod 5)⟦X⟧) : f ^ 5 = expand 5 hfive f := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  ext n
  rw [coeff_expand]
  have h1 : coeff n (f ^ 5) = coeff n ((trunc (n + 1) f : (ZMod 5)⟦X⟧) ^ 5) := by
    have h := congrArg (fun q => Polynomial.coeff q n) (trunc_trunc_pow f (n + 1) 5)
    simp only [coeff_trunc, lt_add_one, ↓reduceIte] at h
    exact h.symm
  rw [h1, ← Polynomial.coe_pow, ← ZMod.expand_card, Polynomial.coeff_coe,
    Polynomial.coeff_expand (by norm_num : 0 < 5)]
  split_ifs with h
  · rw [coeff_trunc, ite_eq_left (by omega)]
  · rfl

/-- For every integer power series $B$, $B(x)^5 \equiv B(x^5) \pmod 5$ coefficientwise. -/
theorem five_dvd_coeff (B : ℤ⟦X⟧) (n : ℕ) :
    (5 : ℤ) ∣ coeff n (B ^ 5 - B.subst ((X : ℤ⟦X⟧) ^ 5)) := by
  have h : ((coeff n (B ^ 5 - B.subst ((X : ℤ⟦X⟧) ^ 5)) : ℤ) : ZMod 5) = 0 := by
    rw [← expand_apply 5 hfive, ← eq_intCast (Int.castRingHom (ZMod 5)), ← coeff_map, map_sub,
      map_pow, map_expand, pow_five_eq_expand, sub_self, map_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h

/-! ### The source equation over $\mathbb{Q}$ -/

/-- The source equation with $A(0) = 0$ and $a(1) = 1$. -/
def Equation (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ A.subst (X * A ^ 4 + X * A ^ 5) = A ^ 5

/-- If $W = W(x^5)$ and $W(0) = 1$, then $W = 1$. -/
lemma eq_one_of_eq_expand {W : ℚ⟦X⟧} (hW : W = expand 5 hfive W) (h0 : constantCoeff W = 1) :
    W = 1 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc : coeff n W = coeff n (expand 5 hfive W) := by rw [← hW]
    rw [hc, coeff_expand, coeff_one]
    by_cases hn : n = 0
    · subst hn
      simpa using h0
    · rw [ite_eq_right hn]
      split_ifs with hd
      · rw [ih (n / 5) (by omega), coeff_one, ite_eq_right (by omega)]
      · rfl

/-- The series reversion of every solution is $x / P(x)$. -/
theorem substInv_eq {B : ℚ⟦X⟧} (hB : Equation B) (hu : IsUnit (coeff 1 B)) :
    B.substInvOfIsUnit hu = S ℚ := by
  obtain ⟨h0, h1, heq⟩ := hB
  set T := B.substInvOfIsUnit hu
  have hT : HasSubst T := HasSubst.substInvOfIsUnit _ _
  have hB' : HasSubst B := hasSubst_of_zero h0
  have hBT : B.subst T = X := subst_substInvOfIsUnit_right _ h0 _
  have hTB : T.subst B = X := subst_substInvOfIsUnit_left _ h0 _
  have hG : HasSubst (X * B ^ 4 + X * B ^ 5) := hasSubst_of_zero (by simp [h0])
  have hT0 : constantCoeff T = 0 := constantCoeff_substInvOfIsUnit _ _
  have hK : HasSubst (T * X ^ 4 + T * X ^ 5) := hasSubst_of_zero (by simp [hT0])
  -- Substituting `T` into the equation gives `B(T x^4 + T x^5) = x^5`.
  have e1 : B.subst (T * X ^ 4 + T * X ^ 5) = X ^ 5 := by
    have h := congrArg (fun f : ℚ⟦X⟧ => f.subst T) heq
    rw [subst_comp_subst_apply hG hT, subst_pow hT, hBT, subst_add hT, subst_mul hT,
      subst_mul hT, subst_pow hT, subst_pow hT, subst_X hT, hBT] at h
    exact h
  -- Applying `T` gives `T x^4 (1 + x) = T(x^5)`.
  have e2 : T * X ^ 4 + T * X ^ 5 = expand 5 hfive T := by
    have h := congrArg (fun f : ℚ⟦X⟧ => T.subst f) e1
    rw [← subst_comp_subst_apply hB' hK, hTB, subst_X hK, ← expand_apply 5 hfive] at h
    exact h
  obtain ⟨U, hU⟩ := X_dvd_iff.mpr hT0
  have hT1 : coeff 1 T = 1 := coeff_one_substInv_of_eq_one hu h1
  have hU0 : constantCoeff U = 1 := by
    have h := coeff_succ_X_mul 0 U
    rw [← hU, zero_add, hT1, coeff_zero_eq_constantCoeff_apply] at h
    exact h.symm
  have e3 : U * (1 + X) = expand 5 hfive U := by
    have h : (X : ℚ⟦X⟧) ^ 5 * (U * (1 + X)) = X ^ 5 * expand 5 hfive U := by
      calc (X : ℚ⟦X⟧) ^ 5 * (U * (1 + X)) = T * X ^ 4 + T * X ^ 5 := by rw [hU]; ring
        _ = expand 5 hfive T := e2
        _ = X ^ 5 * expand 5 hfive U := by rw [hU, map_mul, expand_X]
    exact mul_left_cancel₀ (pow_ne_zero 5 X_ne_zero) h
  have e4 : U * P ℚ = expand 5 hfive (U * P ℚ) := by
    calc U * P ℚ = U * ((1 + X) * expand 5 hfive (P ℚ)) := by rw [← P_eq]
      _ = U * (1 + X) * expand 5 hfive (P ℚ) := by ring
      _ = expand 5 hfive (U * P ℚ) := by rw [e3, map_mul]
  have e5 : U * P ℚ = 1 :=
    eq_one_of_eq_expand e4 (by rw [map_mul, hU0, constantCoeff_P, one_mul])
  have e6 : U = Pinv ℚ := by
    calc U = U * (P ℚ * Pinv ℚ) := by rw [P_mul_Pinv, mul_one]
      _ = U * P ℚ * Pinv ℚ := by ring
      _ = Pinv ℚ := by rw [e5, one_mul]
  rw [hU, e6, S]

/-- The source equation has at most one solution. -/
theorem equation_unique {B C : ℚ⟦X⟧} (hB : Equation B) (hC : Equation C) : B = C := by
  have huB : IsUnit (coeff 1 B) := by rw [hB.2.1]; exact isUnit_one
  have huC : IsUnit (coeff 1 C) := by rw [hC.2.1]; exact isUnit_one
  have hS : HasSubst (S ℚ) := hasSubst_of_zero constantCoeff_S
  have hC' : HasSubst C := hasSubst_of_zero hC.1
  have h1 := subst_substInvOfIsUnit_right B hB.1 huB
  rw [substInv_eq hB huB] at h1
  have h2 := subst_substInvOfIsUnit_left C hC.1 huC
  rw [substInv_eq hC huC] at h2
  calc B = subst (X : ℚ⟦X⟧) B := (X_subst B).symm
    _ = subst (subst C (S ℚ)) B := by rw [h2]
    _ = subst C (subst (S ℚ) B) := (subst_comp_subst_apply hS hC' B).symm
    _ = subst C (X : ℚ⟦X⟧) := by rw [h1]
    _ = C := subst_X hC'

/-- The image of the integer reversion solves the source equation over $\mathbb{Q}$. -/
theorem equation_map_rev : Equation (map (Int.castRingHom ℚ) (rev ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_rev, map_zero]
  · rw [coeff_map, coeff_one_rev, map_one]
  · have hG : HasSubst (X * rev ℤ ^ 4 + X * rev ℤ ^ 5) :=
      hasSubst_of_zero (by simp [constantCoeff_rev])
    have hm : map (Int.castRingHom ℚ) ((rev ℤ).subst (X * rev ℤ ^ 4 + X * rev ℤ ^ 5)) =
        (map (Int.castRingHom ℚ) (rev ℤ)).subst
          (map (Int.castRingHom ℚ) (X * rev ℤ ^ 4 + X * rev ℤ ^ 5)) :=
      map_subst hG (rev ℤ)
    have h := congrArg (map (Int.castRingHom ℚ)) (rev_source (R := ℤ))
    rw [hm, map_pow] at h
    simpa only [map_add, map_mul, map_pow, map_X] using h

/-- OEIS A389535, formula (7): the unique solution $A$ of $A(x A^4 + x A^5) = A^5$ with
$A(0) = 0$ and $a(1) = 1$ has integer coefficients, and $A(x)^5 \equiv A(x^5) \pmod 5$. -/
theorem a389535_conjecture7 :
    (∃! A : ℚ⟦X⟧, Equation A) ∧
      ∀ A : ℚ⟦X⟧, Equation A → ∃ B : ℤ⟦X⟧, map (Int.castRingHom ℚ) B = A ∧
        ∀ n, (5 : ℤ) ∣ coeff n (B ^ 5 - B.subst ((X : ℤ⟦X⟧) ^ 5)) :=
  ⟨⟨_, equation_map_rev, fun _ hB => equation_unique hB equation_map_rev⟩,
    fun _ hA => ⟨rev ℤ, equation_unique equation_map_rev hA, five_dvd_coeff (rev ℤ)⟩⟩

end OeisA389535

namespace OeisA389535

open PowerSeries

theorem exists_unique_solution : ∃! A : ℚ⟦X⟧, IsSolution A :=
  a389535_conjecture7.1

theorem conjecture_seven (A : ℚ⟦X⟧) (hA : IsSolution A) :
    ∃ a : ℕ → ℤ, (∀ n, coeff n A = a n) ∧
      ∀ n, (5 : ℤ) ∣ coeff n (PowerSeries.mk a ^ 5) - (if 5 ∣ n then a (n / 5) else 0) := by
  obtain ⟨B, hB, hdiv⟩ := a389535_conjecture7.2 A hA
  refine ⟨fun n => coeff n B, fun n => ?_, fun n => ?_⟩
  · rw [← hB, coeff_map]
    rfl
  · have hmk : PowerSeries.mk (fun n => coeff n B) = B := by
      ext k
      rw [coeff_mk]
    have h := hdiv n
    rw [map_sub, ← expand_apply 5 hfive, coeff_expand] at h
    rw [hmk]
    exact h

end OeisA389535

end
