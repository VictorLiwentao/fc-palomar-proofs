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
import all Init.Data.Nat.Power2.Basic

/-!
# OEIS A395839: parity and residues modulo 3

The sequence has g.f. $10C(x)^2 - C(x)$, where $C(x) = 1 + xC(x)^2$ is the g.f. of the Catalan
numbers (A000108). We work in $\mathbb{Z}[[x]]$ and quantify over every solution of the source
equation $C = 1 + xC^2$; it has exactly one solution, the Catalan series.

We prove the two conjectures of the entry, for all $n \ge 0$:

* (parity) $a(n)$ is odd iff $n = 2^k - 1$ for some $k \ge 0$;
* (mod 3) $a(3n+1) \equiv C_n$, $a(3n) \equiv 0$ and $a(3n+2) \equiv 0 \pmod 3$.

The bridge is $a(n) = 10C_{n+1} - C_n$. Parity reduces to the parity of $C_n$, and
$v_2(C_n) = s_2(n+1) - 1$ (Legendre's formula). Modulo 3,
$10C^2 - C = 9C^2 + xC^3 \equiv xC^3 = xC(x^3)$ by the Frobenius map.

*References:*
- Paul D. Hanna, [A395839](https://oeis.org/A395839), May 17 2026.
- E. Deutsch and B. E. Sagan, *Congruences for Catalan and Motzkin numbers and related
  sequences*, Theorem 2.1. [arXiv:math/0407326](https://arxiv.org/abs/math/0407326)
-/

@[expose] public section

namespace OeisA395839

open PowerSeries

/-- The equation for the Catalan g.f.: $C = 1 + x C^2$. -/
def IsCatalanEquation (G : ℤ⟦X⟧) : Prop := G = 1 + X * G ^ 2

/-- The coefficients of $10 C^2 - C$. -/
noncomputable def coeffs (G : ℤ⟦X⟧) (n : ℕ) : ℤ := coeff n (10 * G ^ 2 - G)

end OeisA395839

open PowerSeries

namespace OeisA395839Proof

/-! ### The source objects -/

/-- The source equation for the Catalan g.f.: $C = 1 + xC^2$. -/
def IsCatalanEquation (G : ℤ⟦X⟧) : Prop := G = 1 + X * G ^ 2

/-- The coefficients of $10C^2 - C$. -/
noncomputable def coeffs (G : ℤ⟦X⟧) (n : ℕ) : ℤ := coeff n (10 * G ^ 2 - G)

/-- Clause (i): $a(n)$ is odd iff $n = 2^k - 1$ for some $k \ge 0$. -/
def ParityClause (a : ℕ → ℤ) : Prop := ∀ n, Odd (a n) ↔ ∃ k, n = 2 ^ k - 1

/-- Clause (ii): $a(3n+1) \equiv C_n$ and $a(3n) \equiv a(3n+2) \equiv 0 \pmod 3$. -/
def ModThreeClause (a : ℕ → ℤ) : Prop :=
  ∀ n, a (3 * n + 1) ≡ (catalan n : ℤ) [ZMOD 3] ∧ a (3 * n) ≡ 0 [ZMOD 3] ∧
    a (3 * n + 2) ≡ 0 [ZMOD 3]

/-! ### The bridge to the Catalan numbers -/

/-- The Catalan series over $\mathbb{Z}$. -/
noncomputable def catalanZ : ℤ⟦X⟧ := PowerSeries.mk fun n => (catalan n : ℤ)

lemma isCatalanEquation_catalanZ : IsCatalanEquation catalanZ := by
  have h := congrArg (map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  have hc : map (Nat.castRingHom ℤ) catalanSeries = catalanZ := by
    ext n
    simp [catalanZ]
  simp only [map_add, map_mul, map_pow, map_X, map_one, hc] at h
  rw [IsCatalanEquation]
  linear_combination h.symm

lemma coeff_eq_catalan {G : ℤ⟦X⟧} (hG : IsCatalanEquation G) (n : ℕ) :
    coeff n G = catalan n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [hG]
      simp
    · rw [hG, map_add, coeff_one, ite_eq_right n.succ_ne_zero, zero_add, coeff_succ_X_mul, sq,
        coeff_mul, catalan_succ']
      push_cast
      refine Finset.sum_congr rfl fun p hp => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [ih p.1 (by omega), ih p.2 (by omega)]

lemma eq_catalanZ {G : ℤ⟦X⟧} (hG : IsCatalanEquation G) : G = catalanZ := by
  ext n
  rw [coeff_eq_catalan hG]
  simp [catalanZ]

/-- The source equation has exactly one solution in $\mathbb{Z}[[x]]$, the Catalan series. -/
theorem existsUnique_isCatalanEquation : ∃! G : ℤ⟦X⟧, IsCatalanEquation G :=
  ⟨catalanZ, isCatalanEquation_catalanZ, fun _ hG => eq_catalanZ hG⟩

lemma coeff_sq_eq {G : ℤ⟦X⟧} (hG : IsCatalanEquation G) (n : ℕ) :
    coeff n (G ^ 2) = ((catalan (n + 1) : ℕ) : ℤ) := by
  have h := congrArg (coeff (n + 1)) hG
  rw [map_add, coeff_one, ite_eq_right n.succ_ne_zero, zero_add, coeff_succ_X_mul] at h
  rw [← h, coeff_eq_catalan hG]

/-- The closed form $a(n) = 10C_{n+1} - C_n$. -/
theorem coeffs_eq {G : ℤ⟦X⟧} (hG : IsCatalanEquation G) (n : ℕ) :
    coeffs G n = 10 * catalan (n + 1) - catalan n := by
  rw [coeffs, map_sub, show (10 : ℤ⟦X⟧) = PowerSeries.C (10 : ℤ) by simp, coeff_C_mul,
    coeff_sq_eq hG, coeff_eq_catalan hG]

/-! ### Clause (i): parity -/

/-- The binary digit sum. -/
def digitSum (k : ℕ) : ℕ := (Nat.digits 2 k).sum

lemma digitSum_two_mul (k : ℕ) : digitSum (2 * k) = digitSum k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · rw [digitSum, Nat.digits_def' (by norm_num) (by omega)]
    simp [digitSum, Nat.mul_mod_right, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]

lemma digitSum_two_mul_add_one (k : ℕ) : digitSum (2 * k + 1) = digitSum k + 1 := by
  rw [digitSum, Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2, List.sum_cons, digitSum, add_comm]

lemma isPowerOfTwo_two_mul_iff {q : ℕ} (hq : 0 < q) :
    (2 * q).isPowerOfTwo ↔ q.isPowerOfTwo := by
  constructor
  · rintro ⟨j, hj⟩
    rcases j with _ | j
    · omega
    · exact ⟨j, by rw [pow_succ] at hj; omega⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j + 1, by ring⟩

lemma isPowerOfTwo_two_mul_add_one_iff (q : ℕ) :
    (2 * q + 1).isPowerOfTwo ↔ q = 0 := by
  constructor
  · rintro ⟨j, hj⟩
    rcases j with _ | j
    · simpa using hj
    · rw [pow_succ] at hj; omega
  · rintro rfl
    exact Nat.isPowerOfTwo_one

lemma digitSum_pos_and_eq_one_iff (k : ℕ) (hk : 0 < k) :
    0 < digitSum k ∧ (digitSum k = 1 ↔ k.isPowerOfTwo) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' k
    · have hq : 0 < q := by omega
      obtain ⟨h1, h2⟩ := ih q (by omega) hq
      rw [digitSum_two_mul, isPowerOfTwo_two_mul_iff hq]
      exact ⟨h1, h2⟩
    · rw [digitSum_two_mul_add_one, isPowerOfTwo_two_mul_add_one_iff]
      refine ⟨by omega, ?_⟩
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp [digitSum]
      · have := (ih q (by omega) hq).1
        omega

lemma padicValNat_factorial_two (n : ℕ) : padicValNat 2 n.factorial = n - digitSum n := by
  have := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [digitSum] using this

lemma padicValNat_centralBinom (k : ℕ) :
    padicValNat 2 (Nat.centralBinom k) = digitSum k := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hfac : (2 * k).choose k * k.factorial * k.factorial = (2 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rwa [show 2 * k - k = k by omega] at this
  have hC : (2 * k).choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hF : k.factorial ≠ 0 := Nat.factorial_ne_zero k
  have hv := congrArg (padicValNat 2) hfac
  rw [padicValNat.mul (mul_ne_zero hC hF) hF, padicValNat.mul hC hF,
    padicValNat_factorial_two, padicValNat_factorial_two, digitSum_two_mul] at hv
  have hle : digitSum k ≤ k := Nat.digit_sum_le 2 k
  omega

/-- Adding one to $m$: $s_2(m+1) + v_2(m+1) = s_2(m) + 1$. -/
lemma digitSum_succ (m : ℕ) :
    digitSum (m + 1) + padicValNat 2 (m + 1) = digitSum m + 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [digitSum_two_mul_add_one, digitSum_two_mul,
        padicValNat.eq_zero_of_not_dvd (by omega)]
    · have hq := ih q (by omega)
      rw [show 2 * q + 1 + 1 = 2 * (q + 1) by ring, digitSum_two_mul, digitSum_two_mul_add_one,
        padicValNat.mul (by norm_num) (by omega), padicValNat_self]
      omega

/-- $C_n$ is odd iff $n + 1$ is a power of two (Deutsch–Sagan, Theorem 2.1). -/
theorem catalan_odd_iff (n : ℕ) : Odd (catalan n) ↔ (n + 1).isPowerOfTwo := by
  have hc : catalan n ≠ 0 := by
    intro h
    have := succ_mul_catalan_eq_centralBinom n
    rw [h, mul_zero] at this
    exact Nat.centralBinom_ne_zero n this.symm
  have hv : padicValNat 2 (n + 1) + padicValNat 2 (catalan n) = digitSum n := by
    rw [← padicValNat.mul (by omega) hc, succ_mul_catalan_eq_centralBinom,
      padicValNat_centralBinom]
  have hs := digitSum_succ n
  obtain ⟨h1, h2⟩ := digitSum_pos_and_eq_one_iff (n + 1) (by omega)
  have hodd : Odd (catalan n) ↔ padicValNat 2 (catalan n) = 0 := by
    rw [padicValNat.eq_zero_iff, Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    simp [hc]
  rw [hodd, ← h2]
  omega

theorem parityClause {G : ℤ⟦X⟧} (hG : IsCatalanEquation G) : ParityClause (coeffs G) := by
  intro n
  rw [coeffs_eq hG, Int.odd_iff]
  have h : (10 * (catalan (n + 1) : ℤ) - catalan n) % 2 = 1 ↔ (catalan n : ℤ) % 2 = 1 := by
    omega
  rw [h, ← Int.odd_iff, Int.odd_coe_nat, catalan_odd_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by have := Nat.one_le_two_pow (n := k); omega⟩

/-! ### Clause (ii): residues modulo 3 -/

lemma gf_eq {G : ℤ⟦X⟧} (hG : IsCatalanEquation G) :
    10 * G ^ 2 - G = 9 * G ^ 2 + X * G ^ 3 := by
  have h : G = 1 + X * G ^ 2 := hG
  linear_combination G * h

/-- Frobenius in $\mathbb{F}_3[[x]]$: $F^3 = F(x^3)$. -/
lemma pow_three_eq_expand (F : (ZMod 3)⟦X⟧) : F ^ 3 = expand 3 (by norm_num) F := by
  have h := MvPowerSeries.map_frobenius_expand (R := ZMod 3) (σ := Unit) 3 (by norm_num)
    (f := F)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

lemma coeffs_mod_three_zero {G : ℤ⟦X⟧} (hG : IsCatalanEquation G) :
    ((coeffs G 0 : ℤ) : ZMod 3) = 0 := by
  rw [coeffs_eq hG]
  simp [catalan_one, catalan_zero]
  decide

lemma coeffs_mod_three_succ {G : ℤ⟦X⟧} (hG : IsCatalanEquation G) (j : ℕ) :
    ((coeffs G (j + 1) : ℤ) : ZMod 3) =
      if 3 ∣ j then (catalan (j / 3) : ZMod 3) else 0 := by
  set F : (ZMod 3)⟦X⟧ := map (Int.castRingHom (ZMod 3)) G
  have h1 : ((coeffs G (j + 1) : ℤ) : ZMod 3) = coeff (j + 1) (X * F ^ 3) := by
    have h9 : ((9 : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd 9 3).mpr (by norm_num)
    rw [coeffs, gf_eq hG, map_add, show (9 : ℤ⟦X⟧) = PowerSeries.C (9 : ℤ) by simp, coeff_C_mul,
      Int.cast_add, Int.cast_mul, h9, zero_mul, zero_add,
      show X * F ^ 3 = map (Int.castRingHom (ZMod 3)) (X * G ^ 3) by simp [F], coeff_map]
    simp
  rw [h1, coeff_succ_X_mul, pow_three_eq_expand, coeff_expand]
  split_ifs
  · simp [F, coeff_map, coeff_eq_catalan hG]
  · rfl

theorem modThreeClause {G : ℤ⟦X⟧} (hG : IsCatalanEquation G) : ModThreeClause (coeffs G) := by
  intro n
  refine ⟨?_, ?_, ?_⟩ <;> apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
  · rw [coeffs_mod_three_succ hG, ite_eq_left (dvd_mul_right 3 n),
      Nat.mul_div_cancel_left n (by norm_num)]
    simp
  · rcases n with _ | k
    · rw [coeffs_mod_three_zero hG]
      simp
    · rw [show 3 * (k + 1) = (3 * k + 2) + 1 by ring, coeffs_mod_three_succ hG,
        ite_eq_right (by omega)]
      simp
  · rw [show 3 * n + 2 = (3 * n + 1) + 1 by ring, coeffs_mod_three_succ hG, ite_eq_right (by omega)]
    simp

/-! ### The frozen targets -/

/-- Clause (i) of A395839, with the source equation solved uniquely. -/
theorem parity_target :
    (∃! G : ℤ⟦X⟧, IsCatalanEquation G) ∧
      ∀ G : ℤ⟦X⟧, IsCatalanEquation G → ParityClause (coeffs G) :=
  ⟨existsUnique_isCatalanEquation, fun _ hG => parityClause hG⟩

/-- Clause (ii) of A395839, with the source equation solved uniquely. -/
theorem modThree_target :
    (∃! G : ℤ⟦X⟧, IsCatalanEquation G) ∧
      ∀ G : ℤ⟦X⟧, IsCatalanEquation G → ModThreeClause (coeffs G) :=
  ⟨existsUnique_isCatalanEquation, fun _ hG => modThreeClause hG⟩

end OeisA395839Proof

/-! Frozen statement for OEIS A395839 (offset 0). These definitions freeze the two claims; they
assert no theorem.

Source (retrieved 2026-11-03): %N "G.f. 10*C(x)^2 - C(x), where C(x) = 1 + x*C(x)^2 is the g.f.
of the Catalan numbers (A000108)." %C "Conjecture: a(n) is odd iff n is of the form 2^k - 1
(k >= 0)." %C "Conjecture: a(3*n+1) == A000108(n) (mod 3) for n >= 0 ..., with a(3*n) ==
a(3*n+2) == 0 (mod 3) for n >= 0." - Paul D. Hanna. -/

open PowerSeries

namespace A395839Frozen

/-- The source equation for the Catalan g.f.: `C = 1 + x C²`. -/
def IsCatalanEquation (G : ℤ⟦X⟧) : Prop := G = 1 + X * G ^ 2

/-- The coefficients of `10 C² - C`. -/
noncomputable def coeffs (G : ℤ⟦X⟧) (n : ℕ) : ℤ := coeff n (10 * G ^ 2 - G)

/-- Clause (i): `a(n)` is odd iff `n = 2^k - 1` for some `k ≥ 0`. -/
def ParityClause (a : ℕ → ℤ) : Prop := ∀ n, Odd (a n) ↔ ∃ k, n = 2 ^ k - 1

/-- Clause (ii): `a(3n+1) ≡ Cₙ` and `a(3n) ≡ a(3n+2) ≡ 0 (mod 3)`. -/
def ModThreeClause (a : ℕ → ℤ) : Prop :=
  ∀ n, a (3 * n + 1) ≡ (catalan n : ℤ) [ZMOD 3] ∧ a (3 * n) ≡ 0 [ZMOD 3] ∧
    a (3 * n + 2) ≡ 0 [ZMOD 3]

/-- Clause (i), with the source equation solved uniquely. -/
def statementParity : Prop :=
  (∃! G : ℤ⟦X⟧, IsCatalanEquation G) ∧
    ∀ G : ℤ⟦X⟧, IsCatalanEquation G → ParityClause (coeffs G)

/-- Clause (ii), with the source equation solved uniquely. -/
def statementModThree : Prop :=
  (∃! G : ℤ⟦X⟧, IsCatalanEquation G) ∧
    ∀ G : ℤ⟦X⟧, IsCatalanEquation G → ModThreeClause (coeffs G)

end A395839Frozen

/-! The canonical theorems prove the separately frozen statements. Allowed axioms: `propext`,
`Classical.choice`, `Quot.sound`. -/

theorem frozen_parity : A395839Frozen.statementParity := OeisA395839Proof.parity_target

theorem frozen_modThree : A395839Frozen.statementModThree := OeisA395839Proof.modThree_target

namespace OeisA395839

open PowerSeries

theorem odd_iff :
    (∃! G : ℤ⟦X⟧, IsCatalanEquation G) ∧
      ∀ G : ℤ⟦X⟧, IsCatalanEquation G → ∀ n, Odd (coeffs G n) ↔ ∃ k, n = 2 ^ k - 1 :=
  _root_.frozen_parity

theorem mod_three :
    (∃! G : ℤ⟦X⟧, IsCatalanEquation G) ∧
      ∀ G : ℤ⟦X⟧, IsCatalanEquation G → ∀ n, coeffs G (3 * n + 1) ≡ (catalan n : ℤ) [ZMOD 3] ∧
        coeffs G (3 * n) ≡ 0 [ZMOD 3] ∧ coeffs G (3 * n + 2) ≡ 0 [ZMOD 3] :=
  _root_.frozen_modThree

end OeisA395839

end
