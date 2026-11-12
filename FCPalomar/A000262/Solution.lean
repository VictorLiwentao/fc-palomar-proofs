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
# OEIS A000262 and A082579: `a(n + k) ≡ a(n) (mod k)` (Bala's Theorem 1)

Peter Bala conjectured (Nov 14 2017) that the sequences with e.g.f. `exp(x/(1-x))` (A000262)
and `exp(x/(1-x)²)` (A082579) satisfy `k ∣ a(n + k) - a(n)` for all `n` and `k ≥ 2`, and proved
it (Theorem 1 of his note, linked from both entries): the congruence holds whenever the e.g.f. is
`F(x) exp(x G(x))` with `F, G ∈ ℤ[[x]]` and `G(0) = 1`. We formalize Theorem 1 and deduce both
sequences (`G = 1/(1-x)` and `G = 1/(1-x)²`, `F = 1`).

The proof follows Bala.

* `egf_balaSeq`: the e.g.f. `exp(x G)` has the integer coefficients
  `balaSeq G n = ∑_{d ≤ n} n!/d! · [x^{n-d}] G^d`.
* `balaSeq_self`: `balaSeq G k ≡ 1 = balaSeq G 0 (mod k)`.
* `balaSeq_succ`: differentiating `exp(x G)` gives the recurrence
  `a(n+1) = ∑_i c_i · n(n-1)⋯(n-i+1) · a(n-i)` with `c = (x G)'`.
* `transform_add`: such sums satisfy `T(N + k) ≡ T(N) (mod k)` once `a(N-i+k) ≡ a(N-i)`;
  terms with `i > N` vanish modulo `k`. Strong induction gives the congruence for `exp(x G)`
  (`periodic_balaSeq`), and the same lemma handles the factor `F` (Bala's Lemma 1).

*References:*
- [A000262](https://oeis.org/A000262), [A082579](https://oeis.org/A082579).
- P. Bala, *Integer sequences that become periodic on reduction modulo k for all k*, Dec 03
  2017, Theorem 1 and Lemma 1. https://oeis.org/A047974/a047974_1.pdf
-/

@[expose] public section

namespace OeisA262

open PowerSeries

/-- The rational e.g.f. $\sum a(n) x^n / n!$ of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- $k \mid a(n + k) - a(n)$ for every $k \ge 2$ and every $n$. -/
def PeriodicModAll (a : ℕ → ℤ) : Prop :=
  ∀ n k : ℕ, 2 ≤ k → a (n + k) ≡ a n [ZMOD k]

end OeisA262

open PowerSeries Finset

namespace OeisA000262

/-! ### The statements -/

/-- The rational e.g.f. `∑ a(n) xⁿ / n!` of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- `exp(x / (1 - x))`. -/
noncomputable def egfA000262 : ℚ⟦X⟧ := (exp ℚ).subst (X * (1 - X)⁻¹)

/-- `exp(x / (1 - x)²)`. -/
noncomputable def egfA082579 : ℚ⟦X⟧ := (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)

/-- Bala's conjecture: `k ∣ a(n + k) - a(n)` for `k = 2, 3, 4, …` and all `n`. -/
def PeriodicModAll (a : ℕ → ℤ) : Prop :=
  ∀ n k : ℕ, 2 ≤ k → a (n + k) ≡ a n [ZMOD k]

/-- The e.g.f. has a unique integer coefficient sequence, and it satisfies the conjecture. -/
def Target (E : ℚ⟦X⟧) : Prop :=
  (∃! a : ℕ → ℤ, egf a = E) ∧ ∀ a : ℕ → ℤ, egf a = E → PeriodicModAll a

/-! ### E.g.f.s -/

/-- Integer power series as rational power series. -/
noncomputable abbrev toQ : ℤ⟦X⟧ →+* ℚ⟦X⟧ := map (Int.castRingHom ℚ)

lemma coeff_egf (a : ℕ → ℤ) (n : ℕ) : coeff n (egf a) = (a n : ℚ) / n.factorial :=
  coeff_mk _ _

lemma egf_injective : Function.Injective egf := by
  intro a b h
  funext n
  have h1 := congrArg (coeff n) h
  rw [coeff_egf, coeff_egf, div_left_inj' (by positivity)] at h1
  exact_mod_cast h1

/-- `T c s n = ∑_{i ≤ n} c i · n(n-1)⋯(n-i+1) · s (n - i)`. -/
def transform (c s : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ range (n + 1), c i * (n.descFactorial i : ℤ) * s (n - i)

/-- Multiplying an e.g.f. by an integer power series. -/
lemma egf_transform (F : ℤ⟦X⟧) (s : ℕ → ℤ) :
    egf (transform (fun i => coeff i F) s) = toQ F * egf s := by
  ext n
  rw [coeff_egf, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, transform]
  push_cast
  rw [Finset.sum_div]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hf := Nat.factorial_mul_descFactorial hi'
  have hd : n.descFactorial i ≠ 0 := by
    intro h
    rw [h, mul_zero] at hf
    exact Nat.factorial_ne_zero n hf.symm
  have h1 : (n.factorial : ℚ) = (n - i).factorial * n.descFactorial i := by
    exact_mod_cast hf.symm
  have hd' : (n.descFactorial i : ℚ) ≠ 0 := by exact_mod_cast hd
  simp only [coeff_map, coeff_egf, eq_intCast]
  rw [h1]
  field_simp

lemma derivative_egf (s : ℕ → ℤ) : d⁄dX (egf s) = egf fun n => s (n + 1) := by
  ext n
  rw [coeff_derivative, coeff_egf, coeff_egf, Nat.factorial_succ]
  push_cast
  field_simp

lemma derivative_toQ (G : ℤ⟦X⟧) : d⁄dX (toQ G) = toQ (d⁄dX G) := by
  ext n
  simp [coeff_derivative, coeff_map]

/-! ### The coefficients of `exp(x G)` -/

/-- `n! [xⁿ] exp(x G) = ∑_{d ≤ n} n!/d! · [x^{n-d}] G^d`. -/
noncomputable def balaSeq (G : ℤ⟦X⟧) (n : ℕ) : ℤ :=
  ∑ d ∈ range (n + 1), ((n.factorial / d.factorial : ℕ) : ℤ) * coeff (n - d) (G ^ d)

lemma hasSubst_X_mul (H : ℚ⟦X⟧) : HasSubst (X * H) :=
  HasSubst.of_constantCoeff_zero' (by simp)

lemma egf_balaSeq (G : ℤ⟦X⟧) : egf (balaSeq G) = (exp ℚ).subst (X * toQ G) := by
  ext n
  rw [coeff_subst' (hasSubst_X_mul _),
    finsum_eq_finsetSum_of_support_subset (s := range (n + 1))]
  · rw [coeff_egf, balaSeq, Int.cast_sum, Finset.sum_div]
    refine sum_congr rfl fun d hd => ?_
    have hd' : d ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hd)
    rw [coeff_exp, mul_pow, coeff_X_pow_mul', ite_eq_left hd', ← map_pow, coeff_map, Int.cast_mul,
      Int.cast_natCast, Nat.cast_div (Nat.factorial_dvd_factorial hd') (by positivity)]
    simp only [eq_intCast, Algebra.algebraMap_self_apply, smul_eq_mul]
    have : (n.factorial : ℚ) ≠ 0 := by positivity
    have : (d.factorial : ℚ) ≠ 0 := by positivity
    field_simp
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hd
    rw [mul_pow, coeff_X_pow_mul', ite_eq_right (by omega), smul_zero]

lemma balaSeq_zero (G : ℤ⟦X⟧) : balaSeq G 0 = 1 := by
  simp [balaSeq]

lemma balaSeq_self (G : ℤ⟦X⟧) (hG : constantCoeff G = 1) (k : ℕ) :
    (balaSeq G k : ZMod k) = 1 := by
  rw [balaSeq, Finset.sum_range_succ, Nat.div_self (Nat.factorial_pos k), Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply, map_pow, hG, one_pow]
  simp only [Nat.cast_one, mul_one, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    Int.cast_one]
  rw [Finset.sum_eq_zero, zero_add]
  intro d hd
  have hdk : d < k := mem_range.mp hd
  have hdvd : k ∣ k.factorial / d.factorial := by
    have h1 : k.factorial = k * (k - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
    have h2 : d.factorial ∣ (k - 1).factorial := Nat.factorial_dvd_factorial (by omega)
    rw [h1, Nat.mul_div_assoc _ h2]
    exact dvd_mul_right k _
  rw [(CharP.cast_eq_zero_iff (ZMod k) k _).mpr hdvd, zero_mul]

/-- The recurrence from `(exp(x G))' = exp(x G) · (x G)'`. -/
lemma balaSeq_succ (G : ℤ⟦X⟧) (n : ℕ) :
    balaSeq G (n + 1) = transform (fun i => coeff i (d⁄dX (X * G))) (balaSeq G) n := by
  have h : egf (fun n => balaSeq G (n + 1)) =
      egf (transform (fun i => coeff i (d⁄dX (X * G))) (balaSeq G)) := by
    have h2 : toQ (X * G) = X * toQ G := by rw [map_mul, map_X]
    rw [← derivative_egf, egf_balaSeq, derivative_subst (hasSubst_X_mul _), derivative_exp,
      egf_transform, ← derivative_toQ, h2, ← egf_balaSeq, mul_comm]
  exact congrFun (egf_injective h) n

/-! ### The congruence -/

lemma descFactorial_dvd_descFactorial_add (n a r : ℕ) :
    n.descFactorial a ∣ n.descFactorial (a + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← add_assoc, Nat.descFactorial_succ]
    exact Dvd.dvd.mul_left ih _

lemma dvd_descFactorial_add (N k i : ℕ) (h : N < i) : k ∣ (N + k).descFactorial i := by
  have h1 : k ∣ (N + k).descFactorial (N + 1) := by
    rw [Nat.descFactorial_succ, Nat.add_sub_cancel_left]
    exact dvd_mul_right k _
  obtain ⟨r, rfl⟩ : ∃ r, i = N + 1 + r := ⟨i - (N + 1), by omega⟩
  exact h1.trans (descFactorial_dvd_descFactorial_add _ _ _)

lemma descFactorial_cast_add (N k i : ℕ) :
    ((N + k).descFactorial i : ZMod k) = (N.descFactorial i : ZMod k) := by
  rw [← descPochhammer_eval_eq_descFactorial, ← descPochhammer_eval_eq_descFactorial]
  push_cast
  rw [ZMod.natCast_self, add_zero]

/-- The key step: `T(N + k) ≡ T(N) (mod k)` when `s(N - i + k) ≡ s(N - i)` for `i ≤ N`. -/
lemma transform_add (c s : ℕ → ℤ) (N k : ℕ)
    (hs : ∀ i ≤ N, (s (N - i + k) : ZMod k) = s (N - i)) :
    (transform c s (N + k) : ZMod k) = transform c s N := by
  simp only [transform]
  rw [show N + k + 1 = N + 1 + k by ring, sum_range_add]
  push_cast
  rw [sum_eq_zero (s := range k), add_zero]
  · refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [show N + k - i = N - i + k by omega, hs i hi', descFactorial_cast_add]
  · intro j _
    rw [(CharP.cast_eq_zero_iff (ZMod k) k _).mpr
      (dvd_descFactorial_add N k (N + 1 + j) (by omega)), mul_zero, zero_mul]

/-- Bala's induction for a recurrence `s (n + 1) = T c s n`. -/
lemma periodic_of_rec (c s : ℕ → ℤ) (h0 : ∀ k : ℕ, (s k : ZMod k) = s 0)
    (hrec : ∀ n, s (n + 1) = transform c s n) : ∀ n k : ℕ, (s (n + k) : ZMod k) = s n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    rcases n with _ | N
    · rw [zero_add]
      exact h0 k
    · rw [show N + 1 + k = (N + k) + 1 by ring, hrec, hrec]
      exact transform_add c s N k fun i hi => ih (N - i) (by omega) k

/-- Bala's Lemma 1: multiplying by an integer power series keeps the congruence. -/
lemma periodic_transform (c s : ℕ → ℤ) (hs : ∀ n k : ℕ, (s (n + k) : ZMod k) = s n) :
    ∀ n k : ℕ, (transform c s (n + k) : ZMod k) = transform c s n :=
  fun n k => transform_add c s n k fun i _ => hs (n - i) k

theorem periodic_balaSeq (G : ℤ⟦X⟧) (hG : constantCoeff G = 1) :
    ∀ n k : ℕ, (balaSeq G (n + k) : ZMod k) = balaSeq G n :=
  periodic_of_rec _ _ (fun k => by rw [balaSeq_self G hG, balaSeq_zero, Int.cast_one])
    (balaSeq_succ G)

/-- **Bala's Theorem 1.** If `∑ a(n) xⁿ / n! = F(x) exp(x G(x))` with `F, G ∈ ℤ[[x]]` and
`G(0) = 1`, then `a(n + k) ≡ a(n) (mod k)` for all `n` and `k`. -/
theorem bala_theorem1 (F G : ℤ⟦X⟧) (hG : constantCoeff G = 1) (a : ℕ → ℤ)
    (ha : egf a = toQ F * (exp ℚ).subst (X * toQ G)) (n k : ℕ) :
    a (n + k) ≡ a n [ZMOD k] := by
  have h : a = transform (fun i => coeff i F) (balaSeq G) := by
    apply egf_injective
    rw [ha, egf_transform, egf_balaSeq]
  rw [← ZMod.intCast_eq_intCast_iff, h]
  exact periodic_transform _ _ (periodic_balaSeq G hG) n k

/-! ### A000262 and A082579 -/

lemma target_of_eq (E : ℚ⟦X⟧) (G : ℤ⟦X⟧) (hG : constantCoeff G = 1)
    (hE : E = (exp ℚ).subst (X * toQ G)) : Target E := by
  refine ⟨⟨balaSeq G, (by rw [egf_balaSeq, hE] : egf (balaSeq G) = E), fun b hb => ?_⟩,
    fun a ha n k _ => ?_⟩
  · exact egf_injective (hb.trans (by rw [egf_balaSeq, hE]))
  · exact bala_theorem1 1 G hG a (by rw [ha, hE, map_one, one_mul]) n k

lemma toQ_mk_one : toQ (PowerSeries.mk 1) = PowerSeries.mk 1 := by
  ext n
  simp [coeff_map]

lemma constantCoeff_mk_one : constantCoeff (PowerSeries.mk 1 : ℤ⟦X⟧) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  rfl

lemma inv_one_sub : ((1 : ℚ⟦X⟧) - X)⁻¹ = toQ (PowerSeries.mk 1) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp), toQ_mk_one]
  exact mk_one_mul_one_sub_eq_one ℚ

lemma inv_one_sub_sq : (((1 : ℚ⟦X⟧) - X) ^ 2)⁻¹ = toQ (PowerSeries.mk 1 ^ 2) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp), map_pow, toQ_mk_one, ← mul_pow,
    mk_one_mul_one_sub_eq_one ℚ, one_pow]

/-- **A000262**: the e.g.f. `exp(x/(1-x))` has a unique integer coefficient sequence, and
`a(n + k) ≡ a(n) (mod k)` for all `n` and `k ≥ 2`. -/
theorem a000262_target : Target egfA000262 :=
  target_of_eq _ (PowerSeries.mk 1) constantCoeff_mk_one (by rw [egfA000262, inv_one_sub])

/-- **A082579**: the same for the e.g.f. `exp(x/(1-x)²)`. -/
theorem a082579_target : Target egfA082579 :=
  target_of_eq _ (PowerSeries.mk 1 ^ 2) (by rw [map_pow, constantCoeff_mk_one, one_pow])
    (by rw [egfA082579, inv_one_sub_sq])

end OeisA000262

/-! Frozen statements for OEIS A000262 and A082579 (offset 0) and for Bala's Theorem 1.
These definitions freeze the claims; they assert no theorem.

Sources (retrieved 2026-11-03):
- A000262 %C "We conjecture that for k = 2,3,4,..., the difference a(n+k) - a(n) is divisible by
  k ... - Peter Bala, Nov 14 2017" and "The above conjecture is true - see the Bala link. - Peter
  Bala, Jan 20 2018"; %F "E.g.f.: exp(x/(1-x))".
- A082579 %N "Expansion of e.g.f.: exp( x/(1-x)^2 )." and the same two comments.
- P. Bala, "Integer sequences that become periodic on reduction modulo k for all k", Dec 03
  2017 (https://oeis.org/A047974/a047974_1.pdf), Theorem 1. -/

open PowerSeries

namespace A000262Frozen

/-- The rational e.g.f. `∑ a(n) xⁿ / n!` of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- `exp(x / (1 - x))`. -/
noncomputable def egfA000262 : ℚ⟦X⟧ := (exp ℚ).subst (X * (1 - X)⁻¹)

/-- `exp(x / (1 - x)²)`. -/
noncomputable def egfA082579 : ℚ⟦X⟧ := (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)

/-- Bala's conjecture: `k ∣ a(n + k) - a(n)` for `k = 2, 3, 4, …` and all `n`. -/
def PeriodicModAll (a : ℕ → ℤ) : Prop :=
  ∀ n k : ℕ, 2 ≤ k → a (n + k) ≡ a n [ZMOD k]

/-- The e.g.f. has a unique integer coefficient sequence, and it satisfies the conjecture. -/
def Target (E : ℚ⟦X⟧) : Prop :=
  (∃! a : ℕ → ℤ, egf a = E) ∧ ∀ a : ℕ → ℤ, egf a = E → PeriodicModAll a

/-- The A000262 claim. -/
def statementA000262 : Prop := Target egfA000262

/-- The A082579 claim. -/
def statementA082579 : Prop := Target egfA082579

/-- Bala's Theorem 1: if `∑ a(n) xⁿ / n! = F(x) exp(x G(x))` with `F, G ∈ ℤ[[x]]` and `G(0) = 1`,
then `a(n + k) ≡ a(n) (mod k)` for all `n` and `k`. -/
def balaTheorem1 : Prop :=
  ∀ F G : ℤ⟦X⟧, constantCoeff G = 1 → ∀ a : ℕ → ℤ,
    egf a = map (Int.castRingHom ℚ) F * (exp ℚ).subst (X * map (Int.castRingHom ℚ) G) →
      ∀ n k : ℕ, a (n + k) ≡ a n [ZMOD k]

end A000262Frozen

/-! The canonical theorems prove the separately frozen statements. Allowed axioms: `propext`,
`Classical.choice`, `Quot.sound`. -/

theorem frozen_A000262 : A000262Frozen.statementA000262 := OeisA000262.a000262_target

theorem frozen_A082579 : A000262Frozen.statementA082579 := OeisA000262.a082579_target

theorem frozen_balaTheorem1 : A000262Frozen.balaTheorem1 := OeisA000262.bala_theorem1

namespace OeisA262

open PowerSeries

theorem bala_theorem1 :
    ∀ F G : ℤ⟦X⟧, constantCoeff G = 1 → ∀ a : ℕ → ℤ,
      egf a = map (Int.castRingHom ℚ) F * (exp ℚ).subst (X * map (Int.castRingHom ℚ) G) →
        ∀ n k : ℕ, a (n + k) ≡ a n [ZMOD k] :=
  _root_.frozen_balaTheorem1

theorem a000262 :
    (∃! a : ℕ → ℤ, egf a = (exp ℚ).subst (X * (1 - X)⁻¹)) ∧
      ∀ a : ℕ → ℤ, egf a = (exp ℚ).subst (X * (1 - X)⁻¹) → PeriodicModAll a :=
  _root_.frozen_A000262

theorem a082579 :
    (∃! a : ℕ → ℤ, egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)) ∧
      ∀ a : ℕ → ℤ, egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹) → PeriodicModAll a :=
  _root_.frozen_A082579

end OeisA262

end
