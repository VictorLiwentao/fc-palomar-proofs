/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Copyright 2026 Linmiao Xu.

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
# Erdős Problem 494: the case where $|A|$ has a prime factor $p > k$

For a finite set $A \subset \mathbb{C}$, let $A_k$ be the multiset of the sums of the $k$-element
subsets of $A$. Selfridge and Straus proved that $A$ is determined by $A_k$ and $|A|$ when $|A|$
is divisible by a prime $p > k$.

The definitions `sumMultiset` and `Erdos494Unique` are copied verbatim from
`FormalConjectures/ErdosProblems/494.lean`. The three lemmas `e494_newton`, `e494_esymm_eq`
and `e494_eq_of_esymm` are adapted from Linmiao Xu's Apache-2.0 package
`linrock/math-proofs/erdos-494`.

Proof. Let $E_A(t) = \sum_{a \in A} e^{a t}$ and $G_m(A)(t) = e_m(e^{a t} : a \in A)$, so that
$G_k(A)(t) = \sum_{s \in A_k} e^{s t}$ is determined by $A_k$. If $A \ne B$, the power sums of
$A$ and $B$ differ, so $E_A - E_B$ has a lowest nonzero coefficient, at $t^j$ say. Newton's
identities for the family $e^{a t}$ show that every $G_m(A) - G_m(B)$ is divisible by $t^j$,
and that the coefficients $\kappa_m$ of $t^j$ satisfy a linear recursion. Let $c$ be the
coefficient of $t^j$ in $E_A - E_B$. Then $k!\,\kappa_k / c$ is an integer, and for $p \mid |A|$
and $0 < k < p$ Lucas' theorem shows that it is not divisible by $p$. So $\kappa_k \ne 0$, and
$A_k \ne B_k$.

*References:*
- [erdosproblems.com/494](https://www.erdosproblems.com/494)
- [SeSt58] Selfridge, J. L. and Straus, E., On the determination of numbers by their sums
  of a fixed order. Pacific Journal of Math. (1958), 847-856.
-/

@[expose] public section

namespace Erdos494

/--
For a finite set $A \subset \mathbb{C}$ and $k \ge 1$, define $A_k$ as the multiset consisting of
all sums of $k$ distinct elements of $A$.
-/
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

open Finset PowerSeries

/-! ### Newton's identities and recovery from power sums (adapted from linrock) -/

/-- Newton's identities evaluated at the elements of a finset. -/
lemma e494_newton (A : Finset ℂ) (k : ℕ) :
    (k : ℂ) * A.val.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * A.val.esymm a.1 * ∑ x ∈ A, x ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval (fun x : A => (x : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum A ℂ k)
  have hval : (Finset.univ : Finset A).val.map (fun x : A => (x : ℂ)) = A.val := by
    rw [Finset.univ_eq_attach, Finset.attach_val]; exact Multiset.attach_map_val _
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, hval] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
  exact Finset.sum_coe_sort A (fun x => x ^ a.2)

/-- Equal power sums give equal elementary symmetric functions. -/
lemma e494_esymm_eq (A B : Finset ℂ) (hp : ∀ m, ∑ x ∈ A, x ^ m = ∑ x ∈ B, x ^ m) :
    ∀ k, A.val.esymm k = B.val.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm]
    · have hA := e494_newton A k
      have hB := e494_newton B k
      have hrhs : ∑ a ∈ antidiagonal k with a.1 < k,
            (-1 : ℂ) ^ a.1 * A.val.esymm a.1 * ∑ x ∈ A, x ^ a.2
          = ∑ a ∈ antidiagonal k with a.1 < k,
            (-1 : ℂ) ^ a.1 * B.val.esymm a.1 * ∑ x ∈ B, x ^ a.2 := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_filter] at ha
        rw [ih a.1 ha.2, hp a.2]
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk0
      rw [hA, hB, hrhs]

/-- The same cardinality and elementary symmetric functions imply equal finsets. -/
lemma e494_eq_of_esymm (A B : Finset ℂ) (hc : A.card = B.card)
    (he : ∀ k, A.val.esymm k = B.val.esymm k) : A = B := by
  have hpoly : (A.val.map fun t => Polynomial.X - Polynomial.C t).prod =
      (B.val.map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    have : Multiset.card A.val = Multiset.card B.val := hc
    rw [this]
    simp only [he]
  have := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this
  exact Finset.val_inj.mp this

/-- Newton's identities for the images of the elements of a finset in a commutative ring. -/
lemma newton_map {R : Type*} [CommRing R] (f : ℂ → R) (A : Finset ℂ) (k : ℕ) :
    (k : R) * (A.val.map f).esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * (A.val.map f).esymm a.1 *
        ∑ x ∈ A, f x ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval (fun x : A => f x))
    (MvPolynomial.mul_esymm_eq_sum A R k)
  have hval : (Finset.univ : Finset A).val.map (fun x : A => f x) = A.val.map f := by
    rw [Finset.univ_eq_attach, Finset.attach_val]
    exact Multiset.attach_map_val' _ _
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, hval] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
  exact Finset.sum_coe_sort A (fun x => f x ^ a.2)

/-! ### Exponential generating series -/

/-- The series $e^{a t}$. -/
noncomputable def ex (a : ℂ) : ℂ⟦X⟧ := rescale a (exp ℂ)

lemma ex_add (a b : ℂ) : ex a * ex b = ex (a + b) := exp_mul_exp_eq_exp_add a b

lemma ex_zero : ex 0 = 1 := by
  rw [ex, rescale_zero_apply, constantCoeff_exp, map_one]

lemma prod_ex (s : Finset ℂ) : s.prod ex = ex (s.sum id) := by
  induction s using Finset.induction_on with
  | empty => rw [prod_empty, sum_empty, ex_zero]
  | @insert a s ha ih => simp only [prod_insert ha, sum_insert ha, ih, ex_add, id]

lemma ex_pow (a : ℂ) (i : ℕ) : ex a ^ i = rescale (i : ℂ) (ex a) := by
  calc ex a ^ i = rescale a (exp ℂ ^ i) := (map_pow (rescale a) _ _).symm
    _ = rescale a (rescale (i : ℂ) (exp ℂ)) := by rw [exp_pow_eq_rescale_exp]
    _ = rescale (i : ℂ) (ex a) := by rw [ex, rescale_rescale, rescale_rescale, mul_comm]

lemma constantCoeff_rescale' (f : ℂ⟦X⟧) (a : ℂ) : constantCoeff (rescale a f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply]

lemma constantCoeff_ex (a : ℂ) : constantCoeff (ex a) = 1 := by
  rw [ex, constantCoeff_rescale', constantCoeff_exp]

/-- The exponential generating series $E_A(t) = \sum_{a \in A} e^{a t}$ of the power sums. -/
noncomputable def E (A : Finset ℂ) : ℂ⟦X⟧ := ∑ a ∈ A, ex a

lemma coeff_E (A : Finset ℂ) (r : ℕ) :
    coeff r (E A) = (∑ a ∈ A, a ^ r) * algebraMap ℚ ℂ (1 / r.factorial) := by
  simp only [E, map_sum, ex, coeff_rescale, coeff_exp, Finset.sum_mul]

lemma constantCoeff_E (A : Finset ℂ) : constantCoeff (E A) = A.card := by
  simp [E, constantCoeff_ex]

lemma psum_ex (A : Finset ℂ) (i : ℕ) : ∑ x ∈ A, ex x ^ i = rescale (i : ℂ) (E A) := by
  simp only [ex_pow, E, map_sum]

/-- Equal exponential power-sum series and cardinalities give equal finsets. -/
lemma eq_of_E (A B : Finset ℂ) (hc : A.card = B.card) (h : E A = E B) : A = B := by
  apply e494_eq_of_esymm A B hc
  apply e494_esymm_eq A B
  intro m
  have hm := congrArg (fun f => coeff m f) h
  simp only [coeff_E] at hm
  refine mul_right_cancel₀ ?_ hm
  simp [Nat.factorial_ne_zero]

/-- $G_m(A) = e_m(e^{a t} : a \in A)$. -/
noncomputable def G (m : ℕ) (A : Finset ℂ) : ℂ⟦X⟧ := (A.val.map ex).esymm m

lemma G_eq (A : Finset ℂ) (k : ℕ) : G k A = ((sumMultiset A k).map ex).sum := by
  rw [G, Finset.esymm_map_val, sumMultiset, Multiset.map_map]
  simp only [prod_ex]
  rfl

lemma G_zero (A : Finset ℂ) : G 0 A = 1 := by
  rw [G, Finset.esymm_map_val, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty]

lemma constantCoeff_G (B : Finset ℂ) (m : ℕ) : constantCoeff (G m B) = (B.card.choose m : ℂ) := by
  rw [G, Finset.esymm_map_val, map_sum]
  simp [map_prod, constantCoeff_ex, Finset.card_powersetCard]

/-- Newton's identities for $G_m(A)$. -/
lemma newtonG (A : Finset ℂ) (m : ℕ) :
    (m : ℂ⟦X⟧) * G m A = (-1) ^ (m + 1) *
      ∑ a ∈ antidiagonal m with a.1 < m, (-1) ^ a.1 * G a.1 A * rescale (a.2 : ℂ) (E A) := by
  have h := newton_map ex A m
  simp only [psum_ex] at h
  exact h

/-- If $t^j \mid f$, then $[t^j](f g) = [t^j] f \cdot g(0)$. -/
lemma coeff_mul_of_dvd {j : ℕ} (f g : ℂ⟦X⟧) (hf : (X : ℂ⟦X⟧) ^ j ∣ f) :
    coeff j (f * g) = coeff j f * constantCoeff g := by
  obtain ⟨f', rfl⟩ := hf
  rw [mul_assoc, coeff_X_pow_mul', coeff_X_pow_mul', ite_eq_left le_rfl, ite_eq_left le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul]

/-! ### The arithmetic of the leading coefficients -/

/-- The integer that equals $(m+1)!\,\kappa_{m+1} / c$. -/
def Z (n j m : ℕ) (z : ℕ → ℤ) : ℤ :=
  (-1) ^ (m + 1 + 1) * ∑ a ∈ antidiagonal (m + 1) with a.1 < m + 1,
    (-1) ^ a.1 * ((m.descFactorial (m - a.1) : ℤ) * z a.1 * n +
      (m.factorial : ℤ) * (n.choose a.1 : ℤ) * (a.2 : ℤ) ^ j)

lemma step (n j m : ℕ) (c : ℂ) (κ : ℕ → ℂ) (z : ℕ → ℤ)
    (hrec : ((m + 1 : ℕ) : ℂ) * κ (m + 1) = (-1) ^ (m + 1 + 1) *
      ∑ a ∈ antidiagonal (m + 1) with a.1 < m + 1,
        (-1) ^ a.1 * (κ a.1 * n + (n.choose a.1 : ℂ) * ((a.2 : ℂ) ^ j * c)))
    (hz : ∀ r < m + 1, (r.factorial : ℂ) * κ r = c * z r) :
    ((m + 1).factorial : ℂ) * κ (m + 1) = c * (Z n j m z : ℂ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_comm ((m + 1 : ℕ) : ℂ), mul_assoc, hrec, Z]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_filter] at ha
  have hf : (m.factorial : ℂ) = (a.1.factorial : ℂ) * (m.descFactorial (m - a.1) : ℂ) := by
    have h := Nat.factorial_mul_descFactorial (show m - a.1 ≤ m by omega)
    rw [show m - (m - a.1) = a.1 by omega] at h
    exact_mod_cast h.symm
  rw [hf]
  linear_combination ((-1 : ℂ) ^ (m + 1 + 1) * (-1 : ℂ) ^ a.1 * (m.descFactorial (m - a.1) : ℂ) *
    n) * hz a.1 ha.2

/-- If $p \mid n$, $0 < k < p$ and the coefficients satisfy the Newton recursion, then
$\kappa_k \ne 0$. -/
lemma kappa_ne_zero (p k n j : ℕ) (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) (hpn : p ∣ n)
    (c : ℂ) (hc : c ≠ 0) (κ : ℕ → ℂ) (h0 : κ 0 = 0)
    (hrec : ∀ m : ℕ, 0 < m → (m : ℂ) * κ m = (-1) ^ (m + 1) *
      ∑ a ∈ antidiagonal m with a.1 < m,
        (-1) ^ a.1 * (κ a.1 * n + (n.choose a.1 : ℂ) * ((a.2 : ℂ) ^ j * c))) :
    κ k ≠ 0 := by
  have hint : ∀ m, ∃ z : ℤ, (m.factorial : ℂ) * κ m = c * z := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases m with _ | m
      · exact ⟨0, by simp [h0]⟩
      · choose! z hz using ih
        exact ⟨Z n j m z, step n j m c κ z (hrec (m + 1) (by omega)) hz⟩
  choose z hz using hint
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hkey := step n j m c κ z (hrec (m + 1) (by omega)) (fun r _ => hz r)
  intro hκ
  rw [hκ, mul_zero] at hkey
  have hZ : (Z n j m z : ℂ) = 0 := by
    rcases mul_eq_zero.mp hkey.symm with h | h
    · exact absurd h hc
    · exact h
  have hZ' : Z n j m z = 0 := by exact_mod_cast hZ
  have := Fact.mk hp
  have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
  have hchoose : ∀ r, 0 < r → r < p → ((n.choose r : ℕ) : ZMod p) = 0 := by
    intro r hr0 hrp
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := r) (p := p)
    rw [Nat.mod_eq_zero_of_dvd hpn, Nat.mod_eq_of_lt hrp, Nat.choose_eq_zero_of_lt hr0,
      zero_mul] at h
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have hmod : (Z n j m z : ZMod p) =
      (-1) ^ (m + 1 + 1) * ((m.factorial : ℕ) : ZMod p) * ((m + 1 : ℕ) : ZMod p) ^ j := by
    simp only [Z, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_sum,
      Int.cast_add, Int.cast_natCast]
    rw [Finset.sum_eq_single (0, m + 1)]
    · simp [hn0, mul_assoc]
    · intro a ha hne
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      have ha1 : a.1 ≠ 0 := by
        intro h1
        exact hne (Prod.ext h1 (by omega))
      rw [hn0, hchoose a.1 (Nat.pos_of_ne_zero ha1) (by omega)]
      ring
    · intro hnot
      exact absurd (by simp [Finset.HasAntidiagonal.mem_antidiagonal]) hnot
  have hne : (Z n j m z : ZMod p) ≠ 0 := by
    rw [hmod]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_)
      (pow_ne_zero _ ?_)
    · rw [ne_eq, ZMod.natCast_eq_zero_iff, hp.dvd_factorial]
      omega
    · rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
  exact hne (by rw [hZ']; simp)

/-! ### The main argument -/

/-- If $p \mid |B|$, $0 < k < p$, $|A| = |B|$ and $A_k = B_k$, then $A = B$. -/
theorem eq_of_sumMultiset {k p : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p)
    {A B : Finset ℂ} (hcard : A.card = B.card) (hpn : p ∣ B.card)
    (h : sumMultiset A k = sumMultiset B k) : A = B := by
  classical
  by_contra hAB
  have hE : E A - E B ≠ 0 := fun hE => hAB (eq_of_E A B hcard (sub_eq_zero.mp hE))
  have hex : ∃ r, coeff r (E A - E B) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hE (PowerSeries.ext fun r => by rw [hall r, map_zero])
  obtain ⟨j, hj, hlow⟩ : ∃ j, coeff j (E A - E B) ≠ 0 ∧ ∀ r < j, coeff r (E A - E B) = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => not_not.mp (Nat.find_min hex hr)⟩
  have hδj : ∀ i : ℕ, (X : ℂ⟦X⟧) ^ j ∣ rescale (i : ℂ) (E A - E B) := fun i =>
    X_pow_dvd_iff.mpr (fun r hr => by rw [coeff_rescale, hlow r hr, mul_zero])
  have hdiff : ∀ m : ℕ, (m : ℂ⟦X⟧) * (G m A - G m B) = (-1) ^ (m + 1) *
      ∑ a ∈ antidiagonal m with a.1 < m, (-1) ^ a.1 *
        ((G a.1 A - G a.1 B) * rescale (a.2 : ℂ) (E A) +
          G a.1 B * rescale (a.2 : ℂ) (E A - E B)) := by
    intro m
    rw [mul_sub, newtonG, newtonG, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_sub]
    ring
  have hdvd : ∀ m, (X : ℂ⟦X⟧) ^ j ∣ G m A - G m B := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [G_zero, G_zero, sub_self]
        exact dvd_zero _
      · have hu : IsUnit (m : ℂ⟦X⟧) := by
          rw [← map_natCast (C (R := ℂ))]
          exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hm.ne')).map C
        rw [← hu.dvd_mul_left, hdiff m]
        apply Dvd.dvd.mul_left
        apply Finset.dvd_sum
        intro a ha
        rw [Finset.mem_filter] at ha
        apply Dvd.dvd.mul_left
        exact dvd_add (Dvd.dvd.mul_right (ih a.1 ha.2) _) (Dvd.dvd.mul_left (hδj a.2) _)
  have hrec : ∀ m : ℕ, 0 < m → (m : ℂ) * coeff j (G m A - G m B) = (-1) ^ (m + 1) *
      ∑ a ∈ antidiagonal m with a.1 < m, (-1) ^ a.1 *
        (coeff j (G a.1 A - G a.1 B) * B.card +
          (B.card.choose a.1 : ℂ) * ((a.2 : ℂ) ^ j * coeff j (E A - E B))) := by
    intro m _
    have h := congrArg (fun f => coeff j f) (hdiff m)
    rw [← map_natCast (C (R := ℂ)), coeff_C_mul] at h
    rw [h, show ((-1 : ℂ⟦X⟧)) ^ (m + 1) = C ((-1 : ℂ) ^ (m + 1)) by simp, coeff_C_mul, map_sum]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show ((-1 : ℂ⟦X⟧)) ^ a.1 = C ((-1 : ℂ) ^ a.1) by simp, coeff_C_mul, map_add,
      coeff_mul_of_dvd _ _ (hdvd a.1), mul_comm (G a.1 B), coeff_mul_of_dvd _ _ (hδj a.2),
      coeff_rescale, constantCoeff_rescale', constantCoeff_E, constantCoeff_G, hcard]
    ring
  have hGk : G k A = G k B := by rw [G_eq, G_eq, h]
  exact kappa_ne_zero p k B.card j hp hk0 hkp hpn _ hj (fun m => coeff j (G m A - G m B))
    (by simp [G_zero]) hrec (by simp [hGk])

/--
Selfridge and Straus [SeSt58] proved that $A$ is determined by $A_k$
if $|A|$ is divisible by a prime greater than $k$.
-/
theorem erdos_494.variants.card_divisible_by_prime_gt_k :
    ∀ (k card p : ℕ), p.Prime → k ∈ Set.Ioo 0 p → p ∣ card → Erdos494Unique k card := by
  intro k card p hp hk hpc A B hA hB h
  exact eq_of_sumMultiset hp hk.1 hk.2 (hA.trans hB.symm) (hB ▸ hpc) h

end Erdos494

/-!
# Erdős Problem 494: the case $k = 4$, $|A| > 12$

This file reuses the leading-coefficient argument of `Erdos494.lean`. For $k = 4$ the
coefficient is $c\,\Gamma(n, t)$ with
$\Gamma = \binom{n}{3} - 2^t \binom{n}{2} + 3^t n - 4^t$, where $t + 1$ is the index of the first
differing power sum. The proof shows $6\Gamma \ne 0$ for $n \ge 13$: a root forces
$n \mid 6 \cdot 4^t$, so $n = 2^a$ or $3 \cdot 2^a$ with $a \ge 3$; a sign estimate excludes
$n \ge 3 \cdot 2^t + 4$; for smaller $n$, $2^t$ divides $n^2 - 3n + 2 + 6 \cdot 3^t$, which is
$4 \bmod 8$ for odd $t$ and $8 \bmod 16$ for even $t$ when $16 \mid n$; the last case $n = 24$
is checked directly.

*References:*
- [SeSt58] Selfridge, J. L. and Straus, E., On the determination of numbers by their sums
  of a fixed order. Pacific Journal of Math. (1958), 847-856.
-/

namespace Erdos494

open Finset PowerSeries

/-- The leading-coefficient argument for a general `k` and `n`: if every solution of the
coefficient recursion with $\kappa_0 = 0$, $c \ne 0$ and $j \ge 1$ has $\kappa_k \ne 0$, then
sets of size `n` are determined by their `k`-sums. -/
theorem eq_of_sumMultiset_of_kappa {k n : ℕ}
    (hκ : ∀ (j : ℕ) (c : ℂ), 1 ≤ j → c ≠ 0 → ∀ κ : ℕ → ℂ, κ 0 = 0 →
      (∀ m : ℕ, 0 < m → (m : ℂ) * κ m = (-1) ^ (m + 1) *
        ∑ a ∈ antidiagonal m with a.1 < m,
          (-1) ^ a.1 * (κ a.1 * n + (n.choose a.1 : ℂ) * ((a.2 : ℂ) ^ j * c))) → κ k ≠ 0)
    {A B : Finset ℂ} (hA : A.card = n) (hB : B.card = n)
    (h : sumMultiset A k = sumMultiset B k) : A = B := by
  classical
  have hcard : A.card = B.card := hA.trans hB.symm
  by_contra hAB
  have hE : E A - E B ≠ 0 := fun hE => hAB (eq_of_E A B hcard (sub_eq_zero.mp hE))
  have hex : ∃ r, coeff r (E A - E B) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hE (PowerSeries.ext fun r => by rw [hall r, map_zero])
  obtain ⟨j, hj, hlow⟩ : ∃ j, coeff j (E A - E B) ≠ 0 ∧ ∀ r < j, coeff r (E A - E B) = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => not_not.mp (Nat.find_min hex hr)⟩
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      apply hj
      rw [h0, coeff_zero_eq_constantCoeff_apply, map_sub, constantCoeff_E, constantCoeff_E,
        hcard, sub_self]
    · exact h0
  have hδj : ∀ i : ℕ, (X : ℂ⟦X⟧) ^ j ∣ rescale (i : ℂ) (E A - E B) := fun i =>
    X_pow_dvd_iff.mpr (fun r hr => by rw [coeff_rescale, hlow r hr, mul_zero])
  have hdiff : ∀ m : ℕ, (m : ℂ⟦X⟧) * (G m A - G m B) = (-1) ^ (m + 1) *
      ∑ a ∈ antidiagonal m with a.1 < m, (-1) ^ a.1 *
        ((G a.1 A - G a.1 B) * rescale (a.2 : ℂ) (E A) +
          G a.1 B * rescale (a.2 : ℂ) (E A - E B)) := by
    intro m
    rw [mul_sub, newtonG, newtonG, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_sub]
    ring
  have hdvd : ∀ m, (X : ℂ⟦X⟧) ^ j ∣ G m A - G m B := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [G_zero, G_zero, sub_self]
        exact dvd_zero _
      · have hu : IsUnit (m : ℂ⟦X⟧) := by
          rw [← map_natCast (C (R := ℂ))]
          exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hm.ne')).map C
        rw [← hu.dvd_mul_left, hdiff m]
        apply Dvd.dvd.mul_left
        apply Finset.dvd_sum
        intro a ha
        rw [Finset.mem_filter] at ha
        apply Dvd.dvd.mul_left
        exact dvd_add (Dvd.dvd.mul_right (ih a.1 ha.2) _) (Dvd.dvd.mul_left (hδj a.2) _)
  have hrec : ∀ m : ℕ, 0 < m → (m : ℂ) * coeff j (G m A - G m B) = (-1) ^ (m + 1) *
      ∑ a ∈ antidiagonal m with a.1 < m, (-1) ^ a.1 *
        (coeff j (G a.1 A - G a.1 B) * n +
          (n.choose a.1 : ℂ) * ((a.2 : ℂ) ^ j * coeff j (E A - E B))) := by
    intro m _
    have h := congrArg (fun f => coeff j f) (hdiff m)
    rw [← map_natCast (C (R := ℂ)), coeff_C_mul] at h
    rw [h, show ((-1 : ℂ⟦X⟧)) ^ (m + 1) = C ((-1 : ℂ) ^ (m + 1)) by simp, coeff_C_mul, map_sum]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show ((-1 : ℂ⟦X⟧)) ^ a.1 = C ((-1 : ℂ) ^ a.1) by simp, coeff_C_mul, map_add,
      coeff_mul_of_dvd _ _ (hdvd a.1), mul_comm (G a.1 B), coeff_mul_of_dvd _ _ (hδj a.2),
      coeff_rescale, constantCoeff_rescale', constantCoeff_E, constantCoeff_G, hA, hB]
    ring
  have hGk : G k A = G k B := by rw [G_eq, G_eq, h]
  exact hκ j _ hj1 hj (fun m => coeff j (G m A - G m B)) (by simp [G_zero]) hrec (by simp [hGk])

/-! ### The arithmetic for $k = 4$ -/

/-- Six times the $k = 4$ coefficient: $n(n-1)(n-2) - 3 \cdot 2^t n(n-1) + 6 \cdot 3^t n
- 6 \cdot 4^t$. -/
def H (n t : ℕ) : ℤ :=
  (n : ℤ) * (n - 1) * (n - 2) - 3 * 2 ^ t * n * (n - 1) + 6 * 3 ^ t * n - 6 * 4 ^ t

lemma four_pow_ge (t : ℕ) (ht : 12 ≤ t) : 25 * 3 ^ t ≤ 4 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t _ ih =>
    rw [pow_succ, pow_succ]
    omega

lemma H_24 (t : ℕ) : H 24 t ≠ 0 := by
  rcases lt_or_ge t 12 with ht | ht
  · unfold H
    interval_cases t <;> norm_num
  · have h4 : (25 * 3 ^ t : ℤ) ≤ 4 ^ t := by exact_mod_cast four_pow_ge t ht
    have h3 : (3 ^ 12 : ℤ) ≤ 3 ^ t := pow_le_pow_right₀ (by norm_num) ht
    have h2 : (0 : ℤ) ≤ 2 ^ t := by positivity
    unfold H
    push_cast
    refine ne_of_lt ?_
    nlinarith

/-- The sign estimate: for $n \ge 3 \cdot 2^t + 4$, $H(n, t) > 0$. -/
lemma H_pos (n t : ℕ) (hn : 3 * 2 ^ t + 4 ≤ n) : 0 < H n t := by
  have hx : (1 : ℤ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  have hy : (0 : ℤ) ≤ 3 ^ t := by positivity
  have h4 : (4 : ℤ) ^ t = 2 ^ t * 2 ^ t := by
    rw [← mul_pow]
    norm_num
  have hn' : (3 * 2 ^ t + 4 : ℤ) ≤ n := by exact_mod_cast hn
  unfold H
  rw [h4]
  have h1 : (0 : ℤ) ≤ (n : ℤ) - 3 * 2 ^ t - 4 := by linarith
  have h5 : (0 : ℤ) ≤ (n : ℤ) * 3 ^ t := by positivity
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hn1 : (0 : ℤ) ≤ (n : ℤ) - 1 := by linarith
  have hx0 : (0 : ℤ) ≤ 2 ^ t := by positivity
  nlinarith [mul_nonneg (mul_nonneg hn0 hn1) h1, mul_nonneg h1 hn1, mul_nonneg h1 hx0,
    sq_nonneg ((2 : ℤ) ^ t)]

lemma zmod8_three_pow_odd (s : ℕ) : (3 : ZMod 8) ^ (2 * s + 1) = 3 := by
  rw [pow_succ, pow_mul]
  norm_num
  rw [show (9 : ZMod 8) = 1 by decide, one_pow, one_mul]

lemma zmod16_three_pow_even (s : ℕ) :
    (3 : ZMod 16) ^ (2 * s) = 1 ∨ (3 : ZMod 16) ^ (2 * s) = 9 := by
  rw [pow_mul]
  norm_num
  obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' s
  · left
    rw [pow_mul, show (9 : ZMod 16) ^ 2 = 1 by decide, one_pow]
  · right
    rw [pow_succ, pow_mul, show (9 : ZMod 16) ^ 2 = 1 by decide, one_pow, one_mul]

/-- For $n \ge 13$ and every $t$, $H(n, t) \ne 0$. -/
theorem H_ne_zero (n t : ℕ) (hn : 13 ≤ n) : H n t ≠ 0 := by
  intro h0
  -- `n` divides `6 * 4 ^ t = 2 ^ (2 t + 1) * 3`.
  have hdvdZ : (n : ℤ) ∣ 6 * 4 ^ t := by
    refine ⟨(n - 1) * (n - 2) - 3 * 2 ^ t * (n - 1) + 6 * 3 ^ t, ?_⟩
    unfold H at h0
    linear_combination -h0
  have hdvd : n ∣ 2 ^ (2 * t + 1) * 3 := by
    have : (n : ℤ) ∣ ((2 ^ (2 * t + 1) * 3 : ℕ) : ℤ) := by
      push_cast
      have e : (2 : ℤ) ^ (2 * t + 1) * 3 = 6 * 4 ^ t := by rw [pow_succ, pow_mul]; ring
      rw [e]
      exact hdvdZ
    exact_mod_cast this
  obtain ⟨y, z, hy, hz, hyz⟩ := dvd_mul.mp hdvd
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  have hz' : z = 1 ∨ z = 3 := (Nat.dvd_prime Nat.prime_three).mp hz
  have ha3 : 3 ≤ a := by
    by_contra ha
    have : 2 ^ a ≤ 4 := by
      calc 2 ^ a ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    rcases hz' with rfl | rfl <;> omega
  -- The sign estimate excludes large `n`.
  have hsmall : n < 3 * 2 ^ t + 4 := by
    by_contra hge
    exact absurd h0 (H_pos n t (by omega)).ne'
  have ht2 : 2 ≤ t := by
    by_contra ht
    interval_cases t <;> (norm_num at hsmall; omega)
  have hat : a ≤ t + 1 := by
    by_contra ha
    have h2a : 2 ^ t * 4 ≤ 2 ^ a := by
      calc 2 ^ t * 4 = 2 ^ (t + 2) := by ring
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 4 ≤ 2 ^ t := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht2
    rcases hz' with rfl | rfl <;> omega
  -- `2 ^ t` divides `Q = n ^ 2 - 3 n + 2 + 6 * 3 ^ t`.
  set Q : ℤ := (n : ℤ) ^ 2 - 3 * n + 2 + 6 * 3 ^ t with hQ
  have hnQ : (n : ℤ) * Q = 3 * 2 ^ t * n * (n - 1) + 6 * 4 ^ t := by
    unfold H at h0
    rw [hQ]
    linear_combination h0
  have hQdvd : (2 : ℤ) ^ t ∣ Q := by
    have h6 : (6 : ℤ) * 4 ^ t = 2 ^ a * (3 * 2 ^ (2 * t + 1 - a)) := by
      rw [mul_left_comm, ← pow_add, show a + (2 * t + 1 - a) = 2 * t + 1 by omega, pow_succ,
        pow_mul]
      ring
    have hn2 : (n : ℤ) = 2 ^ a * z := by rw [hyz]; push_cast; ring
    have hzQ : (z : ℤ) * Q = 3 * 2 ^ t * z * (n - 1) + 3 * 2 ^ (2 * t + 1 - a) := by
      have h2a : (2 : ℤ) ^ a ≠ 0 := by positivity
      apply mul_left_cancel₀ h2a
      have := hnQ
      rw [h6] at this
      linear_combination this - (Q - 3 * 2 ^ t * ((n : ℤ) - 1)) * hn2
    have hdz : (2 : ℤ) ^ t ∣ (z : ℤ) * Q := by
      rw [hzQ]
      exact dvd_add (((dvd_mul_left _ _).mul_right _).mul_right _)
        ((pow_dvd_pow 2 (by omega)).mul_left _)
    rcases hz' with rfl | rfl
    · simpa using hdz
    · have hcop : IsCoprime ((2 : ℤ) ^ t) 3 := by
        apply IsCoprime.pow_left
        rw [Int.isCoprime_iff_gcd_eq_one]
        rfl
      exact hcop.dvd_of_dvd_mul_left (by simpa using hdz)
  have hn8 : (8 : ℤ) ∣ n := by
    rw [hyz]
    push_cast
    exact Dvd.dvd.mul_right (by
      rw [show (8 : ℤ) = 2 ^ 3 by norm_num]
      exact pow_dvd_pow 2 ha3) _
  rcases Nat.even_or_odd' t with ⟨s, hs | hs⟩
  · -- `t` even
    rcases (show a = 3 ∨ 4 ≤ a by omega) with ha | ha
    · -- `n = 24`
      have hn24 : n = 24 := by
        subst ha
        rcases hz' with rfl | rfl <;> norm_num at hyz <;> omega
      rw [hn24] at h0
      exact H_24 t h0
    · have hn16 : (16 : ℤ) ∣ n := by
        rw [hyz]
        push_cast
        exact Dvd.dvd.mul_right (by
          rw [show (16 : ℤ) = 2 ^ 4 by norm_num]
          exact pow_dvd_pow 2 ha) _
      have ht4 : 4 ≤ t := by omega
      have h16Q : (16 : ℤ) ∣ Q := by
        have h := (pow_dvd_pow (2 : ℤ) ht4).trans hQdvd
        norm_num at h
        exact h
      have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd Q 16).mpr (by exact_mod_cast h16Q)
      have hn0 : ((n : ℤ) : ZMod 16) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mpr (by exact_mod_cast hn16)
      rw [hQ] at hcast
      push_cast at hcast hn0
      rw [hn0, hs] at hcast
      rcases zmod16_three_pow_even s with h | h <;> rw [h] at hcast <;> revert hcast <;> decide
  · -- `t` odd
    have ht3 : 3 ≤ t := by omega
    have h8Q : (8 : ℤ) ∣ Q := by
      have h := (pow_dvd_pow (2 : ℤ) ht3).trans hQdvd
      norm_num at h
      exact h
    have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd Q 8).mpr (by exact_mod_cast h8Q)
    have hn0 : ((n : ℤ) : ZMod 8) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr (by exact_mod_cast hn8)
    rw [hQ] at hcast
    push_cast at hcast hn0
    rw [hn0, hs, zmod8_three_pow_odd] at hcast
    revert hcast
    decide

/-- For $n \ge 13$, the $k = 4$ recursion has $\kappa_4 \ne 0$. -/
lemma kappa_four_ne_zero (n j : ℕ) (hn : 13 ≤ n) (hj : 1 ≤ j) (c : ℂ) (hc : c ≠ 0)
    (κ : ℕ → ℂ) (h0 : κ 0 = 0)
    (hrec : ∀ m : ℕ, 0 < m → (m : ℂ) * κ m = (-1) ^ (m + 1) *
      ∑ a ∈ antidiagonal m with a.1 < m,
        (-1) ^ a.1 * (κ a.1 * n + (n.choose a.1 : ℂ) * ((a.2 : ℂ) ^ j * c))) :
    κ 4 ≠ 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  have hC2 : (n.choose 2 : ℂ) = n * (n - 1) / 2 := Nat.cast_choose_two ℂ n
  have hC3 : (n.choose 3 : ℂ) = n * (n - 1) * (n - 2) / 6 := by
    have h := Nat.choose_succ_right_eq n 2
    have h' : ((n.choose 3 : ℕ) : ℂ) * 3 = (n.choose 2 : ℂ) * ((n - 2 : ℕ) : ℂ) := by
      exact_mod_cast h
    rw [Nat.cast_sub (by omega), hC2] at h'
    push_cast at h'
    linear_combination h' / 3
  have e1 := hrec 1 (by norm_num)
  have e2 := hrec 2 (by norm_num)
  have e3 := hrec 3 (by norm_num)
  have e4 := hrec 4 (by norm_num)
  simp only [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero] at e1 e2 e3 e4
  norm_num [h0, hC2, hC3] at e1 e2 e3 e4
  have h1 : κ 1 = c := by linear_combination e1
  rw [h1] at e2 e3 e4
  have h2 : κ 2 = c * (n - 2 ^ t) := by linear_combination e2 / 2
  rw [h2] at e3 e4
  have h3 : κ 3 = c * (n * (n - 1) / 2 - 2 ^ t * n + 3 ^ t) := by linear_combination e3 / 3
  rw [h3] at e4
  have h4 : κ 4 = c * ((H n t : ℂ) / 6) := by
    unfold H
    push_cast
    linear_combination e4 / 4
  rw [h4]
  refine mul_ne_zero hc (div_ne_zero ?_ (by norm_num))
  exact_mod_cast H_ne_zero n t hn

/--
Selfridge and Straus [SeSt58] showed that the conjecture is true
when $k = 4$ and $|A| > 12$.
-/
theorem erdos_494.variants.k_eq_4_card_gt_12 :
    ∀ card > 12, Erdos494Unique 4 card := by
  intro card hcard A B hA hB h
  exact eq_of_sumMultiset_of_kappa
    (fun j c hj hc κ h0 hrec => kappa_four_ne_zero card j hcard hj c hc κ h0 hrec) hA hB h

end Erdos494



end
