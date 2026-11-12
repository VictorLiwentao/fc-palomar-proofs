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
# Bell numbers modulo a prime are periodic

For a prime $p$, the Bell numbers satisfy $B(n + N_p) \equiv B(n) \pmod p$ with
$N_p = (p^p - 1)/(p - 1)$ (Touchard 1933, Hall 1934). This settles the conjectures of
G. C. Greubel in OEIS A146107, A146109, A146113, A146119 and A146121 ($p = 17, 19, 23, 29, 31$).
Minimality of the period is not claimed.

Proof: let $L$ be the linear functional on $\mathbb{F}_p[X]$ with $L(X^n) = B(n)$. Touchard's
congruence gives $L(h \cdot g) = 0$ for $g = X^p - X - 1$ and every $h$. In `AdjoinRoot g`, the
root $\alpha$ satisfies $\alpha^p = \alpha + 1$, so $\alpha^{p^j} = \alpha + j$ and
$\alpha^{N_p} = \prod_{j < p} (\alpha + j) = \alpha^p - \alpha = 1$. Hence $g \mid X^{N_p} - 1$
and $B(n + N_p) - B(n) = L(X^n (X^{N_p} - 1)) = 0$.

*References:*
- J. Touchard, *Propriétés arithmétiques de certains nombres récurrents*, Ann. Soc. Sci.
  Bruxelles A 53 (1933), 21–31.
- M. Hall, *Arithmetic properties of a partition function*, Bull. Amer. Math. Soc. 40 (1934), 387.
- W. F. Lunnon, P. A. B. Pleasants and N. M. Stephens, *Arithmetic properties of Bell numbers to
  a composite modulus I*, Acta Arith. 35 (1979), 1–16.
- N. J. A. Sloane and G. C. Greubel, OEIS [A146107](https://oeis.org/A146107),
  [A146109](https://oeis.org/A146109), [A146113](https://oeis.org/A146113),
  [A146119](https://oeis.org/A146119), [A146121](https://oeis.org/A146121).
-/

@[expose] public section

namespace OeisA54767

/-- The Bell numbers read modulo `p`. -/
def a (p n : ℕ) : ℕ := Nat.bell n % p

end OeisA54767

open Polynomial

namespace BellPeriod

section Touchard

variable (p : ℕ) [Fact p.Prime]

/-- The umbral functional `L(X^n) = B(n)` on `(ZMod p)[X]`. -/
noncomputable def L : (ZMod p)[X] →ₗ[ZMod p] ZMod p :=
  Polynomial.lsum fun n => (Nat.bell n : ZMod p) • LinearMap.id

theorem L_monomial (n : ℕ) (c : ZMod p) : L p (monomial n c) = (Nat.bell n : ZMod p) * c := by
  simp [L, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

theorem L_X_pow (n : ℕ) : L p (X ^ n) = (Nat.bell n : ZMod p) := by
  have h := L_monomial p n 1
  rwa [← C_mul_X_pow_eq_monomial, C_1, one_mul, mul_one] at h

theorem L_X_pow_succ (n : ℕ) : L p ((X + 1) ^ n) = (Nat.bell (n + 1) : ZMod p) := by
  rw [add_comm, add_pow, map_sum, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have : ((n.choose i : ℕ) : (ZMod p)[X]) = C (n.choose i : ZMod p) := by simp
  rw [one_pow, one_mul, this, mul_comm, ← smul_eq_C_mul, map_smul, L_X_pow]
  simp

theorem L_X_mul (f : (ZMod p)[X]) : L p (X * f) = L p (f.comp (X + 1)) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [mul_add, map_add, hf, hg, add_comp, map_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, mul_smul_comm, map_smul, smul_comp,
      map_smul, X_pow_comp, ← pow_succ', L_X_pow, L_X_pow_succ]

/-- `L(x (x-1) ⋯ (x-k+1) · h(x)) = L(h(x+k))`. -/
theorem L_descPochhammer (k : ℕ) :
    ∀ h : (ZMod p)[X], L p (descPochhammer (ZMod p) k * h) =
      L p (h.comp (X + (k : (ZMod p)[X]))) := by
  induction k with
  | zero => intro h; simp
  | succ k ih =>
    intro h
    rw [descPochhammer_succ_left, mul_assoc, L_X_mul, mul_comp, comp_assoc]
    have e1 : (X - 1 : (ZMod p)[X]).comp (X + 1) = X := by simp
    have e2 : (X + 1 : (ZMod p)[X]).comp (X + (k : (ZMod p)[X])) =
        X + ((k + 1 : ℕ) : (ZMod p)[X]) := by
      simp; ring
    rw [e1, comp_X, ih, comp_assoc, e2]

/-- In characteristic `p`, the falling factorial `x (x-1) ⋯ (x-p+1)` is `x^p - x`. -/
theorem descPochhammer_eq : descPochhammer (ZMod p) p = X ^ p - X := by
  have hp : p.Prime := Fact.out
  have hdeg : (descPochhammer (ZMod p) p).degree = p := by
    rw [degree_eq_natDegree (monic_descPochhammer _ _).ne_zero, descPochhammer_natDegree]
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := monic_X_pow_sub (by simpa using hp.one_lt)
  have hdeg' : (X ^ p - X : (ZMod p)[X]).degree = p := by
    rw [degree_eq_natDegree hmon.ne_zero,
      FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.one_lt]
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (Finset.univ : Finset (ZMod p)) ?_ ?_
  · rw [Finset.card_univ, ZMod.card]
    have := degree_sub_lt_left (hdeg.trans hdeg'.symm) (monic_descPochhammer _ _).ne_zero
      ((monic_descPochhammer _ _).leadingCoeff.trans hmon.leadingCoeff.symm)
    rwa [hdeg] at this
  · intro a _
    rw [descPochhammer_eval_eq_prod_range]
    have h0 : ∏ j ∈ Finset.range p, (a - (j : ZMod p)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 (ZMod.val_lt a)) (by simp)
    rw [h0]
    simp [ZMod.pow_card]

/-- **Touchard's congruence (1933).** $B(n + p) \equiv B(n) + B(n + 1) \pmod p$. -/
theorem bell_add_prime (n : ℕ) :
    ((n + p).bell : ZMod p) = n.bell + (n + 1).bell := by
  have h := L_descPochhammer p p (X ^ n)
  rw [descPochhammer_eq, CharP.cast_eq_zero, add_zero, comp_X, sub_mul, map_sub, ← pow_add,
    ← pow_succ', L_X_pow, L_X_pow, L_X_pow] at h
  rw [add_comm n p]
  linear_combination h

end Touchard

section Period

variable (p : ℕ) [hp : Fact p.Prime]

/-- `X ^ p - X - 1` over `ZMod p`. -/
noncomputable def g : (ZMod p)[X] := X ^ p - X - 1

/-- Touchard's congruence in functional form: `L` vanishes on multiples of `g`. -/
theorem L_g_mul (h : (ZMod p)[X]) : L p (g p * h) = 0 := by
  have h1 := L_descPochhammer p p h
  rw [descPochhammer_eq, CharP.cast_eq_zero, add_zero, comp_X] at h1
  rw [g, sub_mul, one_mul, map_sub, h1, sub_self]

variable {A : Type*} [CommRing A] [CharP A p]

theorem natCast_pow_char (j : ℕ) : (j : A) ^ p = j := by
  induction j with
  | zero => rw [Nat.cast_zero, zero_pow hp.out.ne_zero]
  | succ j ih => rw [Nat.cast_succ, add_pow_char, ih, one_pow]

/-- $\prod_{j < p} (x + j) = x^p - x$ in characteristic $p$. -/
theorem prod_add_natCast (x : A) : ∏ j ∈ Finset.range p, (x + j) = x ^ p - x := by
  have h := descPochhammer_eval_eq_prod_range p (-x)
  rw [← descPochhammer_map (ZMod.castHom (dvd_refl p) A), descPochhammer_eq, eval_map] at h
  simp only [eval₂_sub, eval₂_X_pow, eval₂_X] at h
  have h2 : ∏ j ∈ Finset.range p, (-x - (j : A)) = -∏ j ∈ Finset.range p, (x + j) := by
    rw [show (fun j : ℕ => -x - (j : A)) = fun j : ℕ => -(x + (j : A)) from
        funext fun j => by ring,
      Finset.prod_neg, Finset.card_range, neg_one_pow_char A p, neg_one_mul]
  rw [h2, neg_pow, neg_one_pow_char A p] at h
  linear_combination h

theorem pow_pow_eq_add (x : A) (hx : x ^ p = x + 1) (j : ℕ) : x ^ (p ^ j) = x + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, add_pow_char, hx, natCast_pow_char, Nat.cast_succ]
    ring

/-- If $x^p = x + 1$ in characteristic $p$, then $x^{(p^p - 1)/(p - 1)} = 1$. -/
theorem pow_period_eq_one (x : A) (hx : x ^ p = x + 1) : x ^ ((p ^ p - 1) / (p - 1)) = 1 := by
  rw [← Nat.geomSum_eq hp.out.two_le p, ← Finset.prod_pow_eq_pow_sum]
  simp_rw [pow_pow_eq_add p x hx]
  rw [prod_add_natCast, hx]
  ring

theorem degree_g : (g p).degree = p := by
  have h1 : (X + C 1 : (ZMod p)[X]).degree < (X ^ p : (ZMod p)[X]).degree := by
    rw [degree_X_add_C, degree_X_pow]
    exact_mod_cast hp.out.one_lt
  rw [g, sub_sub, ← C_1, degree_sub_eq_left_of_degree_lt h1, degree_X_pow]

instance : Nontrivial (AdjoinRoot (g p)) :=
  AdjoinRoot.nontrivial (f := g p) (by rw [degree_g]; exact_mod_cast hp.out.ne_zero)

instance : CharP (AdjoinRoot (g p)) p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) (AdjoinRoot (g p))).injective p

theorem root_pow : AdjoinRoot.root (g p) ^ p = AdjoinRoot.root (g p) + 1 := by
  have h : AdjoinRoot.mk (g p) (X ^ p - X - 1) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  linear_combination h

/-- $X^p - X - 1$ divides $X^{(p^p - 1)/(p - 1)} - 1$ over $\mathbb{F}_p$. -/
theorem g_dvd : g p ∣ X ^ ((p ^ p - 1) / (p - 1)) - 1 := by
  apply AdjoinRoot.mk_eq_zero.1
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, pow_period_eq_one p _ (root_pow p), sub_self]

theorem bell_add_period_zmod (n : ℕ) :
    ((n + (p ^ p - 1) / (p - 1)).bell : ZMod p) = n.bell := by
  obtain ⟨q, hq⟩ := g_dvd p
  have h := L_g_mul p (X ^ n * q)
  have e : X ^ n * (X ^ ((p ^ p - 1) / (p - 1)) - 1) = g p * (X ^ n * q) := by
    rw [hq]
    ring
  rw [← e, mul_sub, mul_one, ← pow_add, map_sub, L_X_pow, L_X_pow] at h
  exact sub_eq_zero.1 h

end Period

/-- **Touchard–Hall.** For a prime $p$, $B(n + (p^p - 1)/(p - 1)) \equiv B(n) \pmod p$. -/
theorem bell_add_period {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Nat.bell (n + (p ^ p - 1) / (p - 1)) ≡ Nat.bell n [MOD p] := by
  have := Fact.mk hp
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (bell_add_period_zmod p n)

/-- **OEIS A146107** (G. C. Greubel's conjecture): $a(n) = B(n) \bmod 17$ satisfies
$a(n + 51702516367896047761) = a(n)$. -/
theorem a146107 (n : ℕ) : Nat.bell (n + 51702516367896047761) % 17 = Nat.bell n % 17 := by
  have h := bell_add_period (by norm_num : Nat.Prime 17) n
  rw [show (17 ^ 17 - 1) / (17 - 1) = 51702516367896047761 by norm_num] at h
  exact h

/-- **OEIS A146109** (G. C. Greubel's conjecture): $a(n) = B(n) \bmod 19$ satisfies
$a(n + 109912203092239643840221) = a(n)$. -/
theorem a146109 (n : ℕ) :
    Nat.bell (n + 109912203092239643840221) % 19 = Nat.bell n % 19 := by
  have h := bell_add_period (by norm_num : Nat.Prime 19) n
  rw [show (19 ^ 19 - 1) / (19 - 1) = 109912203092239643840221 by norm_num] at h
  exact h

/-- **OEIS A146113** (G. C. Greubel's conjecture): $a(n) = B(n) \bmod 23$ satisfies
$a(n + 949112181811268728834319677753) = a(n)$. -/
theorem a146113 (n : ℕ) :
    Nat.bell (n + 949112181811268728834319677753) % 23 = Nat.bell n % 23 := by
  have h := bell_add_period (by norm_num : Nat.Prime 23) n
  rw [show (23 ^ 23 - 1) / (23 - 1) = 949112181811268728834319677753 by norm_num] at h
  exact h

/-- **OEIS A146119** (G. C. Greubel's conjecture): $a(n) = B(n) \bmod 29$ satisfies
$a(n + 91703076898614683377208150526107718802981) = a(n)$. -/
theorem a146119 (n : ℕ) :
    Nat.bell (n + 91703076898614683377208150526107718802981) % 29 = Nat.bell n % 29 := by
  have h := bell_add_period (by norm_num : Nat.Prime 29) n
  rw [show (29 ^ 29 - 1) / (29 - 1) = 91703076898614683377208150526107718802981 by norm_num]
    at h
  exact h

/-- **OEIS A146121** (G. C. Greubel's conjecture): $a(n) = B(n) \bmod 31$ satisfies
$a(n + 568972471024107865287021434301977158534824481) = a(n)$. -/
theorem a146121 (n : ℕ) :
    Nat.bell (n + 568972471024107865287021434301977158534824481) % 31 = Nat.bell n % 31 := by
  have h := bell_add_period (by norm_num : Nat.Prime 31) n
  rw [show (31 ^ 31 - 1) / (31 - 1) = 568972471024107865287021434301977158534824481 by
    norm_num] at h
  exact h

end BellPeriod

/-! Separately written source statements for OEIS A146107, A146109, A146113, A146119 and A146121.
They assert no theorem.

Sources, retrieved 2026-11-03 (N. J. A. Sloane, Feb 07 2009; offset 0):
- A146107 (revision #19): "Bell numbers (A000110) read mod 17." "Conjecture:
  a(n+51702516367896047761) = a(n). - G. C. Greubel, Feb 01 2016".
- A146109 (revision #21): mod 19, "a(n+109912203092239643840221) = a(n)".
- A146113 (revision #18): mod 23, "a(n+949112181811268728834319677753) = a(n)".
- A146119 (revision #18): mod 29, "a(n+91703076898614683377208150526107718802981) = a(n)".
- A146121 (revision #16): mod 31, "a(n+568972471024107865287021434301977158534824481) = a(n)".
- A054767: for a prime $p$ the period of the Bell numbers mod $p$ divides $(p^p-1)/(p-1)$.

`Nat.bell` is Mathlib's Bell number (A000110): `Nat.bell 0 = 1` and
$B(n+1) = \sum_{i \le n} \binom{n}{i} B(n - i)$. -/
namespace BellPeriodFrozen

/-- The sequence "Bell numbers read mod `p`". -/
def a (p n : ℕ) : ℕ := Nat.bell n % p

/-- The general statement (A054767): for every prime $p$, $(p^p - 1)/(p - 1)$ is a period. -/
def general : Prop := ∀ p : ℕ, p.Prime → ∀ n : ℕ, a p (n + (p ^ p - 1) / (p - 1)) = a p n

/-- A146107. -/
def a146107 : Prop := ∀ n : ℕ, a 17 (n + 51702516367896047761) = a 17 n

/-- A146109. -/
def a146109 : Prop := ∀ n : ℕ, a 19 (n + 109912203092239643840221) = a 19 n

/-- A146113. -/
def a146113 : Prop := ∀ n : ℕ, a 23 (n + 949112181811268728834319677753) = a 23 n

/-- A146119. -/
def a146119 : Prop := ∀ n : ℕ, a 29 (n + 91703076898614683377208150526107718802981) = a 29 n

/-- A146121. -/
def a146121 : Prop :=
  ∀ n : ℕ, a 31 (n + 568972471024107865287021434301977158534824481) = a 31 n

end BellPeriodFrozen

/-! Kernel checks for the Bell-period candidate: the separately frozen statements, the A000110
recurrence for `Nat.bell`, and a Lean-side axiom check. This file is not Comparator. -/

open BellPeriod

/-- `Nat.bell` satisfies the A000110 recurrence $B(n+1) = \sum_{k=0}^{n} \binom{n}{k} B(k)$. -/
theorem bell_succ_eq_sum (n : ℕ) :
    Nat.bell (n + 1) = ∑ k ∈ Finset.range (n + 1), n.choose k * Nat.bell k := by
  rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm (by omega),
    show n - (n - k) = k by omega]

theorem frozen_general : BellPeriodFrozen.general := fun _ hp n => bell_add_period hp n

theorem frozen_a146107 : BellPeriodFrozen.a146107 := a146107

theorem frozen_a146109 : BellPeriodFrozen.a146109 := a146109

theorem frozen_a146113 : BellPeriodFrozen.a146113 := a146113

theorem frozen_a146119 : BellPeriodFrozen.a146119 := a146119

theorem frozen_a146121 : BellPeriodFrozen.a146121 := a146121

namespace OeisA54767

theorem bell_period :
    ∀ p : ℕ, p.Prime → ∀ n : ℕ, a p (n + (p ^ p - 1) / (p - 1)) = a p n :=
  _root_.frozen_general

theorem a146107 :
    ∀ n : ℕ, a 17 (n + 51702516367896047761) = a 17 n :=
  _root_.frozen_a146107

theorem a146109 :
    ∀ n : ℕ, a 19 (n + 109912203092239643840221) = a 19 n :=
  _root_.frozen_a146109

theorem a146113 :
    ∀ n : ℕ, a 23 (n + 949112181811268728834319677753) = a 23 n :=
  _root_.frozen_a146113

theorem a146119 :
    ∀ n : ℕ, a 29 (n + 91703076898614683377208150526107718802981) = a 29 n :=
  _root_.frozen_a146119

theorem a146121 :
    ∀ n : ℕ, a 31 (n + 568972471024107865287021434301977158534824481) = a 31 n :=
  _root_.frozen_a146121

end OeisA54767

end
