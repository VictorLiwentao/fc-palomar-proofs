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
# Fuss–Catalan numbers $\binom{pn}{n} / ((p-1)n + 1)$ modulo $p$

For a prime $p$, the Fuss–Catalan number $\binom{pn}{n} / ((p-1)n + 1)$ is an integer. Modulo $p$
it is $1$ when $n = (p^k - 1)/(p - 1)$ is a base-$p$ repunit and $0$ otherwise. OEIS A113052 is
the case $p = 5$ and A113047 the case $p = 3$.

*References:*
- Paul Barry, [A113052](https://oeis.org/A113052), October 12, 2005, and
  [A113047](https://oeis.org/A113047), October 11, 2005.
- Robert Israel, [Proof of conjecture](https://oeis.org/A113052/a113052.pdf), June 11, 2018.
- Kevin Ryde, [Proof of characteristic function of the ternary repunits](https://oeis.org/A113047/a113047.txt),
  June 23, 2021.
-/

@[expose] public section

namespace OeisA113052Proof

open Nat

/-- The base-$p$ repunit with $k$ digits: `rep p 0 = 0` and `rep p (k + 1) = p * rep p k + 1`. -/
def rep (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => p * rep p k + 1

lemma rep_spec (p k : ℕ) (hp : 1 ≤ p) : (p - 1) * rep p k + 1 = p ^ k := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    rw [rep, pow_succ, ← ih, Nat.add_sub_cancel]
    rw [Nat.add_sub_cancel] at ih
    ring

/-- The repunit is $(p^k - 1)/(p - 1)$. -/
lemma rep_eq_div (p k : ℕ) (hp : 2 ≤ p) : rep p k = (p ^ k - 1) / (p - 1) := by
  have h := rep_spec p k (by omega)
  rw [show p ^ k - 1 = (p - 1) * rep p k by omega, Nat.mul_div_cancel_left _ (by omega)]

/-- `n` is a base-$p$ repunit. -/
def IsRepunit (p n : ℕ) : Prop := ∃ k, n = rep p k

lemma isRepunit_zero (p : ℕ) : IsRepunit p 0 := ⟨0, rfl⟩

lemma isRepunit_mul_add_one {p : ℕ} (hp : 0 < p) (m : ℕ) :
    IsRepunit p (p * m + 1) ↔ IsRepunit p m := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp [rep] at hk
    | succ k =>
      refine ⟨k, ?_⟩
      rw [rep] at hk
      exact Nat.eq_of_mul_eq_mul_left hp (by omega)
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, rfl⟩

lemma mod_eq_one_of_isRepunit {p n : ℕ} (hp : 2 ≤ p) (h : IsRepunit p n) (hn : n ≠ 0) :
    n % p = 1 := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | zero => exact absurd rfl hn
  | succ k =>
    rw [rep, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)

lemma isRepunit_iff (p n : ℕ) (hp : 2 ≤ p) :
    IsRepunit p n ↔ ∃ k, n = (p ^ k - 1) / (p - 1) := by
  simp only [IsRepunit, rep_eq_div p _ hp]

section Lucas

variable {p : ℕ} [Fact p.Prime]

lemma two_le : 2 ≤ p := (Fact.out : p.Prime).two_le

/-- Lucas' theorem, cast to `ZMod p`. -/
lemma choose_cast (N K : ℕ) :
    (N.choose K : ZMod p) = ((N % p).choose (K % p) : ZMod p) * ((N / p).choose (K / p) : ZMod p) := by
  rw [← Nat.cast_mul]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr Choose.choose_modEq_choose_mod_mul_choose_div_nat

/-- $\binom{pn}{n} \equiv [n = 0] \pmod p$. -/
theorem choose_mul_self_cast (n : ℕ) :
    ((p * n).choose n : ZMod p) = if n = 0 then 1 else 0 := by
  have hp := two_le (p := p)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [choose_cast, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by omega), ite_eq_right (by omega)]
    by_cases hr : n % p = 0
    · obtain ⟨m, hm⟩ : p ∣ n := Nat.dvd_of_mod_eq_zero hr
      have hm0 : m ≠ 0 := by rintro rfl; omega
      have hmn : m < n := by
        rw [hm]
        exact lt_mul_left (Nat.pos_of_ne_zero hm0) (by omega)
      have hdiv : n / p = m := by rw [hm, Nat.mul_div_cancel_left _ (by omega)]
      rw [hr, hdiv]
      conv_lhs => rw [hm]
      rw [ih m hmn, ite_eq_right hm0, mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hr), Nat.cast_zero, zero_mul]

open scoped Classical in
/-- $\binom{pn+1}{n} \equiv [n \text{ is a repunit}] \pmod p$. -/
theorem choose_mul_self_add_one_cast (n : ℕ) :
    ((p * n + 1).choose n : ZMod p) = if IsRepunit p n then 1 else 0 := by
  have hp := two_le (p := p)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [isRepunit_zero]
    have hmod : (p * n + 1) % p = 1 := by
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    have hdiv : (p * n + 1) / p = n := by
      rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
    rw [choose_cast, hmod, hdiv]
    set m := n / p with hm_def
    set r := n % p with hr_def
    have hnmr : n = p * m + r := (Nat.div_add_mod n p).symm
    have hmn : m < n := Nat.div_lt_self hn (by omega)
    rcases (show r = 0 ∨ r = 1 ∨ 2 ≤ r by omega) with h0 | h1 | h2
    · -- `n = p * m` with `m ≠ 0`: not a repunit, and `choose (p * m) m ≡ 0`
      have hm0 : m ≠ 0 := by rintro hm; rw [hm, h0] at hnmr; omega
      have hnot : ¬ IsRepunit p n := fun h => by
        have := mod_eq_one_of_isRepunit hp h (by omega)
        omega
      rw [h0, Nat.choose_zero_right, Nat.cast_one, one_mul, ite_eq_right hnot]
      conv_lhs => rw [hnmr, h0, add_zero]
      rw [choose_mul_self_cast, ite_eq_right hm0]
    · -- `n = p * m + 1`: a repunit exactly when `m` is
      rw [h1, Nat.choose_self, Nat.cast_one, one_mul]
      conv_lhs => rw [hnmr, h1]
      rw [ih m hmn]
      have hiff : IsRepunit p n ↔ IsRepunit p m := by
        rw [hnmr, h1]
        exact isRepunit_mul_add_one (by omega) m
      simp only [hiff]
    · -- the last digit is at least `2`: not a repunit, and `choose 1 r = 0`
      have hnot : ¬ IsRepunit p n := fun h => by
        have := mod_eq_one_of_isRepunit hp h (by omega)
        omega
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, ite_eq_right hnot]

end Lucas

/-- $\binom{pn}{n} (pn + 1) = \binom{pn+1}{n} ((p-1)n + 1)$. -/
lemma choose_identity (p n : ℕ) (hp : 1 ≤ p) :
    (p * n).choose n * (p * n + 1) = (p * n + 1).choose n * ((p - 1) * n + 1) := by
  rw [Nat.choose_mul_succ_eq]
  congr 1
  have hle : n ≤ p * n := Nat.le_mul_of_pos_left n (by omega)
  rw [Nat.sub_one_mul]
  omega

/-- $(p-1)n + 1$ and $pn + 1$ are coprime. -/
lemma coprime_aux (p n : ℕ) (hp : 1 ≤ p) : Nat.Coprime ((p - 1) * n + 1) (p * n + 1) := by
  rw [← Nat.isCoprime_iff_coprime]
  refine ⟨p, -((p - 1 : ℕ) : ℤ), ?_⟩
  push_cast [Nat.cast_sub hp]
  ring

/-- The Fuss–Catalan number $\binom{pn}{n} / ((p-1)n + 1)$ is an integer. -/
theorem dvd_choose (p n : ℕ) (hp : 1 ≤ p) : (p - 1) * n + 1 ∣ (p * n).choose n := by
  have h : (p - 1) * n + 1 ∣ (p * n).choose n * (p * n + 1) :=
    ⟨(p * n + 1).choose n, by rw [choose_identity p n hp, mul_comm]⟩
  exact (coprime_aux p n hp).dvd_of_dvd_mul_right h

open scoped Classical in
/-- For every prime $p$ and every $n$, $\binom{pn}{n} / ((p-1)n + 1)$ is an integer, and it is
congruent modulo $p$ to $1$ if $n = (p^k - 1)/(p - 1)$ for some $k$ and to $0$ otherwise. -/
theorem fussCatalan_mod_prime (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (p - 1) * n + 1 ∣ (p * n).choose n ∧
      (p * n).choose n / ((p - 1) * n + 1) % p =
        if ∃ k, n = (p ^ k - 1) / (p - 1) then 1 else 0 := by
  have := Fact.mk hp
  have hp2 := hp.two_le
  refine ⟨dvd_choose p n (by omega), ?_⟩
  set F := (p * n).choose n / ((p - 1) * n + 1) with hF
  have hFd : F * ((p - 1) * n + 1) = (p * n).choose n := Nat.div_mul_cancel (dvd_choose p n (by omega))
  have hFc : F * (p * n + 1) = (p * n + 1).choose n := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (p - 1) * n + 1 by omega)
    rw [← choose_identity p n (by omega), ← hFd]
    ring
  have hcast : (F : ZMod p) = if IsRepunit p n then 1 else 0 := by
    have h := congrArg (fun x : ℕ => (x : ZMod p)) hFc
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_mul, zero_add,
      mul_one] at h
    rw [h, choose_mul_self_add_one_cast]
  have hval : F % p = (F : ZMod p).val := (ZMod.val_natCast p F).symm
  have hfact : Fact (1 < p) := ⟨by omega⟩
  rw [hval, hcast]
  by_cases hr : IsRepunit p n
  · rw [ite_eq_left hr, ite_eq_left ((isRepunit_iff p n hp2).1 hr)]
    exact ZMod.val_one p
  · rw [ite_eq_right hr, ite_eq_right (fun h => hr ((isRepunit_iff p n hp2).2 h))]
    exact ZMod.val_zero

open scoped Classical in
/-- OEIS A113052 conjecture (Paul Barry): for $p$ prime, $\binom{pn}{n}/((p-1)n+1) \bmod p$ is
the indicator function of the sequence $(p^k - 1)/(p - 1)$. -/
theorem a113052_conjecture (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (p * n).choose n / ((p - 1) * n + 1) % p =
      if ∃ k, n = (p ^ k - 1) / (p - 1) then 1 else 0 :=
  (fussCatalan_mod_prime p hp n).2

open scoped Classical in
/-- OEIS A113047 (Paul Barry; confirmed by Kevin Ryde): $\binom{3n}{n}/(2n+1) \bmod 3$ is the
characteristic function of the ternary repunits $(3^j - 1)/2$. -/
theorem a113047_characteristic (n : ℕ) :
    (3 * n).choose n / (2 * n + 1) % 3 = if ∃ j, n = (3 ^ j - 1) / 2 then 1 else 0 :=
  a113052_conjecture 3 Nat.prime_three n

/-- OEIS A113047 conjecture: $a(n) = \binom{3n}{n}/(2n+1) \bmod 3$ differs from $0$ only when
$n = (3^j - 1)/2$. -/
theorem a113047_conjecture (n : ℕ) (h : (3 * n).choose n / (2 * n + 1) % 3 ≠ 0) :
    ∃ j, n = (3 ^ j - 1) / 2 := by
  by_contra hj
  rw [a113047_characteristic, ite_eq_right hj] at h
  exact h rfl

end OeisA113052Proof

/-! Separately written source statements for OEIS A113052 and A113047. They assert no theorem.

Sources, retrieved 2026-11-03:
- A113052 (Paul Barry, Oct 12 2005; revision #8): "Binomial(5n,n)/(4n+1) mod 5", offset 0, and
  "Conjecture: for p prime, mod(C(p*n,n)/((p-1)*n+1),p) is the indicator function of the
  sequence (p^k-1)/(p-1)." Marked true by Robert Israel, Jun 11 2018.
- A113047 (Paul Barry, Oct 11 2005; revision #29): "a(n) = C(3n,n)/(2n+1) mod 3", offset 0;
  "a(n) differs from 0 only when n=(3^j-1)/2, j>=0" and, by Kevin Ryde, "a(n) = 1 iff n is a
  ternary repunit".

The quotient is written in `ℚ`, with the claim that it is a natural number `c`; the residue is
`c % p`. The index set $(p^k - 1)/(p - 1)$, $k \ge 0$, is also written in `ℚ`. -/
namespace A113052Frozen

open scoped Classical in
/-- The A113052 conjecture, for every prime `p` and every `n ≥ 0`. -/
def conjecture : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℕ, ∃ c : ℕ,
    (c : ℚ) = (Nat.choose (p * n) n : ℚ) / (((p : ℚ) - 1) * n + 1) ∧
      c % p = if ∃ k : ℕ, (n : ℚ) = ((p : ℚ) ^ k - 1) / ((p : ℚ) - 1) then 1 else 0

open scoped Classical in
/-- The A113047 statement: `C(3n,n)/(2n+1) mod 3` is `1` at `n = (3^j - 1)/2` and `0` elsewhere. -/
def a113047 : Prop :=
  ∀ n : ℕ, ∃ c : ℕ, (c : ℚ) = (Nat.choose (3 * n) n : ℚ) / (2 * n + 1) ∧
    c % 3 = if ∃ j : ℕ, (n : ℚ) = ((3 : ℚ) ^ j - 1) / 2 then 1 else 0

end A113052Frozen

/-! Kernel checks for the OEIS A113052 / A113047 candidate: the separately frozen statements and
transitive axioms. This file is not Comparator. -/

open OeisA113052Proof

/-- The repunit condition in `ℚ` agrees with the `ℕ` form used by the candidate. -/
lemma cond_iff (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (∃ k : ℕ, (n : ℚ) = ((p : ℚ) ^ k - 1) / ((p : ℚ) - 1)) ↔ ∃ k, n = (p ^ k - 1) / (p - 1) := by
  have hp1 : ((p : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp
    intro h
    linarith
  refine exists_congr fun k => ?_
  rw [← rep_eq_div p k hp, eq_div_iff hp1]
  constructor
  · intro h
    have hnat : (p - 1) * n + 1 = p ^ k := by
      have h' : (((p - 1) * n + 1 : ℕ) : ℚ) = ((p ^ k : ℕ) : ℚ) := by
        push_cast [Nat.cast_sub (show 1 ≤ p by omega)]
        linarith
      exact_mod_cast h'
    have hs := rep_spec p k (by omega)
    exact Nat.eq_of_mul_eq_mul_left (show 0 < p - 1 by omega) (Nat.add_right_cancel (hnat.trans hs.symm))
  · rintro rfl
    have hs := rep_spec p k (by omega)
    have h' : (((p - 1) * rep p k + 1 : ℕ) : ℚ) = ((p ^ k : ℕ) : ℚ) := by rw [hs]
    push_cast [Nat.cast_sub (show 1 ≤ p by omega)] at h'
    linarith

theorem frozen_conjecture : A113052Frozen.conjecture := by
  intro p hp n
  have hp2 := hp.two_le
  obtain ⟨hdvd, hmod⟩ := fussCatalan_mod_prime p hp n
  refine ⟨(p * n).choose n / ((p - 1) * n + 1), ?_, ?_⟩
  · have hd : (((p - 1) * n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [Nat.cast_div hdvd hd, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show 1 ≤ p by omega),
      Nat.cast_one]
  · rw [hmod]
    by_cases h : ∃ k, n = (p ^ k - 1) / (p - 1)
    · rw [ite_eq_left h, ite_eq_left ((cond_iff p hp2 n).2 h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((cond_iff p hp2 n).1 h'))]

theorem frozen_a113047 : A113052Frozen.a113047 := by
  intro n
  obtain ⟨c, hc, hmod⟩ := frozen_conjecture 3 Nat.prime_three n
  have h3 : ((3 : ℕ) : ℚ) - 1 = 2 := by norm_num
  refine ⟨c, ?_, ?_⟩
  · rw [hc, h3]
  · rw [hmod, h3]
    simp only [Nat.cast_ofNat]

namespace OeisA113052

open scoped Classical

theorem conjecture :
    ∀ p : ℕ, p.Prime → ∀ n : ℕ, ∃ c : ℕ,
      (c : ℚ) = (Nat.choose (p * n) n : ℚ) / (((p : ℚ) - 1) * n + 1) ∧
        c % p = if ∃ k : ℕ, (n : ℚ) = ((p : ℚ) ^ k - 1) / ((p : ℚ) - 1) then 1 else 0 :=
  _root_.frozen_conjecture

theorem a113047 :
    ∀ n : ℕ, ∃ c : ℕ, (c : ℚ) = (Nat.choose (3 * n) n : ℚ) / (2 * n + 1) ∧
      c % 3 = if ∃ j : ℕ, (n : ℚ) = ((3 : ℚ) ^ j - 1) / 2 then 1 else 0 :=
  _root_.frozen_a113047

end OeisA113052

end
