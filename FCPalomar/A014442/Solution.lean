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
# OEIS A014442: each Pythagorean prime $p$ is $a(n)$ for exactly two $n \le p$

OEIS A014442 is $a(n)$ = the largest prime factor of $n^2 + 1$. Michael Kaltman conjectured
(2015) that every prime $p \equiv 1 \pmod 4$ appears exactly twice among $a(1), \ldots, a(p)$,
and that if $a(i) = a(j) = p$ with $i \ne j$ both less than $p$, then $i + j = p$ and
$ij \equiv 1 \pmod p$. Robert Israel proved it in the entry. This file formalizes his proof.

For $i < p$, $a(i) = p$ if and only if $p \mid i^2 + 1$: a prime factor $q > p$ would give
$pq \le i^2 + 1 < p^2$. Since $-1$ is a square modulo $p$, the congruence $i^2 \equiv -1$ has
exactly the two solutions $x$ and $p - x$ in $[1, p - 1]$, and $x(p - x) \equiv -x^2 \equiv 1$.

*References:*
- [A014442](https://oeis.org/A014442)
-/

@[expose] public section

namespace OeisA14442

/-- $a(n)$ is the largest prime factor of $n^2 + 1$ (offset 1; `a 0 = 0`). -/
def a (n : ℕ) : ℕ := (n ^ 2 + 1).primeFactors.sup id

/-- Kaltman's conjecture: a prime $p \equiv 1 \pmod 4$ equals $a(n)$ for exactly two
$n \in [1, p]$, and two distinct such $n$ below $p$ add up to $p$ and multiply to $1$ mod $p$. -/
def Target : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 →
    ((Finset.Icc 1 p).filter fun n => a n = p).card = 2 ∧
    ∀ i j : ℕ, 1 ≤ i → i < p → 1 ≤ j → j < p → i ≠ j → a i = p → a j = p →
      i + j = p ∧ i * j % p = 1

theorem dvd_of_a_eq {n p : ℕ} (hp : p.Prime) (h : a n = p) : p ∣ n ^ 2 + 1 := by
  rcases (n ^ 2 + 1).primeFactors.eq_empty_or_nonempty with he | hne
  · rw [a, he, Finset.sup_empty] at h
    exact absurd h.symm hp.ne_zero
  · obtain ⟨q, hq, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [a, hsup] at h
    obtain rfl : q = p := h
    exact Nat.dvd_of_mem_primeFactors hq

/-- For $i < p$: $a(i) = p$ if and only if $p \mid i^2 + 1$. -/
theorem a_eq_iff {i p : ℕ} (hp : p.Prime) (hi : i < p) : a i = p ↔ p ∣ i ^ 2 + 1 := by
  refine ⟨dvd_of_a_eq hp, fun h => ?_⟩
  have hmem : p ∈ (i ^ 2 + 1).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, h, by positivity⟩
  refine le_antisymm (Finset.sup_le fun q hq => ?_) (Finset.le_sup (f := id) hmem)
  show q ≤ p
  have hqp := Nat.prime_of_mem_primeFactors hq
  by_contra hlt
  push Not at hlt
  have hpq : p ≠ q := by omega
  have hdvd := ((Nat.coprime_primes hp hqp).mpr hpq).mul_dvd_of_dvd_of_dvd h
    (Nat.dvd_of_mem_primeFactors hq)
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have h1 := Nat.mul_le_mul (show i + 1 ≤ p by omega) (show i + 1 ≤ p by omega)
  have h2 := Nat.mul_le_mul_left p (show p + 1 ≤ q by omega)
  have h3 := hp.two_le
  nlinarith

theorem sq_eq_neg_one {p n : ℕ} [Fact p.Prime] (h : p ∣ n ^ 2 + 1) : (n : ZMod p) ^ 2 = -1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Two distinct solutions of $p \mid i^2 + 1$ in $[1, p - 1]$ add up to $p$. -/
theorem add_eq_of_dvd {p i j : ℕ} (hp : p.Prime) (hi1 : 1 ≤ i) (hip : i < p) (hj1 : 1 ≤ j)
    (hjp : j < p) (hij : i ≠ j) (hi : p ∣ i ^ 2 + 1) (hj : p ∣ j ^ 2 + 1) : i + j = p := by
  have := Fact.mk hp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((sq_eq_neg_one hi).trans (sq_eq_neg_one hj).symm) with
    h | h
  · rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hip, Nat.mod_eq_of_lt hjp] at h
    exact absurd h hij
  · have h0 : ((i + j : ℕ) : ZMod p) = 0 := by rw [Nat.cast_add, h, neg_add_cancel]
    exact Nat.eq_of_dvd_of_lt_two_mul (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp h0)
      (by omega)

/-- If $p \mid i^2 + 1$ and $i < p$, then $i (p - i) \equiv 1 \pmod p$. -/
theorem mul_sub_mod {p i : ℕ} (hp : p.Prime) (hip : i < p) (hi : p ∣ i ^ 2 + 1) :
    i * (p - i) % p = 1 := by
  have := Fact.mk hp
  have h : ((i * (p - i) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, Nat.cast_sub hip.le, ZMod.natCast_self, Nat.cast_one]
    linear_combination -sq_eq_neg_one hi
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp.one_lt] at h
  exact h

/-- **OEIS A014442, Kaltman's conjecture** (proved by Israel). -/
theorem a014442_kaltman : Target := by
  intro p hp hp4
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨?_, fun i j hi1 hip hj1 hjp hij hai haj => ?_⟩
  · obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    have hx1 : 1 ≤ r.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero r).mpr hr0)
    have hxp : r.val < p := ZMod.val_lt r
    have hxdvd : p ∣ r.val ^ 2 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
        ZMod.natCast_zmod_val, sq, ← hr, neg_add_cancel]
    have hydvd : p ∣ (p - r.val) ^ 2 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
        Nat.cast_sub hxp.le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub, neg_sq, sq,
        ← hr, neg_add_cancel]
    have hset : ((Finset.Icc 1 p).filter fun n => a n = p) = {r.val, p - r.val} := by
      ext n
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hn1, hnp⟩, han⟩
        have hnd := dvd_of_a_eq hp han
        have hnlt : n < p := by
          refine lt_of_le_of_ne hnp fun hn => ?_
          rw [hn] at hnd
          exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_pow_self p two_ne_zero)).mp hnd)
        by_cases hnx : n = r.val
        · exact Or.inl hnx
        · have := add_eq_of_dvd hp hn1 hnlt hx1 hxp hnx hnd hxdvd
          right
          omega
      · rintro (rfl | rfl)
        · exact ⟨⟨hx1, hxp.le⟩, (a_eq_iff hp hxp).mpr hxdvd⟩
        · exact ⟨⟨by omega, by omega⟩, (a_eq_iff hp (by omega)).mpr hydvd⟩
    rw [hset, Finset.card_pair_eq_two_iff]
    omega
  · have hid := dvd_of_a_eq hp hai
    have hsum := add_eq_of_dvd hp hi1 hip hj1 hjp hij hid (dvd_of_a_eq hp haj)
    refine ⟨hsum, ?_⟩
    rw [show j = p - i by omega]
    exact mul_sub_mod hp hip hid

/-- The entry's first conjecture: every prime $p \equiv 1 \pmod 4$ occurs in the sequence. -/
theorem exists_a_eq {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) : ∃ n, 1 ≤ n ∧ a n = p := by
  have h := (a014442_kaltman p hp hp4).1
  obtain ⟨n, hn⟩ := Finset.card_pos.mp (by omega :
    0 < ((Finset.Icc 1 p).filter fun n => a n = p).card)
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  exact ⟨n, hn.1.1, hn.2⟩

end OeisA14442

namespace OeisA14442

theorem kaltman :
    ∀ p : ℕ, p.Prime → p % 4 = 1 →
      ((Finset.Icc 1 p).filter fun n => a n = p).card = 2 ∧
      ∀ i j : ℕ, 1 ≤ i → i < p → 1 ≤ j → j < p → i ≠ j → a i = p → a j = p →
        i + j = p ∧ i * j % p = 1 :=
  a014442_kaltman

end OeisA14442

end
