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
# Kolberg's theorem: $p(n)$ takes each parity infinitely often

O. Kolberg (1959) proved that the partition number $p(n)$ is even for infinitely many $n$ and odd
for infinitely many $n$. This file proves it with Euler's pentagonal number theorem.

Over $\mathbb{F}_2$, $P(x) E(x) = 1$, where $P = \sum_n p(n) x^n$ and
$E = \prod_{n \ge 1} (1 - x^n)$ has nonzero coefficients exactly at the generalized pentagonal
numbers. If $p(n) \equiv p(n-1) \pmod 2$ for all $n > N$, then $G = (1 - x) P$ is a polynomial
of degree at most $N$ with $G(0) = 1$, and $G E = 1 - x$. So the coefficients of $E$ satisfy a
linear recurrence of order $N$ from degree $2$ on. The gaps between consecutive pentagonal
numbers are unbounded, so $E$ has $N$ consecutive zero coefficients, and the recurrence forces
all later coefficients to vanish. This contradicts the existence of arbitrarily large
pentagonal numbers. Constant parity from some point on is a special case of the assumption.

*References:*
- O. Kolberg, [Note on the parity of the partition function](https://doi.org/10.7146/math.scand.a-10584),
  Math. Scand. 7 (1959), 377–378.
-/


@[expose] public section

namespace Nat

def partitionNumber : ℕ → ℕ := fun n ↦ Fintype.card (Nat.Partition n)

end Nat

/-- `partitionNumber 0 = 1`, copied from
`FormalConjecturesForMathlib/Combinatorics/Enumerative/Partition/Basic.lean`. -/
theorem Nat.partitionNumber_zero : Nat.partitionNumber 0 = 1 := by decide

namespace Kolberg

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

/-- The partition generating function times Euler's product $\prod (1 - x^n)$ is $1$. -/
theorem mk_partitionNumber_mul_pentagonalSeries :
    (mk fun n => (Nat.partitionNumber n : ℤ)) * pentagonalSeries ℤ = 1 := by
  have h3 := (Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ => True)).mul
    (WithPiTopology.hasProd_one_sub_X_pow ℤ)
  have hf : (fun b : ℕ => (if True then ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((b + 1) * j) else 1) *
      (1 - X ^ (b + 1))) = fun _ => 1 := by
    funext b
    rw [ite_eq_left trivial]
    simp only [pow_mul]
    exact WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  have hmk : (mk fun n => ((#(Nat.Partition.restricted n fun _ => True) : ℕ) : ℤ)) =
      mk fun n => (Nat.partitionNumber n : ℤ) := by
    ext n
    rw [coeff_mk, coeff_mk, Nat.partitionNumber, Nat.Partition.restricted]
    simp
  rw [hf, hmk] at h3
  exact h3.unique hasProd_one

/-- Euler's product over `ZMod 2`. -/
noncomputable abbrev E : (ZMod 2)⟦X⟧ := map (Int.castRingHom (ZMod 2)) (pentagonalSeries ℤ)

/-- The partition generating function over `ZMod 2`. -/
noncomputable abbrev P : (ZMod 2)⟦X⟧ := mk fun n => (Nat.partitionNumber n : ZMod 2)

theorem P_mul_E : P * E = 1 := by
  have h := congrArg (map (Int.castRingHom (ZMod 2))) mk_partitionNumber_mul_pentagonalSeries
  rw [map_mul, map_one] at h
  convert h using 2
  ext n
  simp

theorem coeff_E_pentagonal (k : ℤ) : coeff (pentagonal k) E ≠ 0 := by
  rw [coeff_map, coeff_pentagonalSeries_pentagonal]
  rcases Int.isUnit_iff.mp (Units.isUnit (Int.negOnePow k)) with h | h <;> simp [h]

theorem coeff_E_of_notMem {n : ℕ} (h : n ∉ Set.range pentagonal) : coeff n E = 0 := by
  rw [coeff_map, coeff_pentagonalSeries_eq_zero ℤ h, map_zero]

/-- Between $J(3J+1)/2$ and $(J+1)(3J+2)/2$ there are no pentagonal numbers. Taking
$J = N + 1$ gives $N$ consecutive non-pentagonal numbers starting at some $m \ge 2$. -/
theorem exists_gap (N : ℕ) :
    ∃ m, 2 ≤ m ∧ ∀ j, m ≤ j → j < m + N → j ∉ Set.range pentagonal := by
  have hA := two_mul_natCast_pentagonal_neg ((N : ℤ) + 1)
  refine ⟨pentagonal (-((N : ℤ) + 1)) + 1, ?_, ?_⟩
  · have : (1 : ℤ) ≤ pentagonal (-((N : ℤ) + 1)) := by nlinarith
    omega
  · rintro j hj1 hj2 ⟨k, rfl⟩
    have hk := two_mul_natCast_pentagonal k
    have hj1' : (pentagonal (-((N : ℤ) + 1)) : ℤ) + 1 ≤ pentagonal k := by exact_mod_cast hj1
    have hj2' : (pentagonal k : ℤ) < pentagonal (-((N : ℤ) + 1)) + 1 + N := by
      exact_mod_cast hj2
    have hN : (0 : ℤ) ≤ N := by positivity
    rcases le_or_gt ((N : ℤ) + 2) k with h | h
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℤ) ≤ 3 * k + 3 * N + 5)]
    rcases le_or_gt k (-((N : ℤ) + 2)) with h' | h'
    · nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -k - N - 2) (by linarith : (0 : ℤ) ≤ -3 * k + 3 * N + 7)]
    · nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ N + 1 - k) (by linarith : (0 : ℤ) ≤ N + 1 + k)]

theorem exists_pentagonal_ge (M : ℕ) : ∃ k : ℤ, M ≤ pentagonal k := by
  refine ⟨(M : ℤ) + 1, ?_⟩
  have h := two_mul_natCast_pentagonal ((M : ℤ) + 1)
  have : (M : ℤ) ≤ pentagonal ((M : ℤ) + 1) := by nlinarith
  exact_mod_cast this

/-- If $p(n+1) \equiv p(n) \pmod 2$ for all $n \ge N$, we get a contradiction. -/
theorem not_eventually_eq (N : ℕ)
    (h : ∀ n, N ≤ n → (Nat.partitionNumber (n + 1) : ZMod 2) = Nat.partitionNumber n) :
    False := by
  set G : (ZMod 2)⟦X⟧ := (1 - X) * P with hG
  have hGE : G * E = 1 - X := by rw [hG, mul_assoc, P_mul_E, mul_one]
  have hG0 : coeff 0 G = 1 := by
    simp [hG, Nat.partitionNumber_zero]
  have hGN : ∀ i, N < i → coeff i G = 0 := by
    intro i hi
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [hG, sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_mk, coeff_mk, h n (by omega),
      sub_self]
  obtain ⟨m, hm2, hgap⟩ := exists_gap N
  have hzero : ∀ n, m ≤ n → coeff n E = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hmn
      by_cases hlt : n < m + N
      · exact coeff_E_of_notMem (hgap n hmn hlt)
      have h1 : coeff n (G * E) = 0 := by
        rw [hGE, map_sub, coeff_one, coeff_X, ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
      rw [coeff_mul, sum_eq_single (0, n)] at h1
      · rwa [hG0, one_mul] at h1
      · intro x hx hne
        have hx' := mem_antidiagonal.mp hx
        by_cases hxN : N < x.1
        · rw [hGN _ hxN, zero_mul]
        · have hx1 : x.1 ≠ 0 := fun h0 => hne (Prod.ext h0 (by omega))
          rw [ih x.2 (by omega) (by omega), mul_zero]
      · intro h0
        exact absurd (mem_antidiagonal.mpr (zero_add n)) h0
  obtain ⟨k, hk⟩ := exists_pentagonal_ge m
  exact coeff_E_pentagonal k (hzero _ hk)

theorem zmod_two_eq_one {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  revert x
  decide

open Nat in
/-- **Kolberg's theorem** (1959). The partition number $p(n)$ is even for infinitely many $n$
and odd for infinitely many $n$. -/
theorem kolberg :
    {n : ℕ | Even (partitionNumber n)}.Infinite ∧ {n : ℕ | Odd (partitionNumber n)}.Infinite := by
  constructor
  · intro hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    refine not_eventually_eq (B + 1) fun n hn => ?_
    have hodd : ∀ i, B + 1 ≤ i → (partitionNumber i : ZMod 2) = 1 := fun i hi =>
      zmod_two_eq_one fun h0 =>
        absurd (hB (ZMod.natCast_eq_zero_iff_even.mp h0 : i ∈ {n | Even (partitionNumber n)}))
          (by omega)
    rw [hodd n hn, hodd (n + 1) (by omega)]
  · intro hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    refine not_eventually_eq (B + 1) fun n hn => ?_
    have heven : ∀ i, B + 1 ≤ i → (partitionNumber i : ZMod 2) = 0 := fun i hi => by
      by_contra h0
      exact absurd (hB (ZMod.natCast_ne_zero_iff_odd.mp h0 : i ∈ {n | Odd (partitionNumber n)}))
        (by omega)
    rw [heven n hn, heven (n + 1) (by omega)]

end Kolberg

namespace PartitionParity

open Nat Real Filter Topology Asymptotics Polynomial

theorem kolberg :
    {n : ℕ | Even (partitionNumber n)}.Infinite ∧ {n : ℕ | Odd (partitionNumber n)}.Infinite :=
  Kolberg.kolberg

end PartitionParity

end
