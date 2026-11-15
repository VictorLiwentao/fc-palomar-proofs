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
# OEIS A364111: Bala's supercongruences by Coster's method

Let $u(N) = \sum_{k=0}^{N} F(N,k)$ with
$F(N,k) = \binom{N+k-1}{k}^A \binom{2N-2k}{N-k}^B \binom{2k}{k}^C$. OEIS A364111 is
$(A, B, C) = (2, 1, 1)$. For $A \ge 2$, $B, C \ge 1$, a prime $p \ge 5$ and $n, r \ge 1$, the
file proves $u(np^r) \equiv u(np^{r-1}) \pmod{p^{3r}}$, as conjectured by Peter Bala.

Write $N = pN'$ with $N' = np^{r-1}$, so $p^r \mid N$ and $p^{r-1} \mid N'$. No reduction to
$p \nmid n$ is needed. The hypothesis $n \ge 1$ is not used: for $n = 0$ both sides are equal.

*Lemma 1 (carries, `term_dvd`).* If $p^r \mid N$, $0 < k \le N$ and $p^{s+1} \nmid k$, then
$p^{(A+1)(r-s)} \mid F(N,k)$. The identity
$k \binom{N+k-1}{k} = N \binom{N+k-1}{k-1}$ gives $p^{r-s} \mid \binom{N+k-1}{k}$. Kummer's
formula `padicValNat_choose` counts carries. For each $s < i \le r$ the residues
$x = k \bmod p^i$ and $y = (N-k) \bmod p^i$ satisfy $x + y = p^i$. So $2x \ge p^i$ or
$2y \ge p^i$, and $\binom{2k}{k}$ or $\binom{2N-2k}{N-k}$ has a carry at level $i$. Since
$B, C \ge 1$, this adds $r - s$.

*Coster's products (`gstar`).* In `ZMod (p ^ K)` put
$g^*(Z, j) = \prod_{l \le j,\ p \nmid l} (1 + Z/l)$. Splitting $j!$ and the rising products by
residues mod $p$ gives identities in $\mathbb{N}$, and cancelling the unit
$\prod_{l \le pj,\ p \nmid l} l$ gives
$\binom{pX+pj}{pj} = g^*(pX, pj) \binom{X+j}{j}$ and
$\binom{pX+pj-1}{pj} = g^*(pX, pj) \binom{X+j-1}{j}$. For $p \ge 5$ and $p^e \mid k$, the sums
over the units $l \le pk$ satisfy $\sum l^{-2} \equiv 0 \pmod{p^{1+e}}$ (a unit $c$ with
$c^2 \not\equiv 1$ permutes each block) and $\sum l^{-1} \equiv 0 \pmod{p^{2+2e}}$ (pair $l$ with
$pk - l$). A second-order expansion of the product then gives
$g^*(Z, pk) \equiv 1 \pmod{p^{3+s+2e}}$ when $p^{1+s} \mid Z$ and $e \le s$.

*Lemma 3 (recursion, `term_rec`).* If $p^r \mid pN$, $p^m \mid pk$ and $1 \le m \le r$, then
$F(pN, pk) = F(N, k)\,G$ in `ZMod (p ^ K)` with $G \equiv 1 \pmod{p^{3m}}$. Each binomial gets a
factor $g^*$ that is $\equiv 1$ modulo $p^{3m}$ (or $p^{r+2m}$ for the first one).

*Assembly (`u_mul_prime`).* Work in `ZMod (p ^ (3 * r))`. A term with $p \nmid k$ vanishes by
Lemma 1 with $s = 0$, since $(A+1)r \ge 3r$. For $k = pk'$: if $p^r \mid k$, then $G = 1$.
Otherwise $s = v_p(k)$ satisfies $1 \le s < r$. Lemma 1 for $(N', k')$ at level $r-1$ gives
$p^{(A+1)(r-s)} \mid F(N', k')$, so $F(N,k) - F(N',k') = F(N',k')(G-1)$ is divisible by
$p^{(A+1)(r-s)+3s}$, and $(A+1)(r-s) + 3s \ge 3r$ because $A \ge 2$. Summing over the multiples
of $p$ gives $u(pN') \equiv u(N')$.

The method is Coster's, as used by Osburn and Sahu for generalized Domb numbers.

*References:*
- Peter Bala, [A364111](https://oeis.org/A364111), July 7, 2023.
- Robert Osburn and Brundaban Sahu, *A supercongruence for generalized Domb numbers*,
  Funct. Approx. Comment. Math. 48 (2013), 29–36,
  [arXiv:1201.6195](https://arxiv.org/abs/1201.6195).
- M. Coster, *Supercongruences*, PhD thesis, Universiteit Leiden, 1988.
-/

@[expose] public section

open Finset

namespace OeisA364111

/-- Bala's sum $u(N) = \sum_{k=0}^{N} \binom{N+k-1}{k}^A \binom{2N-2k}{N-k}^B \binom{2k}{k}^C$.
At $N = k = 0$ the factor $\binom{-1}{0} = 1$ is `Nat.choose 0 0 = 1`, with the same value. -/
def u (A B C N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (N + 1),
    (N + k - 1).choose k ^ A * (2 * N - 2 * k).choose (N - k) ^ B * (2 * k).choose k ^ C

/-- OEIS A364111: $a(n) = \sum_{k=0}^{n} \binom{n+k-1}{k}^2 \binom{2n-2k}{n-k} \binom{2k}{k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    (n + k - 1).choose k ^ 2 * (2 * n - 2 * k).choose (n - k) * (2 * k).choose k


/-! ### Divisibility helpers in a commutative ring -/

theorem pow_dvd_of_le {M : Type*} [CommRing M] (P : M) {a b : ℕ} {z : M} (hab : a ≤ b)
    (h : P ^ b ∣ z) : P ^ a ∣ z :=
  (pow_dvd_pow P hab).trans h

theorem mul_sub_one_dvd {M : Type*} [CommRing M] {a x y : M} (hx : a ∣ x - 1) (hy : a ∣ y - 1) :
    a ∣ x * y - 1 := by
  have : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right hy _) hx

/-- Second-order expansion of a product `∏ (1 + y i)` when every `y i` is divisible by `P ^ b`. -/
theorem prod_one_add_expand {M : Type*} [CommRing M] (P : M) (b : ℕ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (y : ι → M) (hy : ∀ i ∈ s, P ^ b ∣ y i) :
    P ^ (3 * b) ∣ 2 * ∏ i ∈ s, (1 + y i) -
      (2 + 2 * ∑ i ∈ s, y i + (∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, y i ^ 2) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, sum_insert ha]
    have ih' := ih (fun i hi => hy i (mem_insert_of_mem hi))
    have hya := hy a (mem_insert_self a s)
    have hS : P ^ b ∣ ∑ i ∈ s, y i := dvd_sum (fun i hi => hy i (mem_insert_of_mem hi))
    have hS2 : P ^ (2 * b) ∣ ∑ i ∈ s, y i ^ 2 := dvd_sum (fun i hi => by
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd (hy i (mem_insert_of_mem hi)) 2)
    have hSS : P ^ (2 * b) ∣ (∑ i ∈ s, y i) ^ 2 := by
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hS 2
    have key : 2 * ((1 + y a) * ∏ i ∈ s, (1 + y i)) -
        (2 + 2 * (y a + ∑ i ∈ s, y i) + (y a + ∑ i ∈ s, y i) ^ 2 - (y a ^ 2 + ∑ i ∈ s, y i ^ 2)) =
        (1 + y a) * (2 * ∏ i ∈ s, (1 + y i) -
          (2 + 2 * ∑ i ∈ s, y i + (∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, y i ^ 2)) +
        y a * ((∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, y i ^ 2) := by ring
    rw [key]
    refine dvd_add (dvd_mul_of_dvd_right ih' _) ?_
    have : 3 * b = b + 2 * b := by ring
    rw [this, pow_add]
    exact mul_dvd_mul hya (dvd_sub hSS hS2)

/-! ### Arithmetic in `ZMod (p ^ K)` -/

section ZModPow

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

theorem coprime_pow_of_not_dvd {x : ℕ} (hx : ¬ p ∣ x) (n : ℕ) : Nat.Coprime x (p ^ n) :=
  ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hx).symm.pow_right n

theorem natCast_mul_inv {x : ℕ} (hx : ¬ p ∣ x) :
    (x : ZMod (p ^ K)) * (x : ZMod (p ^ K))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one x (coprime_pow_of_not_dvd hx K)

theorem isUnit_natCast {x : ℕ} (hx : ¬ p ∣ x) : IsUnit (x : ZMod (p ^ K)) :=
  IsUnit.of_mul_eq_one _ (natCast_mul_inv hx)

omit hp in
theorem eq_zero_of_pow_dvd {z : ZMod (p ^ K)} (h : (p : ZMod (p ^ K)) ^ K ∣ z) : z = 0 := by
  obtain ⟨c, hc⟩ := h
  rw [hc, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

omit hp in
theorem not_dvd_two (hp5 : 5 ≤ p) : ¬ p ∣ 2 := fun h => by
  have := Nat.le_of_dvd (by norm_num) h; omega

theorem two_mul_inv_two (hp5 : 5 ≤ p) : (2 : ZMod (p ^ K)) * (2 : ZMod (p ^ K))⁻¹ = 1 := by
  have := natCast_mul_inv (K := K) (not_dvd_two hp5)
  rwa [Nat.cast_ofNat] at this

theorem dvd_of_two_mul_dvd (hp5 : 5 ≤ p) {a : ℕ} {z : ZMod (p ^ K)}
    (h : (p : ZMod (p ^ K)) ^ a ∣ 2 * z) : (p : ZMod (p ^ K)) ^ a ∣ z := by
  have : z = (2 : ZMod (p ^ K))⁻¹ * (2 * z) := by
    rw [← mul_assoc, mul_comm _ (2 : ZMod (p ^ K)), two_mul_inv_two hp5, one_mul]
  rw [this]
  exact dvd_mul_of_dvd_right h _

end ZModPow

theorem castHom_natCast_inv {m n : ℕ} (h : m ∣ n) {x : ℕ} (hx : Nat.Coprime x n) :
    ZMod.castHom h (ZMod m) ((x : ZMod n)⁻¹) = (x : ZMod m)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  rw [← map_natCast (ZMod.castHom h (ZMod m)) x, ← map_mul, ZMod.coe_mul_inv_eq_one x hx, map_one]

section ZModPow2

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

theorem pow_dvd_of_castHom_eq_zero {u : ℕ} (hu : u ≤ K) (z : ZMod (p ^ K))
    (hz : ZMod.castHom (pow_dvd_pow p hu) (ZMod (p ^ u)) z = 0) :
    (p : ZMod (p ^ K)) ^ u ∣ z := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have h1 : ((z.val : ℕ) : ZMod (p ^ u)) = 0 := by
    rw [← map_natCast (ZMod.castHom (pow_dvd_pow p hu) (ZMod (p ^ u))), ZMod.natCast_zmod_val]
    exact hz
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨(c : ZMod (p ^ K)), ?_⟩
  rw [← ZMod.natCast_zmod_val z, hc, Nat.cast_mul, Nat.cast_pow]

end ZModPow2

/-! ### Block sums of inverse squares -/

/-- `x⁻²` in `ZMod (p ^ K)` when `p ∤ x`, and `0` when `p ∣ x`. -/
def invSq (p K x : ℕ) : ZMod (p ^ K) := if p ∣ x then 0 else ((x : ZMod (p ^ K))⁻¹) ^ 2

theorem castHom_invSq {p : ℕ} [hp : Fact p.Prime] {u v : ℕ} (h : p ^ u ∣ p ^ v) (x : ℕ) :
    ZMod.castHom h (ZMod (p ^ u)) (invSq p v x) = invSq p u x := by
  unfold invSq
  by_cases hx : p ∣ x
  · simp [hx]
  · rw [ite_eq_right hx, ite_eq_right hx, map_pow,
      castHom_natCast_inv h (((Nat.Prime.coprime_iff_not_dvd hp.out).2 hx).symm.pow_right v)]

theorem sum_range_natCast {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M] (H : ZMod n → M) :
    ∑ x ∈ range n, H (x : ZMod n) = ∑ z : ZMod n, H z := by
  refine Finset.sum_nbij' (fun x => (x : ZMod n)) (fun z => z.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact mem_univ _
  · intro a _; exact mem_range.2 (ZMod.val_lt a)
  · intro a ha; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 ha)]
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro a _; rfl

open Classical in
/-- `z⁻²` on the units of `ZMod n`, and `0` elsewhere. -/
noncomputable def unitInvSq {n : ℕ} (z : ZMod n) : ZMod n := if IsUnit z then (z⁻¹) ^ 2 else 0

theorem sum_unitInvSq {n : ℕ} [NeZero n] (h2 : IsUnit (2 : ZMod n)) (h3 : IsUnit (3 : ZMod n)) :
    ∑ z : ZMod n, unitInvSq z = 0 := by
  obtain ⟨t, ht⟩ := h2
  have h2u : IsUnit (2 : ZMod n) := ht ▸ t.isUnit
  have h22 : (2 : ZMod n) * (2 : ZMod n)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2u
  have key : ∀ z : ZMod n, unitInvSq ((t : ZMod n) * z) = (2 : ZMod n)⁻¹ ^ 2 * unitInvSq z := by
    intro z
    rw [ht]
    unfold unitInvSq
    by_cases hz : IsUnit z
    · rw [ite_eq_left (h2u.mul hz), ite_eq_left hz]
      have : ((2 : ZMod n) * z)⁻¹ = (2 : ZMod n)⁻¹ * z⁻¹ := by
        apply ZMod.inv_eq_of_mul_eq_one
        calc (2 : ZMod n) * z * (2⁻¹ * z⁻¹) = (2 * 2⁻¹) * (z * z⁻¹) := by ring
          _ = 1 := by rw [h22, ZMod.mul_inv_of_unit _ hz, one_mul]
      rw [this]; ring
    · rw [ite_eq_right (fun h => hz (isUnit_of_mul_isUnit_right h)), ite_eq_right hz, mul_zero]
  have h4 : ∑ z : ZMod n, unitInvSq z = (2 : ZMod n)⁻¹ ^ 2 * ∑ z : ZMod n, unitInvSq z := by
    calc ∑ z : ZMod n, unitInvSq z = ∑ z : ZMod n, unitInvSq ((t : ZMod n) * z) :=
          (Equiv.sum_comp (Units.mulLeft t) unitInvSq).symm
      _ = ∑ z : ZMod n, (2 : ZMod n)⁻¹ ^ 2 * unitInvSq z := sum_congr rfl (fun z _ => key z)
      _ = _ := (mul_sum _ _ _).symm
  have h3S : (3 : ZMod n) * ∑ z : ZMod n, unitInvSq z = 0 := by
    linear_combination 4 * h4 + (∑ z : ZMod n, unitInvSq z) * (2 * (2 : ZMod n)⁻¹ + 1) * h22
  exact (h3.mul_right_eq_zero).1 h3S

section Blocks

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

theorem sum_block_invSq_self (hp5 : 5 ≤ p) {u : ℕ} (hu : 1 ≤ u) (D : ℕ) :
    ∑ i ∈ range (p ^ u), invSq p u (D * p ^ u + i) = 0 := by
  have : NeZero (p ^ u) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpu : p ∣ p ^ u := dvd_pow_self p (by omega)
  have e : ∀ i, invSq p u (D * p ^ u + i) = unitInvSq (i : ZMod (p ^ u)) := by
    intro i
    unfold invSq unitInvSq
    have hcast : ((D * p ^ u + i : ℕ) : ZMod (p ^ u)) = (i : ZMod (p ^ u)) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_self, mul_zero,
        zero_add]
    have hdvd : p ∣ D * p ^ u + i ↔ p ∣ i := Nat.dvd_add_right (dvd_mul_of_dvd_right hpu D)
    have hunit : IsUnit (i : ZMod (p ^ u)) ↔ ¬ p ∣ i := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
        Nat.Prime.coprime_iff_not_dvd hp.out]
    by_cases hi : p ∣ i
    · rw [ite_eq_left (hdvd.2 hi), ite_eq_right (fun h => (hunit.1 h) hi)]
    · rw [ite_eq_right (fun h => hi (hdvd.1 h)), ite_eq_left (hunit.2 hi), hcast]
  have h2 : IsUnit (2 : ZMod (p ^ u)) := by
    have := (ZMod.isUnit_iff_coprime 2 (p ^ u)).2
      (((Nat.coprime_primes Nat.prime_two hp.out).2 (by omega)).pow_right u)
    rwa [Nat.cast_ofNat] at this
  have h3 : IsUnit (3 : ZMod (p ^ u)) := by
    have := (ZMod.isUnit_iff_coprime 3 (p ^ u)).2
      (((Nat.coprime_primes Nat.prime_three hp.out).2 (by omega)).pow_right u)
    rwa [Nat.cast_ofNat] at this
  calc ∑ i ∈ range (p ^ u), invSq p u (D * p ^ u + i)
      = ∑ i ∈ range (p ^ u), unitInvSq (i : ZMod (p ^ u)) := sum_congr rfl (fun i _ => e i)
    _ = ∑ z : ZMod (p ^ u), unitInvSq z := sum_range_natCast unitInvSq
    _ = 0 := sum_unitInvSq h2 h3

/-- Block sums of `x⁻²` (Lemma 3): over the units of a block of length `p ^ u`, for `p ≥ 5`. -/
theorem block_invSq (hp5 : 5 ≤ p) {u : ℕ} (hu : 1 ≤ u) (D : ℕ) :
    (p : ZMod (p ^ K)) ^ u ∣ ∑ i ∈ range (p ^ u), invSq p K (D * p ^ u + i) := by
  rcases le_or_gt u K with huK | huK
  · apply pow_dvd_of_castHom_eq_zero huK
    rw [map_sum]
    simp_rw [castHom_invSq]
    exact sum_block_invSq_self hp5 hu D
  · have h : p ^ K ∣ p ^ u := pow_dvd_pow p huK.le
    have : ∑ i ∈ range (p ^ u), invSq p K (D * p ^ u + i) = 0 := by
      rw [← map_zero (ZMod.castHom h (ZMod (p ^ K))), ← sum_block_invSq_self hp5 hu D, map_sum]
      simp_rw [castHom_invSq]
    rw [this]
    exact dvd_zero _

theorem prefix_invSq (hp5 : 5 ≤ p) {u : ℕ} (hu : 1 ≤ u) (L : ℕ) :
    (p : ZMod (p ^ K)) ^ u ∣ ∑ x ∈ range (L * p ^ u), invSq p K x := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.succ_mul, sum_range_add]
    exact dvd_add ih (block_invSq hp5 hu L)

/-- The harmonic sum over the units in `[1, p k]` is divisible by `p ^ (2 + 2 e)` when
`p ^ e ∣ k`. -/
theorem harmonic_dvd (hp5 : 5 ≤ p) {e k : ℕ} (hk : p ^ e ∣ k) :
    (p : ZMod (p ^ K)) ^ (2 + 2 * e) ∣
      ∑ x ∈ range (p * k + 1), (if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹) := by
  obtain ⟨k₀, hk₀⟩ := hk
  have hpn : p ∣ p * k := dvd_mul_right p k
  have hnP : (p : ZMod (p ^ K)) ^ (1 + e) ∣ ((p * k : ℕ) : ZMod (p ^ K)) :=
    ⟨k₀, by rw [hk₀]; push_cast; ring⟩
  have hnL : p * k = k₀ * p ^ (1 + e) := by rw [hk₀]; ring
  set n := p * k with hn
  set f : ℕ → ZMod (p ^ K) := fun x => if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹ with hf
  have hrefl : ∑ x ∈ range (n + 1), f x = ∑ x ∈ range (n + 1), f (n - x) := by
    have := Finset.sum_range_reflect f (n + 1)
    simp only [Nat.add_sub_cancel] at this
    exact this.symm
  set E : ℕ → ZMod (p ^ K) := fun x =>
    if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹ ^ 2 * ((n - x : ℕ) : ZMod (p ^ K))⁻¹ with hE
  have hterm : ∀ x ∈ range (n + 1),
      f x + f (n - x) = (n : ZMod (p ^ K)) * (- invSq p K x + n * E x) := by
    intro x hx
    have hxn : x ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hx)
    by_cases hpx : p ∣ x
    · have h' : p ∣ n - x := Nat.dvd_sub hpn hpx
      simp [hf, hE, invSq, hpx, h']
    · have hpnx : ¬ p ∣ n - x := fun h => hpx (by
        have := Nat.dvd_sub hpn h; rwa [Nat.sub_sub_self hxn] at this)
      have ha := natCast_mul_inv (K := K) hpx
      have hb := natCast_mul_inv (K := K) hpnx
      have hab : (x : ZMod (p ^ K)) + ((n - x : ℕ) : ZMod (p ^ K)) = n := by
        rw [← Nat.cast_add, Nat.add_sub_cancel' hxn]
      simp only [hf, hE, invSq, ite_eq_right hpx, ite_eq_right hpnx]
      rw [← hab]
      linear_combination
        (-((n - x : ℕ) : ZMod (p ^ K))⁻¹ - (x : ZMod (p ^ K))⁻¹ * ((n - x : ℕ) : ZMod (p ^ K))⁻¹ *
          ((x : ZMod (p ^ K)) + ((n - x : ℕ) : ZMod (p ^ K)))) * ha +
        (-(x : ZMod (p ^ K))⁻¹ - (x : ZMod (p ^ K))⁻¹ ^ 2 *
          ((x : ZMod (p ^ K)) + ((n - x : ℕ) : ZMod (p ^ K)))) * hb
  have h2H : 2 * ∑ x ∈ range (n + 1), f x =
      (n : ZMod (p ^ K)) * ∑ x ∈ range (n + 1), (- invSq p K x + n * E x) := by
    calc 2 * ∑ x ∈ range (n + 1), f x
        = ∑ x ∈ range (n + 1), f x + ∑ x ∈ range (n + 1), f (n - x) := by rw [two_mul, ← hrefl]
      _ = ∑ x ∈ range (n + 1), (f x + f (n - x)) := sum_add_distrib.symm
      _ = ∑ x ∈ range (n + 1), (n : ZMod (p ^ K)) * (- invSq p K x + n * E x) :=
          sum_congr rfl hterm
      _ = _ := (mul_sum _ _ _).symm
  have hQ : (p : ZMod (p ^ K)) ^ (1 + e) ∣ ∑ x ∈ range (n + 1), invSq p K x := by
    rw [sum_range_succ, show invSq p K n = 0 from ite_eq_left hpn, add_zero, hnL]
    exact prefix_invSq hp5 (by omega) k₀
  have hin : (p : ZMod (p ^ K)) ^ (1 + e) ∣ ∑ x ∈ range (n + 1), (- invSq p K x + n * E x) := by
    rw [sum_add_distrib, sum_neg_distrib]
    exact dvd_add (dvd_neg.2 hQ) (dvd_sum fun x _ => dvd_mul_of_dvd_left hnP _)
  apply dvd_of_two_mul_dvd hp5
  rw [h2H, show 2 + 2 * e = (1 + e) + (1 + e) by ring, pow_add]
  exact mul_dvd_mul hnP hin

/-- A Jacobsthal-type bound: `∏ (1 + Z / l)` over the units `l ≤ p k` is `≡ 1` modulo
`p ^ (3 + s + 2 e)` when `p ^ (1 + s) ∣ Z`, `p ^ e ∣ k` and `e ≤ s`. -/
theorem jacobsthal_prod (hp5 : 5 ≤ p) {s e k : ℕ} (hes : e ≤ s) (hk : p ^ e ∣ k)
    (Z : ZMod (p ^ K)) (hZ : (p : ZMod (p ^ K)) ^ (1 + s) ∣ Z) :
    (p : ZMod (p ^ K)) ^ (3 + s + 2 * e) ∣
      (∏ l ∈ range (p * k),
        if p ∣ l + 1 then 1 else 1 + Z * ((l + 1 : ℕ) : ZMod (p ^ K))⁻¹) - 1 := by
  set y : ℕ → ZMod (p ^ K) :=
    fun l => if p ∣ l + 1 then 0 else Z * ((l + 1 : ℕ) : ZMod (p ^ K))⁻¹ with hy
  have hprod : (∏ l ∈ range (p * k),
      if p ∣ l + 1 then 1 else 1 + Z * ((l + 1 : ℕ) : ZMod (p ^ K))⁻¹) =
      ∏ l ∈ range (p * k), (1 + y l) := by
    refine prod_congr rfl (fun l _ => ?_)
    simp only [hy]
    split_ifs <;> simp
  have hyd : ∀ l ∈ range (p * k), (p : ZMod (p ^ K)) ^ (1 + s) ∣ y l := by
    intro l _
    simp only [hy]
    split_ifs
    · exact dvd_zero _
    · exact dvd_mul_of_dvd_left hZ _
  have hexp := prod_one_add_expand (p : ZMod (p ^ K)) (1 + s) (range (p * k)) y hyd
  have hσ1 : ∑ l ∈ range (p * k), y l =
      Z * ∑ x ∈ range (p * k + 1), (if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹) := by
    rw [sum_range_succ', ite_eq_left (dvd_zero p), add_zero, mul_sum]
    refine sum_congr rfl (fun l _ => ?_)
    simp only [hy]
    split_ifs <;> simp
  have h0 : invSq p K 0 = 0 := ite_eq_left (dvd_zero p)
  have hσ2 : ∑ l ∈ range (p * k), y l ^ 2 = Z ^ 2 * ∑ x ∈ range (p * k + 1), invSq p K x := by
    rw [sum_range_succ', h0, add_zero, mul_sum]
    refine sum_congr rfl (fun l _ => ?_)
    simp only [hy, invSq]
    split_ifs <;> ring
  have hH := harmonic_dvd (K := K) hp5 hk
  have hQ : (p : ZMod (p ^ K)) ^ (1 + e) ∣ ∑ x ∈ range (p * k + 1), invSq p K x := by
    obtain ⟨k₀, hk₀⟩ := hk
    rw [sum_range_succ, show invSq p K (p * k) = 0 from ite_eq_left (dvd_mul_right p k), add_zero,
      show p * k = k₀ * p ^ (1 + e) by rw [hk₀]; ring]
    exact prefix_invSq hp5 (by omega) k₀
  rw [hσ1, hσ2] at hexp
  rw [hprod]
  apply dvd_of_two_mul_dvd hp5
  set H := ∑ x ∈ range (p * k + 1), (if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹)
  set Q := ∑ x ∈ range (p * k + 1), invSq p K x
  set Pr := ∏ l ∈ range (p * k), (1 + y l)
  have key : 2 * (Pr - 1) = (2 * Pr - (2 + 2 * (Z * H) + (Z * H) ^ 2 - Z ^ 2 * Q)) +
      (2 * (Z * H) + (Z * H) ^ 2 - Z ^ 2 * Q) := by ring
  rw [key]
  have hZH : (p : ZMod (p ^ K)) ^ (3 + s + 2 * e) ∣ Z * H := by
    rw [show 3 + s + 2 * e = (1 + s) + (2 + 2 * e) by ring, pow_add]
    exact mul_dvd_mul hZ hH
  refine dvd_add (pow_dvd_of_le _ (by omega) hexp) (dvd_sub (dvd_add
    (dvd_mul_of_dvd_right hZH _) (dvd_pow hZH (by norm_num))) ?_)
  have hZ2 : (p : ZMod (p ^ K)) ^ (2 * (1 + s)) ∣ Z ^ 2 := by
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hZ 2
  have := mul_dvd_mul hZ2 hQ
  rw [← pow_add] at this
  exact pow_dvd_of_le _ (by omega) this

end Blocks


/-! ### Products and sums over residue classes -/

@[to_additive sum_range_mul_ite]
theorem prod_range_mul_ite {M : Type*} [CommMonoid M] {p c : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (hc : c < p) (hP : ∀ b i, i < p → (P (p * b + i) ↔ i = c)) (g : ℕ → M) (j : ℕ) :
    ∏ l ∈ range (p * j), (if P l then g l else 1) = ∏ b ∈ range j, g (p * b + c) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, prod_range_add, ih, prod_range_succ]
    congr 1
    rw [prod_eq_single_of_mem c (mem_range.2 hc)]
    · rw [ite_eq_left ((hP j c hc).2 rfl)]
    · intro i hi hic
      rw [ite_eq_right (fun h => hic ((hP j i (mem_range.1 hi)).1 h))]

theorem prod_range_mul_split {M : Type*} [CommMonoid M] {p c : ℕ} (P : ℕ → Prop)
    [DecidablePred P] (hc : c < p) (hP : ∀ b i, i < p → (P (p * b + i) ↔ i = c)) (g : ℕ → M)
    (j : ℕ) :
    ∏ l ∈ range (p * j), g l =
      (∏ l ∈ range (p * j), if P l then 1 else g l) * ∏ b ∈ range j, g (p * b + c) := by
  rw [← prod_range_mul_ite P hc hP g j, ← prod_mul_distrib]
  refine prod_congr rfl (fun l _ => ?_)
  split_ifs <;> simp

theorem dvd_mul_add_iff {p : ℕ} (b i : ℕ) (hi : i < p) : p ∣ p * b + i ↔ i = 0 := by
  rw [Nat.dvd_add_right (dvd_mul_right p b)]
  constructor
  · intro h; exact Nat.eq_zero_of_dvd_of_lt h hi
  · rintro rfl; exact dvd_zero p

theorem dvd_mul_add_succ_iff {p : ℕ} (b i : ℕ) (hi : i < p) :
    p ∣ p * b + i + 1 ↔ i = p - 1 := by
  rw [add_assoc, Nat.dvd_add_right (dvd_mul_right p b)]
  constructor
  · intro h
    have := Nat.le_of_dvd (Nat.succ_pos i) h
    omega
  · intro h; rw [h, Nat.sub_add_cancel (by omega)]

/-- Multiples of `p` in `[0, p M]` carry the sum. -/
theorem sum_range_mul_succ_ite {M : Type*} [AddCommMonoid M] {p : ℕ} (hp : 0 < p) (f : ℕ → M)
    (L : ℕ) :
    ∑ k ∈ range (p * L + 1), (if p ∣ k then f (k / p) else 0) = ∑ k ∈ range (L + 1), f k := by
  have h := sum_range_mul_ite (fun l => p ∣ l) hp (fun b i hi => dvd_mul_add_iff b i hi)
    (fun l => f (l / p)) L
  simp only [add_zero, Nat.mul_div_cancel_left _ hp] at h
  rw [sum_range_succ, h, sum_range_succ, ite_eq_left (dvd_mul_right p L),
    Nat.mul_div_cancel_left _ hp]

/-! ### Splitting factorials and rising products -/

section Split

variable {p : ℕ}

theorem factorial_split (hp : 0 < p) (j : ℕ) :
    (p * j).factorial =
      (∏ l ∈ range (p * j), if p ∣ l + 1 then 1 else (l + 1)) * (p ^ j * j.factorial) := by
  rw [← prod_range_add_one_eq_factorial, prod_range_mul_split (fun l => p ∣ l + 1) (c := p - 1)
    (by omega) (fun b i hi => dvd_mul_add_succ_iff b i hi) (fun l => l + 1)]
  congr 1
  rw [← prod_range_add_one_eq_factorial, show p ^ j = ∏ _b ∈ range j, p by simp,
    ← prod_mul_distrib]
  refine prod_congr rfl (fun b _ => ?_)
  rw [mul_add, mul_one]
  omega

theorem asc_split0 (hp : 0 < p) (X j : ℕ) :
    ∏ l ∈ range (p * j), (p * X + l) =
      (∏ l ∈ range (p * j), if p ∣ l then 1 else (p * X + l)) *
        (p ^ j * ∏ b ∈ range j, (X + b)) := by
  rw [prod_range_mul_split (fun l => p ∣ l) (c := 0) hp (fun b i hi => dvd_mul_add_iff b i hi)]
  congr 1
  rw [show p ^ j = ∏ _b ∈ range j, p by simp, ← prod_mul_distrib]
  refine prod_congr rfl (fun b _ => ?_)
  ring

theorem asc_split1 (hp : 0 < p) (X j : ℕ) :
    ∏ l ∈ range (p * j), (p * X + l + 1) =
      (∏ l ∈ range (p * j), if p ∣ l + 1 then 1 else (p * X + l + 1)) *
        (p ^ j * ∏ b ∈ range j, (X + b + 1)) := by
  rw [prod_range_mul_split (fun l => p ∣ l + 1) (c := p - 1) (by omega)
    (fun b i hi => dvd_mul_add_succ_iff b i hi)]
  congr 1
  rw [show p ^ j = ∏ _b ∈ range j, p by simp, ← prod_mul_distrib]
  refine prod_congr rfl (fun b _ => ?_)
  have : p * X + (p * b + (p - 1)) + 1 = p * X + p * b + p := by omega
  rw [this]
  ring

theorem choose_mul_factorial_succ (n k : ℕ) :
    (n + k).choose k * k.factorial = ∏ i ∈ range k, (n + i + 1) := by
  rw [mul_comm, ← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range]
  exact prod_congr rfl (fun i _ => by ring)

theorem choose_mul_factorial_pred (n k : ℕ) :
    (n + k - 1).choose k * k.factorial = ∏ i ∈ range k, (n + i) := by
  rw [mul_comm, ← Nat.ascFactorial_eq_factorial_mul_choose', Nat.ascFactorial_eq_prod_range]

theorem choose_split_succ_nat (hp : 0 < p) (X j : ℕ) :
    (p * X + p * j).choose (p * j) * (∏ l ∈ range (p * j), if p ∣ l + 1 then 1 else (l + 1)) =
      (∏ l ∈ range (p * j), if p ∣ l + 1 then 1 else (p * X + l + 1)) * (X + j).choose j := by
  have h1 := choose_mul_factorial_succ (p * X) (p * j)
  rw [factorial_split hp, asc_split1 hp, ← choose_mul_factorial_succ X j] at h1
  refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < p ^ j * j.factorial) ?_
  calc _ = (p * X + p * j).choose (p * j) *
        ((∏ l ∈ range (p * j), if p ∣ l + 1 then 1 else (l + 1)) * (p ^ j * j.factorial)) := by
          ring
    _ = _ := h1
    _ = _ := by ring

theorem prod_shift (X j : ℕ) :
    (∏ l ∈ range (p * j), if p ∣ l then 1 else (p * X + l)) =
      ∏ l ∈ range (p * j), if p ∣ l + 1 then 1 else (p * X + l + 1) := by
  have h := prod_range_succ' (fun l => if p ∣ l then 1 else (p * X + l)) (p * j)
  rw [prod_range_succ, ite_eq_left (dvd_mul_right p j), ite_eq_left (dvd_zero p)] at h
  simp only [mul_one] at h
  rw [h]
  exact prod_congr rfl (fun l _ => by rw [add_assoc])

theorem choose_split_pred_nat (hp : 0 < p) (X j : ℕ) :
    (p * X + p * j - 1).choose (p * j) *
        (∏ l ∈ range (p * j), if p ∣ l + 1 then 1 else (l + 1)) =
      (∏ l ∈ range (p * j), if p ∣ l + 1 then 1 else (p * X + l + 1)) *
        (X + j - 1).choose j := by
  have h1 := choose_mul_factorial_pred (p * X) (p * j)
  rw [factorial_split hp, asc_split0 hp, ← choose_mul_factorial_pred X j, prod_shift] at h1
  refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < p ^ j * j.factorial) ?_
  calc _ = (p * X + p * j - 1).choose (p * j) *
        ((∏ l ∈ range (p * j), if p ∣ l + 1 then 1 else (l + 1)) * (p ^ j * j.factorial)) := by
          ring
    _ = _ := h1
    _ = _ := by ring

end Split

/-! ### Coster's products in `ZMod (p ^ K)` -/

section Coster

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

/-- Coster's product `∏ (1 + Z / l)` over the integers `1 ≤ l ≤ j` prime to `p`. -/
def gstar (p K : ℕ) (Z : ZMod (p ^ K)) (j : ℕ) : ZMod (p ^ K) :=
  ∏ l ∈ range j, if p ∣ l + 1 then 1 else 1 + Z * ((l + 1 : ℕ) : ZMod (p ^ K))⁻¹

theorem gstar_mul_units (X j : ℕ) :
    gstar p K (X : ZMod (p ^ K)) j *
        ((∏ l ∈ range j, if p ∣ l + 1 then 1 else (l + 1) : ℕ) : ZMod (p ^ K)) =
      ((∏ l ∈ range j, if p ∣ l + 1 then 1 else (X + l + 1) : ℕ) : ZMod (p ^ K)) := by
  unfold gstar
  rw [Nat.cast_prod, Nat.cast_prod, ← prod_mul_distrib]
  refine prod_congr rfl (fun l _ => ?_)
  by_cases h : p ∣ l + 1
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
    have := natCast_mul_inv (K := K) h
    push_cast at this ⊢
    linear_combination (X : ZMod (p ^ K)) * this

theorem isUnit_units_prod (j : ℕ) :
    IsUnit ((∏ l ∈ range j, if p ∣ l + 1 then 1 else (l + 1) : ℕ) : ZMod (p ^ K)) := by
  rw [ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.prod_left (fun l _ => ?_)
  split_ifs with h
  · exact Nat.coprime_one_left _
  · exact coprime_pow_of_not_dvd h K

theorem choose_split_succ (X j : ℕ) :
    ((p * X + p * j).choose (p * j) : ZMod (p ^ K)) =
      gstar p K ((p * X : ℕ) : ZMod (p ^ K)) (p * j) * ((X + j).choose j : ZMod (p ^ K)) := by
  have h := congrArg (fun n : ℕ => (n : ZMod (p ^ K))) (choose_split_succ_nat hp.out.pos X j)
  simp only [Nat.cast_mul] at h
  rw [← gstar_mul_units] at h
  refine (isUnit_units_prod (p * j)).mul_right_cancel ?_
  rw [h]
  ring

theorem choose_split_pred (X j : ℕ) :
    ((p * X + p * j - 1).choose (p * j) : ZMod (p ^ K)) =
      gstar p K ((p * X : ℕ) : ZMod (p ^ K)) (p * j) * ((X + j - 1).choose j : ZMod (p ^ K)) := by
  have h := congrArg (fun n : ℕ => (n : ZMod (p ^ K))) (choose_split_pred_nat hp.out.pos X j)
  simp only [Nat.cast_mul] at h
  rw [← gstar_mul_units] at h
  refine (isUnit_units_prod (p * j)).mul_right_cancel ?_
  rw [h]
  ring

theorem gstar_sub_one_dvd (hp5 : 5 ≤ p) {m t j X : ℕ} (hm : 1 ≤ m) (hmt : m ≤ t)
    (hj : p ^ m ∣ p * j) (hX : p ^ t ∣ X) :
    (p : ZMod (p ^ K)) ^ (t + 2 * m) ∣ gstar p K (X : ZMod (p ^ K)) (p * j) - 1 := by
  have hj' : p ^ (m - 1) ∣ j := by
    rw [show m = (m - 1) + 1 by omega, pow_succ'] at hj
    exact Nat.dvd_of_mul_dvd_mul_left hp.out.pos hj
  have hZ : (p : ZMod (p ^ K)) ^ (1 + (t - 1)) ∣ (X : ZMod (p ^ K)) := by
    rw [show 1 + (t - 1) = t by omega, ← Nat.cast_pow]
    exact Nat.cast_dvd_cast hX
  have := jacobsthal_prod (K := K) hp5 (s := t - 1) (e := m - 1) (k := j) (by omega) hj' _ hZ
  rw [show 3 + (t - 1) + 2 * (m - 1) = t + 2 * m by omega] at this
  exact this

end Coster


/-! ### The summand -/

/-- The `k`-th summand of `u A B C N`. -/
def term (A B C N k : ℕ) : ℕ :=
  (N + k - 1).choose k ^ A * (2 * N - 2 * k).choose (N - k) ^ B * (2 * k).choose k ^ C

theorem u_eq_sum (A B C N : ℕ) : u A B C N = ∑ k ∈ range (N + 1), term A B C N k := rfl

/-! ### Lemma 1: carries -/

section Carries

variable {p : ℕ} [hp : Fact p.Prime]

theorem choose_pred_dvd {N k s r : ℕ} (hN : p ^ r ∣ N) (hk : 0 < k)
    (hks : ¬ p ^ (s + 1) ∣ k) : p ^ (r - s) ∣ (N + k - 1).choose k := by
  have key : (N + k - 1).choose k * k = (N + k - 1).choose (k - 1) * N := by
    have := Nat.choose_succ_right_eq (N + k - 1) (k - 1)
    rwa [Nat.sub_add_cancel hk, show N + k - 1 - (k - 1) = N by omega] at this
  by_cases hc0 : (N + k - 1).choose k = 0
  · rw [hc0]; exact dvd_zero _
  have hk0 : k ≠ 0 := by omega
  have hdvd : p ^ r ∣ (N + k - 1).choose k * k := key ▸ dvd_mul_of_dvd_right hN _
  rw [padicValNat_dvd_iff_le (mul_ne_zero hc0 hk0), padicValNat.mul hc0 hk0] at hdvd
  have hvk : padicValNat p k ≤ s := by
    by_contra h
    exact hks ((padicValNat_dvd_iff_le hk0).2 (by omega))
  exact (padicValNat_dvd_iff_le hc0).2 (by omega)

theorem central_pair {N k s r : ℕ} (hN : p ^ r ∣ N) (hkN : k ≤ N)
    (hks : ¬ p ^ (s + 1) ∣ k) :
    r - s ≤ padicValNat p ((2 * k).choose k) + padicValNat p ((2 * (N - k)).choose (N - k)) := by
  rcases le_or_gt r s with hrs | hsr
  · omega
  have hk0 : k ≠ 0 := by rintro rfl; exact hks (dvd_zero _)
  have hN0 : 0 < N := by omega
  have hpr : p ^ r ≤ N := Nat.le_of_dvd hN0 hN
  have hrN : r < N := lt_of_lt_of_le (Nat.lt_pow_self hp.out.one_lt) hpr
  have hb1 : Nat.log p (2 * k) < 2 * N + 1 := lt_of_le_of_lt (Nat.log_le_self _ _) (by omega)
  have hb2 : Nat.log p (2 * (N - k)) < 2 * N + 1 :=
    lt_of_le_of_lt (Nat.log_le_self _ _) (by omega)
  rw [padicValNat_choose (by omega) hb1, padicValNat_choose (by omega) hb2]
  have hsub : Ico (s + 1) (r + 1) ⊆
      {i ∈ Ico 1 (2 * N + 1) | p ^ i ≤ k % p ^ i + (2 * k - k) % p ^ i} ∪
        {i ∈ Ico 1 (2 * N + 1) |
          p ^ i ≤ (N - k) % p ^ i + (2 * (N - k) - (N - k)) % p ^ i} := by
    intro i hi
    rw [mem_Ico] at hi
    rw [mem_union, mem_filter, mem_filter, mem_Ico]
    have hpi : 0 < p ^ i := pow_pos hp.out.pos i
    have hiN : p ^ i ∣ N := (pow_dvd_pow p (by omega)).trans hN
    have hik : ¬ p ^ i ∣ k := fun h => hks ((pow_dvd_pow p (by omega)).trans h)
    have hx0 : k % p ^ i ≠ 0 := fun h => hik (Nat.dvd_of_mod_eq_zero h)
    have hxy : p ^ i ∣ k % p ^ i + (N - k) % p ^ i := by
      apply Nat.dvd_of_mod_eq_zero
      rw [← Nat.add_mod, Nat.add_sub_cancel' hkN]
      exact Nat.mod_eq_zero_of_dvd hiN
    have hx := Nat.mod_lt k hpi
    have hy := Nat.mod_lt (N - k) hpi
    have heq : k % p ^ i + (N - k) % p ^ i = p ^ i :=
      Nat.eq_of_dvd_of_lt_two_mul (fun h => hx0 (Nat.eq_zero_of_add_eq_zero_right h)) hxy
        (by omega)
    rw [show 2 * k - k = k by omega, show 2 * (N - k) - (N - k) = N - k by omega]
    omega
  calc r - s = #(Ico (s + 1) (r + 1)) := by simp
    _ ≤ #(_ ∪ _) := card_le_card hsub
    _ ≤ _ := card_union_le _ _

/-- Lemma 1: `p ^ ((A + 1) (r - s))` divides the `k`-th term when `p ^ r ∣ N` and
`p ^ (s + 1) ∤ k`. -/
theorem term_dvd {A B C : ℕ} (hB : 1 ≤ B) (hC : 1 ≤ C) {N k s r : ℕ}
    (hN : p ^ r ∣ N) (hk : 0 < k) (hkN : k ≤ N) (hks : ¬ p ^ (s + 1) ∣ k) :
    p ^ ((A + 1) * (r - s)) ∣ term A B C N k := by
  unfold term
  rw [show 2 * N - 2 * k = 2 * (N - k) by omega]
  have h0 := choose_pred_dvd hN hk hks
  have h12 := central_pair hN hkN hks
  have e0 : p ^ (A * (r - s)) ∣ (N + k - 1).choose k ^ A := by
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h0 A
  have e2 : p ^ (B * padicValNat p ((2 * (N - k)).choose (N - k))) ∣
      (2 * (N - k)).choose (N - k) ^ B := by
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd pow_padicValNat_dvd B
  have e1 : p ^ (C * padicValNat p ((2 * k).choose k)) ∣ (2 * k).choose k ^ C := by
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd pow_padicValNat_dvd C
  have hprod := mul_dvd_mul (mul_dvd_mul e0 e2) e1
  rw [← pow_add, ← pow_add] at hprod
  refine (pow_dvd_pow p ?_).trans hprod
  have := Nat.le_mul_of_pos_left (padicValNat p ((2 * (N - k)).choose (N - k))) hB
  have := Nat.le_mul_of_pos_left (padicValNat p ((2 * k).choose k)) hC
  rw [add_mul, one_mul]
  omega

end Carries

/-! ### Lemma 3: the recursions -/

section Recursion

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

theorem pow_sub_one_dvd' {M : Type*} [CommRing M] {d x : M} (h : d ∣ x - 1) (n : ℕ) :
    d ∣ x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact mul_sub_one_dvd ih h

theorem choose_pred_rec (hp5 : 5 ≤ p) {N k m r : ℕ} (hm : 1 ≤ m) (hmr : m ≤ r)
    (hN : p ^ r ∣ p * N) (hk : p ^ m ∣ p * k) :
    ∃ g : ZMod (p ^ K), (((p * N + p * k - 1).choose (p * k) : ℕ) : ZMod (p ^ K)) =
      g * (((N + k - 1).choose k : ℕ) : ZMod (p ^ K)) ∧ (p : ZMod (p ^ K)) ^ (3 * m) ∣ g - 1 :=
  ⟨_, choose_split_pred N k, pow_dvd_of_le _ (by omega) (gstar_sub_one_dvd hp5 hm hmr hk hN)⟩

theorem choose_central_rec (hp5 : 5 ≤ p) {x m : ℕ} (hm : 1 ≤ m) (hx : p ^ m ∣ p * x) :
    ∃ g : ZMod (p ^ K), (((2 * (p * x)).choose (p * x) : ℕ) : ZMod (p ^ K)) =
      g * (((2 * x).choose x : ℕ) : ZMod (p ^ K)) ∧ (p : ZMod (p ^ K)) ^ (3 * m) ∣ g - 1 := by
  rw [two_mul, two_mul]
  exact ⟨_, choose_split_succ x x,
    pow_dvd_of_le _ (by omega) (gstar_sub_one_dvd hp5 hm le_rfl hx hx)⟩

/-- Lemma 3: `F(pN, pk) = F(N, k) G` with `G ≡ 1 (mod p ^ (3 m))` when `p ^ m ∣ p k`,
`1 ≤ m ≤ r` and `p ^ r ∣ p N`. -/
theorem term_rec (hp5 : 5 ≤ p) (A B C : ℕ) {N k m r : ℕ} (hkN : k ≤ N) (hm : 1 ≤ m)
    (hmr : m ≤ r) (hN : p ^ r ∣ p * N) (hk : p ^ m ∣ p * k) :
    ∃ G : ZMod (p ^ K), (term A B C (p * N) (p * k) : ZMod (p ^ K)) = term A B C N k * G ∧
      (p : ZMod (p ^ K)) ^ (3 * m) ∣ G - 1 := by
  have hsub : p * N - p * k = p * (N - k) := (Nat.mul_sub p N k).symm
  have hNk : p ^ m ∣ p * (N - k) :=
    hsub ▸ Nat.dvd_sub ((pow_dvd_pow p hmr).trans hN) hk
  obtain ⟨g0, e0, h0⟩ := choose_pred_rec (K := K) hp5 hm hmr hN hk
  obtain ⟨g2, e2, h2⟩ := choose_central_rec (K := K) hp5 hm hNk
  obtain ⟨g1, e1, h1⟩ := choose_central_rec (K := K) hp5 hm hk
  refine ⟨g0 ^ A * g2 ^ B * g1 ^ C, ?_, ?_⟩
  · have hpk : p * k ≤ p * N := Nat.mul_le_mul_left p hkN
    unfold term
    rw [show 2 * (p * N) - 2 * (p * k) = 2 * (p * (N - k)) by omega, hsub,
      show 2 * N - 2 * k = 2 * (N - k) by omega]
    simp only [Nat.cast_mul, Nat.cast_pow] at e0 e2 e1 ⊢
    rw [e0, e2, e1]
    ring
  · exact mul_sub_one_dvd (mul_sub_one_dvd (pow_sub_one_dvd' h0 A) (pow_sub_one_dvd' h2 B))
      (pow_sub_one_dvd' h1 C)

end Recursion

/-! ### Assembly -/

theorem u_mul_prime {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {A B C : ℕ} (hA : 2 ≤ A)
    (hB : 1 ≤ B) (hC : 1 ≤ C) {N r : ℕ} (hr : 1 ≤ r) (hN : p ^ (r - 1) ∣ N) :
    (u A B C (p * N) : ZMod (p ^ (3 * r))) = (u A B C N : ZMod (p ^ (3 * r))) := by
  have hpN : p ^ r ∣ p * N := by
    have : p ^ r = p * p ^ (r - 1) := by rw [← pow_succ', Nat.sub_add_cancel hr]
    rw [this]; exact mul_dvd_mul_left p hN
  have hzero : ∀ z : ZMod (p ^ (3 * r)), ∀ e, 3 * r ≤ e →
      (p : ZMod (p ^ (3 * r))) ^ e ∣ z → z = 0 :=
    fun z e he h => eq_zero_of_pow_dvd (pow_dvd_of_le _ he h)
  rw [u_eq_sum, u_eq_sum, Nat.cast_sum, Nat.cast_sum,
    ← sum_range_mul_succ_ite hp.out.pos (fun k => (term A B C N k : ZMod (p ^ (3 * r)))) N]
  refine sum_congr rfl (fun k hk => ?_)
  have hkN : k ≤ p * N := Nat.lt_succ_iff.1 (mem_range.1 hk)
  by_cases hpk : p ∣ k
  · rw [ite_eq_left hpk]
    obtain ⟨k', rfl⟩ := hpk
    rw [Nat.mul_div_cancel_left _ hp.out.pos]
    have hk'N : k' ≤ N := Nat.le_of_mul_le_mul_left hkN hp.out.pos
    by_cases hrk : p ^ r ∣ p * k'
    · obtain ⟨G, hG, hG1⟩ := term_rec (K := 3 * r) hp5 A B C hk'N hr le_rfl hpN hrk
      rw [hG, show G = 1 from sub_eq_zero.1 (hzero _ _ le_rfl hG1), mul_one]
    · have hk0 : p * k' ≠ 0 := fun h => hrk (h ▸ dvd_zero _)
      have hs1 : 1 ≤ padicValNat p (p * k') :=
        one_le_padicValNat_of_dvd hk0 (dvd_mul_right p k')
      have hsdvd : p ^ padicValNat p (p * k') ∣ p * k' := pow_padicValNat_dvd
      have hsr : padicValNat p (p * k') < r := by
        by_contra h; exact hrk ((pow_dvd_pow p (not_lt.1 h)).trans hsdvd)
      have hns : ¬ p ^ (padicValNat p (p * k') + 1) ∣ p * k' :=
        pow_succ_padicValNat_not_dvd hk0
      obtain ⟨G, hG, hG1⟩ := term_rec (K := 3 * r) hp5 A B C hk'N hs1 hsr.le hpN hsdvd
      have hk'0 : 0 < k' := Nat.pos_of_ne_zero (fun h => hk0 (by rw [h, mul_zero]))
      have hns' : ¬ p ^ ((padicValNat p (p * k') - 1) + 1) ∣ k' := by
        rw [Nat.sub_add_cancel hs1]
        intro h; exact hns (by rw [pow_succ']; exact mul_dvd_mul_left p h)
      have hT := term_dvd (A := A) hB hC hN hk'0 hk'N hns'
      have hT' : (p : ZMod (p ^ (3 * r))) ^ ((A + 1) * ((r - 1) - (padicValNat p (p * k') - 1)))
          ∣ (term A B C N k' : ZMod (p ^ (3 * r))) := by
        rw [← Nat.cast_pow]; exact Nat.cast_dvd_cast hT
      rw [hG, ← sub_eq_zero]
      apply hzero _ ((A + 1) * ((r - 1) - (padicValNat p (p * k') - 1)) +
        3 * padicValNat p (p * k'))
      · have h3 := Nat.mul_le_mul_right (r - padicValNat p (p * k'))
          (show 3 ≤ A + 1 by omega)
        rw [show (r - 1) - (padicValNat p (p * k') - 1) = r - padicValNat p (p * k') by omega]
        omega
      · rw [show (term A B C N k' : ZMod (p ^ (3 * r))) * G - term A B C N k' =
          term A B C N k' * (G - 1) by ring, pow_add]
        exact mul_dvd_mul hT' hG1
  · rw [ite_eq_right hpk]
    have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hpk (h ▸ dvd_zero p))
    have hT := term_dvd (A := A) (s := 0) hB hC hpN hk0 hkN (by rwa [zero_add, pow_one])
    apply hzero _ ((A + 1) * (r - 0))
    · have := Nat.mul_le_mul_right r (show 3 ≤ A + 1 by omega)
      rw [Nat.sub_zero]
      omega
    · rw [← Nat.cast_pow]; exact Nat.cast_dvd_cast hT

theorem a_eq_u (n : ℕ) : a n = u 2 1 1 n := by
  simp only [a, u, pow_one]

/--
For integers $A \ge 2$ and $B, C \ge 1$, every prime $p \ge 5$ and all $n, r \ge 1$:
$u(np^r) \equiv u(np^{r-1}) \pmod{p^{3r}}$.
- Peter Bala, OEIS A364111, Jul 07 2023 (the general conjecture).
-/
theorem u_supercongruence {A B C : ℕ} (hA : 2 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    u A B C (n * p ^ r) ≡ u A B C (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have _ := hn
  have := Fact.mk hp
  rw [← ZMod.natCast_eq_natCast_iff]
  have : n * p ^ r = p * (n * p ^ (r - 1)) := by
    rw [← mul_assoc, mul_comm p n, mul_assoc, ← pow_succ', Nat.sub_add_cancel hr]
  rw [this]
  exact u_mul_prime hp5 hA hB hC hr (dvd_mul_left _ _)

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$.
- Peter Bala, OEIS A364111, Jul 07 2023 (the conjecture for A364111).
-/
theorem a_supercongruence {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) : a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  rw [a_eq_u, a_eq_u]
  exact u_supercongruence le_rfl le_rfl le_rfl hp hp5 hn hr

/-! ### Sanity checks -/

example : a 0 = 1 ∧ a 1 = 4 ∧ a 2 = 76 ∧ a 3 = 2560 ∧ a 4 = 106060 := by decide +kernel

/-- The case $n = 1$, $p = 5$, $r = 1$: $a(5) \equiv a(1) = 4 \pmod{125}$. -/
example : a 5 % 125 = 4 := by decide +kernel

end OeisA364111

end
