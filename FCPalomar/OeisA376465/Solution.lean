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
# OEIS A376465: Bala's unshifted supercongruence holds and the shifted one fails

Let $T(m, k) = \sum_{i} \binom{m}{i}^2 \binom{m+k-i}{k-i}$ (A108625) and
$a(n) = \sum_{k=0}^{n} \binom{n}{k}^2 \binom{n+k}{k}^2 T(n-1, k)$ (A376465). This file proves
`OeisA376465.tower`: for every prime $p \ge 5$ and all $n, r \ge 1$,
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$. It also proves `not_shifted_tower`: Bala's companion
$a(np^r - 1) \equiv a(np^{r-1} - 1) \pmod{p^{3r}}$ fails at $p = 5$, $n = 2$, $r = 1$, because
$a(9) \not\equiv a(1) \pmod{125}$ (in fact $a(9) - a(1) \equiv 3 \pmod 5$), checked by
`decide +kernel`.

Write $N = pN'$ with $p^{r-1} \mid N'$, $E(X, y) = (-1)^y \binom{X-1}{y}$ for $X \in \mathbb{Z}$
(so $\binom{N+k}{k} = E(-N, k)$), and $u_c(y) = \prod_{l \le y,\ p \nmid l} (l + c)$ (`uprod`).
All congruences are equalities in `ZMod (p ^ (3 r))`.

1. **Euler's transformation** (`T_euler`).
   $T(M, K) = \sum_i (-1)^{K-i} \binom{M}{K-i} \binom{M+i}{i}^2$ for all $M, K \ge 0$. Both sides
   equal $\sum_j \binom{M}{j} \binom{K}{j} \binom{M+j}{j}$: the left side by Vandermonde
   (`T_eq_mid`), the right side by Vandermonde and the signed sum
   $\sum_t (-1)^{n-t} \binom{M}{n-t} \binom{M+j+t}{t} = \binom{j+n}{n}$ (`signed_vandermonde`,
   from `Ring.add_choose_eq` with the top $-(M+j+1)$). Hence $a(N) = \sum_{i \le k \le N} F(N; k, i)$
   with $F(N; k, i) = \binom{N}{k}^2 \binom{N+k}{k}^2 (-1)^{k-i} \binom{N-1}{k-i} \binom{N+i-1}{i}^2$
   (`a_eq_aE`).
2. **Exact descents** (`E_descent`, `choose_ratio`). For $X \in \mathbb{Z}$,
   $E(pX, y)\, u_0(y) = E(X, \lfloor y/p \rfloor)\, u_{-pX}(y)$ and
   $\binom{pX}{pk} u_0(pk) = \binom{X}{k} u_{-pX}(pk)$. Since $u_{-pX} \equiv u_0$ and $u_0$ is
   prime to $p$, both binomials descend modulo every $p^f \mid pX$ (`E_cong`, `choose_cong`).
   Also $p^f \mid \binom{X}{i}$ when $p^f \mid X$ and $p \nmid i$ (`rchoose_dvd`).
3. **Four layers** (`sum_split`). Split the pairs $(k, i)$ by $p \mid k$ and $p \mid i$.
   - Both divisible (`div_layer`). By step 2, $F(pN'; pk', pi') = F(N'; k', i')\, G$ exactly, where
     $G$ is a product of factors $\prod_{l \le pm,\ p \nmid l} (1 \pm N/l)$. The Jacobsthal-type
     bound `jacobsthal_prod` gives $G \equiv 1 \pmod{p^{r+2+2e}}$ with
     $e = \min(v_p(k'), v_p(i'), r - 1)$. If $e < r - 1$, then $p^{r-1-e}$ divides
     $\binom{N'}{k'}$ or $\binom{N'+i'-1}{i'}$ (`rchoose_pow_dvd`), and both enter $F$ squared.
     These terms sum to $a(N')$.
   - Both units (`layerC_term`). $p^r$ divides $\binom{N}{k}$ and $\binom{N+i-1}{i}$, so
     $p^{4r} \mid F(N; k, i)$.
   - $p \nmid k$, $i = pi'$ (`layerA_term`). From $k \binom{N}{k} = N \binom{N-1}{k-1}$ and step 2,
     $\sum_{i'} F(N; k, pi') \equiv N^2 k^{-2}\, \Psi(N'; \lfloor k/p \rfloor)$ with
     $\Psi(M; j) = \binom{M-1}{j}^2 \binom{M+j}{j}^2 T(M-1, j)$, where $T(M-1, j)$ is taken in
     Euler's form (`TE`).
   - $k = pk'$, $p \nmid i$ (`layerB_term`). After exchanging the two sums, from
     $i \binom{N+i-1}{i} = N \binom{N+i-1}{i-1}$ and step 2,
     $\sum_{k'} F(N; pk', i) \equiv N^2 i^{-2}\, \Omega(N'; \lfloor i/p \rfloor)$ with
     $\Omega(M; l) = \binom{M+l}{l}^2 \sum_{k > l} (-1)^{k-l-1} \binom{M}{k}^2 \binom{M+k}{k}^2
     \binom{M-1}{k-l-1}$.
4. **Kernel descents** (`Psi_descent`, `Omega_descent`). Modulo every $p^f \mid pM$,
   $\Psi(pM; j) \equiv \Psi(M; \lfloor j/p \rfloor)$ and $\Omega(pM; l) \equiv \Omega(M; \lfloor l/p \rfloor)$.
   In the inner sums the terms with an index prime to $p$ vanish by `rchoose_dvd`, and the others
   descend by step 2.
5. **Block sums** (`layerA`, `layerB`). Over the units of a block of length $p^u$,
   $\sum x^{-2} \equiv 0 \pmod{p^u}$ for $p \ge 5$ (`block_invSq`). The nested block lemma
   (`nested_block`), with the kernels $\Psi(np^{r-u}; \cdot)$ or $\Omega(np^{r-u}; \cdot)$ at
   level $u$, gives $p^r \mid \sum_{x < N} x^{-2}\, \Psi(N'; \lfloor x/p \rfloor)$, and the same
   for $\Omega$. With $p^{2r} \mid N^2$ these two layers vanish.
6. **Assembly** (`aE_tower`, `tower`). The four layers give $a(N) \equiv a(N')$.

The hypothesis $p \ge 5$ is used in the block sums and in `jacobsthal_prod` (2 and 3 are units)
and through $p$ odd.

The layer decomposition, the descent and the nested block lemma follow Gessel and Beukers in the
form of Straub (Lemmas 5.1, 5.2 and 5.6 of the reference below: Jacobsthal's congruence, block
sums of $x^{-2}$, and the block lemma). `jacobsthal_prod` is Coster's product form of
Jacobsthal's congruence. The split in two indices with two kernels follows Section 7 of
Kheyri–Hadweni, who treat A376462 this way. Euler's form of A108625 is noted by Bala on A108625.
The shared infrastructure (block sums, harmonic sum, `jacobsthal_prod`, `nested_block`, `uprod`,
`E` and the exact descents) is copied from the OeisA363985 package of this repository, which
copied part of it from the MosN8 package.

*References:*
- Peter Bala, [A376465](https://oeis.org/A376465), Sep 25, 2024, and
  [A108625](https://oeis.org/A108625).
- I. M. Gessel, *Some congruences for Apéry numbers*, J. Number Theory 14 (1982), 362–368.
- F. Beukers, *Some congruences for the Apéry numbers*, J. Number Theory 21 (1985), 141–155.
- A. Straub, *Multivariate Apéry numbers and supercongruences of rational functions*,
  Algebra Number Theory 8 (2014), [arXiv:1401.0854](https://arxiv.org/abs/1401.0854).
- M. Coster, *Supercongruences*, PhD thesis, Universiteit Leiden, 1988.
- Kheyri and Hadweni, *Cubic supercongruences for a Dixon-type sum, fractional factorial ratios
  and two Apéry-like sequences*, Zenodo record 23632164, Section 7.
-/

@[expose] public section

open Finset

namespace OeisA376465

/-- OEIS A108625: $T(m, k) = \sum_{i=0}^{k} \binom{m}{i}^2 \binom{m+k-i}{k-i}$. -/
def T (m k : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), m.choose i ^ 2 * (m + k - i).choose (k - i)

/-- OEIS A376465: $a(n) = \sum_{k=0}^{n} \binom{n}{k}^2 \binom{n+k}{k}^2 T(n-1, k)$.
At $n = 0$ the factor $T(-1, 0) = 1$ is `T 0 0 = 1`, with the same value. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (n + k).choose k ^ 2 * T (n - 1) k

/-! ### Sanity checks -/

example : a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 289 ∧ a 3 = 32909 := by decide +kernel

/-! ### Shared infrastructure

Copied from the OeisA363985 package of this repository (Wentao Li, Apache-2.0), which copied part
of it from the MosN8 package: divisibility helpers, the nested block lemma, block sums of inverse
squares, the harmonic sum, the Jacobsthal-type product bound, the unit products `uprod`, the
signed binomial `E` and the exact descents `E_descent` and `choose_ratio`. -/

theorem pow_dvd_of_le {M : Type*} [CommRing M] (P : M) {a b : ℕ} {z : M} (hab : a ≤ b)
    (h : P ^ b ∣ z) : P ^ a ∣ z :=
  (pow_dvd_pow P hab).trans h

theorem mul_sub_one_dvd {M : Type*} [CommRing M] {a x y : M} (hx : a ∣ x - 1) (hy : a ∣ y - 1) :
    a ∣ x * y - 1 := by
  have : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right hy _) hx

theorem mul_sub_mul_dvd {M : Type*} [CommRing M] {d a a' b b' : M} (ha : d ∣ a - a')
    (hb : d ∣ b - b') : d ∣ a * b - a' * b' := by
  have : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_left ha _)

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

/-! ### Fibres and the nested block lemma -/

theorem sum_fibre {M : Type*} [CommRing M] (w G : ℕ → M) {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ∑ x ∈ range (n * q), w x * G (x / q) =
      ∑ D ∈ range n, G D * ∑ i ∈ range q, w (D * q + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ, mul_sum]
    congr 1
    refine sum_congr rfl (fun i hi => ?_)
    have : (n * q + i) / q = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt (mem_range.1 hi), zero_add]
    rw [this, mul_comm]

/-- The nested block lemma: telescoping a kernel over the levels `x ↦ x / p ^ u`. -/
theorem nested_block {M : Type*} [CommRing M] (P : M) {p s L : ℕ} (hp : 0 < p) (hs : 1 ≤ s)
    (w : ℕ → M) (Kf : ℕ → ℕ → M)
    (hw : ∀ u, 1 ≤ u → u ≤ s → ∀ D < L * p ^ (s - u),
      P ^ u ∣ ∑ i ∈ range (p ^ u), w (D * p ^ u + i))
    (hK : ∀ u, 1 ≤ u → u < s → ∀ A < L * p ^ (s - u),
      P ^ (s - u) ∣ Kf u A - Kf (u + 1) (A / p)) :
    P ^ s ∣ ∑ x ∈ range (L * p ^ s), w x * Kf 1 (x / p) := by
  have hsplit : ∀ u, u ≤ s → L * p ^ s = (L * p ^ (s - u)) * p ^ u := fun u hu => by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hu]
  have hlev : ∀ u, 1 ≤ u → u ≤ s → ∀ (G : ℕ → M) (a : ℕ), a + u = s →
      (∀ D < L * p ^ (s - u), P ^ a ∣ G D) →
      P ^ s ∣ ∑ x ∈ range (L * p ^ s), w x * G (x / p ^ u) := by
    intro u hu1 hus G a hau hG
    rw [hsplit u hus, sum_fibre w G (pow_pos hp u)]
    refine dvd_sum (fun D hD => ?_)
    rw [← hau, pow_add]
    exact mul_dvd_mul (hG D (mem_range.1 hD)) (hw u hu1 hus D (mem_range.1 hD))
  have htel : ∀ j, 1 ≤ j → j ≤ s →
      P ^ s ∣ ∑ x ∈ range (L * p ^ s), w x * (Kf 1 (x / p) - Kf j (x / p ^ j)) := by
    intro j hj1
    induction j, hj1 using Nat.le_induction with
    | base => intro _; simp
    | succ j hj ih =>
      intro hjs
      have hjs' : j < s := hjs
      have e : ∀ x, w x * (Kf 1 (x / p) - Kf (j + 1) (x / p ^ (j + 1))) =
          w x * (Kf 1 (x / p) - Kf j (x / p ^ j)) +
            w x * (Kf j (x / p ^ j) - Kf (j + 1) (x / p ^ j / p)) := by
        intro x
        rw [Nat.div_div_eq_div_mul, ← pow_succ]
        ring
      simp_rw [e, sum_add_distrib]
      refine dvd_add (ih hjs'.le) ?_
      exact hlev j hj hjs'.le (fun A => Kf j A - Kf (j + 1) (A / p)) (s - j) (by omega)
        (fun D hD => hK j hj hjs' D hD)
  have h1 := htel s hs le_rfl
  have h2 := hlev s hs le_rfl (Kf s) 0 (by omega) (fun D _ => by rw [pow_zero]; exact one_dvd _)
  have e : ∑ x ∈ range (L * p ^ s), w x * Kf 1 (x / p) =
      ∑ x ∈ range (L * p ^ s), w x * (Kf 1 (x / p) - Kf s (x / p ^ s)) +
        ∑ x ∈ range (L * p ^ s), w x * Kf s (x / p ^ s) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun x _ => by ring)
  rw [e]
  exact dvd_add h1 h2

/-! ### Arithmetic in `ZMod (p ^ K)` -/

section ZModPow

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

theorem coprime_pow_of_not_dvd {x : ℕ} (hx : ¬ p ∣ x) (n : ℕ) : Nat.Coprime x (p ^ n) :=
  ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hx).symm.pow_right n

theorem natCast_mul_inv {x : ℕ} (hx : ¬ p ∣ x) :
    (x : ZMod (p ^ K)) * (x : ZMod (p ^ K))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one x (coprime_pow_of_not_dvd hx K)

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

/-- Block sums of `x⁻²`: over the units of a block of length `p ^ u`, for `p ≥ 5`. -/
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
      (∏ l ∈ range (p * k), if p ∣ l + 1 then 1 else 1 + Z * ((l + 1 : ℕ) : ZMod (p ^ K))⁻¹) - 1 := by
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

def uprod (p : ℕ) (c : ℤ) (y : ℕ) : ℤ :=
  ∏ l ∈ range y, if p ∣ l + 1 then 1 else ((l + 1 : ℕ) : ℤ) + c

theorem uprod_succ (p : ℕ) (c : ℤ) (y : ℕ) :
    uprod p c (y + 1) = uprod p c y * (if p ∣ y + 1 then 1 else ((y + 1 : ℕ) : ℤ) + c) :=
  prod_range_succ _ _

theorem div_succ_eq {p y : ℕ} (hd : p ∣ y + 1) : y + 1 = p * (y / p + 1) := by
  have h := Nat.div_mul_cancel hd
  rw [Nat.succ_div_of_dvd hd] at h
  rw [mul_comm]
  exact h.symm

theorem uprod_sub_dvd (p : ℕ) {m c : ℤ} (hc : m ∣ c) (y : ℕ) :
    m ∣ uprod p c y - uprod p 0 y := by
  induction y with
  | zero => simp [uprod]
  | succ y ih =>
    rw [uprod_succ, uprod_succ]
    apply mul_sub_mul_dvd ih
    split_ifs
    · simp
    · simpa using hc

theorem isCoprime_uprod {p : ℕ} (hp : p.Prime) (y : ℕ) : IsCoprime (p : ℤ) (uprod p 0 y) := by
  induction y with
  | zero => simp only [uprod, range_zero, prod_empty]; exact isCoprime_one_right
  | succ y ih =>
    rw [uprod_succ]
    refine ih.mul_right ?_
    split_ifs with h
    · exact isCoprime_one_right
    · rw [add_zero]
      exact Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)

/-- If `p ^ n ∣ y z` and `p ^ (j + 1) ∤ y`, then `p ^ (n - j) ∣ z`. -/

theorem pow_dvd_of_pow_dvd_mul {p : ℕ} [hp : Fact p.Prime] {n j y z : ℕ} (h : p ^ n ∣ y * z)
    (hy : ¬ p ^ (j + 1) ∣ y) : p ^ (n - j) ∣ z := by
  have hy0 : y ≠ 0 := by rintro rfl; exact hy (dvd_zero _)
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · exact dvd_zero _
  have hz0 : z ≠ 0 := hz.ne'
  have h1 : n ≤ padicValNat p (y * z) := (padicValNat_dvd_iff_le (mul_ne_zero hy0 hz0)).1 h
  rw [padicValNat.mul hy0 hz0] at h1
  have h2 : padicValNat p y ≤ j := by
    by_contra hc
    rw [not_le] at hc
    exact hy ((pow_dvd_pow p hc).trans pow_padicValNat_dvd)
  exact (padicValNat_dvd_iff_le hz0).2 (by omega)

theorem div_sub_sub_one {p c A : ℕ} (hp : 0 < p) (hc : p ∣ c) (hA : A < c) :
    (c - A - 1) / p = c / p - A / p - 1 := by
  obtain ⟨C, rfl⟩ := hc
  have hq : A / p < C := (Nat.div_lt_iff_lt_mul hp).2 (by rw [mul_comm]; exact hA)
  have hdm := Nat.div_add_mod A p
  have hρ := Nat.mod_lt A hp
  have hC : C = A / p + (C - A / p - 1) + 1 := by omega
  have h1 : p * C = p * (A / p) + p * (C - A / p - 1) + p := by
    conv_lhs => rw [hC]
    ring
  have e : p * C - A - 1 = (p - 1 - A % p) + p * (C - A / p - 1) := by omega
  rw [e, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), zero_add,
    Nat.mul_div_cancel_left _ hp]

section Sums

variable {M : Type*}

theorem sum_range_eq_of_vanish [AddCommMonoid M] (G : ℕ → M) {a b : ℕ} (hab : a ≤ b)
    (hG : ∀ x, a ≤ x → x < b → G x = 0) : ∑ x ∈ range b, G x = ∑ x ∈ range a, G x := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [sum_range_add, sum_eq_zero (fun i hi => hG (a + i) (by omega)
    (by have := mem_range.1 hi; omega)), add_zero]

end Sums

section Concrete

variable {p : ℕ} [hp : Fact p.Prime]

theorem isUnit_uprod {K : ℕ} (y : ℕ) : IsUnit (uprod p 0 y : ZMod (p ^ K)) := by
  obtain ⟨u, v, huv⟩ := (isCoprime_uprod hp.out y).pow_left (m := K)
  refine IsUnit.of_mul_eq_one (v : ZMod (p ^ K)) ?_
  have h := congrArg (Int.cast : ℤ → ZMod (p ^ K)) huv
  have h0 : (p : ZMod (p ^ K)) ^ K = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one, h0,
    mul_zero, zero_add] at h
  rw [mul_comm]
  exact h

theorem uprod_cast {K : ℕ} (c : ℤ) (y : ℕ) :
    (uprod p c y : ZMod (p ^ K)) = (∏ l ∈ range y, if p ∣ l + 1 then 1 else
      1 + (c : ZMod (p ^ K)) * ((l + 1 : ℕ) : ZMod (p ^ K))⁻¹) * (uprod p 0 y : ZMod (p ^ K)) := by
  unfold uprod
  rw [Int.cast_prod, Int.cast_prod, ← prod_mul_distrib]
  refine prod_congr rfl (fun l _ => ?_)
  split_ifs with h
  · simp
  · have := natCast_mul_inv (K := K) h
    rw [Int.cast_add, Int.cast_add, Int.cast_natCast, Int.cast_zero, add_zero]
    linear_combination (-(c : ZMod (p ^ K))) * this

/-- The ratio product `∏ (1 + Z / l)` over the units `l ≤ p k`. -/
def PR (p K : ℕ) (Z : ZMod (p ^ K)) (k : ℕ) : ZMod (p ^ K) :=
  ∏ l ∈ range (p * k), if p ∣ l + 1 then 1 else 1 + Z * ((l + 1 : ℕ) : ZMod (p ^ K))⁻¹

theorem PR_sub_one (hp5 : 5 ≤ p) {K r k e : ℕ} (hr : 1 ≤ r) (he : e ≤ r - 1) (hk : p ^ e ∣ k)
    {Z : ZMod (p ^ K)} (hZ : (p : ZMod (p ^ K)) ^ r ∣ Z) :
    (p : ZMod (p ^ K)) ^ (r + 2 + 2 * e) ∣ PR p K Z k - 1 := by
  have := jacobsthal_prod (K := K) hp5 he hk Z (by rwa [show 1 + (r - 1) = r by omega])
  rwa [show 3 + (r - 1) + 2 * e = r + 2 + 2 * e by omega] at this

omit hp in
theorem intCast_dvd_sub {K e : ℕ} {a b : ℤ} (h : (p : ℤ) ^ e ∣ a - b) :
    (p : ZMod (p ^ K)) ^ e ∣ (a : ZMod (p ^ K)) - (b : ZMod (p ^ K)) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨(c : ZMod (p ^ K)), by rw [← Int.cast_sub, hc, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast]⟩

end Concrete

/-! ### Binomial coefficients with integer tops -/

open Polynomial in
theorem rchoose_succ_mul (X : ℤ) (k : ℕ) :
    Ring.choose X (k + 1) * (k + 1) = Ring.choose X k * (X - k) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose X (k + 1)
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose X k
  rw [descPochhammer_succ_right, smeval_mul, smeval_sub, smeval_X, smeval_natCast] at h1
  simp at h1 h2
  rw [h2, Nat.factorial_succ] at h1
  push_cast at h1
  have hf : (k.factorial : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hf
  linear_combination -h1

open Polynomial in
theorem rchoose_succ_mul' (X : ℤ) (k : ℕ) :
    Ring.choose X (k + 1) * (k + 1) = X * Ring.choose (X - 1) k := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose X (k + 1)
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose (X - 1) k
  rw [descPochhammer_succ_left, smeval_mul, smeval_comp, smeval_sub, smeval_X, smeval_one] at h1
  simp at h1 h2
  rw [h2, Nat.factorial_succ] at h1
  push_cast at h1
  have hf : (k.factorial : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hf
  linear_combination -h1

/-- `E X y = (-1)^y C(X - 1, y) = ∏_{i = 1}^{y} (1 - X / i)`. -/
def E (X : ℤ) (y : ℕ) : ℤ := (-1) ^ y * Ring.choose (X - 1) y

theorem E_zero (X : ℤ) : E X 0 = 1 := by simp [E]

theorem E_succ (X : ℤ) (y : ℕ) : E X (y + 1) * (y + 1) = E X y * (y + 1 - X) := by
  unfold E
  rw [pow_succ, mul_assoc, mul_assoc, rchoose_succ_mul]
  ring

theorem E_natCast {X : ℕ} (hX : 1 ≤ X) (y : ℕ) : E X y = (-1) ^ y * ((X - 1).choose y : ℤ) := by
  unfold E
  rw [show (X : ℤ) - 1 = ((X - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hX]; ring,
    Ring.choose_natCast]

theorem uprod_zero (p : ℕ) (c : ℤ) : uprod p c 0 = 1 := by simp [uprod]

/-- Exact descent for `E`: with `X = p X'`, the factors
`i = p i'` of `∏ (1 - X / i)` give `E X' ⌊y / p⌋`. -/
theorem E_descent {p : ℕ} (hp : 0 < p) (X : ℤ) : ∀ y : ℕ,
    E (p * X) y * uprod p 0 y = E X (y / p) * uprod p (-(p * X)) y
  | 0 => by simp [E_zero, uprod_zero]
  | y + 1 => by
    have ih := E_descent hp X y
    have h1 := E_succ (p * X) y
    rw [uprod_succ, uprod_succ]
    by_cases hd : p ∣ y + 1
    · rw [ite_eq_left hd, ite_eq_left hd, mul_one, mul_one, Nat.succ_div_of_dvd hd]
      have hy : (y : ℤ) + 1 = p * (((y / p : ℕ) : ℤ) + 1) := by exact_mod_cast div_succ_eq hd
      have h2 := E_succ X (y / p)
      apply mul_right_cancel₀ (show (y : ℤ) + 1 ≠ 0 by positivity)
      linear_combination uprod p 0 y * h1 + ((y : ℤ) + 1 - p * X) * ih
        - (p : ℤ) * uprod p (-(p * X)) y * h2
        + (E X (y / p) * uprod p (-(p * X)) y - E X (y / p + 1) * uprod p (-(p * X)) y) * hy
    · rw [ite_eq_right hd, ite_eq_right hd, Nat.succ_div_of_not_dvd hd]
      push_cast
      apply mul_right_cancel₀ (show (y : ℤ) + 1 ≠ 0 by positivity)
      linear_combination ((y : ℤ) + 1) * uprod p 0 y * h1 + ((y : ℤ) + 1) * ((y : ℤ) + 1 - p * X) * ih

theorem uprod_mul_dvd {p : ℕ} (y : ℕ) (hd : p ∣ y + 1) (c : ℤ) : uprod p c (y + 1) = uprod p c y := by
  rw [uprod_succ, ite_eq_left hd, mul_one]

/-- The ratio `C(p X, p k) / C(X, k)` as a ratio of unit products, for every integer `X`. -/
theorem choose_ratio {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (X : ℤ) (k : ℕ) :
    Ring.choose (p * X) (p * k) * uprod p 0 (p * k) =
      Ring.choose X k * uprod p (-(p * X)) (p * k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [uprod_zero]
  obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
  have hp0 := hp.pos
  obtain ⟨y, hy⟩ : ∃ y, p * (k₀ + 1) = y + 1 := ⟨p * (k₀ + 1) - 1, by
    have : 1 ≤ p * (k₀ + 1) := Nat.mul_pos hp0 (by omega)
    omega⟩
  have hyd : p ∣ y + 1 := hy ▸ dvd_mul_right p _
  have hyp : y / p = k₀ := by
    have := Nat.succ_div_of_dvd hyd
    rw [← hy, Nat.mul_div_cancel_left _ hp0] at this
    omega
  rw [hy, uprod_mul_dvd y hyd, uprod_mul_dvd y hyd]
  have h1 := rchoose_succ_mul' ((p : ℤ) * X) y
  have h2 := rchoose_succ_mul' X k₀
  have hd := E_descent hp0 X y
  rw [hyp] at hd
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hsign : (-1 : ℤ) ^ y * (-1) ^ k₀ = 1 := by
    have : y + k₀ + 1 = (p + 1) * (k₀ + 1) - 1 := by
      have : (p + 1) * (k₀ + 1) = p * (k₀ + 1) + (k₀ + 1) := by ring
      omega
    rw [← pow_add]
    obtain ⟨t, ht⟩ := hodd
    have : y + k₀ = 2 * ((t + 1) * (k₀ + 1) - 1) := by
      have h3 : (p + 1) * (k₀ + 1) = 2 * ((t + 1) * (k₀ + 1)) := by rw [ht]; ring
      have h4 : 1 ≤ (t + 1) * (k₀ + 1) := Nat.mul_pos (by omega) (by omega)
      omega
    rw [this, pow_mul]
    simp
  have hyc : ((y : ℤ) + 1) = p * ((k₀ : ℤ) + 1) := by exact_mod_cast hy.symm
  unfold E at hd
  apply mul_right_cancel₀ (show ((y : ℤ) + 1) ≠ 0 by positivity)
  have sq : ((-1 : ℤ) ^ y) * (-1) ^ y = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination uprod p 0 y * h1 + (p : ℤ) * X * (-1) ^ y * hd
    + (p : ℤ) * X * Ring.choose (X - 1) k₀ * uprod p (-(↑p * X)) y * hsign
    - (p : ℤ) * X * Ring.choose (↑p * X - 1) y * uprod p 0 y * sq
    - Ring.choose X (k₀ + 1) * uprod p (-(↑p * X)) y * hyc - (p : ℤ) * uprod p (-(↑p * X)) y * h2

theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

/-- If `p ^ n ∣ y z` in `ℤ` and `p ^ (j + 1) ∤ y`, then `p ^ (n - j) ∣ z`. -/
theorem int_pow_dvd_of_pow_dvd_mul {p : ℕ} [Fact p.Prime] {n j y : ℕ} {z : ℤ}
    (h : (p : ℤ) ^ n ∣ (y : ℤ) * z) (hy : ¬ p ^ (j + 1) ∣ y) : (p : ℤ) ^ (n - j) ∣ z := by
  have h1 : p ^ n ∣ y * z.natAbs := by
    have := Int.ofNat_dvd_left.1 (by exact_mod_cast h : ((p ^ n : ℕ) : ℤ) ∣ (y : ℤ) * z)
    rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
  have h2 := pow_dvd_of_pow_dvd_mul h1 hy
  exact_mod_cast Int.ofNat_dvd_left.2 h2

/-! ### Euler's transformation for the rows of A108625 -/

/-- Vandermonde: `C(m + n, k) = ∑_j C(m, j) C(n, k - j)`. -/
theorem vandermonde (m n k : ℕ) :
    (m + n).choose k = ∑ j ∈ range (k + 1), m.choose j * n.choose (k - j) := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- `C(M + j, j) = ∑_i C(M, i) C(j, i)`, summed up to any bound `K ≥ j`. -/
theorem add_choose_eq_sum (M : ℕ) {j K : ℕ} (hj : j ≤ K) :
    (M + j).choose j = ∑ i ∈ range (K + 1), M.choose i * j.choose i := by
  rw [vandermonde, sum_range_eq_of_vanish (fun i => M.choose i * j.choose i)
    (show j + 1 ≤ K + 1 by omega) (fun i hi _ => by rw [Nat.choose_eq_zero_of_lt (n := j) (by omega),
      mul_zero])]
  refine sum_congr rfl (fun i hi => ?_)
  rw [Nat.choose_symm (Nat.lt_succ_iff.1 (mem_range.1 hi))]

theorem choose_mul_choose_rev {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) :
    K.choose j * j.choose i = K.choose i * (K - i).choose (K - j) := by
  rcases le_or_gt i j with hij | hij
  · rw [Nat.choose_mul (n := K) hij, ← Nat.choose_symm (show j - i ≤ K - i by omega),
      show K - i - (j - i) = K - j by omega]
  · rw [Nat.choose_eq_zero_of_lt hij, Nat.choose_eq_zero_of_lt (show K - i < K - j by omega)]
    ring

/-- The middle form `T(M, K) = ∑_j C(M, j) C(K, j) C(M + j, j)`. -/
theorem T_eq_mid (M K : ℕ) :
    T M K = ∑ j ∈ range (K + 1), M.choose j * K.choose j * (M + j).choose j := by
  have h1 : T M K = ∑ i ∈ range (K + 1), M.choose i * K.choose i * (M + K - i).choose K := by
    unfold T
    refine sum_congr rfl (fun i hi => ?_)
    have hi' := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rcases le_or_gt i M with hiM | hiM
    · have h := Nat.choose_mul (n := M + K - i) (k := K) (s := K - i) (by omega)
      rw [show M + K - i - (K - i) = M by omega, show K - (K - i) = i by omega,
        Nat.choose_symm hi'] at h
      rw [show M.choose i * K.choose i * (M + K - i).choose K =
        M.choose i * ((M + K - i).choose K * K.choose i) by ring, h]
      ring
    · rw [Nat.choose_eq_zero_of_lt hiM]; ring
  rw [h1]
  have h2 : ∀ j ∈ range (K + 1), M.choose j * K.choose j * (M + j).choose j =
      ∑ i ∈ range (K + 1), M.choose i * (M.choose j * (K.choose i * (K - i).choose (K - j))) := by
    intro j hj
    have hj' := Nat.lt_succ_iff.1 (mem_range.1 hj)
    rw [add_choose_eq_sum M hj', mul_sum]
    refine sum_congr rfl (fun i hi => ?_)
    rw [← choose_mul_choose_rev (Nat.lt_succ_iff.1 (mem_range.1 hi)) hj']
    ring
  rw [sum_congr rfl h2, sum_comm]
  refine sum_congr rfl (fun i hi => ?_)
  have hi' := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [show M + K - i = M + (K - i) by omega, vandermonde, mul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  ring

/-- A signed Vandermonde sum: `∑_t (-1)^{n-t} C(M, n-t) C(M+j+t, t) = C(j+n, n)`. -/
theorem signed_vandermonde (M j n : ℕ) :
    ∑ t ∈ range (n + 1), (-1 : ℤ) ^ (n - t) * (M.choose (n - t) : ℤ) * ((M + j + t).choose t : ℤ) =
      ((j + n).choose n : ℤ) := by
  have h := Ring.add_choose_eq n (Commute.all (-((M + j + 1 : ℕ) : ℤ)) (M : ℤ))
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hneg : ∀ (c t : ℕ), Ring.choose (-((c + 1 : ℕ) : ℤ)) t = (-1) ^ t * ((c + t).choose t : ℤ) := by
    intro c t
    rw [Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul,
      show ((c + 1 : ℕ) : ℤ) + t - 1 = ((c + t : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast]
  have hl : -((M + j + 1 : ℕ) : ℤ) + M = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hl, hneg] at h
  have key : ∀ t ∈ range (n + 1), (-1 : ℤ) ^ (n - t) * (M.choose (n - t) : ℤ) *
      ((M + j + t).choose t : ℤ) = (-1) ^ n *
        (Ring.choose (-((M + j + 1 : ℕ) : ℤ)) t * Ring.choose (M : ℤ) (n - t)) := by
    intro t ht
    have ht' := Nat.lt_succ_iff.1 (mem_range.1 ht)
    rw [hneg, Ring.choose_natCast]
    have hs : (-1 : ℤ) ^ n * (-1) ^ t = (-1) ^ (n - t) := by
      rw [← pow_add, show n + t = (n - t) + 2 * t by omega, pow_add, pow_mul]; simp
    linear_combination (-(M.choose (n - t) : ℤ) * ((M + j + t).choose t : ℤ)) * hs
  rw [sum_congr rfl key, ← mul_sum, ← h, ← mul_assoc, neg_one_pow_mul_self, one_mul]

theorem choose_mul_choose_shift (M j t : ℕ) :
    (M + (j + t)).choose (j + t) * (j + t).choose j = (M + j).choose j * (M + j + t).choose t := by
  have h := Nat.choose_mul (n := M + j + t) (k := M + j) (s := M) (by omega)
  rw [show M + j + t - M = j + t by omega, show M + j - M = j by omega] at h
  rw [show (M + j + t).choose t = (M + j + t).choose (M + j) by
      rw [Nat.choose_symm_of_eq_add]; ring,
    show (M + j).choose j = (M + j).choose M by rw [Nat.choose_symm_add],
    show M + (j + t) = M + j + t by ring,
    show (M + j + t).choose (j + t) = (M + j + t).choose M by
      rw [Nat.choose_symm_of_eq_add]; ring]
  linarith [h]

theorem euler_inner (M : ℕ) {j K : ℕ} (hj : j ≤ K) :
    ∑ i ∈ range (K + 1), (-1 : ℤ) ^ (K - i) * (M.choose (K - i) : ℤ) *
      (((M + i).choose i : ℤ) * (i.choose j : ℤ)) = (K.choose j : ℤ) * ((M + j).choose j : ℤ) := by
  rw [show K + 1 = j + (K - j + 1) by omega, sum_range_add,
    sum_eq_zero (fun i hi => by rw [Nat.choose_eq_zero_of_lt (mem_range.1 hi)]; simp), zero_add]
  have e : ∀ t ∈ range (K - j + 1), (-1 : ℤ) ^ (K - (j + t)) * (M.choose (K - (j + t)) : ℤ) *
      (((M + (j + t)).choose (j + t) : ℤ) * ((j + t).choose j : ℤ)) =
      ((M + j).choose j : ℤ) * ((-1 : ℤ) ^ (K - j - t) * (M.choose (K - j - t) : ℤ) *
        ((M + j + t).choose t : ℤ)) := by
    intro t _
    have h := choose_mul_choose_shift M j t
    have h' : ((M + (j + t)).choose (j + t) : ℤ) * ((j + t).choose j : ℤ) =
        ((M + j).choose j : ℤ) * ((M + j + t).choose t : ℤ) := by exact_mod_cast h
    rw [h', show K - (j + t) = K - j - t by omega]
    ring
  rw [sum_congr rfl e, ← mul_sum, signed_vandermonde, show j + (K - j) = K by omega,
    Nat.choose_symm hj]
  ring

/-- Euler's transformation: `T(M, K) = ∑_i (-1)^{K-i} C(M, K-i) C(M+i, i)^2`. -/
theorem T_euler (M K : ℕ) :
    (T M K : ℤ) = ∑ i ∈ range (K + 1),
      (-1 : ℤ) ^ (K - i) * (M.choose (K - i) : ℤ) * ((M + i).choose i : ℤ) ^ 2 := by
  have h1 : ∀ i ∈ range (K + 1), (-1 : ℤ) ^ (K - i) * (M.choose (K - i) : ℤ) *
      ((M + i).choose i : ℤ) ^ 2 = ∑ j ∈ range (K + 1), (M.choose j : ℤ) *
        ((-1 : ℤ) ^ (K - i) * (M.choose (K - i) : ℤ) *
          (((M + i).choose i : ℤ) * (i.choose j : ℤ))) := by
    intro i hi
    have hi' := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have e : ((M + i).choose i : ℤ) = ∑ j ∈ range (K + 1), (M.choose j : ℤ) * (i.choose j : ℤ) := by
      exact_mod_cast add_choose_eq_sum M hi'
    calc (-1 : ℤ) ^ (K - i) * (M.choose (K - i) : ℤ) * ((M + i).choose i : ℤ) ^ 2
        = (-1 : ℤ) ^ (K - i) * (M.choose (K - i) : ℤ) * ((M + i).choose i : ℤ) *
            ((M + i).choose i : ℤ) := by ring
      _ = (-1 : ℤ) ^ (K - i) * (M.choose (K - i) : ℤ) * ((M + i).choose i : ℤ) *
            ∑ j ∈ range (K + 1), (M.choose j : ℤ) * (i.choose j : ℤ) := by rw [← e]
      _ = _ := by rw [mul_sum]; exact sum_congr rfl (fun j _ => by ring)
  rw [sum_congr rfl h1, sum_comm, T_eq_mid]
  push_cast
  refine sum_congr rfl (fun j hj => ?_)
  rw [← mul_sum, euler_inner M (Nat.lt_succ_iff.1 (mem_range.1 hj))]
  ring

/-! ### Congruences from the exact descents -/

/-- From `a u = b v` with `u` prime to `p` and `v ≡ u`, deduce `a ≡ b`. -/
theorem dvd_sub_of_mul_eq {p f : ℕ} {a b u v : ℤ} (h : a * u = b * v)
    (hu : IsCoprime (p : ℤ) u) (huv : (p : ℤ) ^ f ∣ v - u) : (p : ℤ) ^ f ∣ a - b := by
  have h1 : (p : ℤ) ^ f ∣ (a - b) * u := by
    have e : (a - b) * u = b * (v - u) := by linear_combination h
    rw [e]
    exact dvd_mul_of_dvd_right huv _
  exact hu.pow_left.dvd_of_dvd_mul_right h1

/-- `E(pX, y) ≡ E(X, ⌊y/p⌋)` modulo every `p ^ f` dividing `pX`. -/
theorem E_cong {p : ℕ} (hp : p.Prime) {f : ℕ} {X : ℤ} (hX : (p : ℤ) ^ f ∣ p * X) (y : ℕ) :
    (p : ℤ) ^ f ∣ E (p * X) y - E X (y / p) :=
  dvd_sub_of_mul_eq (E_descent hp.pos X y) (isCoprime_uprod hp y)
    (uprod_sub_dvd p (dvd_neg.2 hX) y)

/-- `C(pX, pk) ≡ C(X, k)` modulo every `p ^ f` dividing `pX`. -/
theorem choose_cong {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {f : ℕ} {X : ℤ}
    (hX : (p : ℤ) ^ f ∣ p * X) (k : ℕ) :
    (p : ℤ) ^ f ∣ Ring.choose (p * X) (p * k) - Ring.choose X k :=
  dvd_sub_of_mul_eq (choose_ratio hp hp2 X k) (isCoprime_uprod hp _)
    (uprod_sub_dvd p (dvd_neg.2 hX) _)

/-- `C(X, i)` is divisible by every `p ^ f` dividing `X` when `p ∤ i`. -/
theorem rchoose_dvd {p : ℕ} (hp : p.Prime) {f i : ℕ} (hi : ¬ p ∣ i) {X : ℤ}
    (hX : (p : ℤ) ^ f ∣ X) : (p : ℤ) ^ f ∣ Ring.choose X i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 :=
    ⟨i - 1, by have : i ≠ 0 := fun h => hi (h ▸ dvd_zero p); omega⟩
  have h := rchoose_succ_mul' X k
  have hc : IsCoprime ((p : ℤ) ^ f) ((k : ℤ) + 1) := by
    apply IsCoprime.pow_left
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, Nat.isCoprime_iff_coprime]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hi
  refine hc.dvd_of_dvd_mul_right ?_
  rw [h]
  exact dvd_mul_of_dvd_left hX _

/-- `p ^ (s - e) ∣ C(X, k)` when `p ^ s ∣ X` and `p ^ (e + 1) ∤ k`. -/
theorem rchoose_pow_dvd {p : ℕ} [Fact p.Prime] {s e k : ℕ} (hk : ¬ p ^ (e + 1) ∣ k) {X : ℤ}
    (hX : (p : ℤ) ^ s ∣ X) : (p : ℤ) ^ (s - e) ∣ Ring.choose X k := by
  obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 :=
    ⟨k - 1, by have : k ≠ 0 := fun h => hk (h ▸ dvd_zero _); omega⟩
  refine int_pow_dvd_of_pow_dvd_mul (y := k₀ + 1) ?_ hk
  have h := rchoose_succ_mul' X k₀
  rw [show ((k₀ + 1 : ℕ) : ℤ) = (k₀ : ℤ) + 1 by push_cast; ring, mul_comm, h]
  exact dvd_mul_of_dvd_left hX _

theorem sq_sub_sq_dvd {M : Type*} [CommRing M] {d a b : M} (h : d ∣ a - b) : d ∣ a ^ 2 - b ^ 2 := by
  rw [sq, sq]; exact mul_sub_mul_dvd h h

/-! ### Splitting a range by divisibility -/

theorem sum_dvd_range {M : Type*} [AddCommMonoid M] {p : ℕ} (hp : 0 < p) (g : ℕ → M) :
    ∀ j : ℕ, ∑ i ∈ range (j + 1), (if p ∣ i then g i else 0) =
      ∑ i ∈ range (j / p + 1), g (p * i)
  | 0 => by simp
  | j + 1 => by
    rw [sum_range_succ, sum_dvd_range hp g j]
    by_cases hd : p ∣ j + 1
    · rw [ite_eq_left hd, Nat.succ_div_of_dvd hd, sum_range_succ _ (j / p + 1), ← div_succ_eq hd]
    · rw [ite_eq_right hd, Nat.succ_div_of_not_dvd hd, add_zero]

theorem sum_split {M : Type*} [AddCommMonoid M] {p : ℕ} (hp : 0 < p) (g : ℕ → M) (j : ℕ) :
    ∑ i ∈ range (j + 1), g i = ∑ i ∈ range (j + 1), (if p ∣ i then 0 else g i) +
      ∑ i ∈ range (j / p + 1), g (p * i) := by
  rw [← sum_dvd_range hp g j, ← sum_add_distrib]
  exact sum_congr rfl (fun i _ => by split_ifs <;> simp)

theorem sum_range_ite_lt {M : Type*} [AddCommMonoid M] (g : ℕ → M) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ range a, g i = ∑ i ∈ range b, (if i < a then g i else 0) := by
  rw [sum_range_eq_of_vanish (fun i => if i < a then g i else 0) hab
    (fun i hi _ => by rw [ite_eq_right (by omega)])]
  exact sum_congr rfl (fun i hi => by rw [ite_eq_left (mem_range.1 hi)])

/-! ### The Euler double sum and the two unit-layer kernels -/

/-- The summand `C(N, k)^2 C(N+k, k)^2 (-1)^{k-i} C(N-1, k-i) C(N+i-1, i)^2` of the Euler
double sum, with integer tops: `C(N+k, k) = E(-N, k)` and `C(N+i-1, i)^2 = C(-N, i)^2`. -/
def F (N : ℤ) (k i : ℕ) : ℤ :=
  Ring.choose N k ^ 2 * E (-N) k ^ 2 * E N (k - i) * Ring.choose (-N) i ^ 2

/-- The Euler double sum `∑_{i ≤ k ≤ N} F(N; k, i)`. -/
def aE (N : ℕ) : ℤ := ∑ k ∈ range (N + 1), ∑ i ∈ range (k + 1), F N k i

/-- The Euler form `∑_{i ≤ j} (-1)^{j-i} C(M-1, j-i) C(M+i-1, i)^2` of `T(M-1, j)`. -/
def TE (M : ℤ) (j : ℕ) : ℤ := ∑ i ∈ range (j + 1), E M (j - i) * Ring.choose (-M) i ^ 2

/-- The kernel `Ψ(M; j) = C(M-1, j)^2 C(M+j, j)^2 T(M-1, j)` of the layer `p ∤ k`, `p ∣ i`. -/
def Psi (M : ℤ) (j : ℕ) : ℤ := E M j ^ 2 * E (-M) j ^ 2 * TE M j

/-- The kernel `Ω(M; l) = C(M+l, l)^2 ∑_{k > l} (-1)^{k-l-1} C(M, k)^2 C(M+k, k)^2 C(M-1, k-l-1)`
of the layer `p ∣ k`, `p ∤ i`. -/
def Omega (M l : ℕ) : ℤ :=
  E (-(M : ℤ)) l ^ 2 * ∑ k ∈ range (M + 1),
    if l < k then Ring.choose (M : ℤ) k ^ 2 * E (-(M : ℤ)) k ^ 2 * E M (k - l - 1) else 0

section Descents

variable {p : ℕ}

theorem TE_descent (hp : p.Prime) (hp2 : p ≠ 2) {f : ℕ} {M : ℤ} (hM : (p : ℤ) ^ f ∣ p * M) (j : ℕ) :
    (p : ℤ) ^ f ∣ TE (p * M) j - TE M (j / p) := by
  have hp0 := hp.pos
  have hneg : (p : ℤ) ^ f ∣ p * -M := by rw [mul_neg]; exact dvd_neg.2 hM
  unfold TE
  rw [sum_split hp0 _ j, add_sub_assoc, ← sum_sub_distrib]
  refine dvd_add (dvd_sum (fun i _ => ?_)) (dvd_sum (fun i _ => ?_))
  · split_ifs with hi
    · exact dvd_zero _
    · refine dvd_mul_of_dvd_right ?_ _
      rw [sq]
      refine dvd_mul_of_dvd_left (rchoose_dvd hp hi ?_) _
      rw [← mul_neg]; exact hneg
  · have h1 := E_cong hp hM (j - p * i)
    have hdiv : (j - p * i) / p = j / p - i := Nat.sub_mul_div j p i
    rw [hdiv] at h1
    have h2 := choose_cong hp hp2 hneg i
    rw [← mul_neg]
    exact mul_sub_mul_dvd h1 (sq_sub_sq_dvd h2)

theorem Psi_descent (hp : p.Prime) (hp2 : p ≠ 2) {f : ℕ} {M : ℤ} (hM : (p : ℤ) ^ f ∣ p * M) (j : ℕ) :
    (p : ℤ) ^ f ∣ Psi (p * M) j - Psi M (j / p) := by
  have hneg : (p : ℤ) ^ f ∣ p * -M := by rw [mul_neg]; exact dvd_neg.2 hM
  unfold Psi
  rw [← mul_neg]
  exact mul_sub_mul_dvd (mul_sub_mul_dvd (sq_sub_sq_dvd (E_cong hp hM j))
    (sq_sub_sq_dvd (E_cong hp hneg j))) (TE_descent hp hp2 hM j)

theorem Omega_descent (hp : p.Prime) (hp2 : p ≠ 2) {f M : ℕ} (hM : (p : ℤ) ^ f ∣ p * M) (l : ℕ) :
    (p : ℤ) ^ f ∣ Omega (p * M) l - Omega M (l / p) := by
  have hp0 := hp.pos
  have hneg : (p : ℤ) ^ f ∣ p * -(M : ℤ) := by rw [mul_neg]; exact dvd_neg.2 hM
  have hc : ((p * M : ℕ) : ℤ) = (p : ℤ) * M := by push_cast; ring
  unfold Omega
  rw [hc, ← mul_neg]
  refine mul_sub_mul_dvd (sq_sub_sq_dvd (E_cong hp hneg l)) ?_
  rw [sum_split hp0 _ (p * M), Nat.mul_div_cancel_left _ hp0, add_sub_assoc, ← sum_sub_distrib]
  refine dvd_add (dvd_sum (fun k _ => ?_)) (dvd_sum (fun k _ => ?_))
  · split_ifs with hk hlk
    · exact dvd_zero _
    · refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ?_ _) _
      rw [sq]
      exact dvd_mul_of_dvd_left (rchoose_dvd hp hk hM) _
    · exact dvd_zero _
  · have hiff : l < p * k ↔ l / p < k := by
      rw [Nat.div_lt_iff_lt_mul hp0, mul_comm]
    by_cases hlk : l < p * k
    · rw [ite_eq_left hlk, ite_eq_left (hiff.1 hlk)]
      have h1 := E_cong hp hM (p * k - l - 1)
      rw [div_sub_sub_one hp0 (dvd_mul_right p k) hlk, Nat.mul_div_cancel_left _ hp0] at h1
      have h2 := E_cong hp hneg (p * k)
      rw [Nat.mul_div_cancel_left _ hp0] at h2
      exact mul_sub_mul_dvd (mul_sub_mul_dvd (sq_sub_sq_dvd (choose_cong hp hp2 hM k))
        (sq_sub_sq_dvd h2)) h1
    · rw [ite_eq_right hlk, ite_eq_right (fun h => hlk (hiff.2 h)), sub_zero]
      exact dvd_zero _

end Descents

/-! ### The divisible layer -/

section Divisible

variable {p : ℕ} [hp : Fact p.Prime]

/-- The exact descent of `F` on pairs of multiples of `p`. -/
theorem F_ratio (hp2 : p ≠ 2) (N' k' i' : ℕ) :
    F ((p : ℤ) * N') (p * k') (p * i') *
      (uprod p 0 (p * k') ^ 2 * uprod p 0 (p * k') ^ 2 * uprod p 0 (p * (k' - i')) *
        uprod p 0 (p * i') ^ 2) =
    F N' k' i' *
      (uprod p (-((p : ℤ) * N')) (p * k') ^ 2 * uprod p ((p : ℤ) * N') (p * k') ^ 2 *
        uprod p (-((p : ℤ) * N')) (p * (k' - i')) * uprod p ((p : ℤ) * N') (p * i') ^ 2) := by
  have hpr := hp.out
  have r1 := choose_ratio hpr hp2 (N' : ℤ) k'
  have r2 : E (-((p : ℤ) * N')) (p * k') * uprod p 0 (p * k') =
      E (-(N' : ℤ)) k' * uprod p ((p : ℤ) * N') (p * k') := by
    have h := E_descent hpr.pos (-(N' : ℤ)) (p * k')
    rwa [Nat.mul_div_cancel_left _ hpr.pos, mul_neg, neg_neg] at h
  have r3 := E_descent hpr.pos (N' : ℤ) (p * (k' - i'))
  rw [Nat.mul_div_cancel_left _ hpr.pos] at r3
  have r4 : Ring.choose (-((p : ℤ) * N')) (p * i') * uprod p 0 (p * i') =
      Ring.choose (-(N' : ℤ)) i' * uprod p ((p : ℤ) * N') (p * i') := by
    have h := choose_ratio hpr hp2 (-(N' : ℤ)) i'
    rwa [mul_neg, neg_neg] at h
  unfold F
  rw [← Nat.mul_sub]
  calc _ = (Ring.choose ((p : ℤ) * N') (p * k') * uprod p 0 (p * k')) ^ 2 *
        (E (-((p : ℤ) * N')) (p * k') * uprod p 0 (p * k')) ^ 2 *
        (E ((p : ℤ) * N') (p * (k' - i')) * uprod p 0 (p * (k' - i'))) *
        (Ring.choose (-((p : ℤ) * N')) (p * i') * uprod p 0 (p * i')) ^ 2 := by ring
    _ = _ := by rw [r1, r2, r3, r4]; ring

/-- The divisible layer: `F(pN'; pk', pi') ≡ F(N'; k', i') (mod p^{3r})` when `p^{r-1} ∣ N'`. -/
theorem div_layer (hp5 : 5 ≤ p) {r N' : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N') (k' i' : ℕ) :
    (F ((p : ℤ) * N') (p * k') (p * i') : ZMod (p ^ (3 * r))) =
      (F N' k' i' : ZMod (p ^ (3 * r))) := by
  have hpr := hp.out
  have hp2 : p ≠ 2 := by omega
  have hI := F_ratio hp2 N' k' i'
  set e := Nat.findGreatest (fun e => p ^ e ∣ k' ∧ p ^ e ∣ i') (r - 1) with he
  have he1 : e ≤ r - 1 := Nat.findGreatest_le _
  have he2 : p ^ e ∣ k' ∧ p ^ e ∣ i' :=
    Nat.findGreatest_spec (P := fun e => p ^ e ∣ k' ∧ p ^ e ∣ i') (Nat.zero_le _) (by simp)
  have he3 : e < r - 1 → ¬ (p ^ (e + 1) ∣ k' ∧ p ^ (e + 1) ∣ i') := fun h =>
    Nat.findGreatest_is_greatest (P := fun e => p ^ e ∣ k' ∧ p ^ e ∣ i') (Nat.lt_succ_self _)
      (by omega)
  have hpow : (p : ZMod (p ^ (3 * r))) ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hZ : (p : ZMod (p ^ (3 * r))) ^ r ∣ (((p : ℤ) * N' : ℤ) : ZMod (p ^ (3 * r))) := by
    obtain ⟨t, ht⟩ := hN'
    exact ⟨t, by rw [ht, hpow]; push_cast; ring⟩
  have hZn : (p : ZMod (p ^ (3 * r))) ^ r ∣ ((-((p : ℤ) * N') : ℤ) : ZMod (p ^ (3 * r))) := by
    rw [Int.cast_neg]; exact dvd_neg.2 hZ
  have j1 := PR_sub_one (K := 3 * r) hp5 hr he1 he2.1 hZn
  have j2 := PR_sub_one (K := 3 * r) hp5 hr he1 he2.1 hZ
  have j3 := PR_sub_one (K := 3 * r) hp5 hr he1 (Nat.dvd_sub he2.1 he2.2) hZn
  have j4 := PR_sub_one (K := 3 * r) hp5 hr he1 he2.2 hZ
  set P1 := PR p (3 * r) ((-((p : ℤ) * N') : ℤ) : ZMod (p ^ (3 * r))) k'
  set P2 := PR p (3 * r) (((p : ℤ) * N' : ℤ) : ZMod (p ^ (3 * r))) k'
  set P3 := PR p (3 * r) ((-((p : ℤ) * N') : ℤ) : ZMod (p ^ (3 * r))) (k' - i')
  set P4 := PR p (3 * r) (((p : ℤ) * N' : ℤ) : ZMod (p ^ (3 * r))) i'
  set G := P1 ^ 2 * P2 ^ 2 * P3 * P4 ^ 2 with hG
  have hk : (p : ZMod (p ^ (3 * r))) ^ (r + 2 + 2 * e) ∣ G - 1 := by
    simp only [hG, sq]
    exact mul_sub_one_dvd (mul_sub_one_dvd (mul_sub_one_dvd (mul_sub_one_dvd j1 j1)
      (mul_sub_one_dvd j2 j2)) j3) (mul_sub_one_dvd j4 j4)
  have c1 : (uprod p (-((p : ℤ) * N')) (p * k') : ZMod (p ^ (3 * r))) =
      P1 * (uprod p 0 (p * k') : ZMod (p ^ (3 * r))) := uprod_cast _ _
  have c2 : (uprod p ((p : ℤ) * N') (p * k') : ZMod (p ^ (3 * r))) =
      P2 * (uprod p 0 (p * k') : ZMod (p ^ (3 * r))) := uprod_cast _ _
  have c3 : (uprod p (-((p : ℤ) * N')) (p * (k' - i')) : ZMod (p ^ (3 * r))) =
      P3 * (uprod p 0 (p * (k' - i')) : ZMod (p ^ (3 * r))) := uprod_cast _ _
  have c4 : (uprod p ((p : ℤ) * N') (p * i') : ZMod (p ^ (3 * r))) =
      P4 * (uprod p 0 (p * i') : ZMod (p ^ (3 * r))) := uprod_cast _ _
  set D : ZMod (p ^ (3 * r)) := (uprod p 0 (p * k') : ZMod (p ^ (3 * r))) ^ 2 *
    (uprod p 0 (p * k') : ZMod (p ^ (3 * r))) ^ 2 * (uprod p 0 (p * (k' - i')) : ZMod (p ^ (3 * r))) *
    (uprod p 0 (p * i') : ZMod (p ^ (3 * r))) ^ 2 with hD
  have hDu : IsUnit D := by
    simp only [hD]
    exact (((isUnit_uprod _).pow 2).mul ((isUnit_uprod _).pow 2)).mul (isUnit_uprod _) |>.mul
      ((isUnit_uprod _).pow 2)
  have hI' : (F ((p : ℤ) * N') (p * k') (p * i') : ZMod (p ^ (3 * r))) * D =
      (F N' k' i' : ZMod (p ^ (3 * r))) * G * D := by
    have := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * r))) hI
    push_cast at this
    rw [c1, c2, c3, c4] at this
    simp only [hD, hG]
    linear_combination this
  have hFG : (F ((p : ℤ) * N') (p * k') (p * i') : ZMod (p ^ (3 * r))) =
      (F N' k' i' : ZMod (p ^ (3 * r))) * G := hDu.mul_right_cancel hI'
  apply eq_of_sub_eq_zero
  apply eq_zero_of_pow_dvd
  rw [hFG, show (F N' k' i' : ZMod (p ^ (3 * r))) * G - F N' k' i' =
    (F N' k' i' : ZMod (p ^ (3 * r))) * (G - 1) by ring]
  by_cases hlt : e < r - 1
  · have hnd := he3 hlt
    have hN'' : (p : ℤ) ^ (r - 1) ∣ (N' : ℤ) := by exact_mod_cast hN'
    have hS : (p : ℤ) ^ (2 * (r - 1 - e)) ∣ F N' k' i' := by
      unfold F
      rw [two_mul, pow_add]
      by_cases hk' : p ^ (e + 1) ∣ k'
      · have hi' : ¬ p ^ (e + 1) ∣ i' := fun h => hnd ⟨hk', h⟩
        obtain ⟨c, hc⟩ := rchoose_pow_dvd hi' (dvd_neg.2 hN'')
        rw [hc]
        exact ⟨Ring.choose (N' : ℤ) k' ^ 2 * E (-(N' : ℤ)) k' ^ 2 * E N' (k' - i') * c ^ 2, by ring⟩
      · obtain ⟨c, hc⟩ := rchoose_pow_dvd hk' hN''
        rw [hc]
        exact ⟨c ^ 2 * E (-(N' : ℤ)) k' ^ 2 * E N' (k' - i') * Ring.choose (-(N' : ℤ)) i' ^ 2,
          by ring⟩
    have hS' : (p : ZMod (p ^ (3 * r))) ^ (2 * (r - 1 - e)) ∣ (F N' k' i' : ZMod (p ^ (3 * r))) := by
      obtain ⟨t, ht⟩ := hS
      exact ⟨(t : ZMod (p ^ (3 * r))), by rw [ht]; push_cast; ring⟩
    have := mul_dvd_mul hS' hk
    rwa [← pow_add, show 2 * (r - 1 - e) + (r + 2 + 2 * e) = 3 * r by omega] at this
  · have he' : e = r - 1 := by omega
    rw [he', show r + 2 + 2 * (r - 1) = 3 * r by omega] at hk
    exact dvd_mul_of_dvd_right hk _

end Divisible

/-- `C(X, k)^2 k^2 = X^2 E(X, k-1)^2` for `k ≥ 1`. -/
theorem choose_sq_mul (X : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    Ring.choose X k ^ 2 * (k : ℤ) ^ 2 = X ^ 2 * E X (k - 1) ^ 2 := by
  obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
  have h := rchoose_succ_mul' X k₀
  have hs := neg_one_pow_mul_self k₀
  rw [Nat.add_sub_cancel]
  unfold E
  push_cast
  linear_combination (Ring.choose X (k₀ + 1) * ((k₀ : ℤ) + 1) + X * Ring.choose (X - 1) k₀) * h
    - X ^ 2 * Ring.choose (X - 1) k₀ ^ 2 * hs

theorem pow_dvd_mul_of_dvd {p r N' : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N') :
    (p : ℤ) ^ r ∣ (p : ℤ) * N' := by
  obtain ⟨t, rfl⟩ := hN'
  exact ⟨t, by push_cast; rw [show (p : ℤ) ^ r = p * p ^ (r - 1) by
    rw [← pow_succ']; congr 1; omega]; ring⟩

section UnitLayers

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- If `p ^ a ∣ z` and `p ^ b ∣ x - y` with `K ≤ a + b`, then `z x = z y` in `ZMod (p ^ K)`. -/
theorem mul_eq_of_dvd {K a b : ℕ} (hab : K ≤ a + b) {z : ZMod (p ^ K)}
    (hz : (p : ZMod (p ^ K)) ^ a ∣ z) {x y : ℤ} (hxy : (p : ℤ) ^ b ∣ x - y) :
    z * (x : ZMod (p ^ K)) = z * (y : ZMod (p ^ K)) := by
  apply eq_of_sub_eq_zero
  apply eq_zero_of_pow_dvd
  rw [← mul_sub]
  have := mul_dvd_mul hz (intCast_dvd_sub (K := K) hxy)
  rw [← pow_add] at this
  exact pow_dvd_of_le _ hab this

omit hp in
theorem sq_natCast_dvd {r N' : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N') :
    (p : ZMod (p ^ (3 * r))) ^ (2 * r) ∣ (((p : ℤ) * N' : ℤ) : ZMod (p ^ (3 * r))) ^ 2 := by
  obtain ⟨t, ht⟩ := pow_dvd_mul_of_dvd hr hN'
  have h1 : (p : ZMod (p ^ (3 * r))) ^ r ∣ (((p : ℤ) * N' : ℤ) : ZMod (p ^ (3 * r))) :=
    ⟨(t : ZMod (p ^ (3 * r))), by rw [ht]; push_cast; ring⟩
  rw [pow_mul' (p : ZMod (p ^ (3 * r))) 2 r]
  exact pow_dvd_pow_of_dvd h1 2

/-- Layer `p ∤ k`, `p ∣ i`, for one `k`: `∑_{i'} F(N; k, pi') ≡ N^2 k^{-2} Ψ(N'; ⌊k/p⌋)`. -/
theorem layerA_term (hp5 : 5 ≤ p) {r N' k : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N')
    (hk : ¬ p ∣ k) :
    ∑ i ∈ range (k / p + 1), (F ((p : ℤ) * N') k (p * i) : ZMod (p ^ (3 * r))) =
      (((p : ℤ) * N' : ℤ) : ZMod (p ^ (3 * r))) ^ 2 * invSq p (3 * r) k *
        (Psi N' (k / p) : ZMod (p ^ (3 * r))) := by
  have hpr := hp.out
  have hp2 : p ≠ 2 := by omega
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun h => hk (h ▸ dvd_zero p))
  have hpN := pow_dvd_mul_of_dvd hr hN'
  have hneg : (p : ℤ) ^ r ∣ (p : ℤ) * -(N' : ℤ) := by rw [mul_neg]; exact dvd_neg.2 hpN
  set N : ℤ := (p : ℤ) * N' with hN
  set br : ℕ → ℤ := fun i =>
    E N (k - 1) ^ 2 * E (-N) k ^ 2 * (E N (k - p * i) * Ring.choose (-N) (p * i) ^ 2) with hbr
  have hsq := choose_sq_mul N hk1
  have hex : ∀ i, (F N k (p * i) : ZMod (p ^ (3 * r))) =
      (N : ZMod (p ^ (3 * r))) ^ 2 * invSq p (3 * r) k * (br i : ZMod (p ^ (3 * r))) := by
    intro i
    have e : F N k (p * i) * (k : ℤ) ^ 2 = N ^ 2 * br i := by
      simp only [hbr, F]
      linear_combination (E (-N) k ^ 2 * E N (k - p * i) * Ring.choose (-N) (p * i) ^ 2) * hsq
    have e' := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * r))) e
    push_cast at e'
    have hu := natCast_mul_inv (K := 3 * r) hk
    simp only [invSq, ite_eq_right hk]
    linear_combination ((k : ZMod (p ^ (3 * r)))⁻¹) ^ 2 * e' -
      (F N k (p * i) : ZMod (p ^ (3 * r))) * ((k : ZMod (p ^ (3 * r))) * (k : ZMod (p ^ (3 * r)))⁻¹ + 1) * hu
  have hdiv1 : (k - 1) / p = k / p := by
    have := Nat.succ_div_of_not_dvd (a := k - 1) (by rwa [show k - 1 + 1 = k by omega])
    rw [show k - 1 + 1 = k by omega] at this
    exact this.symm
  have c1 := E_cong hpr hpN (k - 1)
  rw [hdiv1] at c1
  have c2 := E_cong hpr hneg k
  rw [mul_neg] at c2
  have hcong : (p : ℤ) ^ r ∣ ∑ i ∈ range (k / p + 1), br i - Psi N' (k / p) := by
    unfold Psi TE
    rw [mul_sum, ← sum_sub_distrib]
    refine dvd_sum (fun i _ => ?_)
    have c3 := E_cong hpr hpN (k - p * i)
    rw [Nat.sub_mul_div k p i] at c3
    have c4 := choose_cong hpr hp2 hneg i
    rw [mul_neg] at c4
    simp only [hbr]
    exact mul_sub_mul_dvd (mul_sub_mul_dvd (sq_sub_sq_dvd c1) (sq_sub_sq_dvd c2))
      (mul_sub_mul_dvd c3 (sq_sub_sq_dvd c4))
  rw [sum_congr rfl (fun i _ => hex i), ← mul_sum, ← Int.cast_sum]
  exact mul_eq_of_dvd (show 3 * r ≤ 2 * r + r by omega)
    (dvd_mul_of_dvd_left (sq_natCast_dvd hr hN') (invSq p (3 * r) k)) hcong

/-- Layer `p ∣ k`, `p ∤ i`, for one `i`: `∑_{k'} F(N; pk', i) ≡ N^2 i^{-2} Ω(N'; ⌊i/p⌋)`. -/
theorem layerB_term (hp5 : 5 ≤ p) {r N' i : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N')
    (hi : ¬ p ∣ i) :
    ∑ k ∈ range (N' + 1),
        (if i < p * k then (F ((p : ℤ) * N') (p * k) i : ZMod (p ^ (3 * r))) else 0) =
      (((p : ℤ) * N' : ℤ) : ZMod (p ^ (3 * r))) ^ 2 * invSq p (3 * r) i *
        (Omega N' (i / p) : ZMod (p ^ (3 * r))) := by
  have hpr := hp.out
  have hp0 := hpr.pos
  have hp2 : p ≠ 2 := by omega
  have hi1 : 1 ≤ i := Nat.pos_of_ne_zero (fun h => hi (h ▸ dvd_zero p))
  have hpN := pow_dvd_mul_of_dvd hr hN'
  have hneg : (p : ℤ) ^ r ∣ (p : ℤ) * -(N' : ℤ) := by rw [mul_neg]; exact dvd_neg.2 hpN
  set N : ℤ := (p : ℤ) * N' with hN
  set br : ℕ → ℤ := fun k => if i < p * k then
    Ring.choose N (p * k) ^ 2 * E (-N) (p * k) ^ 2 * E N (p * k - i) * E (-N) (i - 1) ^ 2 else 0
    with hbr
  have hsq := choose_sq_mul (-N) hi1
  rw [neg_sq] at hsq
  have hex : ∀ k, (if i < p * k then (F N (p * k) i : ZMod (p ^ (3 * r))) else 0) =
      (N : ZMod (p ^ (3 * r))) ^ 2 * invSq p (3 * r) i * (br k : ZMod (p ^ (3 * r))) := by
    intro k
    simp only [hbr]
    by_cases hik : i < p * k
    · rw [ite_eq_left hik, ite_eq_left hik]
      have e : F N (p * k) i * (i : ℤ) ^ 2 =
          N ^ 2 * (Ring.choose N (p * k) ^ 2 * E (-N) (p * k) ^ 2 * E N (p * k - i) *
            E (-N) (i - 1) ^ 2) := by
        unfold F
        linear_combination (Ring.choose N (p * k) ^ 2 * E (-N) (p * k) ^ 2 * E N (p * k - i)) * hsq
      have e' := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * r))) e
      push_cast at e'
      have hu := natCast_mul_inv (K := 3 * r) hi
      simp only [invSq, ite_eq_right hi]
      push_cast
      linear_combination ((i : ZMod (p ^ (3 * r)))⁻¹) ^ 2 * e' -
        (F N (p * k) i : ZMod (p ^ (3 * r))) *
          ((i : ZMod (p ^ (3 * r))) * (i : ZMod (p ^ (3 * r)))⁻¹ + 1) * hu
    · rw [ite_eq_right hik, ite_eq_right hik, Int.cast_zero, mul_zero]
  have hdiv1 : (i - 1) / p = i / p := by
    have := Nat.succ_div_of_not_dvd (a := i - 1) (by rwa [show i - 1 + 1 = i by omega])
    rw [show i - 1 + 1 = i by omega] at this
    exact this.symm
  have d4 := E_cong hpr hneg (i - 1)
  rw [mul_neg, hdiv1] at d4
  have hcong : (p : ℤ) ^ r ∣ ∑ k ∈ range (N' + 1), br k - Omega N' (i / p) := by
    unfold Omega
    rw [mul_sum, ← sum_sub_distrib]
    refine dvd_sum (fun k _ => ?_)
    simp only [hbr]
    have hiff : i < p * k ↔ i / p < k := by
      rw [Nat.div_lt_iff_lt_mul hp0, mul_comm]
    by_cases hik : i < p * k
    · rw [ite_eq_left hik, ite_eq_left (hiff.1 hik)]
      have d1 := choose_cong hpr hp2 hpN k
      have d2 := E_cong hpr hneg (p * k)
      rw [mul_neg, Nat.mul_div_cancel_left _ hp0] at d2
      have d3 := E_cong hpr hpN (p * k - i)
      have hd3 : (p * k - i) / p = k - i / p - 1 := by
        rw [show p * k - i = p * k - (i - 1) - 1 by omega,
          div_sub_sub_one hp0 (dvd_mul_right p k) (by omega), Nat.mul_div_cancel_left _ hp0, hdiv1]
      rw [hd3] at d3
      rw [show E (-(N' : ℤ)) (i / p) ^ 2 * (Ring.choose (N' : ℤ) k ^ 2 * E (-(N' : ℤ)) k ^ 2 *
          E (N' : ℤ) (k - i / p - 1)) = Ring.choose (N' : ℤ) k ^ 2 * E (-(N' : ℤ)) k ^ 2 *
          E (N' : ℤ) (k - i / p - 1) * E (-(N' : ℤ)) (i / p) ^ 2 by ring]
      exact mul_sub_mul_dvd (mul_sub_mul_dvd (mul_sub_mul_dvd (sq_sub_sq_dvd d1)
        (sq_sub_sq_dvd d2)) d3) (sq_sub_sq_dvd d4)
    · rw [ite_eq_right hik, ite_eq_right (fun h => hik (hiff.2 h)), mul_zero, sub_zero]
      exact dvd_zero _
  rw [sum_congr rfl (fun k _ => hex k), ← mul_sum, ← Int.cast_sum]
  exact mul_eq_of_dvd (show 3 * r ≤ 2 * r + r by omega)
    (dvd_mul_of_dvd_left (sq_natCast_dvd hr hN') (invSq p (3 * r) i)) hcong

/-- Layer `p ∤ k`, `p ∤ i`: each term is divisible by `p^{4r}`. -/
theorem layerC_term {r N' k i : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N') (hk : ¬ p ∣ k)
    (hi : ¬ p ∣ i) : (F ((p : ℤ) * N') k i : ZMod (p ^ (3 * r))) = 0 := by
  have hpr := hp.out
  have hpN := pow_dvd_mul_of_dvd hr hN'
  obtain ⟨a, ha⟩ := rchoose_dvd hpr hk hpN
  obtain ⟨b, hb⟩ := rchoose_dvd hpr hi (dvd_neg.2 hpN)
  have hF : (p : ℤ) ^ (3 * r) ∣ F ((p : ℤ) * N') k i := by
    unfold F
    rw [ha, hb]
    exact ⟨(p : ℤ) ^ r * a ^ 2 * E (-((p : ℤ) * N')) k ^ 2 * E ((p : ℤ) * N') (k - i) * b ^ 2,
      by ring⟩
  apply eq_zero_of_pow_dvd
  obtain ⟨t, ht⟩ := hF
  exact ⟨(t : ZMod (p ^ (3 * r))), by rw [ht]; push_cast; ring⟩

end UnitLayers

section Tower

variable {p : ℕ} [hp : Fact p.Prime]

/-- Layer `p ∤ k`, `p ∣ i` in total: `∑_{p ∤ k} ∑_{i'} F(N; k, pi') ≡ 0 (mod p^{3r})`. -/
theorem layerA (hp5 : 5 ≤ p) {n r N' : ℕ} (hr : 1 ≤ r) (hN'd : n * p ^ (r - 1) = N') :
    ∑ k ∈ range (p * N' + 1), (if p ∣ k then 0 else
      ∑ i ∈ range (k / p + 1), (F ((p : ℤ) * N') k (p * i) : ZMod (p ^ (3 * r)))) = 0 := by
  have hpr := hp.out
  have hp0 := hpr.pos
  have hp2 : p ≠ 2 := by omega
  have hN' : p ^ (r - 1) ∣ N' := hN'd ▸ dvd_mul_left _ _
  have step : ∀ k ∈ range (p * N' + 1), (if p ∣ k then 0 else
      ∑ i ∈ range (k / p + 1), (F ((p : ℤ) * N') k (p * i) : ZMod (p ^ (3 * r)))) =
      (((p : ℤ) * N' : ℤ) : ZMod (p ^ (3 * r))) ^ 2 *
        (invSq p (3 * r) k * (Psi N' (k / p) : ZMod (p ^ (3 * r)))) := by
    intro k _
    by_cases hk : p ∣ k
    · rw [ite_eq_left hk]; simp [invSq, hk]
    · rw [ite_eq_right hk, layerA_term hp5 hr hN' hk, mul_assoc]
  rw [sum_congr rfl step, ← mul_sum, sum_range_succ,
    show invSq p (3 * r) (p * N') = 0 from ite_eq_left (dvd_mul_right p N'), zero_mul, add_zero]
  have hNr : p * N' = n * p ^ r := by
    rw [← hN'd, show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]; ring
  rw [hNr]
  have hnb := nested_block (p : ZMod (p ^ (3 * r))) (p := p) (s := r) (L := n) hp0 hr
    (invSq p (3 * r)) (fun u A => (Psi ((n * p ^ (r - u) : ℕ) : ℤ) A : ZMod (p ^ (3 * r))))
    (fun u hu _ D _ => block_invSq hp5 hu D)
    (fun u hu hur A _ => by
      have hM : n * p ^ (r - u) = p * (n * p ^ (r - (u + 1))) := by
        rw [show r - u = (r - (u + 1)) + 1 by omega, pow_succ]; ring
      have hd := Psi_descent hpr hp2 (f := r - u) (M := ((n * p ^ (r - (u + 1)) : ℕ) : ℤ))
        (by rw [← Nat.cast_mul, ← hM]; exact ⟨n, by push_cast; ring⟩) A
      rw [← Nat.cast_mul, ← hM] at hd
      exact intCast_dvd_sub hd)
  simp only [hN'd] at hnb
  apply eq_zero_of_pow_dvd
  have := mul_dvd_mul (sq_natCast_dvd hr hN') hnb
  rwa [← pow_add, show 2 * r + r = 3 * r by ring] at this

/-- Layer `p ∣ k`, `p ∤ i` in total: `∑_{p ∤ i} ∑_{k'} F(N; pk', i) ≡ 0 (mod p^{3r})`. -/
theorem layerB (hp5 : 5 ≤ p) {n r N' : ℕ} (hr : 1 ≤ r) (hN'd : n * p ^ (r - 1) = N') :
    ∑ i ∈ range (p * N' + 1), (if p ∣ i then 0 else
      ∑ k ∈ range (N' + 1),
        (if i < p * k then (F ((p : ℤ) * N') (p * k) i : ZMod (p ^ (3 * r))) else 0)) = 0 := by
  have hpr := hp.out
  have hp0 := hpr.pos
  have hp2 : p ≠ 2 := by omega
  have hN' : p ^ (r - 1) ∣ N' := hN'd ▸ dvd_mul_left _ _
  have step : ∀ i ∈ range (p * N' + 1), (if p ∣ i then 0 else
      ∑ k ∈ range (N' + 1),
        (if i < p * k then (F ((p : ℤ) * N') (p * k) i : ZMod (p ^ (3 * r))) else 0)) =
      (((p : ℤ) * N' : ℤ) : ZMod (p ^ (3 * r))) ^ 2 *
        (invSq p (3 * r) i * (Omega N' (i / p) : ZMod (p ^ (3 * r)))) := by
    intro i _
    by_cases hi : p ∣ i
    · rw [ite_eq_left hi]; simp [invSq, hi]
    · rw [ite_eq_right hi, layerB_term hp5 hr hN' hi, mul_assoc]
  rw [sum_congr rfl step, ← mul_sum, sum_range_succ,
    show invSq p (3 * r) (p * N') = 0 from ite_eq_left (dvd_mul_right p N'), zero_mul, add_zero]
  have hNr : p * N' = n * p ^ r := by
    rw [← hN'd, show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]; ring
  rw [hNr]
  have hnb := nested_block (p : ZMod (p ^ (3 * r))) (p := p) (s := r) (L := n) hp0 hr
    (invSq p (3 * r)) (fun u A => (Omega (n * p ^ (r - u)) A : ZMod (p ^ (3 * r))))
    (fun u hu _ D _ => block_invSq hp5 hu D)
    (fun u hu hur A _ => by
      have hM : n * p ^ (r - u) = p * (n * p ^ (r - (u + 1))) := by
        rw [show r - u = (r - (u + 1)) + 1 by omega, pow_succ]; ring
      have hd := Omega_descent hpr hp2 (f := r - u) (M := n * p ^ (r - (u + 1)))
        (by rw [← Nat.cast_mul, ← hM]; exact ⟨n, by push_cast; ring⟩) A
      rw [← hM] at hd
      exact intCast_dvd_sub hd)
  simp only [hN'd] at hnb
  apply eq_zero_of_pow_dvd
  have := mul_dvd_mul (sq_natCast_dvd hr hN') hnb
  rwa [← pow_add, show 2 * r + r = 3 * r by ring] at this

/-- The tower for the Euler double sum, in `ZMod (p ^ (3 r))`. -/
theorem aE_tower (hp5 : 5 ≤ p) {n r : ℕ} (hr : 1 ≤ r) :
    (aE (n * p ^ r) : ZMod (p ^ (3 * r))) = (aE (n * p ^ (r - 1)) : ZMod (p ^ (3 * r))) := by
  have hpr := hp.out
  have hp0 := hpr.pos
  have hNN : n * p ^ r = p * (n * p ^ (r - 1)) := by
    rw [show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]; ring
  rw [hNN]
  generalize hN'd : n * p ^ (r - 1) = N'
  have hN' : p ^ (r - 1) ∣ N' := hN'd ▸ dvd_mul_left _ _
  unfold aE
  simp only [Nat.cast_mul, Int.cast_sum]
  have e1 : ∀ k, ∑ i ∈ range (k + 1), (F ((p : ℤ) * N') k i : ZMod (p ^ (3 * r))) =
      ∑ i ∈ range (k + 1), (if p ∣ i then 0 else (F ((p : ℤ) * N') k i : ZMod (p ^ (3 * r)))) +
      ∑ i ∈ range (k / p + 1), (F ((p : ℤ) * N') k (p * i) : ZMod (p ^ (3 * r))) :=
    fun k => sum_split hp0 _ k
  rw [sum_congr rfl (fun k _ => e1 k), sum_split hp0 _ (p * N'), Nat.mul_div_cancel_left _ hp0]
  have hC : ∑ k ∈ range (p * N' + 1), (if p ∣ k then 0 else ∑ i ∈ range (k + 1),
      (if p ∣ i then 0 else (F ((p : ℤ) * N') k i : ZMod (p ^ (3 * r))))) = 0 := by
    refine sum_eq_zero (fun k _ => ?_)
    by_cases hk : p ∣ k
    · rw [ite_eq_left hk]
    · rw [ite_eq_right hk]
      refine sum_eq_zero (fun i _ => ?_)
      by_cases hi : p ∣ i
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi]; exact layerC_term hr hN' hk hi
  have hsplit : ∑ k ∈ range (p * N' + 1), (if p ∣ k then 0 else
      (∑ i ∈ range (k + 1), (if p ∣ i then 0 else (F ((p : ℤ) * N') k i : ZMod (p ^ (3 * r)))) +
        ∑ i ∈ range (k / p + 1), (F ((p : ℤ) * N') k (p * i) : ZMod (p ^ (3 * r))))) =
      ∑ k ∈ range (p * N' + 1), (if p ∣ k then 0 else ∑ i ∈ range (k + 1),
        (if p ∣ i then 0 else (F ((p : ℤ) * N') k i : ZMod (p ^ (3 * r))))) +
      ∑ k ∈ range (p * N' + 1), (if p ∣ k then 0 else
        ∑ i ∈ range (k / p + 1), (F ((p : ℤ) * N') k (p * i) : ZMod (p ^ (3 * r)))) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun k _ => by split_ifs <;> simp)
  rw [hsplit, hC, layerA hp5 hr hN'd, zero_add, sum_add_distrib]
  have hB : ∑ k ∈ range (N' + 1), ∑ i ∈ range (p * k + 1),
      (if p ∣ i then 0 else (F ((p : ℤ) * N') (p * k) i : ZMod (p ^ (3 * r)))) = 0 := by
    calc _ = ∑ k ∈ range (N' + 1), ∑ i ∈ range (p * N' + 1), (if p ∣ i then 0 else
          if i < p * k then (F ((p : ℤ) * N') (p * k) i : ZMod (p ^ (3 * r))) else 0) := by
          refine sum_congr rfl (fun k hk => ?_)
          have hk' := Nat.lt_succ_iff.1 (mem_range.1 hk)
          rw [sum_range_ite_lt _ (show p * k + 1 ≤ p * N' + 1 by
            have := Nat.mul_le_mul_left p hk'; omega)]
          refine sum_congr rfl (fun i _ => ?_)
          by_cases hi : p ∣ i
          · simp [hi]
          · by_cases hik : i < p * k
            · simp [hi, hik, show i < p * k + 1 by omega]
            · have h' : ¬ i < p * k + 1 := fun h => by
                have : i = p * k := by omega
                exact hi (this ▸ dvd_mul_right p k)
              simp [hi, hik, h']
      _ = ∑ i ∈ range (p * N' + 1), (if p ∣ i then 0 else ∑ k ∈ range (N' + 1),
          (if i < p * k then (F ((p : ℤ) * N') (p * k) i : ZMod (p ^ (3 * r))) else 0)) := by
          rw [sum_comm]
          refine sum_congr rfl (fun i _ => ?_)
          by_cases hi : p ∣ i
          · rw [ite_eq_left hi]; simp [hi]
          · rw [ite_eq_right hi]
            exact sum_congr rfl (fun k _ => ite_eq_right hi)
      _ = 0 := layerB hp5 hr hN'd
  have hD : ∑ k ∈ range (N' + 1), ∑ i ∈ range (p * k / p + 1),
      (F ((p : ℤ) * N') (p * k) (p * i) : ZMod (p ^ (3 * r))) =
      ∑ k ∈ range (N' + 1), ∑ i ∈ range (k + 1), (F N' k i : ZMod (p ^ (3 * r))) :=
    sum_congr rfl (fun k _ => by
      rw [Nat.mul_div_cancel_left _ hp0]
      exact sum_congr rfl (fun i _ => div_layer hp5 hr hN' k i))
  rw [hB, hD, zero_add, zero_add]

end Tower

theorem E_neg_natCast (N k : ℕ) : E (-(N : ℤ)) k = ((N + k).choose k : ℤ) := by
  unfold E
  rw [show -(N : ℤ) - 1 = -((N + 1 : ℕ) : ℤ) by push_cast; ring, Ring.choose_neg, Units.smul_def,
    Int.coe_negOnePow_natCast, smul_eq_mul,
    show ((N + 1 : ℕ) : ℤ) + k - 1 = ((N + k : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast,
    ← mul_assoc, neg_one_pow_mul_self, one_mul]

theorem rchoose_neg_sq {N : ℕ} (hN : 1 ≤ N) (i : ℕ) :
    Ring.choose (-(N : ℤ)) i ^ 2 = ((N - 1 + i).choose i : ℤ) ^ 2 := by
  rw [Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul,
    show (N : ℤ) + i - 1 = ((N - 1 + i : ℕ) : ℤ) by push_cast [Nat.cast_sub hN]; ring,
    Ring.choose_natCast, mul_pow, sq ((-1 : ℤ) ^ i), neg_one_pow_mul_self, one_mul]

/-- The Euler double sum: `a(N) = ∑_{i ≤ k ≤ N} F(N; k, i)` for `N ≥ 1`. -/
theorem a_eq_aE {N : ℕ} (hN : 1 ≤ N) : (a N : ℤ) = aE N := by
  unfold a aE
  push_cast
  refine sum_congr rfl (fun k _ => ?_)
  rw [T_euler, mul_sum]
  refine sum_congr rfl (fun i _ => ?_)
  unfold F
  rw [Ring.choose_natCast, E_neg_natCast, E_natCast hN, rchoose_neg_sq hN]
  ring

/--
For every prime $p \ge 5$ and all $n, r \ge 1$: $a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$.
- Peter Bala, OEIS A376465, Sep 25 2024 (the first congruence of the pair).
-/
theorem tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have := Fact.mk hp
  have h1 : 1 ≤ n * p ^ r := Nat.mul_pos hn (pow_pos hp.pos r)
  have h2 : 1 ≤ n * p ^ (r - 1) := Nat.mul_pos hn (pow_pos hp.pos (r - 1))
  rw [← ZMod.natCast_eq_natCast_iff]
  have e1 := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * r))) (a_eq_aE h1)
  have e2 := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * r))) (a_eq_aE h2)
  rw [Int.cast_natCast] at e1 e2
  rw [e1, e2, aE_tower hp5 hr]

/--
Bala's second congruence fails: it is not true that for every prime $p \ge 5$ and all
$n, r \ge 1$, $a(np^r - 1) \equiv a(np^{r-1} - 1) \pmod{p^{3r}}$. The case $p = 5$, $n = 2$,
$r = 1$ would give $a(9) \equiv a(1) \pmod{125}$, which `decide +kernel` refutes.
- Peter Bala, OEIS A376465, Sep 25 2024 (the second congruence of the pair, conjectured).
-/
theorem not_shifted_tower : ¬ ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 0 < n → 0 < r →
    a (n * p ^ r - 1) ≡ a (n * p ^ (r - 1) - 1) [MOD p ^ (3 * r)] := by
  intro h
  have h9 : a 9 ≡ a 1 [MOD 125] := h 5 Nat.prime_five le_rfl 2 1 (by norm_num) (by norm_num)
  exact absurd h9 (by decide +kernel)

end OeisA376465

end
