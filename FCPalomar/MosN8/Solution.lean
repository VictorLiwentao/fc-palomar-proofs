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
# McCarthy–Osburn–Straub Conjecture 1.3 for $\sigma_8$, with a shifted companion

This file proves `MosN8.tower` and `MosN8.shifted_tower`: for every prime $p \ge 5$ and all
$m, r \ge 1$,
$$A(m p^r) \equiv A(m p^{r-1}), \qquad A(m p^r - 1) \equiv A(m p^{r-1} - 1) \pmod{p^{3r}},$$
where $A(n) = \sum_{k \in [0,n]^4,\ k_1 + k_2 = k_3 + k_4} \prod_i \binom{n}{k_i}\binom{n+k_i}{k_i}$.
Through [MOS20, Proposition 3.1], whose proof is computer-assisted, $A(n)$ is the leading
coefficient $A_{\sigma_8}(n)$ of Brown's cellular integral for $\sigma_8 = (8,3,6,1,4,7,2,5)$, so
`tower` is Conjecture 1.3 of [MOS20] for $\sigma_8$. The Lean statement is about the explicit sum.

Write $N = m p^r$, $N' = N / p$, $M = N - \delta$ and $M' = N' - \delta$ with $\delta \in \{0, 1\}$,
and $f(x) = \binom{M}{x}\binom{M+x}{x}$. All congruences are equalities in `ZMod (p ^ (3 r))`.

1. **Convolution form** (`fourfold_eq`, `A_cast_eq`). $A(M) = \sum_s c(s)^2$ with
   $c(s) = \sum_{x \le s} f(x) f(s - x)$.
2. **Property (F)** (`F0`, `F1`). $x f(x) = N g(x)$ with $g = $ `g0` ($\delta = 0$) or `g1`
   ($\delta = 1$). So $p^r \mid f(x)$ for $p \nmid x$, and $p^{r-j} \mid f(y)$ when
   $p^{j+1} \nmid y$ (`pow_dvd_of_pow_dvd_mul`).
3. **Splitting** (`conv_eq_split`, `conv_sq_eq`). Split $c(s) = \gamma + \alpha + \beta$ by how
   many of $x$, $s - x$ are divisible by $p$ (two, one, none). By (F),
   $c(s)^2 = \gamma^2 + \alpha^2 + 2 \gamma \beta$.
4. **Divisible layer** (`layer_sum`, `layer_four`). $\sum_s \gamma(s)^2 = \sum_{s'} c'(s')^2 = A(M')$,
   termwise over $a + b = a' + b'$. The exact descent identities (`descent_add_exact`,
   `descent_sub_exact`) give $f(p k) = f'(k) \rho_k$ (`ratio_add`, `ratio_sub`, `ratio_choose`,
   `ratio_shift`), where $\rho_k$ is a product of factors $\prod_{l \le pk,\ p \nmid l}(1 \pm N/l)$.
   A Jacobsthal-type bound proved here (`jacobsthal_prod`: a second-order expansion of the
   product, the harmonic sum `harmonic_dvd` and the inverse-square block sums) gives
   $\rho_k \equiv 1 \pmod{p^{r + 2 + 2e}}$ for $p^e \mid k$, $e \le r - 1$. The minimum valuation
   among $a, b, a', b'$ is attained twice (`two_le_count`), which supplies the missing
   $p^{2(r - 1 - e)}$.
5. **Two-unit classes** (`split_sum_zero`, `one_side_sum_zero`). For fixed divisible entries the
   sum is (prefactor) $\cdot N^2 \cdot$ (kernel sum), with prefactor divisible by $p^{r - \tau}$
   (`pref_dvd`) for $\tau = \min(r, v_p(\cdot))$ (`exists_tau`). The kernel sum is divisible by
   $p^\tau$ (`kernel_sum`, `kernel_one_side`, `kernel_split`): the signed kernel descends through
   $x \mapsto \lfloor x / p^u \rfloor$ (`hZ_descent`, `g0_descent`, `g1_descent`), the weights are
   $\equiv \pm x^{-2}$, the block sums of $x^{-2}$ over the units of a block of length $p^u$ vanish
   modulo $p^u$ for $p \ge 5$ (`block_invSq`), and the nested block lemma (`nested_block`) closes
   the sum.

`main_abstract` combines steps 3–5 for an abstract kernel; `tower_zmod` ($\delta = 0$) and
`tower_shift_zmod` ($\delta = 1$) supply the hypotheses. The hypothesis $p \ge 5$ is used in the
block sums (2 and 3 are units) and through $p$ odd.

*References:*
- [MOS20] D. McCarthy, R. Osburn and A. Straub, *Sequences, modular forms and cellular
  integrals*, Math. Proc. Cambridge Philos. Soc. (2020); arXiv:1705.05586.
-/

@[expose] public section

open Finset

namespace MosN8

/-- The summand $\binom{n}{k} \binom{n + k}{k}$. -/
def term (n k : ℕ) : ℕ := n.choose k * (n + k).choose k

/-- The MOS sum $A(n)$: the sum over $k \in [0, n]^4$ with $k_1 + k_2 = k_3 + k_4$ of
$\prod_{i=1}^{4} \binom{n}{k_i} \binom{n + k_i}{k_i}$. -/
def A (n : ℕ) : ℕ :=
  ∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1), ∑ k₃ ∈ range (n + 1), ∑ k₄ ∈ range (n + 1),
    if k₁ + k₂ = k₃ + k₄ then term n k₁ * term n k₂ * term n k₃ * term n k₄ else 0

/-! ### Sanity checks -/

example : A 0 = 1 := by decide

example : A 1 = 33 := by decide

example : A 2 = 8929 := by decide

/-! ### Divisibility helpers in a commutative ring -/

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

/-- `∏ (l + c)` over the `l ∈ [1, y]` with `p ∤ l`. -/
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

/-- Exact descent for `C(X + y, y)` with `X = p X'`. -/
theorem descent_add_exact {p : ℕ} (X' : ℕ) : ∀ y : ℕ,
    (((p * X' + y).choose y : ℕ) : ℤ) * uprod p 0 y =
      (((X' + y / p).choose (y / p) : ℕ) : ℤ) * uprod p ((p : ℤ) * X') y
  | 0 => by simp [uprod]
  | y + 1 => by
    have ih := descent_add_exact (p := p) X' y
    have h1 : (((p * X' + (y + 1)).choose (y + 1) : ℕ) : ℤ) * ((y : ℤ) + 1) =
        ((p : ℤ) * X' + y + 1) * (((p * X' + y).choose y : ℕ) : ℤ) := by
      have := Nat.add_one_mul_choose_eq (p * X' + y) y
      rw [show p * X' + (y + 1) = p * X' + y + 1 by ring]
      exact_mod_cast this.symm
    rw [uprod_succ, uprod_succ]
    by_cases hd : p ∣ y + 1
    · rw [ite_eq_left hd, ite_eq_left hd, mul_one, mul_one, Nat.succ_div_of_dvd hd]
      have hy : (y : ℤ) + 1 = p * (((y / p : ℕ) : ℤ) + 1) := by exact_mod_cast div_succ_eq hd
      have h2 : (((X' + (y / p + 1)).choose (y / p + 1) : ℕ) : ℤ) * (((y / p : ℕ) : ℤ) + 1) =
          ((X' : ℤ) + (y / p : ℕ) + 1) * (((X' + y / p).choose (y / p) : ℕ) : ℤ) := by
        have := Nat.add_one_mul_choose_eq (X' + y / p) (y / p)
        rw [show X' + (y / p + 1) = X' + y / p + 1 by ring]
        exact_mod_cast this.symm
      apply mul_right_cancel₀ (show (y : ℤ) + 1 ≠ 0 by positivity)
      linear_combination (uprod p 0 y) * h1 + ((p : ℤ) * X' + y + 1) * ih
        - (p : ℤ) * uprod p ((p : ℤ) * X') y * h2
        + ((((X' + y / p).choose (y / p) : ℕ) : ℤ) * uprod p ((p : ℤ) * X') y
          - (((X' + (y / p + 1)).choose (y / p + 1) : ℕ) : ℤ) * uprod p ((p : ℤ) * X') y) * hy
    · rw [ite_eq_right hd, ite_eq_right hd, Nat.succ_div_of_not_dvd hd]
      push_cast
      linear_combination (uprod p 0 y) * h1 + ((p : ℤ) * X' + y + 1) * ih

theorem choose_succ_right_int (n k : ℕ) :
    ((n.choose (k + 1) : ℕ) : ℤ) * ((k : ℤ) + 1) = ((n.choose k : ℕ) : ℤ) * ((n : ℤ) - k) := by
  rcases le_or_gt k n with h | h
  · have := Nat.choose_succ_right_eq n k
    rw [← Nat.cast_sub h]
    exact_mod_cast this
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- Exact signed descent for `C(X - 1, y)` with `X = p X'`. -/
theorem descent_sub_exact {p : ℕ} (hp : 0 < p) {X' : ℕ} (hX' : 1 ≤ X') : ∀ y : ℕ,
    (-1 : ℤ) ^ y * (((p * X' - 1).choose y : ℕ) : ℤ) * uprod p 0 y =
      (-1 : ℤ) ^ (y / p) * (((X' - 1).choose (y / p) : ℕ) : ℤ) * uprod p (-((p : ℤ) * X')) y
  | 0 => by simp [uprod]
  | y + 1 => by
    have ih := descent_sub_exact hp hX' y
    have hpX : 1 ≤ p * X' := Nat.mul_pos hp hX'
    have h1 : (((p * X' - 1).choose (y + 1) : ℕ) : ℤ) * ((y : ℤ) + 1) =
        (((p * X' - 1).choose y : ℕ) : ℤ) * ((p : ℤ) * X' - 1 - y) := by
      rw [choose_succ_right_int, Nat.cast_sub hpX]
      push_cast
      ring
    rw [uprod_succ, uprod_succ]
    by_cases hd : p ∣ y + 1
    · rw [ite_eq_left hd, ite_eq_left hd, mul_one, mul_one, Nat.succ_div_of_dvd hd]
      have hy : (y : ℤ) + 1 = p * (((y / p : ℕ) : ℤ) + 1) := by exact_mod_cast div_succ_eq hd
      have h2 : (((X' - 1).choose (y / p + 1) : ℕ) : ℤ) * (((y / p : ℕ) : ℤ) + 1) =
          (((X' - 1).choose (y / p) : ℕ) : ℤ) * ((X' : ℤ) - 1 - (y / p : ℕ)) := by
        rw [choose_succ_right_int, Nat.cast_sub hX']
        push_cast
        ring
      apply mul_right_cancel₀ (show (y : ℤ) + 1 ≠ 0 by positivity)
      linear_combination (-1 : ℤ) ^ (y + 1) * uprod p 0 y * h1
        - (p : ℤ) * ((X' : ℤ) - (y / p : ℕ) - 1) * ih
        - (p : ℤ) * (-1 : ℤ) ^ (y / p + 1) * uprod p (-((p : ℤ) * X')) y * h2
        - ((-1 : ℤ) ^ (y + 1) * uprod p 0 y * (((p * X' - 1).choose y : ℕ) : ℤ)
          + (-1 : ℤ) ^ (y / p + 1) * (((X' - 1).choose (y / p + 1) : ℕ) : ℤ) *
            uprod p (-((p : ℤ) * X')) y) * hy
    · rw [ite_eq_right hd, ite_eq_right hd, Nat.succ_div_of_not_dvd hd]
      push_cast
      linear_combination (-1 : ℤ) ^ (y + 1) * uprod p 0 y * h1 + ((y : ℤ) + 1 - p * X') * ih

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

/-- Descent for `C(X + y, y)` modulo `p ^ e`, where `p ^ e ∣ X = p X'` (Lemma 2). -/
theorem descent_add_dvd {p : ℕ} (hp : p.Prime) {e X' : ℕ} (he : (p : ℤ) ^ e ∣ (p : ℤ) * X')
    (y : ℕ) :
    (p : ℤ) ^ e ∣ (((p * X' + y).choose y : ℕ) : ℤ) - (((X' + y / p).choose (y / p) : ℕ) : ℤ) := by
  have h := descent_add_exact (p := p) X' y
  have h2 : (p : ℤ) ^ e ∣ ((((p * X' + y).choose y : ℕ) : ℤ) -
      (((X' + y / p).choose (y / p) : ℕ) : ℤ)) * uprod p 0 y := by
    have : ((((p * X' + y).choose y : ℕ) : ℤ) - (((X' + y / p).choose (y / p) : ℕ) : ℤ)) *
        uprod p 0 y = (((X' + y / p).choose (y / p) : ℕ) : ℤ) *
          (uprod p ((p : ℤ) * X') y - uprod p 0 y) := by
      linear_combination h
    rw [this]
    exact dvd_mul_of_dvd_right (uprod_sub_dvd p he y) _
  exact ((isCoprime_uprod hp y).pow_left).dvd_of_dvd_mul_right h2

/-- Signed descent for `C(X - 1, y)` modulo `p ^ e`, where `p ^ e ∣ X = p X'` (Lemma 2′). -/
theorem descent_sub_dvd {p : ℕ} (hp : p.Prime) {e X' : ℕ} (hX' : 1 ≤ X')
    (he : (p : ℤ) ^ e ∣ (p : ℤ) * X') (y : ℕ) :
    (p : ℤ) ^ e ∣ (-1) ^ y * (((p * X' - 1).choose y : ℕ) : ℤ) -
      (-1) ^ (y / p) * (((X' - 1).choose (y / p) : ℕ) : ℤ) := by
  have h := descent_sub_exact hp.pos hX' y
  have h2 : (p : ℤ) ^ e ∣ ((-1) ^ y * (((p * X' - 1).choose y : ℕ) : ℤ) -
      (-1) ^ (y / p) * (((X' - 1).choose (y / p) : ℕ) : ℤ)) * uprod p 0 y := by
    have : ((-1) ^ y * (((p * X' - 1).choose y : ℕ) : ℤ) -
        (-1) ^ (y / p) * (((X' - 1).choose (y / p) : ℕ) : ℤ)) * uprod p 0 y =
        (-1) ^ (y / p) * (((X' - 1).choose (y / p) : ℕ) : ℤ) *
          (uprod p (-((p : ℤ) * X')) y - uprod p 0 y) := by
      linear_combination h
    rw [this]
    exact dvd_mul_of_dvd_right (uprod_sub_dvd p (dvd_neg.2 he) y) _
  exact ((isCoprime_uprod hp y).pow_left).dvd_of_dvd_mul_right h2

/-- The signed kernel factor `(-1)^Z C(X - 1, Z) C(X + Z, Z)`. -/
def hZ (X Z : ℕ) : ℤ := (-1) ^ Z * (((X - 1).choose Z : ℕ) : ℤ) * (((X + Z).choose Z : ℕ) : ℤ)

theorem hZ_descent {p : ℕ} (hp : p.Prime) {e X' : ℕ} (hX' : 1 ≤ X')
    (he : (p : ℤ) ^ e ∣ (p : ℤ) * X') (Z : ℕ) :
    (p : ℤ) ^ e ∣ hZ (p * X') Z - hZ X' (Z / p) := by
  unfold hZ
  exact mul_sub_mul_dvd (descent_sub_dvd hp hX' he Z) (descent_add_dvd hp he Z)

/-- The kernel of the unshifted sum: `x f(N; x) = N g₀(x)`. -/
def g0 (N x : ℕ) : ℕ := (N - 1).choose (x - 1) * (N + x).choose x

/-- The kernel of the shifted sum: `x f(N - 1; x) = N g₁(x)`. -/
def g1 (N x : ℕ) : ℕ := (N - 1).choose x * (N + x - 1).choose (x - 1)

theorem exists_succ_of_not_dvd {p x : ℕ} (hx : ¬ p ∣ x) : ∃ x₀, x = x₀ + 1 :=
  ⟨x - 1, by have : x ≠ 0 := fun h => hx (h ▸ dvd_zero p); omega⟩

theorem g0_descent {p : ℕ} (hp : p.Prime) {e N' : ℕ} (hN' : 1 ≤ N')
    (he : (p : ℤ) ^ e ∣ (p : ℤ) * N') {x : ℕ} (hx : ¬ p ∣ x) :
    (p : ℤ) ^ e ∣ (-1) ^ (x + 1) * (g0 (p * N') x : ℤ) - hZ N' (x / p) := by
  obtain ⟨x₀, rfl⟩ := exists_succ_of_not_dvd hx
  have hq : (x₀ + 1) / p = x₀ / p := Nat.succ_div_of_not_dvd hx
  have e1 := descent_sub_dvd hp hN' he x₀
  have e2 := descent_add_dvd hp he (x₀ + 1)
  rw [hq] at e2
  unfold g0 hZ
  simp only [hq, Nat.add_sub_cancel]
  convert mul_sub_mul_dvd e1 e2 using 1
  push_cast
  ring

theorem g1_descent {p : ℕ} (hp : p.Prime) {e N' : ℕ} (hN' : 1 ≤ N')
    (he : (p : ℤ) ^ e ∣ (p : ℤ) * N') {x : ℕ} (hx : ¬ p ∣ x) :
    (p : ℤ) ^ e ∣ (-1) ^ x * (g1 (p * N') x : ℤ) - hZ N' (x / p) := by
  obtain ⟨x₀, rfl⟩ := exists_succ_of_not_dvd hx
  have hq : (x₀ + 1) / p = x₀ / p := Nat.succ_div_of_not_dvd hx
  have e1 := descent_sub_dvd hp hN' he (x₀ + 1)
  have e2 := descent_add_dvd hp he x₀
  rw [hq] at e1
  unfold g1 hZ
  simp only [hq, show p * N' + (x₀ + 1) - 1 = p * N' + x₀ by omega, Nat.add_sub_cancel]
  convert mul_sub_mul_dvd e1 e2 using 1
  push_cast
  ring

theorem mul_choose_eq {N x : ℕ} (hx : 1 ≤ x) : x * N.choose x = N * (N - 1).choose (x - 1) := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀, x = x₀ + 1 := ⟨x - 1, by omega⟩
  rcases N with _ | N₀
  · simp
  · rw [Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.add_one_mul_choose_eq, mul_comm]

theorem mul_choose_shift {N x : ℕ} (hN : 1 ≤ N) (hx : 1 ≤ x) :
    x * (N - 1 + x).choose x = N * (N + x - 1).choose (x - 1) := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀, x = x₀ + 1 := ⟨x - 1, by omega⟩
  have := Nat.choose_succ_right_eq (N - 1 + (x₀ + 1)) x₀
  rw [show N - 1 + (x₀ + 1) - x₀ = N by omega] at this
  rw [show N + (x₀ + 1) - 1 = N - 1 + (x₀ + 1) by omega, Nat.add_sub_cancel, mul_comm, this,
    mul_comm]

/-- Property (F) for the unshifted sum. -/
theorem F0 {N x : ℕ} (hx : 1 ≤ x) : x * term N x = N * g0 N x := by
  unfold term g0
  rw [← mul_assoc, mul_choose_eq hx, mul_assoc]

/-- Property (F) for the shifted sum. -/
theorem F1 {N x : ℕ} (hN : 1 ≤ N) (hx : 1 ≤ x) : x * term (N - 1) x = N * g1 N x := by
  unfold term g1
  rw [mul_left_comm, mul_choose_shift hN hx, mul_left_comm]

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

theorem mul_pow_div {p L τ u : ℕ} (hp : 0 < p) (hu : u ≤ τ) :
    L * p ^ τ / p ^ u = L * p ^ (τ - u) := by
  rw [show L * p ^ τ = L * p ^ (τ - u) * p ^ u by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hu]]
  exact Nat.mul_div_cancel _ (pow_pos hp u)

section Kernel

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

/-- The core of Proposition 6: the weighted kernel sum over the units of `[0, L p ^ τ)` is
divisible by `p ^ τ`. -/
theorem kernel_sum (hp5 : 5 ≤ p) {r τ L c₀ c₁ : ℕ} (hτ1 : 1 ≤ τ) (hτr : τ ≤ r)
    (h : ℕ → ℕ → ZMod (p ^ K))
    (hh : ∀ u A, 1 ≤ u → u < r → (p : ZMod (p ^ K)) ^ (r - u) ∣ h u A - h (u + 1) (A / p))
    (g : ℕ → ZMod (p ^ K))
    (hg : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ K)) ^ r ∣ (-1) ^ (x + c₀) * g x - h 1 (x / p))
    (y : ℕ → ℕ) (B : ℕ → ℕ → ℕ) (σ : ZMod (p ^ K))
    (hyu : ∀ x < L * p ^ τ, ¬ p ∣ x → ¬ p ∣ y x)
    (hyc : ∀ x < L * p ^ τ, ¬ p ∣ x →
      (p : ZMod (p ^ K)) ^ τ ∣ (x : ZMod (p ^ K)) - σ * (y x : ZMod (p ^ K)))
    (hys : ∀ x < L * p ^ τ, ¬ p ∣ x → (-1 : ZMod (p ^ K)) ^ (x + y x) = (-1) ^ c₁)
    (hB1 : ∀ x < L * p ^ τ, ¬ p ∣ x → y x / p = B 1 (x / p))
    (hB : ∀ u, 1 ≤ u → u < τ → ∀ A < L * p ^ (τ - u), B u A / p = B (u + 1) (A / p)) :
    (p : ZMod (p ^ K)) ^ τ ∣ ∑ x ∈ range (L * p ^ τ),
      (if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹ * (y x : ZMod (p ^ K))⁻¹ * (g x * g (y x))) := by
  have hp0 : 0 < p := hp.out.pos
  set w : ℕ → ZMod (p ^ K) := fun x =>
    if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹ * (y x : ZMod (p ^ K))⁻¹ with hw
  set Kf : ℕ → ℕ → ZMod (p ^ K) := fun u A => h u A * h u (B u A) with hKf
  have step1 : ∀ x < L * p ^ τ, ¬ p ∣ x →
      (p : ZMod (p ^ K)) ^ r ∣ g x * g (y x) - (-1) ^ c₁ * Kf 1 (x / p) := by
    intro x hx hpx
    obtain ⟨e1, he1⟩ := hg x hpx
    obtain ⟨e2, he2⟩ := hg (y x) (hyu x hx hpx)
    rw [hB1 x hx hpx] at he2
    have ha : ((-1 : ZMod (p ^ K)) ^ (x + c₀)) * (-1) ^ (x + c₀) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have hb : ((-1 : ZMod (p ^ K)) ^ (y x + c₀)) * (-1) ^ (y x + c₀) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have hab : ((-1 : ZMod (p ^ K)) ^ (x + c₀)) * (-1) ^ (y x + c₀) = (-1) ^ c₁ := by
      rw [← pow_add, show x + c₀ + (y x + c₀) = (x + y x) + 2 * c₀ by ring, pow_add,
        hys x hx hpx, pow_mul]
      simp
    refine ⟨(-1) ^ c₁ * (h 1 (x / p) * e2 + e1 * h 1 (B 1 (x / p)) +
      e1 * ((p : ZMod (p ^ K)) ^ r * e2)), ?_⟩
    simp only [hKf]
    linear_combination ((-1) ^ c₁ * (h 1 (B 1 (x / p)) + (p : ZMod (p ^ K)) ^ r * e2)) * he1
      + ((-1) ^ c₁ * (-1) ^ (x + c₀) * g x) * he2
      + ((-1) ^ (x + c₀) * (-1) ^ (y x + c₀) * g x * g (y x)) * hab
      + (- g x * g (y x) * ((-1) ^ (y x + c₀)) ^ 2) * ha
      + (- g x * g (y x)) * hb
  have hsplit : ∑ x ∈ range (L * p ^ τ),
      (if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹ * (y x : ZMod (p ^ K))⁻¹ * (g x * g (y x))) =
      (-1) ^ c₁ * ∑ x ∈ range (L * p ^ τ), w x * Kf 1 (x / p) +
      ∑ x ∈ range (L * p ^ τ), w x * (g x * g (y x) - (-1) ^ c₁ * Kf 1 (x / p)) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun x _ => ?_)
    simp only [hw]
    split_ifs <;> ring
  rw [hsplit]
  refine dvd_add (dvd_mul_of_dvd_right ?_ _) (dvd_sum (fun x hx => ?_))
  · refine nested_block (p : ZMod (p ^ K)) hp0 hτ1 w Kf ?_ ?_
    · intro u hu1 huτ D hD
      have hsum : ∑ i ∈ range (p ^ u), w (D * p ^ u + i) =
          σ * ∑ i ∈ range (p ^ u), invSq p K (D * p ^ u + i) +
          ∑ i ∈ range (p ^ u), (w (D * p ^ u + i) - σ * invSq p K (D * p ^ u + i)) := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl (fun i _ => by ring)
      rw [hsum]
      refine dvd_add (dvd_mul_of_dvd_right (block_invSq hp5 hu1 D) _) (dvd_sum (fun i hi => ?_))
      have hxlt : D * p ^ u + i < L * p ^ τ := by
        have hi' := mem_range.1 hi
        calc D * p ^ u + i < D * p ^ u + p ^ u := by omega
          _ = (D + 1) * p ^ u := by ring
          _ ≤ (L * p ^ (τ - u)) * p ^ u := Nat.mul_le_mul_right _ hD
          _ = L * p ^ τ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel huτ]
      set x := D * p ^ u + i
      simp only [hw, invSq]
      split_ifs with hpx
      · simp
      · have hxa := natCast_mul_inv (K := K) hpx
        have hyb := natCast_mul_inv (K := K) (hyu x hxlt hpx)
        have e : (x : ZMod (p ^ K))⁻¹ * (y x : ZMod (p ^ K))⁻¹ - σ * (x : ZMod (p ^ K))⁻¹ ^ 2 =
            ((x : ZMod (p ^ K))⁻¹ ^ 2 * (y x : ZMod (p ^ K))⁻¹) *
              ((x : ZMod (p ^ K)) - σ * (y x : ZMod (p ^ K))) := by
          linear_combination (-(x : ZMod (p ^ K))⁻¹ * (y x : ZMod (p ^ K))⁻¹) * hxa +
            (σ * (x : ZMod (p ^ K))⁻¹ ^ 2) * hyb
        rw [e]
        exact dvd_mul_of_dvd_right (pow_dvd_of_le _ huτ (hyc x hxlt hpx)) _
    · intro u hu1 huτ A hA
      simp only [hKf]
      rw [← hB u hu1 huτ A hA]
      exact pow_dvd_of_le _ (by omega)
        (mul_sub_mul_dvd (hh u A hu1 (by omega)) (hh u (B u A) hu1 (by omega)))
  · simp only [hw]
    split_ifs with hpx
    · simp
    · exact dvd_mul_of_dvd_right (pow_dvd_of_le _ hτr (step1 x (mem_range.1 hx) hpx)) _

/-- Proposition 6, one side: `y = d - x` with `d = L p ^ τ`. -/
theorem kernel_one_side (hp5 : 5 ≤ p) {r τ L c₀ : ℕ} (hτ1 : 1 ≤ τ) (hτr : τ ≤ r)
    (h : ℕ → ℕ → ZMod (p ^ K))
    (hh : ∀ u A, 1 ≤ u → u < r → (p : ZMod (p ^ K)) ^ (r - u) ∣ h u A - h (u + 1) (A / p))
    (g : ℕ → ZMod (p ^ K))
    (hg : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ K)) ^ r ∣ (-1) ^ (x + c₀) * g x - h 1 (x / p)) :
    (p : ZMod (p ^ K)) ^ τ ∣ ∑ x ∈ range (L * p ^ τ),
      (if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹ * ((L * p ^ τ - x : ℕ) : ZMod (p ^ K))⁻¹ *
        (g x * g (L * p ^ τ - x))) := by
  have hp0 : 0 < p := hp.out.pos
  have hpd : p ∣ L * p ^ τ := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) L
  refine kernel_sum hp5 hτ1 hτr h hh g hg (fun x => L * p ^ τ - x)
    (fun u A => L * p ^ τ / p ^ u - A - 1) (-1) (c₁ := L * p ^ τ) ?_ ?_ ?_ ?_ ?_
  · intro x hx hpx hpy
    apply hpx
    have := Nat.dvd_sub hpd hpy
    rwa [Nat.sub_sub_self hx.le] at this
  · intro x hx _
    rw [neg_one_mul, sub_neg_eq_add, ← Nat.cast_add, Nat.add_sub_cancel' hx.le]
    exact ⟨L, by push_cast; ring⟩
  · intro x hx _
    rw [Nat.add_sub_cancel' hx.le]
  · intro x hx hpx
    obtain ⟨x₀, rfl⟩ := exists_succ_of_not_dvd hpx
    rw [pow_one, show L * p ^ τ - (x₀ + 1) = L * p ^ τ - x₀ - 1 by omega,
      div_sub_sub_one hp0 hpd (by omega), Nat.succ_div_of_not_dvd hpx]
  · intro u hu1 huτ A hA
    have hdu : L * p ^ τ / p ^ u = L * p ^ (τ - u) := mul_pow_div hp0 huτ.le
    have hpdu : p ∣ L * p ^ τ / p ^ u := by
      rw [hdu]; exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) L
    rw [div_sub_sub_one hp0 hpdu (by rw [hdu]; exact hA), Nat.div_div_eq_div_mul, ← pow_succ]

/-- Proposition 6, split: `y = x + t` with `t = T p ^ τ`. -/
theorem kernel_split (hp5 : 5 ≤ p) {r τ L T c₀ : ℕ} (hτ1 : 1 ≤ τ) (hτr : τ ≤ r)
    (h : ℕ → ℕ → ZMod (p ^ K))
    (hh : ∀ u A, 1 ≤ u → u < r → (p : ZMod (p ^ K)) ^ (r - u) ∣ h u A - h (u + 1) (A / p))
    (g : ℕ → ZMod (p ^ K))
    (hg : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ K)) ^ r ∣ (-1) ^ (x + c₀) * g x - h 1 (x / p)) :
    (p : ZMod (p ^ K)) ^ τ ∣ ∑ x ∈ range (L * p ^ τ),
      (if p ∣ x then 0 else (x : ZMod (p ^ K))⁻¹ * ((x + T * p ^ τ : ℕ) : ZMod (p ^ K))⁻¹ *
        (g x * g (x + T * p ^ τ))) := by
  have hp0 : 0 < p := hp.out.pos
  have hpt : p ∣ T * p ^ τ := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) T
  refine kernel_sum hp5 hτ1 hτr h hh g hg (fun x => x + T * p ^ τ)
    (fun u A => A + T * p ^ τ / p ^ u) 1 (c₁ := T * p ^ τ) ?_ ?_ ?_ ?_ ?_
  · intro x _ hpx hpy
    exact hpx ((Nat.dvd_add_left hpt).1 hpy)
  · intro x _ _
    rw [one_mul, Nat.cast_add, sub_add_cancel_left]
    exact dvd_neg.2 ⟨T, by push_cast; ring⟩
  · intro x _ _
    rw [show x + (x + T * p ^ τ) = T * p ^ τ + 2 * x by ring, pow_add, pow_mul]
    simp
  · intro x _ _
    rw [pow_one, Nat.add_div_of_dvd_left hpt]
  · intro u hu1 huτ A _
    have htu : T * p ^ τ / p ^ u = T * p ^ (τ - u) := mul_pow_div hp0 huτ.le
    have hptu : p ∣ T * p ^ τ / p ^ u := by
      rw [htu]; exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) T
    rw [Nat.add_div_of_dvd_left hptu, Nat.div_div_eq_div_mul, ← pow_succ]

end Kernel

/-! ### Finite sums over ranges -/

section Sums

variable {M : Type*}

/-- The convolution `∑_{x ≤ s} F(x) F(s - x)`. -/
def conv [CommSemiring M] (F : ℕ → M) (s : ℕ) : M := ∑ x ∈ range (s + 1), F x * F (s - x)

theorem sum_range_ite_lt [AddCommMonoid M] (G : ℕ → M) (a b : ℕ) :
    ∑ x ∈ range a, (if x < b then G x else 0) = ∑ x ∈ range (min a b), G x := by
  rw [← sum_filter]
  congr 1
  ext x
  simp [lt_min_iff]

theorem sum_range_eq_of_vanish [AddCommMonoid M] (G : ℕ → M) {a b : ℕ} (hab : a ≤ b)
    (hG : ∀ x, a ≤ x → x < b → G x = 0) : ∑ x ∈ range b, G x = ∑ x ∈ range a, G x := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [sum_range_add, sum_eq_zero (fun i hi => hG (a + i) (by omega)
    (by have := mem_range.1 hi; omega)), add_zero]

theorem sum_range_mul_of_vanish [AddCommMonoid M] (G : ℕ → M) {p : ℕ} (hp : 0 < p)
    (hG : ∀ s, ¬ p ∣ s → G s = 0) (B : ℕ) :
    ∑ s ∈ range (p * B), G s = ∑ a ∈ range B, G (p * a) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [sum_range_succ', sum_eq_zero, zero_add, add_zero]
    intro i hi
    apply hG
    intro hd
    have h1 := (Nat.dvd_add_right (dvd_mul_right (q + 1) B)).1 hd
    have h2 := Nat.le_of_dvd (by omega) h1
    have h3 := mem_range.1 hi
    omega

theorem double_sum_eq_conv [CommSemiring M] (n : ℕ) (T : ℕ → M) (hT : ∀ z, n < z → T z = 0)
    (s : ℕ) :
    ∑ k₃ ∈ range (n + 1), ∑ k₄ ∈ range (n + 1), (if s = k₃ + k₄ then T k₃ * T k₄ else 0) =
      conv T s := by
  have inner : ∀ k₃, ∑ k₄ ∈ range (n + 1), (if s = k₃ + k₄ then T k₃ * T k₄ else 0) =
      if k₃ < s + 1 then T k₃ * T (s - k₃) else 0 := by
    intro k₃
    by_cases hk : k₃ ≤ s
    · rw [ite_eq_left (by omega : k₃ < s + 1)]
      have e : ∀ k₄, (if s = k₃ + k₄ then T k₃ * T k₄ else 0) =
          if k₄ = s - k₃ then T k₃ * T k₄ else 0 := by
        intro k₄
        by_cases h : k₄ = s - k₃
        · rw [ite_eq_left (by omega : s = k₃ + k₄), ite_eq_left h]
        · rw [ite_eq_right (by omega : ¬ s = k₃ + k₄), ite_eq_right h]
      simp_rw [e]
      rw [sum_ite_eq']
      split_ifs with hm
      · rfl
      · rw [hT (s - k₃) (by simp at hm; omega), mul_zero]
    · rw [ite_eq_right (by omega : ¬ k₃ < s + 1)]
      exact sum_eq_zero (fun k₄ _ => ite_eq_right (by omega))
  simp_rw [inner]
  rw [sum_range_ite_lt, conv, sum_range_eq_of_vanish (fun x => T x * T (s - x))
    (min_le_right (n + 1) (s + 1)) (fun x h1 h2 => by rw [hT x (by omega), zero_mul])]

/-- The four-fold sum with `k₁ + k₂ = k₃ + k₄` is a sum of squared convolutions. -/
theorem fourfold_eq [CommSemiring M] (n : ℕ) (T : ℕ → M) (hT : ∀ z, n < z → T z = 0) :
    (∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1), ∑ k₃ ∈ range (n + 1), ∑ k₄ ∈ range (n + 1),
      if k₁ + k₂ = k₃ + k₄ then T k₁ * T k₂ * T k₃ * T k₄ else 0) =
    ∑ s ∈ range (2 * n + 1), conv T s * conv T s := by
  have h1 : ∀ k₁ k₂, (∑ k₃ ∈ range (n + 1), ∑ k₄ ∈ range (n + 1),
      if k₁ + k₂ = k₃ + k₄ then T k₁ * T k₂ * T k₃ * T k₄ else 0) =
      T k₁ * T k₂ * conv T (k₁ + k₂) := by
    intro k₁ k₂
    rw [← double_sum_eq_conv n T hT (k₁ + k₂), mul_sum]
    refine sum_congr rfl (fun k₃ _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun k₄ _ => ?_)
    split_ifs <;> ring
  simp_rw [h1]
  have h2 : ∀ k₁ ∈ range (n + 1), ∀ k₂ ∈ range (n + 1), T k₁ * T k₂ * conv T (k₁ + k₂) =
      ∑ s ∈ range (2 * n + 1), (if s = k₁ + k₂ then T k₁ * T k₂ * conv T s else 0) := by
    intro k₁ hk₁ k₂ hk₂
    rw [sum_ite_eq', ite_eq_left (mem_range.2 (by simp at hk₁ hk₂; omega))]
  calc ∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1), T k₁ * T k₂ * conv T (k₁ + k₂)
      = ∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1), ∑ s ∈ range (2 * n + 1),
          (if s = k₁ + k₂ then T k₁ * T k₂ * conv T s else 0) :=
        sum_congr rfl (fun k₁ hk₁ => sum_congr rfl (fun k₂ hk₂ => h2 k₁ hk₁ k₂ hk₂))
    _ = ∑ k₁ ∈ range (n + 1), ∑ s ∈ range (2 * n + 1), ∑ k₂ ∈ range (n + 1),
          (if s = k₁ + k₂ then T k₁ * T k₂ * conv T s else 0) :=
        sum_congr rfl (fun k₁ _ => sum_comm)
    _ = ∑ s ∈ range (2 * n + 1), ∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1),
          (if s = k₁ + k₂ then T k₁ * T k₂ * conv T s else 0) := sum_comm
    _ = ∑ s ∈ range (2 * n + 1), conv T s * conv T s := by
        refine sum_congr rfl (fun s _ => ?_)
        have hc := double_sum_eq_conv n T hT s
        calc _ = (∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1),
                (if s = k₁ + k₂ then T k₁ * T k₂ else 0)) * conv T s := by
              rw [sum_mul]
              refine sum_congr rfl (fun k₁ _ => ?_)
              rw [sum_mul]
              refine sum_congr rfl (fun k₂ _ => ?_)
              split_ifs <;> ring
          _ = conv T s * conv T s := by rw [hc]

/-! ### Splitting a convolution by divisibility -/

/-- Terms of the convolution with both indices divisible by `p`. -/
def gam [CommSemiring M] (p : ℕ) (F : ℕ → M) (s : ℕ) : M :=
  ∑ x ∈ range (s + 1), if p ∣ x ∧ p ∣ s - x then F x * F (s - x) else 0

/-- Terms of the convolution with exactly one index divisible by `p`. -/
def alp [CommSemiring M] (p : ℕ) (F : ℕ → M) (s : ℕ) : M :=
  ∑ x ∈ range (s + 1), if (p ∣ x ↔ ¬ p ∣ s - x) then F x * F (s - x) else 0

/-- Terms of the convolution with no index divisible by `p`. -/
def bet [CommSemiring M] (p : ℕ) (F : ℕ → M) (s : ℕ) : M :=
  ∑ x ∈ range (s + 1), if ¬ p ∣ x ∧ ¬ p ∣ s - x then F x * F (s - x) else 0

/-- The split-class summand: `F(p a) F(s - p a)` for `p ∤ s` and `p a ≤ s`. -/
def phi [CommSemiring M] (p : ℕ) (F : ℕ → M) (s a : ℕ) : M :=
  if ¬ p ∣ s ∧ p * a ≤ s then F (p * a) * F (s - p * a) else 0

theorem conv_eq_split [CommSemiring M] (p : ℕ) (F : ℕ → M) (s : ℕ) :
    conv F s = gam p F s + alp p F s + bet p F s := by
  unfold conv gam alp bet
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun x _ => ?_)
  by_cases h1 : p ∣ x <;> by_cases h2 : p ∣ s - x <;> simp [h1, h2]

theorem dvd_sub_iff_of_dvd {p s x : ℕ} (hs : p ∣ s) (hx : x ≤ s) : p ∣ s - x ↔ p ∣ x := by
  constructor
  · intro h
    have := Nat.dvd_sub hs h
    rwa [Nat.sub_sub_self hx] at this
  · intro h
    exact Nat.dvd_sub hs h

theorem alp_eq_zero [CommSemiring M] {p : ℕ} (F : ℕ → M) {s : ℕ} (hs : p ∣ s) :
    alp p F s = 0 := by
  unfold alp
  refine sum_eq_zero (fun x hx => ite_eq_right ?_)
  have hxs : x ≤ s := Nat.lt_succ_iff.1 (mem_range.1 hx)
  rw [dvd_sub_iff_of_dvd hs hxs]
  tauto

theorem gam_eq_zero [CommSemiring M] {p : ℕ} (F : ℕ → M) {s : ℕ} (hs : ¬ p ∣ s) :
    gam p F s = 0 := by
  unfold gam
  refine sum_eq_zero (fun x hx => ite_eq_right ?_)
  rintro ⟨h1, h2⟩
  have hxs : x ≤ s := Nat.lt_succ_iff.1 (mem_range.1 hx)
  exact hs (by have := dvd_add h1 h2; rwa [Nat.add_sub_cancel' hxs] at this)

theorem alp_eq_two_sum [CommSemiring M] {p : ℕ} (hp0 : 0 < p) (F : ℕ → M) {s B : ℕ}
    (hsB : s < B) : alp p F s = 2 * ∑ a ∈ range B, phi p F s a := by
  by_cases hs : p ∣ s
  · rw [alp_eq_zero F hs]
    unfold phi
    simp [hs]
  have h1 : alp p F s = ∑ x ∈ range (s + 1), (if p ∣ x then F x * F (s - x) else 0) +
      ∑ x ∈ range (s + 1), (if p ∣ s - x then F x * F (s - x) else 0) := by
    unfold alp
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun x hx => ?_)
    have hxs : x ≤ s := Nat.lt_succ_iff.1 (mem_range.1 hx)
    by_cases h1 : p ∣ x
    · have h2 : ¬ p ∣ s - x := fun h2 => hs (by
        have := dvd_add h1 h2; rwa [Nat.add_sub_cancel' hxs] at this)
      simp [h1, h2]
    · by_cases h2 : p ∣ s - x <;> simp [h1, h2]
  have h2 : ∑ x ∈ range (s + 1), (if p ∣ s - x then F x * F (s - x) else 0) =
      ∑ x ∈ range (s + 1), (if p ∣ x then F x * F (s - x) else 0) := by
    rw [← Finset.sum_range_reflect (fun x => if p ∣ x then F x * F (s - x) else 0) (s + 1)]
    refine sum_congr rfl (fun x hx => ?_)
    have hxs : x ≤ s := Nat.lt_succ_iff.1 (mem_range.1 hx)
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hxs]
    split_ifs <;> ring
  have h3 : ∑ x ∈ range (s + 1), (if p ∣ x then F x * F (s - x) else 0) =
      ∑ a ∈ range B, phi p F s a := by
    have e1 : ∑ x ∈ range (s + 1), (if p ∣ x then F x * F (s - x) else 0) =
        ∑ x ∈ range (p * B), (if p ∣ x ∧ x ≤ s then F x * F (s - x) else 0) := by
      rw [sum_range_eq_of_vanish _ (show s + 1 ≤ p * B by
        have := Nat.le_mul_of_pos_left B hp0; omega) ?_]
      · refine sum_congr rfl (fun x hx => ?_)
        have hxs : x ≤ s := Nat.lt_succ_iff.1 (mem_range.1 hx)
        by_cases h : p ∣ x <;> simp [h, hxs]
      · intro x hx1 _
        exact ite_eq_right (fun h => by have := h.2; omega)
    rw [e1, sum_range_mul_of_vanish _ hp0 (fun x hx => ite_eq_right (fun h => hx h.1))]
    refine sum_congr rfl (fun a _ => ?_)
    unfold phi
    by_cases ha : p * a ≤ s <;> simp [ha, hs]
  rw [h1, h2, h3, two_mul]

theorem exists_tau {p t r : ℕ} (hr : 1 ≤ r) (hpt : p ∣ t) :
    ∃ τ, 1 ≤ τ ∧ τ ≤ r ∧ p ^ τ ∣ t ∧ (τ < r → ¬ p ^ (τ + 1) ∣ t) := by
  refine ⟨Nat.findGreatest (fun j => p ^ j ∣ t) r, ?_, Nat.findGreatest_le r, ?_, fun h => ?_⟩
  · exact Nat.le_findGreatest (P := fun j => p ^ j ∣ t) hr (by simpa using hpt)
  · exact Nat.findGreatest_spec (P := fun j => p ^ j ∣ t) (Nat.zero_le r) (by simp)
  · exact Nat.findGreatest_is_greatest (P := fun j => p ^ j ∣ t) (Nat.lt_succ_self _) (by omega)

end Sums

/-! ### The main congruence for an abstract kernel -/

section Abstract

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem alp_dvd {K r : ℕ} (F : ℕ → ZMod (p ^ K))
    (hFu : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ K)) ^ r ∣ F x) (s : ℕ) :
    (p : ZMod (p ^ K)) ^ r ∣ alp p F s := by
  unfold alp
  refine dvd_sum (fun x _ => ?_)
  split_ifs with h
  · by_cases hx : p ∣ x
    · exact dvd_mul_of_dvd_right (hFu _ (h.1 hx)) _
    · exact dvd_mul_of_dvd_left (hFu _ hx) _
  · exact dvd_zero _

omit hp in
theorem bet_dvd {K r : ℕ} (F : ℕ → ZMod (p ^ K))
    (hFu : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ K)) ^ r ∣ F x) (s : ℕ) :
    (p : ZMod (p ^ K)) ^ (2 * r) ∣ bet p F s := by
  unfold bet
  refine dvd_sum (fun x _ => ?_)
  split_ifs with h
  · rw [two_mul, pow_add]
    exact mul_dvd_mul (hFu _ h.1) (hFu _ h.2)
  · exact dvd_zero _

omit hp in
theorem conv_sq_eq {r : ℕ} (F : ℕ → ZMod (p ^ (3 * r)))
    (hFu : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ (3 * r))) ^ r ∣ F x) (s : ℕ) :
    conv F s * conv F s =
      gam p F s * gam p F s + alp p F s * alp p F s + 2 * (gam p F s * bet p F s) := by
  have hββ : bet p F s * bet p F s = 0 := by
    have := mul_dvd_mul (bet_dvd F hFu s) (bet_dvd F hFu s)
    rw [← pow_add] at this
    exact eq_zero_of_pow_dvd (pow_dvd_of_le _ (by omega) this)
  have hαβ : alp p F s * bet p F s = 0 := by
    have := mul_dvd_mul (alp_dvd F hFu s) (bet_dvd F hFu s)
    rw [← pow_add] at this
    exact eq_zero_of_pow_dvd (pow_dvd_of_le _ (by omega) this)
  have hαγ : alp p F s * gam p F s = 0 := by
    by_cases hs : p ∣ s
    · rw [alp_eq_zero F hs, zero_mul]
    · rw [gam_eq_zero F hs, mul_zero]
  rw [conv_eq_split p F s]
  linear_combination hββ + 2 * hαβ + 2 * hαγ

omit hp in
/-- The divisible layer (Lemma 5, summed). -/
theorem layer_sum {K : ℕ} (hp0 : 0 < p) (F F' : ℕ → ZMod (p ^ K))
    (hdiv : ∀ a b a' b', a + b = a' + b' →
      F (p * a) * F (p * b) * (F (p * a') * F (p * b')) = F' a * F' b * (F' a' * F' b'))
    (B' : ℕ) :
    ∑ s ∈ range (p * B'), gam p F s * gam p F s = ∑ s ∈ range B', conv F' s * conv F' s := by
  rw [sum_range_mul_of_vanish _ hp0 (fun s hs => by rw [gam_eq_zero F hs, zero_mul])]
  refine sum_congr rfl (fun s _ => ?_)
  have hγ : gam p F (p * s) = ∑ a ∈ range (s + 1), F (p * a) * F (p * (s - a)) := by
    unfold gam
    rw [← sum_range_eq_of_vanish _ (show p * s + 1 ≤ p * (s + 1) by rw [Nat.mul_succ]; omega) ?_]
    · rw [sum_range_mul_of_vanish _ hp0 ?_]
      · refine sum_congr rfl (fun a _ => ?_)
        rw [ite_eq_left ⟨dvd_mul_right p a, by rw [← mul_tsub]; exact dvd_mul_right p _⟩,
          ← mul_tsub]
      · intro x hx
        exact ite_eq_right (fun h => hx h.1)
    · intro x hx1 hx2
      apply ite_eq_right
      rintro ⟨⟨c, rfl⟩, _⟩
      have h3 : p * s < p * c := by omega
      have h4 := Nat.lt_of_mul_lt_mul_left h3
      have h5 := Nat.lt_of_mul_lt_mul_left hx2
      omega
  rw [hγ, conv, sum_mul_sum, sum_mul_sum]
  refine sum_congr rfl (fun a ha => sum_congr rfl (fun a' ha' => ?_))
  apply hdiv
  have := mem_range.1 ha
  have := mem_range.1 ha'
  omega

omit hp in
theorem pref_dvd {K r : ℕ} (F : ℕ → ZMod (p ^ K))
    (hpre : ∀ y j, j ≤ r → ¬ p ^ (j + 1) ∣ y → (p : ZMod (p ^ K)) ^ (r - j) ∣ F y)
    {y₁ y₂ c τ : ℕ} (hτr : τ ≤ r)
    (hc : p ^ (τ + 1) ∣ y₁ → p ^ (τ + 1) ∣ y₂ → p ^ (τ + 1) ∣ c)
    (hmax : τ < r → ¬ p ^ (τ + 1) ∣ c) :
    (p : ZMod (p ^ K)) ^ (r - τ) ∣ F y₁ * F y₂ := by
  rcases eq_or_lt_of_le hτr with h | h
  · rw [h, Nat.sub_self, pow_zero]
    exact one_dvd _
  · by_cases h1 : p ^ (τ + 1) ∣ y₁
    · exact dvd_mul_of_dvd_right (hpre y₂ τ hτr (fun h2 => hmax h (hc h1 h2))) _
    · exact dvd_mul_of_dvd_left (hpre y₁ τ hτr h1) _

theorem hZ_cast_descent {K r m : ℕ} (hm : 1 ≤ m) (u A : ℕ) (hur : u < r) :
    (p : ZMod (p ^ K)) ^ (r - u) ∣ (hZ (m * p ^ (r - u)) A : ZMod (p ^ K)) -
      (hZ (m * p ^ (r - (u + 1))) (A / p) : ZMod (p ^ K)) := by
  have hX : m * p ^ (r - u) = p * (m * p ^ (r - (u + 1))) := by
    rw [show r - u = (r - (u + 1)) + 1 by omega, pow_succ]
    ring
  have hX' : 1 ≤ m * p ^ (r - (u + 1)) := Nat.mul_pos hm (pow_pos hp.out.pos _)
  have he : (p : ℤ) ^ (r - u) ∣ (p : ℤ) * ((m * p ^ (r - (u + 1)) : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← hX]
    exact ⟨m, by push_cast; ring⟩
  have h1 := hZ_descent hp.out hX' he A
  rw [← hX] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨(c : ZMod (p ^ K)), ?_⟩
  rw [← Int.cast_sub, hc, Int.cast_mul, Int.cast_pow, Int.cast_natCast]

/-- The two-unit classes split across the two sides sum to `0` modulo `p ^ (3 r)`. -/
theorem split_sum_zero (hp5 : 5 ≤ p) {r m M c₀ : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hM : M ≤ m * p ^ r) (F g : ℕ → ZMod (p ^ (3 * r)))
    (hF0 : ∀ z, M < z → F z = 0)
    (hFg : ∀ x, ¬ p ∣ x → F x =
      ((m * p ^ r : ℕ) : ZMod (p ^ (3 * r))) * (x : ZMod (p ^ (3 * r)))⁻¹ * g x)
    (hg : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ (3 * r))) ^ r ∣
      (-1) ^ (x + c₀) * g x - (hZ (m * p ^ (r - 1)) (x / p) : ZMod (p ^ (3 * r))))
    (hpre : ∀ y j, j ≤ r → ¬ p ^ (j + 1) ∣ y → (p : ZMod (p ^ (3 * r))) ^ (r - j) ∣ F y)
    {B : ℕ} (hB : 2 * (m * p ^ r) ≤ B) :
    ∑ s ∈ range B, alp p F s * alp p F s = 0 := by
  have hp0 : 0 < p := hp.out.pos
  have hpN : p ∣ m * p ^ r := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) m
  have key_le : ∀ a b, b ≤ a → ∑ s ∈ range B, phi p F s a * phi p F s b = 0 := by
    intro a b hba
    by_cases haM : M < p * a
    · refine sum_eq_zero (fun s _ => ?_)
      unfold phi
      rw [hF0 _ haM]
      split_ifs <;> simp
    rw [not_lt] at haM
    have hpab : p * b ≤ p * a := Nat.mul_le_mul_left p hba
    have hpt : p ∣ p * a - p * b := Nat.dvd_sub (dvd_mul_right p a) (dvd_mul_right p b)
    have e1 : ∀ s, phi p F s a * phi p F s b = F (p * a) * F (p * b) *
        (if ¬ p ∣ s ∧ p * a ≤ s then F (s - p * a) * F (s - p * a + (p * a - p * b)) else 0) := by
      intro s
      unfold phi
      by_cases hs : ¬ p ∣ s ∧ p * a ≤ s
      · rw [ite_eq_left hs, ite_eq_left hs, ite_eq_left ⟨hs.1, le_trans hpab hs.2⟩,
          show s - p * b = s - p * a + (p * a - p * b) by omega]
        ring
      · rw [ite_eq_right hs, ite_eq_right hs, zero_mul, mul_zero]
    have e2 : ∑ s ∈ range B, (if ¬ p ∣ s ∧ p * a ≤ s then
        F (s - p * a) * F (s - p * a + (p * a - p * b)) else 0) =
        ∑ x ∈ range (m * p ^ r), (if p ∣ x then 0 else F x * F (x + (p * a - p * b))) := by
      obtain ⟨c, hc⟩ : ∃ c, B = p * a + c := ⟨B - p * a, by omega⟩
      rw [hc, sum_range_add, sum_eq_zero (fun s hs => ite_eq_right (fun h => by
        have := mem_range.1 hs; have := h.2; omega)), zero_add]
      have hdx : ∀ x, p ∣ p * a + x ↔ p ∣ x := fun x => Nat.dvd_add_right (dvd_mul_right p a)
      rw [sum_range_eq_of_vanish _ (show m * p ^ r ≤ c by omega) ?_]
      · refine sum_congr rfl (fun x _ => ?_)
        simp only [Nat.add_sub_cancel_left, hdx, le_add_iff_nonneg_right, zero_le, and_true]
        by_cases h : p ∣ x <;> simp [h]
      · intro x hx1 _
        have hxM : ¬ p ∣ x → M < x := fun h => by
          have hxN : x ≠ m * p ^ r := fun hx => h (hx ▸ hpN)
          omega
        by_cases h : p ∣ x
        · simp [hdx, h]
        · simp [hdx, h, hF0 x (hxM h)]
    have e3 : ∑ x ∈ range (m * p ^ r), (if p ∣ x then 0 else F x * F (x + (p * a - p * b))) =
        ((m * p ^ r : ℕ) : ZMod (p ^ (3 * r))) ^ 2 * ∑ x ∈ range (m * p ^ r),
          (if p ∣ x then 0 else (x : ZMod (p ^ (3 * r)))⁻¹ *
            ((x + (p * a - p * b) : ℕ) : ZMod (p ^ (3 * r)))⁻¹ *
              (g x * g (x + (p * a - p * b)))) := by
      rw [mul_sum]
      refine sum_congr rfl (fun x _ => ?_)
      split_ifs with hx
      · simp
      · have hxt : ¬ p ∣ x + (p * a - p * b) := fun h => hx ((Nat.dvd_add_left hpt).1 h)
        rw [hFg x hx, hFg _ hxt]
        ring
    rw [sum_congr rfl (fun s _ => e1 s), ← mul_sum, e2, e3]
    obtain ⟨τ, hτ1, hτr, hτt, hτmax⟩ := exists_tau hr hpt
    have hker := kernel_split (K := 3 * r) hp5 (L := m * p ^ (r - τ))
      (T := (p * a - p * b) / p ^ τ) (c₀ := c₀) hτ1 hτr
      (fun u A => (hZ (m * p ^ (r - u)) A : ZMod (p ^ (3 * r))))
      (fun u A _ hur => hZ_cast_descent hm u A hur) g hg
    have hLN : m * p ^ (r - τ) * p ^ τ = m * p ^ r := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hτr]
    rw [hLN, Nat.div_mul_cancel hτt] at hker
    have hNP : (p : ZMod (p ^ (3 * r))) ^ (2 * r) ∣ ((m * p ^ r : ℕ) : ZMod (p ^ (3 * r))) ^ 2 :=
      ⟨(m : ZMod (p ^ (3 * r))) ^ 2, by push_cast; ring⟩
    have hpref := pref_dvd F hpre (y₁ := p * a) (y₂ := p * b) hτr (fun h1 h2 => Nat.dvd_sub h1 h2)
      hτmax
    apply eq_zero_of_pow_dvd
    have := mul_dvd_mul hpref (mul_dvd_mul hNP hker)
    rw [← pow_add, ← pow_add] at this
    exact pow_dvd_of_le _ (by omega) this
  have key : ∀ a b, ∑ s ∈ range B, phi p F s a * phi p F s b = 0 := by
    intro a b
    rcases le_total b a with h | h
    · exact key_le a b h
    · rw [← key_le b a h]
      exact sum_congr rfl (fun s _ => mul_comm _ _)
  have hα : ∀ s ∈ range B, alp p F s * alp p F s =
      4 * ∑ a ∈ range B, ∑ b ∈ range B, phi p F s a * phi p F s b := by
    intro s hs
    rw [alp_eq_two_sum hp0 F (mem_range.1 hs), mul_mul_mul_comm, sum_mul_sum]
    ring
  rw [sum_congr rfl hα, ← mul_sum]
  rw [show ∑ s ∈ range B, ∑ a ∈ range B, ∑ b ∈ range B, phi p F s a * phi p F s b =
      ∑ a ∈ range B, ∑ b ∈ range B, ∑ s ∈ range B, phi p F s a * phi p F s b by
    rw [sum_comm]
    exact sum_congr rfl (fun a _ => sum_comm)]
  rw [sum_eq_zero (fun a _ => sum_eq_zero (fun b _ => key a b)), mul_zero]

/-- The two-unit classes on one side sum to `0` modulo `p ^ (3 r)`. -/
theorem one_side_sum_zero (hp5 : 5 ≤ p) {r m c₀ : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (F g : ℕ → ZMod (p ^ (3 * r)))
    (hFg : ∀ x, ¬ p ∣ x → F x =
      ((m * p ^ r : ℕ) : ZMod (p ^ (3 * r))) * (x : ZMod (p ^ (3 * r)))⁻¹ * g x)
    (hg : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ (3 * r))) ^ r ∣
      (-1) ^ (x + c₀) * g x - (hZ (m * p ^ (r - 1)) (x / p) : ZMod (p ^ (3 * r))))
    (hpre : ∀ y j, j ≤ r → ¬ p ^ (j + 1) ∣ y → (p : ZMod (p ^ (3 * r))) ^ (r - j) ∣ F y)
    (B : ℕ) :
    ∑ s ∈ range B, gam p F s * bet p F s = 0 := by
  refine sum_eq_zero (fun s _ => ?_)
  by_cases hs : p ∣ s
  · rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp [bet]
    obtain ⟨τ, hτ1, hτr, hτs, hτmax⟩ := exists_tau hr hs
    have hγ : (p : ZMod (p ^ (3 * r))) ^ (r - τ) ∣ gam p F s := by
      unfold gam
      refine dvd_sum (fun x hx => ?_)
      have hxs : x ≤ s := Nat.lt_succ_iff.1 (mem_range.1 hx)
      split_ifs
      · exact pref_dvd F hpre (y₁ := x) (y₂ := s - x) hτr (fun h1 h2 => by
          have := dvd_add h1 h2; rwa [Nat.add_sub_cancel' hxs] at this) hτmax
      · exact dvd_zero _
    have hβ : bet p F s = ((m * p ^ r : ℕ) : ZMod (p ^ (3 * r))) ^ 2 * ∑ x ∈ range s,
        (if p ∣ x then 0 else (x : ZMod (p ^ (3 * r)))⁻¹ * ((s - x : ℕ) : ZMod (p ^ (3 * r)))⁻¹ *
          (g x * g (s - x))) := by
      unfold bet
      rw [sum_range_succ, ite_eq_right (fun h => h.1 hs), add_zero, mul_sum]
      refine sum_congr rfl (fun x hx => ?_)
      have hxs : x ≤ s := (mem_range.1 hx).le
      simp only [dvd_sub_iff_of_dvd hs hxs]
      split_ifs with h1 h2 h2
      · exact absurd h2 h1.1
      · rw [hFg x h2, hFg (s - x) (by rwa [dvd_sub_iff_of_dvd hs hxs])]
        ring
      · simp
      · exact absurd ⟨h2, h2⟩ h1
    obtain ⟨L, hL⟩ := hτs
    have hsL : s = L * p ^ τ := by rw [hL, mul_comm]
    have hker := kernel_one_side (K := 3 * r) hp5 (L := L) (c₀ := c₀) hτ1 hτr
      (fun u A => (hZ (m * p ^ (r - u)) A : ZMod (p ^ (3 * r))))
      (fun u A _ hur => hZ_cast_descent hm u A hur) g hg
    rw [← hsL] at hker
    have hNP : (p : ZMod (p ^ (3 * r))) ^ (2 * r) ∣ ((m * p ^ r : ℕ) : ZMod (p ^ (3 * r))) ^ 2 :=
      ⟨(m : ZMod (p ^ (3 * r))) ^ 2, by push_cast; ring⟩
    rw [hβ]
    apply eq_zero_of_pow_dvd
    have := mul_dvd_mul hγ (mul_dvd_mul hNP hker)
    rw [← pow_add, ← pow_add] at this
    exact pow_dvd_of_le _ (by omega) this
  · rw [gam_eq_zero F hs, zero_mul]

/-- The main congruence for an abstract kernel `F` with a descent kernel `g`. -/
theorem main_abstract (hp5 : 5 ≤ p) {r m M c₀ : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hM : M ≤ m * p ^ r) (F F' g : ℕ → ZMod (p ^ (3 * r)))
    (hF0 : ∀ z, M < z → F z = 0)
    (hFg : ∀ x, ¬ p ∣ x → F x =
      ((m * p ^ r : ℕ) : ZMod (p ^ (3 * r))) * (x : ZMod (p ^ (3 * r)))⁻¹ * g x)
    (hg : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ (3 * r))) ^ r ∣
      (-1) ^ (x + c₀) * g x - (hZ (m * p ^ (r - 1)) (x / p) : ZMod (p ^ (3 * r))))
    (hpre : ∀ y j, j ≤ r → ¬ p ^ (j + 1) ∣ y → (p : ZMod (p ^ (3 * r))) ^ (r - j) ∣ F y)
    (hdiv : ∀ a b a' b', a + b = a' + b' →
      F (p * a) * F (p * b) * (F (p * a') * F (p * b')) = F' a * F' b * (F' a' * F' b')) :
    ∑ s ∈ range (p * (2 * (m * p ^ (r - 1)) + 1)), conv F s * conv F s =
      ∑ s ∈ range (2 * (m * p ^ (r - 1)) + 1), conv F' s * conv F' s := by
  have hp0 : 0 < p := hp.out.pos
  have hFu : ∀ x, ¬ p ∣ x → (p : ZMod (p ^ (3 * r))) ^ r ∣ F x := fun x hx => by
    have := hpre x 0 (Nat.zero_le r) (by simpa using hx)
    simpa using this
  have hpr : p ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hB : 2 * (m * p ^ r) ≤ p * (2 * (m * p ^ (r - 1)) + 1) := by
    rw [hpr]
    nlinarith
  calc ∑ s ∈ range (p * (2 * (m * p ^ (r - 1)) + 1)), conv F s * conv F s
      = ∑ s ∈ range (p * (2 * (m * p ^ (r - 1)) + 1)),
          (gam p F s * gam p F s + alp p F s * alp p F s + 2 * (gam p F s * bet p F s)) :=
        sum_congr rfl (fun s _ => conv_sq_eq F hFu s)
    _ = ∑ s ∈ range (p * (2 * (m * p ^ (r - 1)) + 1)), gam p F s * gam p F s +
        ∑ s ∈ range (p * (2 * (m * p ^ (r - 1)) + 1)), alp p F s * alp p F s +
        2 * ∑ s ∈ range (p * (2 * (m * p ^ (r - 1)) + 1)), gam p F s * bet p F s := by
        rw [sum_add_distrib, sum_add_distrib, mul_sum]
    _ = _ := by
        rw [layer_sum hp0 F F' hdiv, split_sum_zero hp5 hr hm hM F g hF0 hFg hg hpre hB,
          one_side_sum_zero hp5 hr hm F g hFg hg hpre, add_zero, mul_zero, add_zero]

end Abstract

theorem choose_mul_sub {N x : ℕ} (hN : 1 ≤ N) : N.choose x * (N - x) = N * (N - 1).choose x := by
  have := Nat.choose_mul_succ_eq (N - 1) x
  rw [show N - 1 + 1 = N by omega] at this
  rw [mul_comm N, this]

theorem choose_shift_mul {n k : ℕ} (hn : 1 ≤ n) :
    (n - 1 + k).choose k * (n + k) = n * (n + k).choose k := by
  have := Nat.add_one_mul_choose_eq (n - 1 + k) (n - 1)
  rw [show n - 1 + k + 1 = n + k by omega, show n - 1 + 1 = n by omega,
    Nat.choose_symm_add, Nat.choose_symm_add] at this
  rw [mul_comm, this, mul_comm]

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

theorem ratio_cast {K k C C' : ℕ} {c : ℤ}
    (h : (C : ℤ) * uprod p 0 (p * k) = (C' : ℤ) * uprod p c (p * k)) :
    (C : ZMod (p ^ K)) = (C' : ZMod (p ^ K)) * PR p K (c : ZMod (p ^ K)) k := by
  have h2 := congrArg (Int.cast : ℤ → ZMod (p ^ K)) h
  simp only [Int.cast_mul, Int.cast_natCast] at h2
  rw [uprod_cast c (p * k), ← mul_assoc] at h2
  exact (IsUnit.mul_left_inj (isUnit_uprod (p * k))).1 h2

theorem PR_sub_one (hp5 : 5 ≤ p) {K r k e : ℕ} (hr : 1 ≤ r) (he : e ≤ r - 1) (hk : p ^ e ∣ k)
    {Z : ZMod (p ^ K)} (hZ : (p : ZMod (p ^ K)) ^ r ∣ Z) :
    (p : ZMod (p ^ K)) ^ (r + 2 + 2 * e) ∣ PR p K Z k - 1 := by
  have := jacobsthal_prod (K := K) hp5 he hk Z (by rwa [show 1 + (r - 1) = r by omega])
  rwa [show 3 + (r - 1) + 2 * e = r + 2 + 2 * e by omega] at this

omit hp in
theorem pow_dvd_pN' {K r N' : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N') :
    (p : ZMod (p ^ K)) ^ r ∣ (((p : ℤ) * N' : ℤ) : ZMod (p ^ K)) := by
  obtain ⟨c, rfl⟩ := hN'
  refine ⟨(c : ZMod (p ^ K)), ?_⟩
  have : (p : ZMod (p ^ K)) ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  push_cast
  rw [this]
  ring

omit hp in
theorem intCast_dvd_sub {K e : ℕ} {a b : ℤ} (h : (p : ℤ) ^ e ∣ a - b) :
    (p : ZMod (p ^ K)) ^ e ∣ (a : ZMod (p ^ K)) - (b : ZMod (p ^ K)) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨(c : ZMod (p ^ K)), by rw [← Int.cast_sub, hc, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast]⟩

theorem pre_of_F {K n N y j T G : ℕ} (hN : p ^ n ∣ N) (hF : y * T = N * G)
    (hy : ¬ p ^ (j + 1) ∣ y) : (p : ZMod (p ^ K)) ^ (n - j) ∣ (T : ZMod (p ^ K)) := by
  have h1 : p ^ n ∣ y * T := hF ▸ dvd_mul_of_dvd_left hN G
  obtain ⟨c, hc⟩ := pow_dvd_of_pow_dvd_mul h1 hy
  exact ⟨(c : ZMod (p ^ K)), by rw [hc]; push_cast; ring⟩

theorem ratio_sub_int (hp5 : 5 ≤ p) {N' k : ℕ} (hN' : 1 ≤ N') :
    (((p * N' - 1).choose (p * k) : ℕ) : ℤ) * uprod p 0 (p * k) =
      (((N' - 1).choose k : ℕ) : ℤ) * uprod p (-((p : ℤ) * N')) (p * k) := by
  have h := descent_sub_exact hp.out.pos hN' (p * k)
  rw [Nat.mul_div_cancel_left k hp.out.pos] at h
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hs : (-1 : ℤ) ^ (p * k) = (-1) ^ k := by rw [pow_mul, hodd.neg_one_pow]
  rw [hs, mul_assoc, mul_assoc] at h
  exact mul_left_cancel₀ (pow_ne_zero k (by norm_num)) h

theorem ratio_choose_int (hp5 : 5 ≤ p) {N' k : ℕ} (hk : k < N') :
    (((p * N').choose (p * k) : ℕ) : ℤ) * uprod p 0 (p * k) =
      ((N'.choose k : ℕ) : ℤ) * uprod p (-((p : ℤ) * N')) (p * k) := by
  have hp0 := hp.out.pos
  have e1 := ratio_sub_int hp5 (k := k) (N' := N') (by omega)
  have hle : p * k ≤ p * N' := Nat.mul_le_mul_left p hk.le
  have e2 : (((p * N').choose (p * k) : ℕ) : ℤ) * ((p : ℤ) * N' - p * k) =
      (p : ℤ) * N' * (((p * N' - 1).choose (p * k) : ℕ) : ℤ) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) (choose_mul_sub (N := p * N') (x := p * k)
      (Nat.mul_pos hp0 (by omega)))
    push_cast [Nat.cast_sub hle] at h
    linear_combination h
  have e3 : ((N'.choose k : ℕ) : ℤ) * ((N' : ℤ) - k) = (N' : ℤ) * (((N' - 1).choose k : ℕ) : ℤ) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) (choose_mul_sub (N := N') (x := k) (by omega))
    push_cast [Nat.cast_sub hk.le] at h
    linear_combination h
  have hne : (p : ℤ) * ((N' : ℤ) - k) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hp0.ne') (sub_ne_zero.2 (by exact_mod_cast hk.ne'))
  apply mul_right_cancel₀ hne
  linear_combination (uprod p 0 (p * k)) * e2 + (p : ℤ) * N' * e1 -
    (p : ℤ) * uprod p (-((p : ℤ) * N')) (p * k) * e3

theorem ratio_shift_int {N' k : ℕ} (hN' : 1 ≤ N') :
    (((p * N' - 1 + p * k).choose (p * k) : ℕ) : ℤ) * uprod p 0 (p * k) =
      (((N' - 1 + k).choose k : ℕ) : ℤ) * uprod p ((p : ℤ) * N') (p * k) := by
  have hp0 := hp.out.pos
  have e1 := descent_add_exact (p := p) N' (p * k)
  rw [Nat.mul_div_cancel_left k hp0] at e1
  have e2 : (((p * N' - 1 + p * k).choose (p * k) : ℕ) : ℤ) * ((p : ℤ) * N' + p * k) =
      (p : ℤ) * N' * (((p * N' + p * k).choose (p * k) : ℕ) : ℤ) := by
    exact_mod_cast choose_shift_mul (n := p * N') (k := p * k) (Nat.mul_pos hp0 hN')
  have e3 : (((N' - 1 + k).choose k : ℕ) : ℤ) * ((N' : ℤ) + k) =
      (N' : ℤ) * (((N' + k).choose k : ℕ) : ℤ) := by
    exact_mod_cast choose_shift_mul (n := N') (k := k) hN'
  have hne : (p : ℤ) * ((N' : ℤ) + k) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hp0.ne') (by omega)
  apply mul_right_cancel₀ hne
  linear_combination (uprod p 0 (p * k)) * e2 + (p : ℤ) * N' * e1 -
    (p : ℤ) * uprod p ((p : ℤ) * N') (p * k) * e3

theorem ratio_choose (hp5 : 5 ≤ p) {K N' : ℕ} (k : ℕ) :
    (((p * N').choose (p * k) : ℕ) : ZMod (p ^ K)) = ((N'.choose k : ℕ) : ZMod (p ^ K)) *
      (if k < N' then PR p K ((-((p : ℤ) * N') : ℤ) : ZMod (p ^ K)) k else 1) := by
  rcases lt_trichotomy k N' with hk | hk | hk
  · rw [ite_eq_left hk]
    exact ratio_cast (ratio_choose_int hp5 hk)
  · subst hk
    rw [ite_eq_right (lt_irrefl _), Nat.choose_self, Nat.choose_self]
    simp
  · have hlt : p * N' < p * k := by have := hp.out.pos; nlinarith
    rw [ite_eq_right (by omega), Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt hlt]
    simp

/-- Among four divisibility facts tied by `a + b = a' + b'`, at least two fail. -/
theorem two_le_count (A B C D : Prop) [Decidable A] [Decidable B] [Decidable C] [Decidable D]
    (h0 : ¬ (A ∧ B ∧ C ∧ D)) (hA : B → C → D → A) (hB : A → C → D → B)
    (hC : A → B → D → C) (hD : A → B → C → D) :
    2 ≤ (if A then 0 else 1) + (if B then 0 else 1) + ((if C then 0 else 1) + (if D then 0 else 1)) := by
  by_cases a : A <;> by_cases b : B <;> by_cases c : C <;> by_cases d : D <;> simp_all

omit hp in
/-- Lemma 5: the divisible layer, termwise; the minimum valuation is attained twice. -/
theorem layer_four {r : ℕ} (F F' ρ : ℕ → ZMod (p ^ (3 * r)))
    (hρ : ∀ k, F (p * k) = F' k * ρ k)
    (hρ1 : ∀ k e, e ≤ r - 1 → p ^ e ∣ k → (p : ZMod (p ^ (3 * r))) ^ (r + 2 + 2 * e) ∣ ρ k - 1)
    (hF' : ∀ k j, j ≤ r - 1 → ¬ p ^ (j + 1) ∣ k → (p : ZMod (p ^ (3 * r))) ^ (r - 1 - j) ∣ F' k)
    (a b a' b' : ℕ) (h : a + b = a' + b') :
    F (p * a) * F (p * b) * (F (p * a') * F (p * b')) = F' a * F' b * (F' a' * F' b') := by
  rw [hρ a, hρ b, hρ a', hρ b']
  set Q : ℕ → Prop := fun j => p ^ j ∣ a ∧ p ^ j ∣ b ∧ p ^ j ∣ a' ∧ p ^ j ∣ b' with hQ
  set μ := Nat.findGreatest Q (r - 1) with hμ
  have hμle : μ ≤ r - 1 := Nat.findGreatest_le _
  have hμspec : Q μ := Nat.findGreatest_spec (P := Q) (Nat.zero_le _) (by simp [hQ])
  obtain ⟨hda, hdb, hda', hdb'⟩ := hμspec
  have hR : (p : ZMod (p ^ (3 * r))) ^ (r + 2 + 2 * μ) ∣ ρ a * ρ b * (ρ a' * ρ b') - 1 :=
    mul_sub_one_dvd (mul_sub_one_dvd (hρ1 a μ hμle hda) (hρ1 b μ hμle hdb))
      (mul_sub_one_dvd (hρ1 a' μ hμle hda') (hρ1 b' μ hμle hdb'))
  have hprod : (p : ZMod (p ^ (3 * r))) ^ (2 * (r - 1 - μ)) ∣ F' a * F' b * (F' a' * F' b') := by
    rcases eq_or_lt_of_le hμle with hμe | hμlt
    · rw [hμe, Nat.sub_self, mul_zero, pow_zero]
      exact one_dvd _
    · have hng : ¬ Q (μ + 1) := Nat.findGreatest_is_greatest (P := Q) (Nat.lt_succ_self _)
        (by omega)
      have hd : ∀ k, (p : ZMod (p ^ (3 * r))) ^ ((r - 1 - μ) * (if p ^ (μ + 1) ∣ k then 0 else 1))
          ∣ F' k := by
        intro k
        split_ifs with hk
        · rw [mul_zero, pow_zero]
          exact one_dvd _
        · rw [mul_one]
          exact hF' k μ hμle hk
      have hcount := two_le_count (p ^ (μ + 1) ∣ a) (p ^ (μ + 1) ∣ b) (p ^ (μ + 1) ∣ a')
        (p ^ (μ + 1) ∣ b') hng
        (fun hb ha' hb' => (Nat.dvd_add_left hb).1 (h ▸ dvd_add ha' hb'))
        (fun ha ha' hb' => (Nat.dvd_add_right ha).1 (h ▸ dvd_add ha' hb'))
        (fun ha hb hb' => (Nat.dvd_add_left hb').1 (h.symm ▸ dvd_add ha hb))
        (fun ha hb ha' => (Nat.dvd_add_right ha').1 (h.symm ▸ dvd_add ha hb))
      have := mul_dvd_mul (mul_dvd_mul (hd a) (hd b)) (mul_dvd_mul (hd a') (hd b'))
      rw [← pow_add, ← pow_add, ← pow_add, ← mul_add, ← mul_add, ← mul_add] at this
      refine pow_dvd_of_le _ ?_ this
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left _ hcount
  have hzero : F' a * F' b * (F' a' * F' b') * (ρ a * ρ b * (ρ a' * ρ b') - 1) = 0 := by
    apply eq_zero_of_pow_dvd
    have := mul_dvd_mul hprod hR
    rw [← pow_add] at this
    exact pow_dvd_of_le _ (by omega) this
  linear_combination hzero

omit hp in
theorem A_cast_eq {K n B : ℕ} (hB : 2 * n + 1 ≤ B) :
    (A n : ZMod (p ^ K)) = ∑ s ∈ range B, conv (fun x => (term n x : ZMod (p ^ K))) s *
      conv (fun x => (term n x : ZMod (p ^ K))) s := by
  have hT : ∀ z, n < z → (term n z : ZMod (p ^ K)) = 0 := fun z hz => by
    simp [term, Nat.choose_eq_zero_of_lt hz]
  have h1 : (A n : ZMod (p ^ K)) = ∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1),
      ∑ k₃ ∈ range (n + 1), ∑ k₄ ∈ range (n + 1), if k₁ + k₂ = k₃ + k₄ then
        (term n k₁ : ZMod (p ^ K)) * term n k₂ * term n k₃ * term n k₄ else 0 := by
    unfold A
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  rw [h1, fourfold_eq n _ hT]
  symm
  apply sum_range_eq_of_vanish _ hB
  intro s hs _
  have : conv (fun x => (term n x : ZMod (p ^ K))) s = 0 := by
    unfold conv
    refine sum_eq_zero (fun x hx => ?_)
    dsimp only
    have hxs := mem_range.1 hx
    rcases le_or_gt x n with h | h
    · rw [hT (s - x) (by omega), mul_zero]
    · rw [hT x h, zero_mul]
  rw [this, zero_mul]

theorem ratio_add {K N' : ℕ} (k : ℕ) :
    (((p * N' + p * k).choose (p * k) : ℕ) : ZMod (p ^ K)) =
      (((N' + k).choose k : ℕ) : ZMod (p ^ K)) * PR p K (((p : ℤ) * N' : ℤ) : ZMod (p ^ K)) k := by
  have h := descent_add_exact (p := p) N' (p * k)
  rw [Nat.mul_div_cancel_left k hp.out.pos] at h
  exact ratio_cast h

theorem ratio_sub (hp5 : 5 ≤ p) {K N' : ℕ} (hN' : 1 ≤ N') (k : ℕ) :
    (((p * N' - 1).choose (p * k) : ℕ) : ZMod (p ^ K)) =
      (((N' - 1).choose k : ℕ) : ZMod (p ^ K)) *
        PR p K ((-((p : ℤ) * N') : ℤ) : ZMod (p ^ K)) k :=
  ratio_cast (ratio_sub_int hp5 hN')

theorem ratio_shift {K N' : ℕ} (hN' : 1 ≤ N') (k : ℕ) :
    (((p * N' - 1 + p * k).choose (p * k) : ℕ) : ZMod (p ^ K)) =
      (((N' - 1 + k).choose k : ℕ) : ZMod (p ^ K)) *
        PR p K (((p : ℤ) * N' : ℤ) : ZMod (p ^ K)) k :=
  ratio_cast (ratio_shift_int hN')

theorem PR_neg_sub_one (hp5 : 5 ≤ p) {K r N' k e : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N')
    (he : e ≤ r - 1) (hk : p ^ e ∣ k) :
    (p : ZMod (p ^ K)) ^ (r + 2 + 2 * e) ∣ PR p K ((-((p : ℤ) * N') : ℤ) : ZMod (p ^ K)) k - 1 :=
  PR_sub_one hp5 hr he hk (by rw [Int.cast_neg]; exact dvd_neg.2 (pow_dvd_pN' hr hN'))

theorem PR_pos_sub_one (hp5 : 5 ≤ p) {K r N' k e : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N')
    (he : e ≤ r - 1) (hk : p ^ e ∣ k) :
    (p : ZMod (p ^ K)) ^ (r + 2 + 2 * e) ∣ PR p K (((p : ℤ) * N' : ℤ) : ZMod (p ^ K)) k - 1 :=
  PR_sub_one hp5 hr he hk (pow_dvd_pN' hr hN')

omit hp in
theorem not_dvd_pos {x j : ℕ} (hx : ¬ p ^ j ∣ x) : 1 ≤ x :=
  Nat.pos_of_ne_zero (fun h => hx (h ▸ dvd_zero _))

/-- The unshifted tower in `ZMod (p ^ (3 r))`. -/
theorem tower_zmod (hp5 : 5 ≤ p) {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (A (m * p ^ r) : ZMod (p ^ (3 * r))) = (A (m * p ^ (r - 1)) : ZMod (p ^ (3 * r))) := by
  have hp0 : 0 < p := hp.out.pos
  have hpr : p ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hN : m * p ^ r = p * (m * p ^ (r - 1)) := by rw [hpr]; ring
  have hN'1 : 1 ≤ m * p ^ (r - 1) := Nat.mul_pos hm (pow_pos hp0 _)
  have hpN' : p ^ (r - 1) ∣ m * p ^ (r - 1) := dvd_mul_left _ _
  have hpN : p ^ r ∣ m * p ^ r := dvd_mul_left _ _
  have he : (p : ℤ) ^ r ∣ (p : ℤ) * ((m * p ^ (r - 1) : ℕ) : ℤ) :=
    ⟨m, by rw [← Nat.cast_mul, ← hN]; push_cast; ring⟩
  have hB : 2 * (m * p ^ r) + 1 ≤ p * (2 * (m * p ^ (r - 1)) + 1) := by
    rw [hN, show p * (2 * (m * p ^ (r - 1)) + 1) = 2 * (p * (m * p ^ (r - 1))) + p by ring]
    omega
  have hρ : ∀ k, (term (m * p ^ r) (p * k) : ZMod (p ^ (3 * r))) =
      (term (m * p ^ (r - 1)) k : ZMod (p ^ (3 * r))) *
        ((if k < m * p ^ (r - 1) then
          PR p (3 * r) ((-((p : ℤ) * (m * p ^ (r - 1) : ℕ)) : ℤ) : ZMod (p ^ (3 * r))) k else 1) *
          PR p (3 * r) (((p : ℤ) * (m * p ^ (r - 1) : ℕ) : ℤ) : ZMod (p ^ (3 * r))) k) := by
    intro k
    rw [hN]
    unfold term
    rw [Nat.cast_mul, Nat.cast_mul, ratio_choose hp5 k, ratio_add k]
    ring
  have hρ1 : ∀ k e, e ≤ r - 1 → p ^ e ∣ k → (p : ZMod (p ^ (3 * r))) ^ (r + 2 + 2 * e) ∣
      (if k < m * p ^ (r - 1) then
          PR p (3 * r) ((-((p : ℤ) * (m * p ^ (r - 1) : ℕ)) : ℤ) : ZMod (p ^ (3 * r))) k else 1) *
          PR p (3 * r) (((p : ℤ) * (m * p ^ (r - 1) : ℕ) : ℤ) : ZMod (p ^ (3 * r))) k - 1 := by
    intro k e he hk
    apply mul_sub_one_dvd
    · split_ifs
      · exact PR_neg_sub_one hp5 hr hpN' he hk
      · simp
    · exact PR_pos_sub_one hp5 hr hpN' he hk
  have hF' : ∀ k j, j ≤ r - 1 → ¬ p ^ (j + 1) ∣ k →
      (p : ZMod (p ^ (3 * r))) ^ (r - 1 - j) ∣ (term (m * p ^ (r - 1)) k : ZMod (p ^ (3 * r))) :=
    fun k j _ hk => pre_of_F hpN' (F0 (not_dvd_pos hk)) hk
  rw [A_cast_eq hB, A_cast_eq (le_refl (2 * (m * p ^ (r - 1)) + 1))]
  refine main_abstract hp5 hr hm (le_refl _)
    (fun x => (term (m * p ^ r) x : ZMod (p ^ (3 * r))))
    (fun x => (term (m * p ^ (r - 1)) x : ZMod (p ^ (3 * r))))
    (fun x => (g0 (m * p ^ r) x : ZMod (p ^ (3 * r)))) (c₀ := 1) ?_ ?_ ?_ ?_
    (fun a b a' b' h => layer_four (fun x => (term (m * p ^ r) x : ZMod (p ^ (3 * r)))) _ _ hρ hρ1
      hF' a b a' b' h)
  · intro z hz
    simp [term, Nat.choose_eq_zero_of_lt hz]
  · intro x hx
    have h : (x : ZMod (p ^ (3 * r))) * (term (m * p ^ r) x : ZMod (p ^ (3 * r))) =
        ((m * p ^ r : ℕ) : ZMod (p ^ (3 * r))) * (g0 (m * p ^ r) x : ZMod (p ^ (3 * r))) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul]
      exact congrArg _ <| F0 (N := m * p ^ r) (x := x) (not_dvd_pos (x := x) (j := 1) (by simpa using hx))
    have hinv := natCast_mul_inv (K := 3 * r) hx
    linear_combination (x : ZMod (p ^ (3 * r)))⁻¹ * h -
      (term (m * p ^ r) x : ZMod (p ^ (3 * r))) * hinv
  · intro x hx
    have := intCast_dvd_sub (K := 3 * r) (g0_descent hp.out hN'1 he hx)
    rw [← hN] at this
    push_cast at this
    exact this
  · intro y j _ hy
    exact pre_of_F hpN (F0 (not_dvd_pos hy)) hy

/-- The shifted tower in `ZMod (p ^ (3 r))`. -/
theorem tower_shift_zmod (hp5 : 5 ≤ p) {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (A (m * p ^ r - 1) : ZMod (p ^ (3 * r))) = (A (m * p ^ (r - 1) - 1) : ZMod (p ^ (3 * r))) := by
  have hp0 : 0 < p := hp.out.pos
  have hpr : p ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hN : m * p ^ r = p * (m * p ^ (r - 1)) := by rw [hpr]; ring
  have hN'1 : 1 ≤ m * p ^ (r - 1) := Nat.mul_pos hm (pow_pos hp0 _)
  have hN1 : 1 ≤ m * p ^ r := Nat.mul_pos hm (pow_pos hp0 _)
  have hpN' : p ^ (r - 1) ∣ m * p ^ (r - 1) := dvd_mul_left _ _
  have hpN : p ^ r ∣ m * p ^ r := dvd_mul_left _ _
  have he : (p : ℤ) ^ r ∣ (p : ℤ) * ((m * p ^ (r - 1) : ℕ) : ℤ) :=
    ⟨m, by rw [← Nat.cast_mul, ← hN]; push_cast; ring⟩
  have hB : 2 * (m * p ^ r - 1) + 1 ≤ p * (2 * (m * p ^ (r - 1)) + 1) := by
    rw [hN, show p * (2 * (m * p ^ (r - 1)) + 1) = 2 * (p * (m * p ^ (r - 1))) + p by ring]
    omega
  have hB' : 2 * (m * p ^ (r - 1) - 1) + 1 ≤ 2 * (m * p ^ (r - 1)) + 1 := by omega
  have hρ : ∀ k, (term (m * p ^ r - 1) (p * k) : ZMod (p ^ (3 * r))) =
      (term (m * p ^ (r - 1) - 1) k : ZMod (p ^ (3 * r))) *
        (PR p (3 * r) ((-((p : ℤ) * (m * p ^ (r - 1) : ℕ)) : ℤ) : ZMod (p ^ (3 * r))) k *
          PR p (3 * r) (((p : ℤ) * (m * p ^ (r - 1) : ℕ) : ℤ) : ZMod (p ^ (3 * r))) k) := by
    intro k
    rw [hN]
    unfold term
    rw [Nat.cast_mul, Nat.cast_mul, ratio_sub hp5 hN'1 k, ratio_shift hN'1 k]
    ring
  have hρ1 : ∀ k e, e ≤ r - 1 → p ^ e ∣ k → (p : ZMod (p ^ (3 * r))) ^ (r + 2 + 2 * e) ∣
      PR p (3 * r) ((-((p : ℤ) * (m * p ^ (r - 1) : ℕ)) : ℤ) : ZMod (p ^ (3 * r))) k *
        PR p (3 * r) (((p : ℤ) * (m * p ^ (r - 1) : ℕ) : ℤ) : ZMod (p ^ (3 * r))) k - 1 :=
    fun k e he hk => mul_sub_one_dvd (PR_neg_sub_one hp5 hr hpN' he hk)
      (PR_pos_sub_one hp5 hr hpN' he hk)
  have hF' : ∀ k j, j ≤ r - 1 → ¬ p ^ (j + 1) ∣ k →
      (p : ZMod (p ^ (3 * r))) ^ (r - 1 - j) ∣
        (term (m * p ^ (r - 1) - 1) k : ZMod (p ^ (3 * r))) :=
    fun k j _ hk => pre_of_F hpN' (F1 hN'1 (not_dvd_pos hk)) hk
  rw [A_cast_eq hB, A_cast_eq hB']
  refine main_abstract hp5 hr hm (M := m * p ^ r - 1) (Nat.sub_le _ 1)
    (fun x => (term (m * p ^ r - 1) x : ZMod (p ^ (3 * r))))
    (fun x => (term (m * p ^ (r - 1) - 1) x : ZMod (p ^ (3 * r))))
    (fun x => (g1 (m * p ^ r) x : ZMod (p ^ (3 * r)))) (c₀ := 0) ?_ ?_ ?_ ?_
    (fun a b a' b' h => layer_four (fun x => (term (m * p ^ r - 1) x : ZMod (p ^ (3 * r)))) _ _ hρ
      hρ1 hF' a b a' b' h)
  · intro z hz
    simp [term, Nat.choose_eq_zero_of_lt hz]
  · intro x hx
    have h : (x : ZMod (p ^ (3 * r))) * (term (m * p ^ r - 1) x : ZMod (p ^ (3 * r))) =
        ((m * p ^ r : ℕ) : ZMod (p ^ (3 * r))) * (g1 (m * p ^ r) x : ZMod (p ^ (3 * r))) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul]
      exact congrArg _ <| F1 (N := m * p ^ r) (x := x) hN1 (not_dvd_pos (x := x) (j := 1) (by simpa using hx))
    have hinv := natCast_mul_inv (K := 3 * r) hx
    linear_combination (x : ZMod (p ^ (3 * r)))⁻¹ * h -
      (term (m * p ^ r - 1) x : ZMod (p ^ (3 * r))) * hinv
  · intro x hx
    have := intCast_dvd_sub (K := 3 * r) (g1_descent hp.out hN'1 he hx)
    rw [← hN] at this
    push_cast at this
    simpa using this
  · intro y j _ hy
    exact pre_of_F hpN (F1 hN1 (not_dvd_pos hy)) hy

end Concrete


/-- MOS Conjecture 1.3 for $\sigma_8$, for the sum $A(n)$: for every prime $p \ge 5$ and all
$m, r \ge 1$, $A(m p^r) \equiv A(m p^{r-1}) \pmod{p^{3r}}$. -/
theorem tower (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    A (m * p ^ r) ≡ A (m * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have := Fact.mk hp
  rw [← ZMod.natCast_eq_natCast_iff]
  exact tower_zmod hp5 hm hr

/-- The shifted companion: for every prime $p \ge 5$ and all $m, r \ge 1$,
$A(m p^r - 1) \equiv A(m p^{r-1} - 1) \pmod{p^{3r}}$. -/
theorem shifted_tower (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (m r : ℕ) (hm : 1 ≤ m)
    (hr : 1 ≤ r) :
    A (m * p ^ r - 1) ≡ A (m * p ^ (r - 1) - 1) [MOD p ^ (3 * r)] := by
  have := Fact.mk hp
  rw [← ZMod.natCast_eq_natCast_iff]
  exact tower_shift_zmod hp5 hm hr

end MosN8

end
