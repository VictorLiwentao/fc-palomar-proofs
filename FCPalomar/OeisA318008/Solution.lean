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
# OEIS A318008: Hanna's parity conjecture

Let $A(x) = \sum_{n \ge 1} a(n) x^n \in \mathbb{Q}[[x]]$ satisfy $A(A(x - x^2)) = x + x^2$. The
file proves that $A$ exists and is unique (the normalization $a(1) = 1$ is forced, not assumed),
that every $a(n)$ is an integer, and that $a(n)$ is odd if and only if $n = 2^k - 1$ or
$n = 2^{k+1} - 2$ for some $k \ge 1$. This settles Paul D. Hanna's conjecture. It also proves
that OEIS A277292 is the odd bisection of $A$ and that A277292$(n)$ is odd if and only if $n$ is
a power of $2$.

Write $\varphi(y) = y + y^2$, $\psi(y) = y - y^2$, $c = x + c^2$ for the Catalan series (from
Mathlib's `catalanSeries`), and $E(G) = G(\varphi(G))$. Composition is `PowerSeries.subst`.
Mathlib's `substInv` API shows that a right compositional inverse is a two-sided inverse, and
that right inverses are unique.

*Composition estimates.* Substitution is a ring homomorphism. If $x^m$ divides $g' - g$, then
$f(g') - f(g) \equiv \sum_{j < N} f_j (g'^j - g^j) \pmod{x^{m + N - 1}}$. Hence, for
$G = x + g_2 x^2 + \dots$, replacing $G$ by $G + \delta x^m$ changes $E(G)$ by $2\delta x^m$
modulo $x^{m+1}$ (for $m \ge 2$), and by $2\delta x^m + (m+2)(1 + g_2)\delta x^{m+1}$ modulo
$x^{m+2}$ (for $m \ge 3$).

*Causal fixed points.* An operator $T$ on power series is causal if coefficient $n$ of $T(f)$
depends only on the coefficients of $f$ below $n$. A causal operator has exactly one fixed point,
built one coefficient at a time. (This follows the OeisA326097 package of this repository.)

*Existence and uniqueness over $\mathbb{Q}$.* The operator $T_G$ adds half the degree-$n$ error
of $E(G) = c$ to $g_n$. It is causal (pivot $2$), and its fixed points are the solutions of
$E(G) = c$ with $G = x + O(x^2)$; let $G_0$ be the fixed point. Then $A_0 = \varphi(G_0)$ is a
solution: $A_0(A_0) = \varphi(E(G_0)) = \varphi(c)$ and $c(\psi) = x$. Conversely, let $A$ be a
solution. Then $A(A) = \varphi(c)$. Put $G = \varphi^{-1}(A)$ with $\varphi^{-1}(x) = -c(-x)$.
Then $A = \varphi(G)$ and $E(G) = c$. Degree $1$ gives $g_1^2 = 1$, and degree $2$ rules out
$g_1 = -1$. So $G = G_0$ and $A = A_0$.

*Reversibility.* $\psi(G_0)$ is a right inverse, hence a two-sided inverse, of $\varphi(G_0)$.
So $G_0(\psi(G_0))$ is a right inverse of $\varphi$, hence equals $-c(-x)$. It follows that
$-G_0(-x)$ also solves $E(G) = c$, so it equals $G_0$: the series $G_0$ is odd.

*Integrality.* For odd $G$ and odd $n \ge 3$, the coefficient $g_n$ enters degree $n$ of $E(G)$
with pivot $2$ and degree $n + 1$ with pivot $n + 2$. The operator $T_B$ on odd series uses
degree $n + 1$ minus $\frac{n+1}{2}$ times degree $n$, whose pivot is $1$. It is causal over
every commutative ring and commutes with ring maps, so it has a fixed point $\kappa$ over
$\mathbb{Z}$ whose image is the fixed point over any ring. The series $G_0$ is a fixed point over
$\mathbb{Q}$, so $G_0$ is the image of $\kappa$, and $A_0 = \kappa + \kappa^2$ is integral.

*Parity.* Over $\mathbb{F}_2$, let $U = \sum_{k \ge 1} x^{2^k - 1}$. Frobenius gives
$U = x + x U^2 = x (1 + U)^2$. Let $\mu = x/(1+x)$, so $\mu(\mu) = x$. Then $w = \mu(U)$ satisfies
$w + w^2 = x$, so $w$ is the compositional inverse of $\varphi$, and $\mu(w) = U$. A short
computation gives $E(U) = U(\varphi(\mu(w))) = w$. Over $\mathbb{F}_2$, $\varphi = \psi$, so
$c$ is also the inverse of $\varphi$ and $w = c$. So $U$ is odd and solves $E(U) = c$: it is the
fixed point of $T_B$ over $\mathbb{F}_2$, hence the reduction of $\kappa$. Therefore
$A_0 \equiv U + U^2 \pmod 2$. The support of $U$ is $\{2^k - 1\}$ (odd numbers) and the support of
$U^2$ is $\{2^{k+1} - 2\}$ (even numbers).

*A277292.* Its equation $\mathrm{Rev}(G + G^2) = G - G^2$ says that $\psi(G)$ is the inverse of
$\varphi(G)$. Then $\psi(E(G)) = x$, so $E(G) = c$ and $G = G_0$. So $G$ is odd, and since
$G_0^2$ is even, the odd coefficients of $A_0 = G_0 + G_0^2$ are those of $G_0$. Modulo $2$,
$[x^{2n-1}] G_0 = [x^{2n-1}] U$, which is $1$ exactly when $n$ is a power of $2$.

*References:*
- Paul D. Hanna, [A318008](https://oeis.org/A318008), September 6, 2018.
- Paul D. Hanna, [A277292](https://oeis.org/A277292), October 12, 2016.
-/

@[expose] public section

namespace OeisA318008

open PowerSeries

/-- The defining equation $A(A(x - x^2)) = x + x^2$ of OEIS A318008, for $A$ with $A(0) = 0$. -/
def IsSolution (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ A.subst (A.subst (X - X ^ 2 : ℚ⟦X⟧)) = X + X ^ 2

section General
variable {R : Type*} [CommRing R]

lemma hs {g : R⟦X⟧} (hg : constantCoeff g = 0) : HasSubst g :=
  HasSubst.of_constantCoeff_zero' hg

lemma cc_subst {g : R⟦X⟧} (hg : constantCoeff g = 0) (f : R⟦X⟧) :
    constantCoeff (f.subst g) = constantCoeff f := by
  change MvPowerSeries.constantCoeff (f.subst g) = constantCoeff f
  rw [PowerSeries.constantCoeff_subst (hs hg)]
  simp only [map_pow]
  change (∑ᶠ d : ℕ, coeff d f • (constantCoeff g ^ d)) = constantCoeff f
  rw [finsum_eq_single (a := 0)]
  · simp
  · intro d hd
    simp [hg, hd]

lemma subst_assoc {g h : R⟦X⟧} (hg : constantCoeff g = 0) (hh : constantCoeff h = 0)
    (f : R⟦X⟧) : PowerSeries.subst h (f.subst g) = f.subst (g.subst h : R⟦X⟧) :=
  subst_comp_subst_apply (hs hg) (hs hh) f

lemma trunc_eq_sum (f : R⟦X⟧) (M : ℕ) :
    ((trunc M f : Polynomial R) : R⟦X⟧) = ∑ j ∈ Finset.range M, C (coeff j f) * X ^ j := by
  ext n
  simp only [Polynomial.coeff_coe, coeff_trunc, map_sum, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma subst_C' {g : R⟦X⟧} (hg : constantCoeff g = 0) (r : R) : (C r).subst g = C r := by
  rw [← coe_substAlgHom (hs hg)]
  have : (C r : R⟦X⟧) = algebraMap R R⟦X⟧ r := by simp
  rw [this, AlgHom.commutes]

lemma subst_eq_sum {g : R⟦X⟧} (hg : constantCoeff g = 0) (f : R⟦X⟧) (M : ℕ) :
    f.subst g = ∑ j ∈ Finset.range M, C (coeff j f) * g ^ j +
      g ^ M * (mk fun i => coeff (i + M) f).subst g := by
  have h := hs hg
  conv_lhs => rw [eq_X_pow_mul_shift_add_trunc M f, trunc_eq_sum]
  rw [subst_add h, subst_mul h, subst_pow h, subst_X h, add_comm]
  congr 1
  rw [← coe_substAlgHom h, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_pow, coe_substAlgHom h, subst_X h, subst_C' hg]

lemma X_pow_dvd_pow_sub_pow {m j : ℕ} (hj : 1 ≤ j) {g g' : R⟦X⟧} (hgg : X ^ m ∣ g' - g)
    (hg : X ∣ g) (hg' : X ∣ g') : X ^ (m + j - 1) ∣ g' ^ j - g ^ j := by
  rw [← geom_sum₂_mul]
  have hsum : X ^ (j - 1) ∣ ∑ i ∈ Finset.range j, g' ^ i * g ^ (j - 1 - i) := by
    apply Finset.dvd_sum
    intro i hi
    have hi' : i ≤ j - 1 := by simp at hi; omega
    calc (X : R⟦X⟧) ^ (j - 1) = X ^ i * X ^ (j - 1 - i) := by rw [← pow_add]; congr 1; omega
      _ ∣ _ := mul_dvd_mul (pow_dvd_pow_of_dvd hg' i) (pow_dvd_pow_of_dvd hg _)
  have e : m + j - 1 = (j - 1) + m := by omega
  rw [e, pow_add]
  exact mul_dvd_mul hsum hgg

/-- Taylor expansion of a composition in the inner argument. -/
lemma taylor {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) {g g' : R⟦X⟧} (hg : constantCoeff g = 0)
    (hg' : constantCoeff g' = 0) (hgg : X ^ m ∣ g' - g) (f : R⟦X⟧) :
    X ^ (m + N - 1) ∣ f.subst g' - f.subst g -
      ∑ j ∈ Finset.range N, C (coeff j f) * (g' ^ j - g ^ j) := by
  set M := m + N - 1 with hM
  have hNM : N ≤ M := by omega
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => C (coeff j f) * (g' ^ j - g ^ j)) hNM
  have hdiff : ∑ j ∈ Finset.range M, C (coeff j f) * g' ^ j -
      ∑ j ∈ Finset.range M, C (coeff j f) * g ^ j =
      ∑ j ∈ Finset.range M, C (coeff j f) * (g' ^ j - g ^ j) := by
    rw [← Finset.sum_sub_distrib]
    simp only [mul_sub]
  have key : f.subst g' - f.subst g - ∑ j ∈ Finset.range N, C (coeff j f) * (g' ^ j - g ^ j) =
      ∑ j ∈ Finset.Ico N M, C (coeff j f) * (g' ^ j - g ^ j) +
        (g' ^ M * (mk fun i => coeff (i + M) f).subst g' -
          g ^ M * (mk fun i => coeff (i + M) f).subst g) := by
    rw [subst_eq_sum hg' f M, subst_eq_sum hg f M]
    linear_combination hdiff - hsplit
  rw [key]
  have hX : X ∣ g := X_dvd_iff.mpr hg
  have hX' : X ∣ g' := X_dvd_iff.mpr hg'
  refine dvd_add (Finset.dvd_sum fun j hj => ?_) (dvd_sub ?_ ?_)
  · have hj' : N ≤ j := (Finset.mem_Ico.mp hj).1
    exact Dvd.dvd.mul_left ((pow_dvd_pow X (by omega)).trans
      (X_pow_dvd_pow_sub_pow (by omega) hgg hX hX')) _
  · exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hX' M) _
  · exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hX M) _

lemma subst_congr {N : ℕ} {f f' g g' : R⟦X⟧} (hg : constantCoeff g = 0)
    (hg' : constantCoeff g' = 0) (hf : X ^ N ∣ f' - f) (hgg : X ^ N ∣ g' - g) :
    X ^ N ∣ f'.subst g' - f.subst g := by
  obtain ⟨a, ha⟩ := hf
  have h1 : (f' - f).subst g' = g' ^ N * a.subst g' := by
    rw [ha, subst_mul (hs hg'), subst_pow (hs hg'), subst_X (hs hg')]
  have h2 : X ^ N ∣ f.subst g' - f.subst g := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have := taylor (m := N) (N := 1) hN le_rfl hg hg' hgg f
      simpa using this
  have : f'.subst g' - f.subst g = (f' - f).subst g' + (f.subst g' - f.subst g) := by
    rw [subst_sub (hs hg')]; ring
  rw [this, h1]
  exact dvd_add (Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hg') N) _) h2

lemma coeff_one_subst {g : R⟦X⟧} (hg : constantCoeff g = 0) (f : R⟦X⟧) :
    coeff 1 (f.subst g) = coeff 1 f * coeff 1 g := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.mpr hg
  rw [subst_eq_sum hg f 2]
  simp [Finset.sum_range_succ, mul_pow, coeff_X_pow_mul', coeff_C_mul, mul_assoc,
    coeff_zero_eq_constantCoeff_apply]

lemma coeff_two_subst {g : R⟦X⟧} (hg : constantCoeff g = 0) (f : R⟦X⟧) :
    coeff 2 (f.subst g) = coeff 1 f * coeff 2 g + coeff 2 f * coeff 1 g ^ 2 := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.mpr hg
  rw [subst_eq_sum hg f 3]
  simp [Finset.sum_range_succ, mul_pow, coeff_X_pow_mul', coeff_C_mul, mul_assoc,
    coeff_zero_eq_constantCoeff_apply]

lemma X_sq_dvd_sub_X {G : R⟦X⟧} (h0 : constantCoeff G = 0) (h1 : coeff 1 G = 1) :
    X ^ 2 ∣ G - X := by
  rw [X_pow_dvd_iff]
  intro i hi
  interval_cases i
  · simp [coeff_zero_eq_constantCoeff_apply, h0]
  · simp [h1]

lemma X_cube_dvd {G : R⟦X⟧} (h0 : constantCoeff G = 0) (h1 : coeff 1 G = 1) :
    X ^ 3 ∣ G - X - C (coeff 2 G) * X ^ 2 := by
  rw [X_pow_dvd_iff]
  intro i hi
  interval_cases i
  · simp [coeff_zero_eq_constantCoeff_apply, h0]
  · simp [h1]
  · simp [coeff_X]

lemma one_add_X_mul_pow (v : R⟦X⟧) (m : ℕ) :
    X ^ 2 ∣ (1 + X * v) ^ m - (1 + (m : R⟦X⟧) * X * v) := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(1 + X * v) * q + (m : R⟦X⟧) * v ^ 2, ?_⟩
    push_cast
    linear_combination (1 + X * v) * hq

lemma pow_near_X {y : R⟦X⟧} (b : R⟦X⟧) (hy : X ^ 3 ∣ y - X - b * X ^ 2) (m : ℕ) :
    X ^ (m + 2) ∣ y ^ m - X ^ m * (1 + (m : R⟦X⟧) * b * X) := by
  obtain ⟨w, hw⟩ := hy
  obtain ⟨q, hq⟩ := one_add_X_mul_pow (b + X * w) m
  have hy' : y = X * (1 + X * (b + X * w)) := by linear_combination hw
  refine ⟨(m : R⟦X⟧) * w + q, ?_⟩
  rw [hy', mul_pow]
  linear_combination X ^ m * hq

lemma pow_near_X' {y : R⟦X⟧} (hy : X ^ 2 ∣ y - X) (m : ℕ) :
    X ^ (m + 1) ∣ y ^ m - X ^ m := by
  obtain ⟨v, hv⟩ := hy
  have h := pow_near_X v (y := y) ⟨0, by linear_combination hv⟩ m
  have h2 : X ^ (m + 1) ∣ X ^ m * (1 + (m : R⟦X⟧) * v * X) - X ^ m :=
    ⟨(m : R⟦X⟧) * v, by ring⟩
  have := dvd_add ((pow_dvd_pow X (by omega)).trans h) h2
  simpa using this

/-- `E G = G(φ(G))` with `φ(y) = y + y²`. -/
noncomputable def E (G : R⟦X⟧) : R⟦X⟧ := G.subst (G + G ^ 2)

lemma cc_add_sq {G : R⟦X⟧} (h0 : constantCoeff G = 0) : constantCoeff (G + G ^ 2) = 0 := by
  simp [h0]

lemma cc_E {G : R⟦X⟧} (h0 : constantCoeff G = 0) : constantCoeff (E G) = 0 := by
  rw [E, cc_subst (cc_add_sq h0), h0]

lemma cc_monomial {m : ℕ} (hm : 1 ≤ m) (δ : R) : constantCoeff (C δ * X ^ m : R⟦X⟧) = 0 := by
  simp [zero_pow (by omega : m ≠ 0)]

lemma E_congr {N : ℕ} {F F' : R⟦X⟧} (h0 : constantCoeff F = 0) (h0' : constantCoeff F' = 0)
    (h : X ^ N ∣ F' - F) : X ^ N ∣ E F' - E F := by
  apply subst_congr (cc_add_sq h0) (cc_add_sq h0') h
  have : F' + F' ^ 2 - (F + F ^ 2) = (F' - F) * (1 + F' + F) := by ring
  rw [this]
  exact Dvd.dvd.mul_right h _

lemma E_of_add {G G' : R⟦X⟧} {m : ℕ} {δ : R} (hG' : G' = G + C δ * X ^ m)
    (hc : constantCoeff (G' + G' ^ 2) = 0) :
    E G' = G.subst (G' + G' ^ 2) + C δ * (G' + G' ^ 2) ^ m := by
  have h := hs hc
  have e : PowerSeries.subst (G' + G' ^ 2) G' =
      PowerSeries.subst (G' + G' ^ 2) (G + C δ * X ^ m) := by rw [← hG']
  rw [E, e, subst_add h, subst_mul h, subst_C' hc, subst_pow h, subst_X h]

/-- Changing `G` by `δ x^m` changes `G(φ(G))` by `2δ x^m` in degree `m`. -/
lemma E_perturb {G : R⟦X⟧} (h0 : constantCoeff G = 0) (h1 : coeff 1 G = 1) {m : ℕ}
    (hm : 2 ≤ m) (δ : R) :
    X ^ (m + 1) ∣ E (G + C δ * X ^ m) - E G - C (2 * δ) * X ^ m := by
  obtain ⟨G', hG'⟩ : ∃ G', G' = G + C δ * X ^ m := ⟨_, rfl⟩
  rw [← hG']
  have hG'0 : constantCoeff G' = 0 := by rw [hG', map_add, h0, cc_monomial (by omega), add_zero]
  have hy := cc_add_sq h0
  have hy' := cc_add_sq hG'0
  have hd : (G' + G' ^ 2) - (G + G ^ 2) = C δ * X ^ m * (1 + G + G') := by rw [hG']; ring
  have hdvd : X ^ m ∣ (G' + G' ^ 2) - (G + G ^ 2) := by
    rw [hd, mul_assoc]; exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  have hT := taylor (m := m) (N := 2) (by omega) (by norm_num) hy hy' hdvd G
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, sub_self, mul_zero,
    zero_add, pow_one, h1, map_one, one_mul] at hT
  rw [show m + 2 - 1 = m + 1 by omega] at hT
  have hX2' : X ^ 2 ∣ G' - X := by
    have : G' - X = (G - X) + C δ * X ^ m := by rw [hG']; ring
    rw [this]
    exact dvd_add (X_sq_dvd_sub_X h0 h1) (Dvd.dvd.mul_left (pow_dvd_pow X hm) _)
  have hy'X : X ^ 2 ∣ (G' + G' ^ 2) - X := by
    have : (G' + G' ^ 2) - X = (G' - X) + G' ^ 2 := by ring
    rw [this]
    exact dvd_add hX2' (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hG'0) 2)
  have hpow := pow_near_X' hy'X m
  have hGG : X ∣ G + G' := X_dvd_iff.mpr (by rw [map_add, h0, hG'0, add_zero])
  have key : E G' - E G - C (2 * δ) * X ^ m =
      (G.subst (G' + G' ^ 2) - G.subst (G + G ^ 2) - ((G' + G' ^ 2) - (G + G ^ 2))) +
        C δ * ((G' + G' ^ 2) ^ m - X ^ m) + C δ * X ^ m * (G + G') := by
    rw [E_of_add hG' hy', E, map_mul, map_ofNat]
    linear_combination hd
  rw [key]
  refine dvd_add (dvd_add hT (Dvd.dvd.mul_left hpow _)) ?_
  rw [pow_succ, mul_assoc]
  exact Dvd.dvd.mul_left (mul_dvd_mul_left _ hGG) _

/-- Changing `G` by `δ x^m` changes `G(φ(G))` by `2δ x^m + (m+2)(1+g₂)δ x^{m+1}` up to degree
`m + 1`. -/
lemma E_perturb2 {G : R⟦X⟧} (h0 : constantCoeff G = 0) (h1 : coeff 1 G = 1) {m : ℕ}
    (hm : 3 ≤ m) (δ : R) :
    X ^ (m + 2) ∣ E (G + C δ * X ^ m) - E G -
      (C (2 * δ) * X ^ m + C ((m + 2) * (1 + coeff 2 G) * δ) * X ^ (m + 1)) := by
  obtain ⟨G', hG'⟩ : ∃ G', G' = G + C δ * X ^ m := ⟨_, rfl⟩
  rw [← hG']
  set a := coeff 2 G with ha
  have hG'0 : constantCoeff G' = 0 := by rw [hG', map_add, h0, cc_monomial (by omega), add_zero]
  have hy := cc_add_sq h0
  have hy' := cc_add_sq hG'0
  have hd : (G' + G' ^ 2) - (G + G ^ 2) = C δ * X ^ m * (1 + G + G') := by rw [hG']; ring
  have hdvd : X ^ m ∣ (G' + G' ^ 2) - (G + G ^ 2) := by
    rw [hd, mul_assoc]; exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  have hT := taylor (m := m) (N := 3) (by omega) (by norm_num) hy hy' hdvd G
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, sub_self, mul_zero,
    zero_add, pow_one, h1, map_one, one_mul] at hT
  rw [show m + 3 - 1 = m + 2 by omega] at hT
  have hG3 := X_cube_dvd h0 h1
  rw [← ha] at hG3
  have hG'3 : X ^ 3 ∣ G' - X - C a * X ^ 2 := by
    have : G' - X - C a * X ^ 2 = (G - X - C a * X ^ 2) + C δ * X ^ m := by rw [hG']; ring
    rw [this]
    exact dvd_add hG3 (Dvd.dvd.mul_left (pow_dvd_pow X hm) _)
  have hX2 : X ^ 2 ∣ G - X := X_sq_dvd_sub_X h0 h1
  have hX2' : X ^ 2 ∣ G' - X := by
    have : G' - X = (G' - X - C a * X ^ 2) + C a * X ^ 2 := by ring
    rw [this]
    exact dvd_add ((pow_dvd_pow X (by norm_num)).trans hG'3) (dvd_mul_left _ _)
  have hXG : X ∣ G := X_dvd_iff.mpr h0
  have hXG' : X ∣ G' := X_dvd_iff.mpr hG'0
  have hy'3 : X ^ 3 ∣ (G' + G' ^ 2) - X - (1 + C a) * X ^ 2 := by
    have : (G' + G' ^ 2) - X - (1 + C a) * X ^ 2 =
        (G' - X - C a * X ^ 2) + (G' - X) * (G' + X) := by ring
    rw [this]
    refine dvd_add hG'3 ?_
    rw [pow_succ]
    exact mul_dvd_mul hX2' (dvd_add hXG' (dvd_refl X))
  have hpow := pow_near_X (1 + C a) hy'3 m
  have hZ : X ^ 2 ∣ (G - X) + (G' - X) +
      C a * ((1 + G + G') * ((G' + G' ^ 2) + (G + G ^ 2)) - 2 * X) := by
    refine dvd_add (dvd_add hX2 hX2') (Dvd.dvd.mul_left ?_ _)
    have : (1 + G + G') * ((G' + G' ^ 2) + (G + G ^ 2)) - 2 * X =
        ((G - X) + (G' - X) + G ^ 2 + G' ^ 2) + (G + G') * ((G' + G' ^ 2) + (G + G ^ 2)) := by
      ring
    rw [this]
    refine dvd_add (dvd_add (dvd_add (dvd_add hX2 hX2') (pow_dvd_pow_of_dvd hXG 2))
      (pow_dvd_pow_of_dvd hXG' 2)) ?_
    rw [pow_two]
    exact mul_dvd_mul (dvd_add hXG hXG')
      (dvd_add (dvd_add hXG' (dvd_pow hXG' two_ne_zero))
        (dvd_add hXG (dvd_pow hXG two_ne_zero)))
  have key : E G' - E G -
      (C (2 * δ) * X ^ m + C ((m + 2) * (1 + a) * δ) * X ^ (m + 1)) =
      (G.subst (G' + G' ^ 2) - G.subst (G + G ^ 2) -
        ((G' + G' ^ 2 - (G + G ^ 2)) + C a * ((G' + G' ^ 2) ^ 2 - (G + G ^ 2) ^ 2))) +
      C δ * ((G' + G' ^ 2) ^ m - X ^ m * (1 + (m : R⟦X⟧) * (1 + C a) * X)) +
      C δ * X ^ m * ((G - X) + (G' - X) +
        C a * ((1 + G + G') * ((G' + G' ^ 2) + (G + G ^ 2)) - 2 * X)) := by
    rw [E_of_add hG' hy', E]
    simp only [map_mul, map_add, map_ofNat, map_natCast, map_one]
    linear_combination (1 + C a * ((G' + G' ^ 2) + (G + G ^ 2))) * hd
  rw [key]
  refine dvd_add (dvd_add hT (Dvd.dvd.mul_left hpow _)) ?_
  rw [pow_add, mul_assoc]
  exact Dvd.dvd.mul_left (mul_dvd_mul_left _ hZ) _

end General

section Fix
variable {R : Type*} [CommRing R]

/-- Coefficient `n` of `T f` depends only on the coefficients of `f` below `n`. -/
def Causal (T : R⟦X⟧ → R⟦X⟧) : Prop :=
  ∀ n f g, (∀ k < n, coeff k f = coeff k g) → coeff n (T f) = coeff n (T g)

lemma Causal.eq {T : R⟦X⟧ → R⟦X⟧} (hT : Causal T) {f g : R⟦X⟧} (hf : T f = f)
    (hg : T g = g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    calc coeff n f = coeff n (T f) := by rw [hf]
      _ = coeff n (T g) := hT n f g ih
      _ = coeff n g := by rw [hg]

/-- The coefficients of the fixed point of a causal operator, one at a time. -/
noncomputable def fixSeq (T : R⟦X⟧ → R⟦X⟧) (n : ℕ) : R :=
  coeff n (T (mk fun k => if _h : k < n then fixSeq T k else 0))
termination_by n

/-- The fixed point of a causal operator. -/
noncomputable def fix (T : R⟦X⟧ → R⟦X⟧) : R⟦X⟧ := mk (fixSeq T)

lemma Causal.fix_eq {T : R⟦X⟧ → R⟦X⟧} (hT : Causal T) : T (fix T) = fix T := by
  ext n
  conv_rhs => rw [fix, coeff_mk, fixSeq]
  apply hT
  intro k hk
  simp [fix, hk]

lemma Causal.eq_map_fix {S : Type*} [CommRing S] (φ : R →+* S) {T : R⟦X⟧ → R⟦X⟧}
    {T' : S⟦X⟧ → S⟦X⟧} (hT : Causal T) (hT' : Causal T')
    (hcomm : ∀ f, map φ (T f) = T' (map φ f)) {g : S⟦X⟧} (hg : T' g = g) :
    g = map φ (fix T) :=
  hT'.eq hg (by rw [← hcomm, hT.fix_eq])

end Fix

section Ops
variable {R : Type*} [CommRing R]

lemma coeff_one_sq {G : R⟦X⟧} (h0 : constantCoeff G = 0) : coeff 1 (G ^ 2) = 0 := by
  have : X ^ 2 ∣ G ^ 2 := pow_dvd_pow_of_dvd (X_dvd_iff.mpr h0) 2
  exact X_pow_dvd_iff.mp this 1 (by norm_num)

lemma coeff_one_E {G : R⟦X⟧} (h0 : constantCoeff G = 0) (h1 : coeff 1 G = 1) :
    coeff 1 (E G) = 1 := by
  rw [E, coeff_one_subst (cc_add_sq h0), h1, map_add, coeff_one_sq h0, h1]
  simp

/-- The Catalan series $c = \sum_{n \ge 1} C_{n-1} x^n$, so that $c = x + c^2$. -/
noncomputable def cat (R : Type*) [CommRing R] : R⟦X⟧ := X * map (Nat.castRingHom R) catalanSeries

lemma cc_cat : constantCoeff (cat R) = 0 := by simp [cat]

lemma coeff_one_cat : coeff 1 (cat R) = 1 := by
  rw [cat, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_map, catalanSeries_coeff,
    catalan_zero, map_one]

lemma coeff_two_cat : coeff 2 (cat R) = 1 := by
  rw [cat, show (2 : ℕ) = 1 + 1 from rfl, coeff_succ_X_mul, coeff_map, catalanSeries_coeff,
    catalan_one, map_one]

lemma cat_sub_sq : cat R - cat R ^ 2 = X := by
  have h := congrArg (map (Nat.castRingHom R)) catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_X, map_one] at h
  rw [cat]
  linear_combination (-X) * h

lemma map_cat {S : Type*} [CommRing S] (φ : R →+* S) : map φ (cat R) = cat S := by
  rw [cat, cat, map_mul, map_X, ← RingHom.comp_apply (map φ), ← map_comp,
    Subsingleton.elim (φ.comp (Nat.castRingHom R)) (Nat.castRingHom S)]

lemma map_E {S : Type*} [CommRing S] (φ : R →+* S) {K : R⟦X⟧} (h0 : constantCoeff K = 0) :
    map φ (E K) = E (map φ K) := by
  have h := map_subst (hs (cc_add_sq h0)) (h := φ) K
  rw [E, E]
  refine h.trans ?_
  congr 1
  change map φ (K + K ^ 2) = _
  rw [map_add, map_pow]

/-- The odd normalization of `K`: linear coefficient `1` and the odd coefficients of `K`
from degree `3` on. -/
noncomputable def oddPart (K : R⟦X⟧) : R⟦X⟧ :=
  X + mk fun i => if i % 2 = 1 ∧ 3 ≤ i then coeff i K else 0

lemma coeff_oddPart (K : R⟦X⟧) (i : ℕ) :
    coeff i (oddPart K) = if i = 1 then 1 else if i % 2 = 1 ∧ 3 ≤ i then coeff i K else 0 := by
  simp only [oddPart, map_add, coeff_X, coeff_mk]
  split_ifs <;> first | omega | simp

lemma cc_oddPart (K : R⟦X⟧) : constantCoeff (oddPart K) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_oddPart]; simp

lemma coeff_one_oddPart (K : R⟦X⟧) : coeff 1 (oddPart K) = 1 := by
  rw [coeff_oddPart]; simp

lemma coeff_two_oddPart (K : R⟦X⟧) : coeff 2 (oddPart K) = 0 := by
  rw [coeff_oddPart]; simp

lemma map_oddPart {S : Type*} [CommRing S] (φ : R →+* S) (K : R⟦X⟧) :
    map φ (oddPart K) = oddPart (map φ K) := by
  ext i
  rw [coeff_map, coeff_oddPart, coeff_oddPart]
  split_ifs <;> simp [coeff_map]

/-- The operator for odd solutions of $K(\varphi(K)) = c$. In odd degree $n \ge 3$ it combines
degree $n + 1$ (pivot $n + 2$) and degree $n$ (pivot $2$) so that the pivot is
$(n + 2) - \frac{n+1}{2} \cdot 2 = 1$. -/
noncomputable def TB (K : R⟦X⟧) : R⟦X⟧ := mk fun n =>
  if n % 2 = 1 ∧ 3 ≤ n then
    coeff n K + (coeff (n + 1) (cat R - E (oddPart K)) -
      (((n + 1) / 2 : ℕ) : R) * coeff n (cat R - E (oddPart K)))
  else coeff n (X : R⟦X⟧)

lemma TB_causal : Causal (TB (R := R)) := by
  intro n f g hfg
  simp only [TB, coeff_mk]
  split_ifs with hn
  swap
  · rfl
  obtain ⟨hodd, h3⟩ := hn
  set δ := coeff n f - coeff n g with hδ
  have hc : constantCoeff (oddPart g + C δ * X ^ n) = 0 := by
    rw [map_add, cc_oddPart, cc_monomial (by omega), add_zero]
  have hdiff : X ^ (n + 2) ∣ oddPart f - (oddPart g + C δ * X ^ n) := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [map_sub, map_add, coeff_oddPart, coeff_oddPart, coeff_C_mul_X_pow]
    by_cases hin : i < n
    · rw [hfg i hin]
      split_ifs <;> first | omega | ring
    · rcases (show i = n ∨ i = n + 1 by omega) with rfl | rfl
      · split_ifs <;> first | omega | (rw [hδ]; ring)
      · split_ifs <;> first | omega | ring
  have h1 := E_congr hc (cc_oddPart f) hdiff
  have h2 := E_perturb2 (cc_oddPart g) (coeff_one_oddPart g) h3 δ
  rw [coeff_two_oddPart] at h2
  have h := X_pow_dvd_iff.mp (dvd_add h1 h2)
  have e0 := h n (by omega)
  have e1 := h (n + 1) (by omega)
  simp only [map_add, map_sub, coeff_C_mul_X_pow, ↓reduceIte,
    ite_eq_right (show n ≠ n + 1 by omega), ite_eq_right (show n + 1 ≠ n by omega), add_zero,
    zero_add] at e0 e1
  have ht : ((((n + 1) / 2 : ℕ)) : R) * 2 = n + 1 := by
    have := congrArg (Nat.cast : ℕ → R) (show (n + 1) / 2 * 2 = n + 1 by omega)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using this
  simp only [map_sub]
  linear_combination -e1 + ((((n + 1) / 2 : ℕ)) : R) * e0 + δ * ht - hδ

lemma map_TB {S : Type*} [CommRing S] (φ : R →+* S) (K : R⟦X⟧) :
    map φ (TB K) = TB (map φ K) := by
  ext n
  simp only [TB, coeff_map, coeff_mk]
  split_ifs
  · simp only [map_add, map_sub, map_mul, map_natCast, ← coeff_map, map_cat,
      map_E φ (cc_oddPart K), map_oddPart]
  · rw [← coeff_map, map_X]

lemma TB_eq_of {K : R⟦X⟧} (hK : oddPart K = K) (hE : E K = cat R) : TB K = K := by
  ext n
  simp only [TB, coeff_mk, hK, hE, sub_self, map_zero, mul_zero, add_zero]
  split_ifs with hn
  · rfl
  · rw [← hK, coeff_oddPart, coeff_X]
    split_ifs <;> rfl

/-- The normalization of `G`: constant coefficient `0`, linear coefficient `1`. -/
noncomputable def normPart (G : R⟦X⟧) : R⟦X⟧ := X + mk fun i => if 2 ≤ i then coeff i G else 0

lemma coeff_normPart (G : R⟦X⟧) (i : ℕ) :
    coeff i (normPart G) = if i = 1 then 1 else if 2 ≤ i then coeff i G else 0 := by
  simp only [normPart, map_add, coeff_X, coeff_mk]
  split_ifs <;> first | omega | simp

lemma cc_normPart (G : R⟦X⟧) : constantCoeff (normPart G) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_normPart]; simp

lemma coeff_one_normPart (G : R⟦X⟧) : coeff 1 (normPart G) = 1 := by
  rw [coeff_normPart]; simp

lemma normPart_eq {G : R⟦X⟧} (h0 : constantCoeff G = 0) (h1 : coeff 1 G = 1) :
    normPart G = G := by
  ext i
  rw [coeff_normPart]
  rcases i with _ | _ | i
  · simp [coeff_zero_eq_constantCoeff_apply, h0]
  · simp [h1]
  · simp

end Ops

section Rat

/-- The operator for $G(\varphi(G)) = c$ over $\mathbb{Q}$; the pivot in degree $n$ is $2$. -/
noncomputable def TG (G : ℚ⟦X⟧) : ℚ⟦X⟧ := mk fun n =>
  if 2 ≤ n then coeff n G + coeff n (cat ℚ - E (normPart G)) / 2 else coeff n (X : ℚ⟦X⟧)

lemma TG_causal : Causal TG := by
  intro n f g hfg
  simp only [TG, coeff_mk]
  split_ifs with hn
  swap
  · rfl
  set δ := coeff n f - coeff n g with hδ
  have hc : constantCoeff (normPart g + C δ * X ^ n) = 0 := by
    rw [map_add, cc_normPart, cc_monomial (by omega), add_zero]
  have hdiff : X ^ (n + 1) ∣ normPart f - (normPart g + C δ * X ^ n) := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [map_sub, map_add, coeff_normPart, coeff_normPart, coeff_C_mul_X_pow]
    by_cases hin : i < n
    · rw [hfg i hin]
      split_ifs <;> first | omega | ring
    · obtain rfl : i = n := by omega
      split_ifs <;> first | omega | (rw [hδ]; ring)
  have h1 := E_congr hc (cc_normPart f) hdiff
  have h2 := E_perturb (cc_normPart g) (coeff_one_normPart g) hn δ
  have h := X_pow_dvd_iff.mp (dvd_add h1 h2)
  have e0 := h n (by omega)
  simp only [map_add, map_sub, coeff_C_mul_X_pow, ↓reduceIte] at e0
  simp only [map_sub]
  linear_combination (-1 / 2 : ℚ) * e0 - hδ

lemma TG_eq_iff (G : ℚ⟦X⟧) :
    TG G = G ↔ constantCoeff G = 0 ∧ coeff 1 G = 1 ∧ E G = cat ℚ := by
  constructor
  · intro h
    have hc : ∀ n, coeff n (TG G) = coeff n G := fun n => by rw [h]
    have h0 : constantCoeff G = 0 := by
      have := hc 0
      simp [TG] at this
      exact this.symm
    have h1 : coeff 1 G = 1 := by
      have := hc 1
      simp [TG] at this
      exact this.symm
    refine ⟨h0, h1, ?_⟩
    rw [← sub_eq_zero]
    ext n
    rw [map_zero, map_sub]
    rcases n with _ | _ | n
    · simp [coeff_zero_eq_constantCoeff_apply, cc_cat, cc_E h0]
    · rw [coeff_one_cat, coeff_one_E h0 h1, sub_self]
    · have := hc (n + 2)
      simp only [TG, coeff_mk, ite_eq_left (by omega : 2 ≤ n + 2), normPart_eq h0 h1, map_sub] at this
      linear_combination -(2 : ℚ) * this
  · rintro ⟨h0, h1, hE⟩
    ext n
    simp only [TG, coeff_mk, normPart_eq h0 h1, hE, sub_self, map_zero, zero_div, add_zero]
    split_ifs with hn
    · rfl
    · rcases n with _ | _ | n
      · simp [coeff_zero_eq_constantCoeff_apply, h0]
      · simp [h1]
      · omega

end Rat

section SubstHelpers
variable {R : Type*} [CommRing R]

lemma cc_negX : constantCoeff (-X : R⟦X⟧) = 0 := by simp

lemma neg_subst {g : R⟦X⟧} (hg : constantCoeff g = 0) (f : R⟦X⟧) :
    ((-f).subst g : R⟦X⟧) = -(f.subst g) := by
  rw [← coe_substAlgHom (hs hg), map_neg]

lemma negX_subst {g : R⟦X⟧} (hg : constantCoeff g = 0) : ((-X : R⟦X⟧).subst g : R⟦X⟧) = -g := by
  rw [neg_subst hg, subst_X (hs hg)]

lemma add_sq_subst {g : R⟦X⟧} (hg : constantCoeff g = 0) (f : R⟦X⟧) :
    ((f + f ^ 2).subst g : R⟦X⟧) = f.subst g + (f.subst g) ^ 2 := by
  rw [subst_add (hs hg), subst_pow (hs hg)]

lemma sub_sq_subst {g : R⟦X⟧} (hg : constantCoeff g = 0) (f : R⟦X⟧) :
    ((f - f ^ 2).subst g : R⟦X⟧) = f.subst g - (f.subst g) ^ 2 := by
  rw [subst_sub (hs hg), subst_pow (hs hg)]

lemma phi_subst {g : R⟦X⟧} (hg : constantCoeff g = 0) :
    ((X + X ^ 2 : R⟦X⟧).subst g : R⟦X⟧) = g + g ^ 2 := by
  rw [add_sq_subst hg, subst_X (hs hg)]

lemma psi_subst {g : R⟦X⟧} (hg : constantCoeff g = 0) :
    ((X - X ^ 2 : R⟦X⟧).subst g : R⟦X⟧) = g - g ^ 2 := by
  rw [sub_sq_subst hg, subst_X (hs hg)]

lemma coeff_subst_negX (f : R⟦X⟧) (n : ℕ) :
    coeff n (f.subst (-X : R⟦X⟧)) = (-1) ^ n * coeff n f := by
  rw [show (-X : R⟦X⟧) = (-1 : R) • X by simp, ← rescale_eq_subst, coeff_rescale]

lemma cc_phi : constantCoeff (X + X ^ 2 : R⟦X⟧) = 0 := by simp

lemma cc_psi : constantCoeff (X - X ^ 2 : R⟦X⟧) = 0 := by simp

lemma unit_phi : IsUnit (coeff 1 (X + X ^ 2 : R⟦X⟧)) := by
  simp [coeff_X_pow]

lemma unit_psi : IsUnit (coeff 1 (X - X ^ 2 : R⟦X⟧)) := by
  simp [coeff_X_pow]

/-- A right compositional inverse is a left inverse. -/
lemma left_inv {P Q : R⟦X⟧} (hP0 : constantCoeff P = 0) (hP1 : IsUnit (coeff 1 P))
    (hQ0 : constantCoeff Q = 0) (h : (P.subst Q : R⟦X⟧) = X) : (Q.subst P : R⟦X⟧) = X :=
  subst_eq_X_of_subst_eq_X P hP0 hP1 (hs hQ0) h

/-- Right compositional inverses are unique. -/
lemma right_inv_unique {P Q₁ Q₂ : R⟦X⟧} (hP0 : constantCoeff P = 0) (hP1 : IsUnit (coeff 1 P))
    (h1 : constantCoeff Q₁ = 0) (h2 : constantCoeff Q₂ = 0) (e1 : (P.subst Q₁ : R⟦X⟧) = X)
    (e2 : (P.subst Q₂ : R⟦X⟧) = X) : Q₁ = Q₂ := by
  rw [eq_substInvOfIsUnit_of_subst_eq_X P hP0 hP1 (hs h1) e1,
    eq_substInvOfIsUnit_of_subst_eq_X P hP0 hP1 (hs h2) e2]

lemma cat_right_inv : ((X - X ^ 2 : R⟦X⟧).subst (cat R) : R⟦X⟧) = X := by
  rw [psi_subst cc_cat, cat_sub_sq]

lemma cat_left_inv : ((cat R).subst (X - X ^ 2 : R⟦X⟧) : R⟦X⟧) = X :=
  left_inv cc_psi unit_psi cc_cat cat_right_inv

/-- The compositional inverse $\varphi^{-1}(x) = -c(-x)$ of $\varphi(x) = x + x^2$. -/
noncomputable def phiInv (R : Type*) [CommRing R] : R⟦X⟧ := -((cat R).subst (-X : R⟦X⟧))

lemma cc_phiInv : constantCoeff (phiInv R) = 0 := by
  rw [phiInv, map_neg, cc_subst cc_negX, cc_cat, neg_zero]

lemma phi_phiInv : ((X + X ^ 2 : R⟦X⟧).subst (phiInv R) : R⟦X⟧) = X := by
  rw [phi_subst cc_phiInv, phiInv]
  have := congrArg (fun F : R⟦X⟧ => (F.subst (-X : R⟦X⟧) : R⟦X⟧)) (cat_sub_sq (R := R))
  simp only [sub_sq_subst cc_negX, subst_X (hs (cc_negX (R := R)))] at this
  linear_combination -this

lemma phiInv_phi : ((phiInv R).subst (X + X ^ 2 : R⟦X⟧) : R⟦X⟧) = X :=
  left_inv cc_phi unit_phi cc_phiInv phi_phiInv

lemma coeff_two_sq {G : R⟦X⟧} (h0 : constantCoeff G = 0) : coeff 2 (G ^ 2) = coeff 1 G ^ 2 := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.mpr h0
  rw [mul_pow, coeff_X_pow_mul', ite_eq_left le_rfl]
  simp [coeff_zero_eq_constantCoeff_apply]

end SubstHelpers

section Main

/-- The unique solution of $G(\varphi(G)) = c$ with $G = x + O(x^2)$ over $\mathbb{Q}$. -/
noncomputable def G₀ : ℚ⟦X⟧ := fix TG

lemma G₀_spec : constantCoeff G₀ = 0 ∧ coeff 1 G₀ = 1 ∧ E G₀ = cat ℚ :=
  (TG_eq_iff _).mp TG_causal.fix_eq

lemma eq_G₀ {G : ℚ⟦X⟧} (h0 : constantCoeff G = 0) (h1 : coeff 1 G = 1) (hE : E G = cat ℚ) :
    G = G₀ :=
  TG_causal.eq ((TG_eq_iff G).mpr ⟨h0, h1, hE⟩) TG_causal.fix_eq

/-- `G₀ - G₀²` is the compositional inverse of `G₀ + G₀²`. -/
lemma G₀_rev : ((G₀ + G₀ ^ 2).subst (G₀ - G₀ ^ 2) : ℚ⟦X⟧) = X := by
  obtain ⟨h0, h1, hE⟩ := G₀_spec
  have hy0 := cc_add_sq h0
  have hL0 : constantCoeff (G₀ - G₀ ^ 2) = 0 := by simp [h0]
  have hL1 : coeff 1 (G₀ - G₀ ^ 2) = 1 := by rw [map_sub, coeff_one_sq h0, h1, sub_zero]
  have s1 : ((G₀ - G₀ ^ 2).subst (G₀ + G₀ ^ 2) : ℚ⟦X⟧) = X := by
    rw [sub_sq_subst hy0]
    change E G₀ - E G₀ ^ 2 = X
    rw [hE, cat_sub_sq]
  exact left_inv hL0 (by rw [hL1]; exact isUnit_one) hy0 s1

/-- Reversibility: `G₀` is odd. -/
lemma G₀_odd {n : ℕ} (hn : n % 2 = 0) : coeff n G₀ = 0 := by
  obtain ⟨h0, h1, hE⟩ := G₀_spec
  have hL0 : constantCoeff (G₀ - G₀ ^ 2) = 0 := by simp [h0]
  have s2 := G₀_rev
  rw [add_sq_subst hL0] at s2
  have hc'0 : constantCoeff (G₀.subst (G₀ - G₀ ^ 2) : ℚ⟦X⟧) = 0 := by rw [cc_subst hL0, h0]
  -- Both `G₀(ψ(G₀))` and `φ⁻¹` are right inverses of `φ`.
  have s5 := right_inv_unique cc_phi unit_phi hc'0 cc_phiInv
    (by rw [phi_subst hc'0]; exact s2) phi_phiInv
  -- So `G' = -G₀(-x)` is also a normalized solution.
  have hG'0 : constantCoeff (-(G₀.subst (-X : ℚ⟦X⟧)) : ℚ⟦X⟧) = 0 := by
    rw [map_neg, cc_subst cc_negX, h0, neg_zero]
  have hG'1 : coeff 1 (-(G₀.subst (-X : ℚ⟦X⟧)) : ℚ⟦X⟧) = 1 := by
    rw [map_neg, coeff_subst_negX, h1]; norm_num
  have hH0 : constantCoeff (-((G₀ - G₀ ^ 2).subst (-X : ℚ⟦X⟧)) : ℚ⟦X⟧) = 0 := by
    rw [map_neg, cc_subst cc_negX, hL0, neg_zero]
  have hE' : E (-(G₀.subst (-X : ℚ⟦X⟧))) = cat ℚ := by
    have e1 : (-(G₀.subst (-X : ℚ⟦X⟧)) : ℚ⟦X⟧) + (-(G₀.subst (-X : ℚ⟦X⟧))) ^ 2 =
        -((G₀ - G₀ ^ 2).subst (-X : ℚ⟦X⟧)) := by
      rw [sub_sq_subst cc_negX]; ring
    rw [E, e1, neg_subst hH0, subst_assoc cc_negX hH0, negX_subst hH0, neg_neg,
      ← subst_assoc hL0 cc_negX, s5, phiInv, neg_subst cc_negX, subst_assoc cc_negX cc_negX,
      negX_subst cc_negX, neg_neg, neg_neg, X_subst]
  have hc := congrArg (coeff n) (eq_G₀ hG'0 hG'1 hE')
  rw [map_neg, coeff_subst_negX, Even.neg_one_pow (Nat.even_iff.mpr hn), one_mul] at hc
  linarith

/-- The integer solution: the fixed point of `TB` over `ℤ`. -/
noncomputable def κ : ℤ⟦X⟧ := fix (TB (R := ℤ))

lemma oddPart_G₀ : oddPart G₀ = G₀ := by
  obtain ⟨h0, h1, -⟩ := G₀_spec
  ext i
  rw [coeff_oddPart]
  split_ifs with h1' h2'
  · rw [h1', h1]
  · rfl
  · rcases Nat.mod_two_eq_zero_or_one i with h | h
    · exact (G₀_odd h).symm
    · obtain rfl : i = 1 := by omega
      exact absurd rfl h1'

lemma G₀_eq_map : G₀ = map (Int.castRingHom ℚ) κ :=
  TB_causal.eq_map_fix (Int.castRingHom ℚ) TB_causal (map_TB _) (TB_eq_of oddPart_G₀ G₀_spec.2.2)

end Main

section F2

lemma two_eq_zero : (2 : (ZMod 2)⟦X⟧) = 0 := by
  rw [show (2 : (ZMod 2)⟦X⟧) = C (2 : ZMod 2) from (map_ofNat C 2).symm,
    show (2 : ZMod 2) = 0 from rfl, map_zero]

/-- `n = 2^k - 1` for some `k ≥ 1`. -/
def Mersenne (n : ℕ) : Prop := ∃ k, 1 ≤ k ∧ n = 2 ^ k - 1

lemma Mersenne.mod_two {n : ℕ} (h : Mersenne n) : n % 2 = 1 := by
  obtain ⟨k, hk, rfl⟩ := h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  have := Nat.one_le_two_pow (n := j)
  omega

lemma not_mersenne_zero : ¬ Mersenne 0 := by
  rintro ⟨k, hk, h⟩
  have := Nat.one_lt_two_pow (n := k) (by omega)
  omega

lemma mersenne_double_add_one (j : ℕ) : Mersenne (2 * j + 1) ↔ j = 0 ∨ Mersenne j := by
  constructor
  · rintro ⟨k, hk, h⟩
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ] at h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · left; simp at h; omega
    · right; exact ⟨i, hi, by omega⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨1, le_rfl, rfl⟩
    · refine ⟨k + 1, by omega, ?_⟩
      rw [pow_succ]
      have := Nat.one_le_two_pow (n := k)
      omega

/-- The solution modulo `2`: `U = ∑_{k ≥ 1} x^{2^k - 1}`. -/
noncomputable def U : (ZMod 2)⟦X⟧ := by
  classical
  exact mk fun n => if Mersenne n then 1 else 0

lemma coeff_U (n : ℕ) [Decidable (Mersenne n)] : coeff n U = if Mersenne n then 1 else 0 := by
  rw [U, coeff_mk]
  congr

lemma cc_U : constantCoeff U = 0 := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_U, ite_eq_right not_mersenne_zero]

lemma coeff_U_sq (n : ℕ) : coeff n (U ^ 2) = if n % 2 = 0 then coeff (n / 2) U else 0 := by
  have h : coeff n (U ^ Fintype.card (ZMod 2)) =
      if Fintype.card (ZMod 2) ∣ n then coeff (n / Fintype.card (ZMod 2)) U else 0 := by
    rw [← FiniteField.PowerSeries.expand_card, coeff_expand]
  rw [ZMod.card] at h
  rw [h]
  simp only [Nat.dvd_iff_mod_eq_zero]

lemma U_eq : U = X + X * U ^ 2 := by
  classical
  ext n
  rw [map_add, coeff_X]
  rcases n with _ | j
  · simp [coeff_U, not_mersenne_zero]
  · rw [coeff_succ_X_mul, coeff_U_sq, coeff_U]
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i := ⟨j / 2, by omega⟩
      rw [mersenne_double_add_one, coeff_U, ite_eq_left h, Nat.mul_div_cancel_left i two_pos]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [not_mersenne_zero]
      · simp [show i ≠ 0 by omega]
    · have hne : ¬ Mersenne (j + 1) := fun hm => by have := hm.mod_two; omega
      rw [ite_eq_right hne, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]

lemma U_eq' : U = X * (1 + U) ^ 2 := by
  linear_combination U_eq - X * U * two_eq_zero

/-- The involution `μ(u) = u/(1+u)` over `𝔽₂`. -/
noncomputable def μ : (ZMod 2)⟦X⟧ := X * (1 + X)⁻¹

lemma cc_μ : constantCoeff μ = 0 := by simp [μ]

lemma μ_mul : μ * (1 + X) = X := by
  rw [μ, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]

lemma subst_μ_mul {g : (ZMod 2)⟦X⟧} (hg : constantCoeff g = 0) :
    (μ.subst g : (ZMod 2)⟦X⟧) * (1 + g) = g := by
  have h := congrArg (substAlgHom (R := ZMod 2) (hs hg)) μ_mul
  simp only [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom] at h
  exact h

lemma μ_μ : (μ.subst μ : (ZMod 2)⟦X⟧) = X := by
  have h1 := subst_μ_mul cc_μ
  linear_combination (-(1 + X)) * h1 + (μ.subst μ - 1) * μ_mul +
    ((μ.subst μ : (ZMod 2)⟦X⟧) + μ.subst μ * X - X) * two_eq_zero

lemma cc_w : constantCoeff (μ.subst U : (ZMod 2)⟦X⟧) = 0 := by rw [cc_subst cc_U, cc_μ]

/-- `w = μ(U)` satisfies `w + w² = x`. -/
lemma w_phi : (μ.subst U : (ZMod 2)⟦X⟧) + (μ.subst U) ^ 2 = X := by
  have hw := subst_μ_mul cc_U
  have key : ((μ.subst U : (ZMod 2)⟦X⟧) + (μ.subst U) ^ 2 - X) * (1 + U) ^ 2 = 0 := by
    linear_combination ((1 + U) + ((μ.subst U : (ZMod 2)⟦X⟧) * (1 + U) + U)) * hw + U_eq' +
      U ^ 2 * two_eq_zero
  have hne : (1 + U) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg constantCoeff h
    simp [cc_U] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)

lemma U_subst : (U.subst (U + U ^ 2) : (ZMod 2)⟦X⟧) = cat (ZMod 2) := by
  have s1 : ((X + X ^ 2 : (ZMod 2)⟦X⟧).subst (μ.subst U) : (ZMod 2)⟦X⟧) = X := by
    rw [phi_subst cc_w]; exact w_phi
  have s2 := left_inv cc_phi unit_phi cc_w s1
  have s3 : (μ.subst (μ.subst U : (ZMod 2)⟦X⟧) : (ZMod 2)⟦X⟧) = U := by
    rw [← subst_assoc cc_μ cc_U, μ_μ, subst_X (hs cc_U)]
  have hφμ : constantCoeff ((X + X ^ 2 : (ZMod 2)⟦X⟧).subst μ : (ZMod 2)⟦X⟧) = 0 := by
    rw [cc_subst cc_μ, cc_phi]
  have t1 : (U.subst ((X + X ^ 2 : (ZMod 2)⟦X⟧).subst μ) : (ZMod 2)⟦X⟧) = X := by
    conv_lhs => rw [← s3]
    rw [subst_assoc cc_w hφμ, ← subst_assoc cc_phi cc_μ, s2, subst_X (hs cc_μ), μ_μ]
  have t2 : U + U ^ 2 =
      (PowerSeries.subst (μ.subst U) ((X + X ^ 2 : (ZMod 2)⟦X⟧).subst μ) : (ZMod 2)⟦X⟧) := by
    rw [subst_assoc cc_μ cc_w, s3, phi_subst cc_U]
  have hcat : ((X + X ^ 2 : (ZMod 2)⟦X⟧).subst (cat (ZMod 2)) : (ZMod 2)⟦X⟧) = X := by
    rw [phi_subst cc_cat]
    linear_combination cat_sub_sq (R := ZMod 2) + cat (ZMod 2) ^ 2 * two_eq_zero
  rw [t2, ← subst_assoc hφμ cc_w, t1, subst_X (hs cc_w)]
  exact right_inv_unique cc_phi unit_phi cc_w cc_cat s1 hcat

lemma oddPart_U : oddPart U = U := by
  classical
  ext i
  rw [coeff_oddPart, coeff_U]
  by_cases h1 : i = 1
  · subst h1
    simp [show Mersenne 1 from ⟨1, le_rfl, rfl⟩]
  · by_cases h2 : i % 2 = 1 ∧ 3 ≤ i
    · simp [h1, h2]
    · have hM : ¬ Mersenne i := fun hm => h2 ⟨hm.mod_two, by have := hm.mod_two; omega⟩
      simp [h1, h2, hM]

lemma U_eq_map : U = map (Int.castRingHom (ZMod 2)) κ :=
  TB_causal.eq_map_fix (Int.castRingHom (ZMod 2)) TB_causal (map_TB _)
    (TB_eq_of oddPart_U U_subst)

end F2

section Statement

/-- If `G(φ(G)) = c`, the linear coefficient of `G` is `1`: `-1` fails in degree `2`. -/
lemma coeff_one_eq_one {G : ℚ⟦X⟧} (hG0 : constantCoeff G = 0) (hEG : E G = cat ℚ) :
    coeff 1 G = 1 := by
  have e1 := congrArg (coeff 1) hEG
  have e2 := congrArg (coeff 2) hEG
  rw [E, coeff_one_subst (cc_add_sq hG0), coeff_one_cat, map_add, coeff_one_sq hG0,
    add_zero] at e1
  rw [E, coeff_two_subst (cc_add_sq hG0), coeff_two_cat, map_add, map_add, coeff_one_sq hG0,
    add_zero, coeff_two_sq hG0] at e2
  have : (coeff 1 G - 1) * (coeff 1 G + 1) = 0 := by linear_combination e1
  rcases mul_eq_zero.mp this with h | h
  · linear_combination h
  · have hg : coeff 1 G = -1 := by linear_combination h
    rw [hg] at e2
    exfalso
    linarith

lemma isSolution_A₀ : IsSolution (G₀ + G₀ ^ 2) := by
  obtain ⟨h0, -, hE⟩ := G₀_spec
  have hA0 := cc_add_sq h0
  refine ⟨hA0, ?_⟩
  have hAA : ((G₀ + G₀ ^ 2).subst (G₀ + G₀ ^ 2) : ℚ⟦X⟧) = cat ℚ + cat ℚ ^ 2 := by
    rw [add_sq_subst hA0]
    change E G₀ + E G₀ ^ 2 = _
    rw [hE]
  rw [← subst_assoc hA0 cc_psi, hAA, add_sq_subst cc_psi, cat_left_inv]

lemma eq_of_isSolution {A : ℚ⟦X⟧} (hA : IsSolution A) : A = G₀ + G₀ ^ 2 := by
  obtain ⟨hA0, hAeq⟩ := hA
  -- `A(A(x)) = φ(c(x))`.
  have hAA : (A.subst A : ℚ⟦X⟧) = cat ℚ + cat ℚ ^ 2 := by
    have h := congrArg (fun F : ℚ⟦X⟧ => (F.subst (cat ℚ) : ℚ⟦X⟧)) hAeq
    rw [← subst_assoc hA0 cc_psi, subst_assoc cc_psi cc_cat, cat_right_inv, X_subst,
      phi_subst cc_cat] at h
    exact h
  -- `G = φ⁻¹(A)` satisfies `A = φ(G)` and `G(φ(G)) = c`.
  have hG0 : constantCoeff ((phiInv ℚ).subst A : ℚ⟦X⟧) = 0 := by
    rw [cc_subst hA0, cc_phiInv]
  have hAG : A = ((phiInv ℚ).subst A : ℚ⟦X⟧) + ((phiInv ℚ).subst A : ℚ⟦X⟧) ^ 2 := by
    rw [← phi_subst hG0, ← subst_assoc cc_phiInv hA0, phi_phiInv, subst_X (hs hA0)]
  have hEG : E ((phiInv ℚ).subst A) = cat ℚ := by
    rw [E, ← hAG, subst_assoc hA0 hA0, hAA, ← phi_subst cc_cat, ← subst_assoc cc_phi cc_cat,
      phiInv_phi, subst_X (hs cc_cat)]
  rw [hAG, eq_G₀ hG0 (coeff_one_eq_one hG0 hEG) hEG]

/-- OEIS A318008: exactly one $A(x) \in \mathbb{Q}[[x]]$ with $A(0) = 0$ satisfies
$A(A(x - x^2)) = x + x^2$. -/
theorem exists_unique_solution : ∃! A : ℚ⟦X⟧, IsSolution A :=
  ⟨G₀ + G₀ ^ 2, isSolution_A₀, fun _ hA => eq_of_isSolution hA⟩

lemma mersenne_half_iff {n : ℕ} (h : n % 2 = 0) :
    Mersenne (n / 2) ↔ ∃ k ≥ 1, n = 2 ^ k - 1 ∨ n = 2 ^ (k + 1) - 2 := by
  constructor
  · rintro ⟨k, hk, hk'⟩
    refine ⟨k, hk, Or.inr ?_⟩
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := k)
    omega
  · rintro ⟨k, hk, h1 | h1⟩
    · exfalso
      have := (show Mersenne n from ⟨k, hk, h1⟩).mod_two
      omega
    · refine ⟨k, hk, ?_⟩
      rw [pow_succ] at h1
      omega

lemma mersenne_iff_of_odd {n : ℕ} (h : n % 2 = 1) :
    Mersenne n ↔ ∃ k ≥ 1, n = 2 ^ k - 1 ∨ n = 2 ^ (k + 1) - 2 := by
  constructor
  · rintro ⟨k, hk, hk'⟩
    exact ⟨k, hk, Or.inl hk'⟩
  · rintro ⟨k, hk, h1 | h1⟩
    · exact ⟨k, hk, h1⟩
    · exfalso
      rw [pow_succ] at h1
      have := Nat.one_le_two_pow (n := k)
      omega

lemma ite_eq_one_iff {p : Prop} [Decidable p] : ((if p then 1 else 0 : ZMod 2) = 1) ↔ p := by
  split_ifs with h <;> simp [h]

lemma coeff_U_add_sq (n : ℕ) :
    coeff n (U + U ^ 2) = 1 ↔ ∃ k ≥ 1, n = 2 ^ k - 1 ∨ n = 2 ^ (k + 1) - 2 := by
  classical
  rw [map_add, coeff_U_sq, coeff_U, coeff_U]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hM : ¬ Mersenne n := fun hm => by have := hm.mod_two; omega
    rw [ite_eq_right hM, zero_add, ite_eq_left h, ite_eq_one_iff, mersenne_half_iff h]
  · rw [ite_eq_right (by omega : ¬ n % 2 = 0), add_zero, ite_eq_one_iff, mersenne_iff_of_odd h]

/-- Hanna's parity conjecture for OEIS A318008: every $a(n) = [x^n] A(x)$ is an integer, and
$a(n)$ is odd if and only if $n = 2^k - 1$ or $n = 2^{k+1} - 2$ for some $k \ge 1$. -/
theorem parity_conjecture (A : ℚ⟦X⟧) (hA : IsSolution A) (n : ℕ) :
    ∃ a : ℤ, coeff n A = a ∧ (Odd a ↔ ∃ k ≥ 1, n = 2 ^ k - 1 ∨ n = 2 ^ (k + 1) - 2) := by
  refine ⟨coeff n (κ + κ ^ 2), ?_, ?_⟩
  · rw [eq_of_isSolution hA, G₀_eq_map, ← map_pow, ← map_add, coeff_map, eq_intCast]
  · rw [← ZMod.intCast_eq_one_iff_odd, ← coeff_U_add_sq, U_eq_map, ← map_pow, ← map_add,
      coeff_map, eq_intCast]

/-! ### Sanity checks: $a(1) = a(2) = 1$, as in the data of the entry. -/

example (A : ℚ⟦X⟧) (hA : IsSolution A) : coeff 1 A = 1 := by
  obtain ⟨h0, h1, -⟩ := G₀_spec
  rw [eq_of_isSolution hA, map_add, h1, coeff_one_sq h0, add_zero]

example (A : ℚ⟦X⟧) (hA : IsSolution A) : coeff 2 A = 1 := by
  obtain ⟨h0, h1, -⟩ := G₀_spec
  rw [eq_of_isSolution hA, map_add, G₀_odd (by norm_num), coeff_two_sq h0, h1]
  norm_num

end Statement

section A277292

/-- The defining equation $\mathrm{Rev}(G + G^2) = G - G^2$ of OEIS A277292, for $G$ with
$G(0) = 0$: the series $G - G^2$ is the compositional inverse of $G + G^2$. -/
def IsSolution277292 (G : ℚ⟦X⟧) : Prop :=
  constantCoeff G = 0 ∧ (G + G ^ 2).subst (G - G ^ 2) = X

lemma eq_G₀_of_isSolution277292 {G : ℚ⟦X⟧} (hG : IsSolution277292 G) : G = G₀ := by
  obtain ⟨h0, hrev⟩ := hG
  have hy0 := cc_add_sq h0
  have hL0 : constantCoeff (G - G ^ 2) = 0 := by simp [h0]
  have h1 := congrArg (coeff 1) hrev
  rw [coeff_one_subst hL0, map_add, map_sub, coeff_one_sq h0, add_zero, sub_zero, coeff_one_X]
    at h1
  have hu : IsUnit (coeff 1 (G + G ^ 2)) := by
    rw [map_add, coeff_one_sq h0, add_zero]
    exact isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  have s := left_inv hy0 hu hL0 hrev
  have hE : E G = cat ℚ := right_inv_unique cc_psi unit_psi (cc_E h0) cc_cat
    (by rw [psi_subst (cc_E h0)]; rw [sub_sq_subst hy0] at s; exact s) cat_right_inv
  exact eq_G₀ h0 (coeff_one_eq_one h0 hE) hE

/-- OEIS A277292: exactly one $G(x) \in \mathbb{Q}[[x]]$ with $G(0) = 0$ satisfies
$\mathrm{Rev}(G + G^2) = G - G^2$. -/
theorem a277292_existsUnique : ∃! G : ℚ⟦X⟧, IsSolution277292 G :=
  ⟨G₀, ⟨G₀_spec.1, G₀_rev⟩, fun _ hG => eq_G₀_of_isSolution277292 hG⟩

/-- The series $G$ of OEIS A277292 is odd, as the formula $G(x) = \sum_{n \ge 1} b(n) x^{2n-1}$
of the entry states. -/
theorem a277292_odd (G : ℚ⟦X⟧) (hG : IsSolution277292 G) (n : ℕ) : coeff (2 * n) G = 0 := by
  rw [eq_G₀_of_isSolution277292 hG]
  exact G₀_odd (by omega)

lemma coeff_G₀_sq_odd {n : ℕ} (hn : n % 2 = 1) : coeff n (G₀ ^ 2) = 0 := by
  have hneg : (G₀.subst (-X : ℚ⟦X⟧) : ℚ⟦X⟧) = -G₀ := by
    ext m
    rw [coeff_subst_negX, map_neg]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [G₀_odd h]
      simp
    · rw [Odd.neg_one_pow (Nat.odd_iff.mpr h)]
      ring
  have h := congrArg (fun F : ℚ⟦X⟧ => coeff n (F ^ 2)) hneg
  rw [← subst_pow (hs cc_negX), coeff_subst_negX, Odd.neg_one_pow (Nat.odd_iff.mpr hn),
    neg_sq] at h
  linarith

/-- The comment $a(2n - 1) = \mathrm{A277292}(n)$ of OEIS A318008: the odd coefficients of $A$
are those of $G$. -/
theorem a318008_odd_bisection (A G : ℚ⟦X⟧) (hA : IsSolution A) (hG : IsSolution277292 G)
    (n : ℕ) (hn : 1 ≤ n) : coeff (2 * n - 1) A = coeff (2 * n - 1) G := by
  rw [eq_of_isSolution hA, eq_G₀_of_isSolution277292 hG, map_add,
    coeff_G₀_sq_odd (by omega), add_zero]

lemma mersenne_two_mul_sub_one {n : ℕ} (hn : 1 ≤ n) : Mersenne (2 * n - 1) ↔ ∃ j, n = 2 ^ j := by
  constructor
  · rintro ⟨k, hk, h⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ] at h
    exact ⟨j, by omega⟩
  · rintro ⟨j, rfl⟩
    refine ⟨j + 1, by omega, ?_⟩
    rw [pow_succ]
    omega

/-- OEIS A277292 is integral, and $\mathrm{A277292}(n) = [x^{2n-1}] G(x)$ is odd if and only if
$n$ is a power of $2$. -/
theorem a277292_parity (G : ℚ⟦X⟧) (hG : IsSolution277292 G) (n : ℕ) (hn : 1 ≤ n) :
    ∃ b : ℤ, coeff (2 * n - 1) G = b ∧ (Odd b ↔ ∃ j, n = 2 ^ j) := by
  classical
  refine ⟨coeff (2 * n - 1) κ, ?_, ?_⟩
  · rw [eq_G₀_of_isSolution277292 hG, G₀_eq_map, coeff_map, eq_intCast]
  · have h : ((coeff (2 * n - 1) κ : ℤ) : ZMod 2) = coeff (2 * n - 1) U := by
      rw [U_eq_map, coeff_map, eq_intCast]
    rw [← ZMod.intCast_eq_one_iff_odd, h, coeff_U, ite_eq_one_iff, mersenne_two_mul_sub_one hn]

end A277292

end OeisA318008

end
