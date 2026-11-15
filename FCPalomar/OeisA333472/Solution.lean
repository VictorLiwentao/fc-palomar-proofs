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
# OEIS A333472: Bala's quadratic supercongruences for $[x^{rn}]\, c(x/(1+x))^{sn}$

Let $c(x) = \sum_{n \ge 0} C_n x^n$ be the Catalan generating function, $F(x) = c(x/(1+x))$
and $a(r,s;n) = [x^{rn}]\, F(x)^{sn}$. This file proves `OeisA333472.a_tower`: for every prime
$p \ge 5$, every $r \ge 1$, every $s \in \mathbb{Z}$ and all $n, k \ge 1$,
$$a(r,s;np^k) \equiv a(r,s;np^{k-1}) \pmod{p^{2k}},$$
as conjectured by Peter Bala on A333472. The case $r = s = 1$ is `a333472_tower`. It suffices
to show $|a(r,s;pM) - a(r,s;M)|_p \le |pM|_p^2$ for $M \ge 1$ (`main_estimate`) and to take
$M = np^{k-1}$. Write $\theta = W\, d/dW$ (`theta`), $\Phi = 1 + W + W^2$,
$Q = (1 - W^2)/\Phi$ and $G = (1+W)^s \Phi^r$.

1. **Quadratic equation** (`F_quad`). Mathlib's $c = 1 + xc^2$ and the substitution
   $x \mapsto x/(1+x)$ give $(1+x)F = 1 + x + xF^2$.
2. **Lagrange inversion** (`F_subst`, `lagrange`, `a_eq_coeff_Qz`). Put $f(W) = W/\Phi(W)$.
   Both $F(f(W))$ and $1 + W$ solve $(1+f)u = 1 + f + fu^2$, whose solution is unique, so
   $F(f(W)) = 1 + W$. The residue identity $[W^{m+1}](1-W^2)\Phi^m = 0$ (`residue`) follows from
   $(m+1)(1 - W^2)\Phi^m = (m+1)\Phi^{m+1} - \theta\Phi^{m+1}$. Splitting $P$ into its
   truncation and a multiple of $x^{m+2}$ then gives
   $[x^{m+1}]P = [W^{m+1}]\, P(f(W))\,(1-W^2)\Phi^m$ for every power series $P$. Applied to
   $P = F^{sN}$ this is $a(r,s;N) = [W^{rN}]\, Q\, G^N$ for $N \ge 1$ and every $s \in \mathbb{Z}$.
3. **Exponential expansion** (`expansion`). Over $\mathbb{Q}$, $\Lambda = \theta G/G =
   s\,W/(1+W) + r(1 - Q)$ (`hasLD_Gq`) has integer coefficients with $\lambda_{pn} = \lambda_n$,
   because $p$ is odd and $q_{pn} = q_n$ for $p \ne 3$ (`coeff_Λ_mul`). So
   $Z = \sum_{p \nmid n} \lambda_n W^n/n$ is $p$-integral and $\theta Z = \Lambda - \Lambda(W^p)$
   (`theta_Zs`). The unit $E = G^{pM}/G(W^p)^M$ satisfies $\theta E = pM\, \theta Z \cdot E$,
   so a uniqueness argument for $\theta D = KD + R$ (`X_pow_dvd_of_theta`) gives
   $E \equiv \sum_{t \le T} (pM)^t Z^t/t!$ modulo $W^{T+1}$ (`X_pow_dvd_sub_expTrunc`). The
   extraction $[W^{pN}]\, A(W^p) B = \sum_{i+j=N} [W^i]A\, [W^{pj}]B$
   (`coeff_p_mul_expand_mul`) then gives $a(pM) = \sum_t \frac{(pM)^t}{t!} S_t$ with
   $S_t = \sum_{i+j=rM} [W^i]G^M\, [W^{pj}](QZ^t)$, and $S_0 = a(M)$.
4. **Terms $t \ge 2$** (`norm_pow_div_factorial`). Legendre's formula gives
   $v_p(t!) \le t - 2$ for $p \ge 5$, so $|(pM)^t/t!|_p \le |pM|_p^2$, and $|S_t|_p \le 1$.
5. **Term $t = 1$** (`norm_Sx_one`). From $\theta G^M = M \Lambda G^M$,
   $|i\, [W^i]G^M|_p \le |M|_p$ (`norm_coeff_Gq_pow`). If $|[W^{pj}](QZ)|_p \le |p|_p |j|_p$,
   each term of $S_1$ is at most $|p|_p |M|_p$: use $|j|_p \le |M|_p$, or else $|i|_p = |j|_p$
   for $i = rM - j$. Write $Z = sV_1 + rV_3$ with $V_1 = \sum_{p \nmid n} (-1)^{n+1} W^n/n$.
   - **Lemma B** (`coeff_Qq_V₃`). $Q = Q(W^p) - \theta V_3$ and $V_3\, \theta V_3 =
     \theta(V_3^2)/2$, so $[W^{pj}](QV_3) = -\frac{pj}{2} [W^{pj}] V_3^2$.
   - **Lemma A** (`lemmaA`). $\Phi$ divides $W_1 = ((1+W)^p - 1 - W^p)/p$ in $\mathbb{Z}[W]$,
     because $1 + W \equiv -W^2$ and $W^3 \equiv 1$ modulo $\Phi$ (`phi_dvd_aux`). So
     $QW_1^{h+1}$ is a polynomial of degree at most $(h+1)(p-1)$ with no constant term
     (`exists_W_K`, `exists_series`). With $Y = W_1/(1+W^p)$ we have
     $\theta Y = (1 + pY)\, \theta V_1$, hence $V_1 \equiv \sum_{h < H} (-1)^h p^h Y^{h+1}/(h+1)$
     (`X_pow_dvd_V₁_sub_LH`). After the extraction only the indices $1 \le i \le h$ remain,
     with the factor $[W^{j-i}](1+W)^{-h-1} = \pm\binom{h+j-i}{h}$ and
     $j \mid h!\binom{h+j-i}{h}$ (`dvd_factorial_mul_choose`). With $v_p((h+1)!) \le h - 1$ this
     gives $|[W^{pj}](QV_1)|_p \le |p|_p |j|_p$.

The sign of $s$ is never used, so negative $s$ needs no separate case. The second form of
Lagrange inversion is in Gessel's survey; here it is proved directly for this $\Phi$. Writing
$G^p/G(W^p)$ as $\exp(pZ)$ with $p$-integral $Z$ is the Frobenius method of Dwork-type
congruences, as in the work of Schwarz, Vologodsky and Walcher on framing.

*References:*
- Peter Bala, [A333472](https://oeis.org/A333472), March 23, 2020.
- I. M. Gessel, *Lagrange inversion*, J. Combin. Theory Ser. A 144 (2016).
- A. Schwarz, V. Vologodsky and J. Walcher, *Framing the di-logarithm (over $\mathbb{Z}$)*,
  [arXiv:1306.4298](https://arxiv.org/abs/1306.4298), 2013.
- A. Schwarz, V. Vologodsky and J. Walcher, *Integrality of framing and geometric origin of
  2-functions*, [arXiv:1702.07135](https://arxiv.org/abs/1702.07135), 2017.
-/

@[expose] public section

namespace OeisA333472

open PowerSeries

/-- The Catalan generating function $c(x) = \sum_{n \ge 0} C_n x^n$ over $\mathbb{Z}$, where
$C_n$ = `catalan n` are the Catalan numbers (OEIS A000108). -/
noncomputable def c : PowerSeries ℤ := PowerSeries.mk fun n => (catalan n : ℤ)

/-- $F(x) = c(x/(1+x))$, where $x/(1+x)$ is $x$ times the inverse `invOfUnit (1 + X) 1` of
$1 + x$. -/
noncomputable def F : PowerSeries ℤ := c.subst (X * invOfUnit (1 + X) 1 : PowerSeries ℤ)

/-- The integer power $F(x)^m$ for $m \in \mathbb{Z}$. For $m < 0$ it is $(F^{-1})^{-m}$, where
$F^{-1}$ = `invOfUnit F 1` is the inverse of $F$, as $F(0) = 1$. -/
noncomputable def Fzpow (m : ℤ) : PowerSeries ℤ :=
  if 0 ≤ m then F ^ m.toNat else invOfUnit F 1 ^ m.natAbs

/-- Bala's $a(r,s;n) = [x^{rn}]\, F(x)^{sn}$. -/
noncomputable def a (r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (Fzpow (s * n))

/-- OEIS A333472: $a(n) = [x^n]\, c(x/(1+x))^n$. -/
noncomputable def A333472 (n : ℕ) : ℤ := coeff n (F ^ n)

end OeisA333472

namespace OeisA333472

open PowerSeries Finset

/-! ## The Euler operator -/

section

section Theta

variable {R : Type*} [CommRing R]

/-- The Euler operator $\theta = X \frac{d}{dX}$, coefficientwise $[X^n]\,\theta A = n\,[X^n] A$. -/
noncomputable def theta (A : R⟦X⟧) : R⟦X⟧ := mk fun n => (n : R) * coeff n A

@[simp] theorem coeff_theta (A : R⟦X⟧) (n : ℕ) : coeff n (theta A) = n * coeff n A := by
  simp [theta]

theorem theta_add (A B : R⟦X⟧) : theta (A + B) = theta A + theta B := by
  ext n; simp [mul_add]

theorem theta_sub (A B : R⟦X⟧) : theta (A - B) = theta A - theta B := by
  ext n; simp [mul_sub]

theorem theta_smul (c : R) (A : R⟦X⟧) : theta (c • A) = c • theta A := by
  ext n; simp; ring

theorem theta_sum {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧) :
    theta (∑ i ∈ s, f i) = ∑ i ∈ s, theta (f i) := by
  ext n; simp [Finset.mul_sum]

theorem theta_C (c : R) : theta (C c) = 0 := by
  ext n; simp only [coeff_theta, coeff_C, map_zero]; split_ifs with h <;> simp [h]

theorem theta_one : theta (1 : R⟦X⟧) = 0 := by
  simpa using theta_C (R := R) 1

theorem theta_X : theta (X : R⟦X⟧) = X := by
  ext n; simp only [coeff_theta, coeff_X]; split_ifs with h <;> simp [h]

theorem theta_mul (A B : R⟦X⟧) : theta (A * B) = theta A * B + A * theta B := by
  ext n
  simp only [coeff_theta, map_add, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx]; push_cast; ring

theorem theta_pow (A : R⟦X⟧) (n : ℕ) :
    theta (A ^ (n + 1)) = ((n + 1 : ℕ) : R⟦X⟧) * A ^ n * theta A := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, theta_mul, ih]; push_cast; ring

theorem X_dvd_theta (A : R⟦X⟧) : X ∣ theta A := by
  rw [← pow_one X, X_pow_dvd_iff]
  intro m hm
  obtain rfl : m = 0 := by omega
  simp

theorem coeff_mul_eq_of_X_pow_dvd {n : ℕ} (A : R⟦X⟧) {B B' : R⟦X⟧}
    (h : X ^ (n + 1) ∣ B - B') : coeff n (A * B) = coeff n (A * B') := by
  have h2 : X ^ (n + 1) ∣ A * B - A * B' := by
    rw [← mul_sub]; exact Dvd.dvd.mul_left h A
  have := (X_pow_dvd_iff.mp h2) n (by omega)
  rwa [map_sub, sub_eq_zero] at this

theorem coeff_eq_zero_of_X_pow_dvd {n k : ℕ} {A : R⟦X⟧} (h : X ^ k ∣ A) (hn : n < k) :
    coeff n A = 0 :=
  X_pow_dvd_iff.mp h n hn

theorem X_pow_succ_dvd_of {n : ℕ} {A : R⟦X⟧} (h : X ^ n ∣ A) (h0 : coeff n A = 0) :
    X ^ (n + 1) ∣ A := by
  rw [X_pow_dvd_iff] at h ⊢
  intro m hm
  rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
  · exact h m hm
  · exact h0

end Theta

/-- Uniqueness for $\theta D = K D + R$ modulo $X^{T+1}$: if $X \mid K$, $X^{T+1} \mid R$ and
$D(0) = 0$, then $X^{T+1} \mid D$. -/
theorem X_pow_dvd_of_theta {D K Rr : ℚ⟦X⟧} {T : ℕ} (hD : theta D = K * D + Rr) (hK : X ∣ K)
    (hR : X ^ (T + 1) ∣ Rr) (h0 : constantCoeff D = 0) : X ^ (T + 1) ∣ D := by
  suffices ∀ n, n ≤ T + 1 → X ^ n ∣ D from this _ le_rfl
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have IH := ih (by omega)
    refine X_pow_succ_dvd_of IH ?_
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa using h0
    · have h1 : X ^ (n + 1) ∣ K * D := by
        rw [pow_succ']; exact mul_dvd_mul hK IH
      have h2 : X ^ (n + 1) ∣ Rr := (pow_dvd_pow X hn).trans hR
      have h3 : X ^ (n + 1) ∣ theta D := hD ▸ dvd_add h1 h2
      have h4 := coeff_eq_zero_of_X_pow_dvd h3 (Nat.lt_succ_self n)
      rw [coeff_theta] at h4
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h (by exact_mod_cast hpos.ne')
      · exact h

end

/-! ## The quadratic equation and Lagrange inversion -/

section

noncomputable section

/-! ## The quadratic equation for `F` -/

/-- $t = x/(1+x)$. -/
abbrev tX : ℤ⟦X⟧ := X * invOfUnit (1 + X) 1

theorem one_add_X_mul_inv : (1 + X : ℤ⟦X⟧) * invOfUnit (1 + X) 1 = 1 :=
  mul_invOfUnit _ _ (by simp)

theorem hasSubst_tX : HasSubst tX := HasSubst.of_constantCoeff_zero' (by simp)

theorem c_eq : c = 1 + X * c ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  have hc : PowerSeries.map (Nat.castRingHom ℤ) catalanSeries = c := by ext n; simp [c]
  simp only [map_add, map_mul, map_pow, map_X, map_one, hc] at h
  linear_combination -h

theorem F_eq : F = 1 + tX * F ^ 2 := by
  have h := congrArg (substAlgHom hasSubst_tX) c_eq
  rw [map_add, map_one, map_mul, map_pow, substAlgHom_X] at h
  simpa [F, coe_substAlgHom] using h

theorem F_quad : (1 + X) * F = 1 + X + X * F ^ 2 := by
  have h := F_eq
  have h2 : (1 + X) * tX = X := by
    rw [tX, mul_left_comm, one_add_X_mul_inv, mul_one]
  calc (1 + X) * F = (1 + X) * (1 + tX * F ^ 2) := by rw [← h]
    _ = 1 + X + ((1 + X) * tX) * F ^ 2 := by ring
    _ = 1 + X + X * F ^ 2 := by rw [h2]

theorem constantCoeff_F : constantCoeff F = 1 := by
  rw [F_eq]; simp

/-- `F` as a unit. -/
def Fu : ℤ⟦X⟧ˣ :=
  ⟨F, invOfUnit F 1, mul_invOfUnit F 1 (by simp [constantCoeff_F]),
    invOfUnit_mul F 1 (by simp [constantCoeff_F])⟩

theorem Fzpow_eq (m : ℤ) : Fzpow m = ((Fu ^ m : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  unfold Fzpow
  split_ifs with h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [Fu]
  · have hk : m = -((m.natAbs : ℕ) : ℤ) := by omega
    rw [hk, zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
    simp [Fu]

/-! ## The Lagrange variable -/

/-- $\Phi(W) = 1 + W + W^2$. -/
abbrev Φ : ℤ⟦X⟧ := 1 + X + X ^ 2

theorem constantCoeff_Φ : constantCoeff Φ = 1 := by simp

/-- $\Phi$ as a unit. -/
def Φu : ℤ⟦X⟧ˣ :=
  ⟨Φ, invOfUnit Φ 1, mul_invOfUnit Φ 1 (by simp), invOfUnit_mul Φ 1 (by simp)⟩

/-- $1 + W$ as a unit. -/
def onePlusXu : ℤ⟦X⟧ˣ :=
  ⟨1 + X, invOfUnit (1 + X) 1, mul_invOfUnit _ 1 (by simp), invOfUnit_mul _ 1 (by simp)⟩

/-- $f(W) = W / \Phi(W)$, the compositional inverse of $W(x)$. -/
abbrev fX : ℤ⟦X⟧ := X * invOfUnit Φ 1

theorem hasSubst_fX : HasSubst fX := HasSubst.of_constantCoeff_zero' (by simp)

theorem fX_mul_Φ : fX * Φ = X := by
  rw [fX, mul_assoc, invOfUnit_mul Φ 1 (by simp), mul_one]

theorem F_subst : substAlgHom hasSubst_fX F = 1 + X := by
  set u := substAlgHom hasSubst_fX F with hu
  have h := congrArg (substAlgHom hasSubst_fX) F_quad
  simp only [map_add, map_one, map_mul, map_pow, substAlgHom_X, ← hu] at h
  have hv : (1 + fX) * (1 + X) = 1 + fX + fX * (1 + X) ^ 2 := by
    linear_combination (-1 : ℤ⟦X⟧) * fX_mul_Φ
  have hprod : (u - (1 + X)) * (1 + fX - fX * (u + (1 + X))) = 0 := by
    linear_combination h - hv
  have hne : (1 + fX - fX * (u + (1 + X))) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp at this
  have := (mul_eq_zero.mp hprod).resolve_right hne
  exact sub_eq_zero.mp this

/-- Substituting $x = f(W)$ sends `Fu` to $1 + W$. -/
theorem units_map_Fu :
    Units.map (substAlgHom hasSubst_fX).toRingHom.toMonoidHom Fu = onePlusXu := by
  apply Units.ext
  exact F_subst

theorem subst_Fzpow (m : ℤ) :
    substAlgHom hasSubst_fX (Fzpow m) = ((onePlusXu ^ m : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  rw [Fzpow_eq, ← units_map_Fu, ← map_zpow]
  rfl

/-! ## The residue identity and the Lagrange formula -/

theorem theta_Φ : theta Φ = X + 2 * X ^ 2 := by
  rw [theta_add, theta_add, theta_one, theta_X, show (X : ℤ⟦X⟧) ^ 2 = X ^ (1 + 1) by ring,
    theta_pow, theta_X]
  push_cast; ring

/-- $[W^{k+1}]\,(1 - W^2)\,\Phi^k = 0$. -/
theorem residue (k : ℕ) : coeff (k + 1) ((1 - X ^ 2) * Φ ^ k) = 0 := by
  have h1 : (1 - X ^ 2) * Φ ^ k = Φ ^ (k + 1) - Φ ^ k * theta Φ := by
    rw [theta_Φ]; ring
  have h2 := theta_pow Φ k
  have h3 : ((k + 1 : ℕ) : ℤ⟦X⟧) * ((1 - X ^ 2) * Φ ^ k) =
      ((k + 1 : ℕ) : ℤ⟦X⟧) * Φ ^ (k + 1) - theta (Φ ^ (k + 1)) := by
    rw [h2, h1]; ring
  have h4 := congrArg (coeff (k + 1)) h3
  rw [map_sub, coeff_theta, ← map_natCast (C (R := ℤ)), coeff_C_mul, coeff_C_mul] at h4
  simp only [sub_self] at h4
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by positivity)
  · exact h

theorem Φinv_pow_mul_Φ_pow {k m : ℕ} (h : k ≤ m) :
    invOfUnit Φ 1 ^ k * Φ ^ m = Φ ^ (m - k) := by
  have : ((Φu⁻¹ ^ k * Φu ^ m : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = ((Φu ^ (m - k) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
    congr 1
    rw [pow_sub _ h, inv_pow, mul_comm]
  simpa [Φu] using this

/-- **Lagrange inversion** for $x\,\Phi(W) = W$: for every power series $P$,
$[x^{m+1}]\,P = [W^{m+1}]\,P(f(W))\,(1 - W^2)\,\Phi(W)^m$. -/
theorem lagrange (m : ℕ) (P : ℤ⟦X⟧) :
    coeff (m + 1) P = coeff (m + 1) (substAlgHom hasSubst_fX P * ((1 - X ^ 2) * Φ ^ m)) := by
  set n := m + 1 with hn
  set K : ℤ⟦X⟧ := (1 - X ^ 2) * Φ ^ m
  set S : ℤ⟦X⟧ := ∑ k ∈ range (n + 1), coeff k P • X ^ k
  have hcS : ∀ i, i < n + 1 → coeff i S = coeff i P := by
    intro i hi
    simp only [S, map_sum, map_zsmul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [hi]
  obtain ⟨R, hR⟩ : X ^ (n + 1) ∣ P - S := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [map_sub, hcS i hi, sub_self]
  have hP : P = S + X ^ (n + 1) * R := by rw [← hR]; ring
  set φ : ℤ⟦X⟧ →ₐ[ℤ] ℤ⟦X⟧ := substAlgHom hasSubst_fX
  have hφP : φ P = ∑ k ∈ range (n + 1), coeff k P • fX ^ k + fX ^ (n + 1) * φ R := by
    conv_lhs => rw [hP]
    simp [S, φ, map_sum, map_pow, substAlgHom_X]
  have htail : coeff n (fX ^ (n + 1) * φ R * K) = 0 := by
    apply coeff_eq_zero_of_X_pow_dvd _ (Nat.lt_succ_self n)
    rw [fX, mul_pow, mul_assoc, mul_assoc]
    exact Dvd.intro _ rfl
  have hterm : ∀ k ∈ range (n + 1), coeff n (fX ^ k * K) = if k = n then 1 else 0 := by
    intro k hk
    rw [mem_range] at hk
    have e1 : fX ^ k * K = X ^ k * ((1 - X ^ 2) * (invOfUnit Φ 1 ^ k * Φ ^ m)) := by
      simp only [K, fX]; ring
    rw [e1]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [Φinv_pow_mul_Φ_pow (by omega), ite_eq_right (by omega)]
      obtain ⟨j, hj⟩ : ∃ j, m - k = j := ⟨_, rfl⟩
      rw [hj, coeff_X_pow_mul', ite_eq_left (by omega),
        show n - k = j + 1 by omega]
      exact residue j
    · rw [ite_eq_left rfl, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
        show invOfUnit Φ 1 ^ n * Φ ^ m = invOfUnit Φ 1 by
          rw [hn, pow_succ, mul_comm, ← mul_assoc, ← mul_pow, mul_invOfUnit Φ 1 (by simp),
            one_pow, one_mul]]
      simp
  rw [hφP, add_mul, map_add, htail, add_zero, Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, map_zsmul]
  rw [Finset.sum_congr rfl fun k hk => by rw [hterm k hk]]
  simp [hn]

end

end

/-! ## Cartier extraction, logarithmic derivatives and the truncated exponential -/

section

section Frob

variable (p : ℕ) (hp : p ≠ 0)

theorem theta_expand {R : Type*} [CommRing R] (A : R⟦X⟧) :
    theta (expand p hp A) = (p : R⟦X⟧) * expand p hp (theta A) := by
  ext n
  rw [← map_natCast (C (R := R)), coeff_C_mul]
  simp only [coeff_theta, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
    push_cast; ring
  · simp

/-- The Cartier extraction: $[X^{pN}]\,A(X^p)\,B = \sum_{i+j=N} [X^i]A\,[X^{pj}]B$. -/
theorem coeff_p_mul_expand_mul {R : Type*} [CommRing R] (A B : R⟦X⟧) (N : ℕ) :
    coeff (p * N) (expand p hp A * B) =
      ∑ x ∈ antidiagonal N, coeff x.1 A * coeff (p * x.2) B := by
  rw [coeff_mul]
  let e : ℕ × ℕ ↪ ℕ × ℕ := ⟨fun x => (p * x.1, p * x.2), fun x y h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h.1)
      (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h.2)⟩
  have hsub : (antidiagonal N).map e ⊆ antidiagonal (p * N) := by
    intro x hx
    simp only [Finset.mem_map, Finset.HasAntidiagonal.mem_antidiagonal] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    show p * y.1 + p * y.2 = p * N
    rw [← mul_add, hy]
  rw [← Finset.sum_subset hsub, Finset.sum_map]
  · refine Finset.sum_congr rfl fun x _ => ?_
    show coeff (p * x.1) (expand p hp A) * coeff (p * x.2) B = _
    rw [coeff_expand_mul]
  · intro x hx hnot
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hnd : ¬ p ∣ x.1 := by
      rintro ⟨a, ha⟩
      apply hnot
      rw [Finset.mem_map]
      have hb : x.2 = p * (N - a) := by
        rw [Nat.mul_sub]
        have : p * a ≤ p * N := by rw [← ha]; omega
        omega
      refine ⟨(a, N - a), ?_, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]
        have : p * a ≤ p * N := by rw [← ha]; omega
        have := Nat.le_of_mul_le_mul_left this (Nat.pos_of_ne_zero hp)
        simp only; omega
      · exact Prod.ext ha.symm hb.symm
    rw [coeff_expand_of_not_dvd p hp _ hnd, zero_mul]

/-- Logarithmic derivative: `θ u = L * u`. -/
def HasLD (u : ℚ⟦X⟧ˣ) (L : ℚ⟦X⟧) : Prop := theta (u : ℚ⟦X⟧) = L * u

theorem HasLD.mul {u v : ℚ⟦X⟧ˣ} {L M : ℚ⟦X⟧} (hu : HasLD u L) (hv : HasLD v M) :
    HasLD (u * v) (L + M) := by
  unfold HasLD at *
  rw [Units.val_mul, theta_mul, hu, hv]; ring

theorem HasLD.inv {u : ℚ⟦X⟧ˣ} {L : ℚ⟦X⟧} (hu : HasLD u L) : HasLD u⁻¹ (-L) := by
  unfold HasLD at *
  set i : ℚ⟦X⟧ := ↑u⁻¹ with hi_def
  have hu1 : (u : ℚ⟦X⟧) * i = 1 := Units.mul_inv u
  have hi : i * (u : ℚ⟦X⟧) = 1 := Units.inv_mul u
  have h1 : theta ((u : ℚ⟦X⟧) * i) = 0 := by rw [hu1, theta_one]
  rw [theta_mul, hu] at h1
  linear_combination i * h1 - theta i * hi - L * i * hu1

theorem HasLD.pow {u : ℚ⟦X⟧ˣ} {L : ℚ⟦X⟧} (hu : HasLD u L) (n : ℕ) :
    HasLD (u ^ n) ((n : ℚ⟦X⟧) * L) := by
  induction n with
  | zero =>
    unfold HasLD; simp [theta_one]
  | succ n ih =>
    have := ih.mul hu
    rw [← pow_succ] at this
    unfold HasLD at *
    rw [this]; push_cast; ring

theorem HasLD.zpow {u : ℚ⟦X⟧ˣ} {L : ℚ⟦X⟧} (hu : HasLD u L) (k : ℤ) :
    HasLD (u ^ k) ((k : ℚ⟦X⟧) * L) := by
  rcases k with n | n
  · simpa using hu.pow n
  · rw [zpow_negSucc]
    have := (hu.pow (n + 1)).inv
    unfold HasLD at *
    rw [this, Int.cast_negSucc]; push_cast; ring

theorem HasLD.congr {u : ℚ⟦X⟧ˣ} {L M : ℚ⟦X⟧} (hu : HasLD u L) (h : L = M) : HasLD u M :=
  h ▸ hu

/-- The units map of `expand`. -/
noncomputable def exU : ℚ⟦X⟧ˣ →* ℚ⟦X⟧ˣ := Units.map (expand p hp).toRingHom.toMonoidHom

@[simp] theorem val_exU (u : ℚ⟦X⟧ˣ) : ((exU p hp u : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = expand p hp u := rfl

theorem HasLD.expand {u : ℚ⟦X⟧ˣ} {L : ℚ⟦X⟧} (hu : HasLD u L) :
    HasLD (exU p hp u) ((p : ℚ⟦X⟧) * PowerSeries.expand p hp L) := by
  unfold HasLD at *
  rw [val_exU, theta_expand, hu, map_mul]; ring

/-- $V_L = \sum_{p \nmid n} \frac{[X^n]L}{n} X^n$. -/
noncomputable def Vof (L : ℚ⟦X⟧) : ℚ⟦X⟧ := mk fun n => if p ∣ n then 0 else coeff n L / n

theorem coeff_Vof (L : ℚ⟦X⟧) (n : ℕ) :
    coeff n (Vof p L) = if p ∣ n then 0 else coeff n L / n := by
  simp [Vof]

theorem theta_Vof (L : ℚ⟦X⟧) (hper : ∀ m, coeff (p * m) L = coeff m L) :
    theta (Vof p L) = L - expand p hp L := by
  ext n
  rw [coeff_theta, coeff_Vof, map_sub, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), hper]; ring
  · have hn : (n : ℚ) ≠ 0 := by
      have : n ≠ 0 := by rintro rfl; exact h (dvd_zero p)
      exact_mod_cast this
    field_simp; ring

theorem Vof_add (L M : ℚ⟦X⟧) : Vof p (L + M) = Vof p L + Vof p M := by
  ext n; simp only [coeff_Vof, map_add]; split_ifs <;> ring

theorem Vof_C_mul (a : ℚ) (L : ℚ⟦X⟧) : Vof p (C a * L) = C a * Vof p L := by
  ext n; simp only [coeff_Vof, coeff_C_mul]; split_ifs <;> ring

theorem X_dvd_Vof (L : ℚ⟦X⟧) : X ∣ Vof p L := by
  rw [← pow_one X, X_pow_dvd_iff]
  intro m hm
  obtain rfl : m = 0 := by omega
  simp [coeff_Vof]

theorem coeff_p_mul_Vof (L : ℚ⟦X⟧) (j : ℕ) : coeff (p * j) (Vof p L) = 0 := by
  simp [coeff_Vof]

/-- The expansion of $A(X^p)\,V$ has no monomial $X^{pj}$ when $V = V_L$. -/
theorem coeff_p_mul_expand_mul_Vof (A L : ℚ⟦X⟧) (j : ℕ) :
    coeff (p * j) (expand p hp A * Vof p L) = 0 := by
  rw [coeff_p_mul_expand_mul]
  exact Finset.sum_eq_zero fun x _ => by rw [coeff_p_mul_Vof, mul_zero]

end Frob

/-! ## The truncated exponential -/

/-- $E_T = \sum_{t \le T} \frac{c^t}{t!} Z^t$. -/
noncomputable def expTrunc (c : ℚ) (Z : ℚ⟦X⟧) (T : ℕ) : ℚ⟦X⟧ :=
  ∑ t ∈ range (T + 1), C (c ^ t / t.factorial) * Z ^ t

theorem theta_C_mul (a : ℚ) (A : ℚ⟦X⟧) : theta (C a * A) = C a * theta A := by
  ext n; simp [coeff_C_mul]; ring

theorem theta_expTrunc (c : ℚ) (Z : ℚ⟦X⟧) (T : ℕ) :
    theta (expTrunc c Z T) =
      C c * theta Z * expTrunc c Z T - C (c ^ (T + 1) / T.factorial) * (theta Z * Z ^ T) := by
  induction T with
  | zero =>
    simp [expTrunc, theta_one]
  | succ T ih =>
    have hsplit : expTrunc c Z (T + 1) =
        expTrunc c Z T + C (c ^ (T + 1) / (T + 1).factorial) * Z ^ (T + 1) := by
      simp only [expTrunc]; rw [Finset.sum_range_succ _ (T + 1)]
    rw [hsplit, theta_add, ih, theta_C_mul, theta_pow]
    have e1 : C (c ^ (T + 1) / (T + 1).factorial) * ((T + 1 : ℕ) : ℚ⟦X⟧) =
        C (c ^ (T + 1) / T.factorial) := by
      rw [← map_natCast (C (R := ℚ)), ← map_mul]
      congr 1
      rw [Nat.factorial_succ]; push_cast
      field_simp
    have e2 : C c * C (c ^ (T + 1) / (T + 1).factorial) = C (c ^ (T + 1 + 1) / (T + 1).factorial) := by
      rw [← map_mul]; congr 1; ring
    linear_combination (Z ^ T * theta Z) * e1 - (theta Z * Z ^ (T + 1)) * e2

theorem constantCoeff_expTrunc (c : ℚ) {Z : ℚ⟦X⟧} (hZ : X ∣ Z) (T : ℕ) :
    constantCoeff (expTrunc c Z T) = 1 := by
  have hZ0 : constantCoeff Z = 0 := by
    obtain ⟨W, rfl⟩ := hZ; simp
  simp only [expTrunc, map_sum, map_mul, constantCoeff_C, map_pow, hZ0]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro t _ ht; simp [ht]
  · simp

/-- If $\theta E = c\,\theta Z \cdot E$ and $E(0) = 1$, then $E \equiv \sum_{t \le T} c^t Z^t / t!$
modulo $X^{T+1}$. -/
theorem X_pow_dvd_sub_expTrunc {c : ℚ} {Z E : ℚ⟦X⟧} (T : ℕ) (hZ : X ∣ Z)
    (hE : theta E = C c * theta Z * E) (hE0 : constantCoeff E = 1) :
    X ^ (T + 1) ∣ E - expTrunc c Z T := by
  apply X_pow_dvd_of_theta (K := C c * theta Z)
    (Rr := C (c ^ (T + 1) / T.factorial) * (theta Z * Z ^ T))
  · rw [theta_sub, hE, theta_expTrunc]; ring
  · exact Dvd.dvd.mul_left (X_dvd_theta Z) _
  · apply Dvd.dvd.mul_left
    rw [pow_succ']
    exact mul_dvd_mul (X_dvd_theta Z) (pow_dvd_pow_of_dvd hZ T)
  · rw [map_sub, hE0, constantCoeff_expTrunc c hZ, sub_self]

end

/-! ## `p`-adic norms -/

section

section Norm

variable {p : ℕ} [hp : Fact p.Prime]

theorem mul_le_one_of_le {a b : ℚ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 := by
  nlinarith

/-- All coefficients of `A` are `p`-integral. -/
def PI (p : ℕ) (A : ℚ⟦X⟧) : Prop := ∀ n, padicNorm p (coeff n A) ≤ 1

theorem PI.add {A B : ℚ⟦X⟧} (hA : PI p A) (hB : PI p B) : PI p (A + B) := fun n => by
  rw [map_add]; exact padicNorm.nonarchimedean.trans (max_le (hA n) (hB n))

omit hp in
theorem PI.neg {A : ℚ⟦X⟧} (hA : PI p A) : PI p (-A) := fun n => by
  rw [map_neg, padicNorm.neg]; exact hA n

theorem PI.sub {A B : ℚ⟦X⟧} (hA : PI p A) (hB : PI p B) : PI p (A - B) := by
  rw [sub_eq_add_neg]; exact hA.add hB.neg

theorem PI.mul {A B : ℚ⟦X⟧} (hA : PI p A) (hB : PI p B) : PI p (A * B) := fun n => by
  rw [coeff_mul]
  refine padicNorm.sum_le' (fun x _ => ?_) zero_le_one
  rw [padicNorm.mul]
  exact mul_le_one_of_le (hA _) (padicNorm.nonneg _) (hB _)

omit hp in
theorem PI.one : PI p (1 : ℚ⟦X⟧) := fun n => by
  rw [coeff_one]; split_ifs <;> simp

theorem PI.pow {A : ℚ⟦X⟧} (hA : PI p A) (n : ℕ) : PI p (A ^ n) := by
  induction n with
  | zero => simpa using PI.one
  | succ n ih => rw [pow_succ]; exact ih.mul hA

theorem PI.C_mul {a : ℚ} (ha : padicNorm p a ≤ 1) {A : ℚ⟦X⟧} (hA : PI p A) :
    PI p (C a * A) := fun n => by
  rw [coeff_C_mul, padicNorm.mul]
  exact mul_le_one_of_le ha (padicNorm.nonneg _) (hA n)

theorem PI.map_int (A : ℤ⟦X⟧) : PI p (map (Int.castRingHom ℚ) A) := fun n => by
  rw [coeff_map]; exact padicNorm.of_int _

omit hp in
theorem PI.expand {q : ℕ} (hq : q ≠ 0) {A : ℚ⟦X⟧} (hA : PI p A) :
    PI p (expand q hq A) := fun n => by
  rw [coeff_expand]; split_ifs
  · exact hA _
  · simp

omit hp in
theorem PI.X : PI p (X : ℚ⟦X⟧) := fun n => by
  rw [coeff_X]; split_ifs <;> simp

theorem PI.sum {ι : Type*} (s : Finset ι) {f : ι → ℚ⟦X⟧} (hf : ∀ i ∈ s, PI p (f i)) :
    PI p (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]
  exact padicNorm.sum_le' (fun i hi => hf i hi n) zero_le_one

theorem padicNorm_inv_nat_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : padicNorm p ((n : ℚ)⁻¹) = 1 := by
  have h1 := (padicNorm.nat_eq_one_iff (p := p) n).mpr hn
  have hn0 : (n : ℚ) ≠ 0 := by
    have : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
    exact_mod_cast this
  have h2 : padicNorm p ((n : ℚ) * (n : ℚ)⁻¹) = 1 := by rw [mul_inv_cancel₀ hn0, padicNorm.one]
  rw [padicNorm.mul, h1, one_mul] at h2
  exact h2

theorem PI.Vof {L : ℚ⟦X⟧} (hL : PI p L) : PI p (Vof p L) := fun n => by
  rw [coeff_Vof]; split_ifs with h
  · simp
  · rw [div_eq_mul_inv, padicNorm.mul, padicNorm_inv_nat_of_not_dvd h, mul_one]; exact hL n

theorem padicNorm_p_pos : 0 < padicNorm p (p : ℚ) := by
  rw [padicNorm.padicNorm_p_of_prime]; exact inv_pos.mpr (by exact_mod_cast hp.out.pos)

theorem padicNorm_p_le_one : padicNorm p (p : ℚ) ≤ 1 := by
  exact_mod_cast padicNorm.of_nat (p := p) p

theorem padicNorm_pow (x : ℚ) (n : ℕ) : padicNorm p (x ^ n) = padicNorm p x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

/-- $|n|_p = |p|_p^{v_p(n)}$. -/
theorem padicNorm_nat_eq (n : ℕ) (hn : n ≠ 0) :
    padicNorm p (n : ℚ) = padicNorm p (p : ℚ) ^ padicValNat p n := by
  have h := Nat.ordProj_mul_ordCompl_eq_self n p
  rw [Nat.factorization_def n hp.out] at h
  have hc : ¬ p ∣ n / p ^ padicValNat p n := by
    have := Nat.not_dvd_ordCompl hp.out hn
    rwa [Nat.factorization_def n hp.out] at this
  conv_lhs => rw [← h]
  push_cast
  rw [padicNorm.mul, padicNorm_pow, (padicNorm.nat_eq_one_iff _).mpr hc, mul_one]

/-- For $p \ge 5$ and $t \ge 2$: $v_p(t!) \le t - 2$. -/
theorem padicValNat_factorial_le_sub_two (h5 : 5 ≤ p) {t : ℕ} (ht : 2 ≤ t) :
    padicValNat p t.factorial ≤ t - 2 := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := t) (by omega)
  have h4 : 4 * padicValNat p t.factorial ≤ (p - 1) * padicValNat p t.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- For $p \ge 5$ and $t \ge 2$: $|p|_p^{t-2} \le |t!|_p$. -/
theorem norm_p_pow_le_norm_factorial (h5 : 5 ≤ p) {t : ℕ} (ht : 2 ≤ t) :
    padicNorm p (p : ℚ) ^ (t - 2) ≤ padicNorm p (t.factorial : ℚ) := by
  rw [padicNorm_nat_eq _ (Nat.factorial_ne_zero t)]
  exact pow_le_pow_of_le_one (padicNorm.nonneg _) padicNorm_p_le_one
    (padicValNat_factorial_le_sub_two h5 ht)

end Norm

end

/-! ## The series over `ℚ` -/

section

noncomputable section

/-! ## The series over `ℚ` -/

/-- The coefficient map `ℤ⟦X⟧ → ℚ⟦X⟧`. -/
abbrev ι : ℤ⟦X⟧ →+* ℚ⟦X⟧ := PowerSeries.map (Int.castRingHom ℚ)

/-- The units map of `ι`. -/
def ιU : ℤ⟦X⟧ˣ →* ℚ⟦X⟧ˣ := Units.map ι.toMonoidHom

@[simp] theorem val_ιU (u : ℤ⟦X⟧ˣ) : ((ιU u : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = ι u := rfl

/-- $G = (1+W)^s\,\Phi^r$ over `ℤ`. -/
def Gz (r : ℕ) (s : ℤ) : ℤ⟦X⟧ˣ := onePlusXu ^ s * Φu ^ r

/-- $Q = (1 - W^2)/\Phi$ over `ℤ`. -/
def Qz : ℤ⟦X⟧ := (1 - X ^ 2) * invOfUnit Φ 1

/-- The coefficients of `Qz`: $q_0 = 1$, and for $m \ge 1$, $q_m = 2$ if $3 \mid m$ and $-1$
otherwise. -/
def qf (n : ℕ) : ℤ := if n = 0 then 1 else if 3 ∣ n then 2 else -1

theorem mk_qf_mul_Φ : mk qf * Φ = 1 - X ^ 2 := by
  ext n
  simp only [Φ, mul_add, mul_one, map_add, map_sub, coeff_one, coeff_X_pow, coeff_mul_X_pow']
  rcases n with _ | _ | _ | n
  · simp [qf]
  · simp [qf, coeff_succ_mul_X]
  · simp [qf, coeff_succ_mul_X]
  · simp only [coeff_succ_mul_X, coeff_mk, show n + 1 + 1 + 1 - 2 = n + 1 by omega,
      show 2 ≤ n + 1 + 1 + 1 by omega, ite_true, show n + 1 + 1 + 1 ≠ 0 by omega,
      show n + 1 + 1 + 1 ≠ 2 by omega, ite_false, sub_zero]
    unfold qf
    simp only [show n + 1 + 1 + 1 ≠ 0 by omega, show n + 1 + 1 ≠ 0 by omega,
      show n + 1 ≠ 0 by omega, ite_false]
    split_ifs <;> omega

theorem Qz_eq : Qz = mk qf := by
  rw [Qz, ← mk_qf_mul_Φ, mul_assoc, mul_invOfUnit Φ 1 (by simp), mul_one]

theorem a_eq_coeff_Qz (r : ℕ) (s : ℤ) (N : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    a r s N = coeff (r * N) (Qz * ((Gz r s ^ N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)) := by
  obtain ⟨m, hm⟩ : ∃ m, r * N = m + 1 := ⟨r * N - 1, by
    have : 1 ≤ r * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega⟩
  rw [a, hm, lagrange m, subst_Fzpow]
  congr 1
  have h1 : ((Gz r s ^ N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) =
      ((onePlusXu ^ (s * N) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) * Φ ^ (m + 1) := by
    rw [Gz, mul_pow, ← zpow_natCast, ← zpow_mul, ← pow_mul, ← hm, Units.val_mul]
    simp [Φu, mul_comm r N]
  rw [h1, Qz]
  have h2 : invOfUnit Φ 1 * Φ ^ (m + 1) = Φ ^ m := by
    rw [pow_succ, mul_comm, mul_assoc, mul_invOfUnit Φ 1 (by simp), mul_one]
  linear_combination -((onePlusXu ^ (s * ↑N) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) * (1 - X ^ 2) * h2

/-- $Q$ over `ℚ`. -/
def Qq : ℚ⟦X⟧ := ι Qz

/-- $G$ over `ℚ`. -/
def Gq (r : ℕ) (s : ℤ) : ℚ⟦X⟧ˣ := ιU (Gz r s)

theorem a_eq_coeff_Qq (r : ℕ) (s : ℤ) (N : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    (a r s N : ℚ) = coeff (r * N) (Qq * ((Gq r s ^ N : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) := by
  rw [a_eq_coeff_Qz r s N hr hN, Qq, Gq, ← map_pow, val_ιU, ← map_mul, coeff_map]
  rfl

theorem coeff_Qq (n : ℕ) : coeff n Qq = (qf n : ℚ) := by
  rw [Qq, Qz_eq, coeff_map, coeff_mk]; rfl

/-- $(1+X)^{-1} = \sum (-1)^n X^n$ over `ℚ`. -/
def Inv1 : ℚ⟦X⟧ := mk fun n => (-1) ^ n

/-- $\Lambda_1 = \theta \log(1+X) = X/(1+X)$. -/
def Λ₁ : ℚ⟦X⟧ := X * Inv1

/-- $\Lambda_3 = \theta \log \Phi = 1 - Q$. -/
def Λ₃ : ℚ⟦X⟧ := 1 - Qq

/-- $\Lambda = \theta \log G = s\Lambda_1 + r\Lambda_3$. -/
def Λ (r : ℕ) (s : ℤ) : ℚ⟦X⟧ := C (s : ℚ) * Λ₁ + C (r : ℚ) * Λ₃

theorem one_add_X_mul_Inv1 : (1 + X : ℚ⟦X⟧) * Inv1 = 1 := by
  rw [mul_comm]; exact mk_neg_one_pow_mul_one_add_eq_one ℚ

theorem val_onePlusXq : ((ιU onePlusXu : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 + X := by
  simp [onePlusXu]

theorem val_onePlusXq_inv : ((ιU onePlusXu⁻¹ : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = Inv1 := by
  have h1 := Units.inv_mul (ιU onePlusXu)
  rw [← map_inv] at h1
  calc ((ιU onePlusXu⁻¹ : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)
      = ((ιU onePlusXu⁻¹ : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * ((1 + X) * Inv1) := by
        rw [one_add_X_mul_Inv1, mul_one]
    _ = Inv1 := by rw [← val_onePlusXq, ← mul_assoc, h1, one_mul]

theorem val_Φq : ((ιU Φu : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 + X + X ^ 2 := by
  simp [Φu]

theorem Qq_mul_Φq : Qq * (1 + X + X ^ 2) = 1 - X ^ 2 := by
  have h := congrArg ι mk_qf_mul_Φ
  rw [← Qz_eq] at h
  simpa [Qq] using h

theorem theta_Φ' {R : Type*} [CommRing R] :
    theta (1 + X + X ^ 2 : R⟦X⟧) = X + 2 * X ^ 2 := by
  rw [theta_add, theta_add, theta_one, theta_X, show (X : R⟦X⟧) ^ 2 = X ^ (1 + 1) by ring,
    theta_pow, theta_X]
  push_cast; ring

theorem hasLD_onePlusXq : HasLD (ιU onePlusXu) Λ₁ := by
  unfold HasLD
  rw [val_onePlusXq, theta_add, theta_one, theta_X, Λ₁, mul_assoc, mul_comm Inv1,
    one_add_X_mul_Inv1]; ring

theorem hasLD_Φq : HasLD (ιU Φu) Λ₃ := by
  unfold HasLD
  rw [val_Φq, theta_Φ', Λ₃, sub_mul, Qq_mul_Φq]; ring

theorem Gq_eq (r : ℕ) (s : ℤ) : Gq r s = ιU onePlusXu ^ s * ιU Φu ^ r := by
  rw [Gq, Gz, map_mul, map_zpow, map_pow]

theorem hasLD_Gq (r : ℕ) (s : ℤ) : HasLD (Gq r s) (Λ r s) := by
  rw [Gq_eq]
  refine ((hasLD_onePlusXq.zpow s).mul (hasLD_Φq.pow r)).congr ?_
  simp [Λ, map_intCast, map_natCast]

/-- The constant-coefficient map on units. -/
def cU : ℚ⟦X⟧ˣ →* ℚˣ := Units.map (constantCoeff (R := ℚ)).toMonoidHom

@[simp] theorem val_cU (u : ℚ⟦X⟧ˣ) : ((cU u : ℚˣ) : ℚ) = constantCoeff (u : ℚ⟦X⟧) := rfl

theorem cU_Gq (r : ℕ) (s : ℤ) : cU (Gq r s) = 1 := by
  rw [Gq_eq, map_mul, map_zpow, map_pow]
  have h1 : cU (ιU onePlusXu) = 1 := Units.ext (by rw [val_cU, val_onePlusXq]; simp)
  have h2 : cU (ιU Φu) = 1 := Units.ext (by rw [val_cU, val_Φq]; simp)
  rw [h1, h2, one_zpow, one_pow, one_mul]

theorem constantCoeff_Gq_pow (r : ℕ) (s : ℤ) (N : ℕ) :
    constantCoeff ((Gq r s ^ N : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 := by
  rw [← val_cU, map_pow, cU_Gq, one_pow]; rfl

end

end

/-! ## The exponential expansion of $a(pM)$ -/

section

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

theorem hp0 : p ≠ 0 := hp.out.ne_zero

/-! ## Coefficients and periodicity -/

theorem coeff_Λ₁ (n : ℕ) : coeff n Λ₁ = if n = 0 then 0 else (-1) ^ (n + 1) := by
  rcases n with _ | n
  · simp [Λ₁]
  · rw [Λ₁, coeff_succ_X_mul]; simp [Inv1, pow_succ]

theorem coeff_Λ₃ (n : ℕ) : coeff n Λ₃ = if n = 0 then 0 else -(qf n : ℚ) := by
  rw [Λ₃, map_sub, coeff_one, coeff_Qq]
  split_ifs with h <;> simp [h, qf]

omit hp in
theorem qf_mul (hpp : p.Prime) (h5 : 5 ≤ p) (m : ℕ) : qf (p * m) = qf m := by
  unfold qf
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hpm : p * m ≠ 0 := Nat.mul_ne_zero (by omega) hm.ne'
  have h3 : 3 ∣ p * m ↔ 3 ∣ m := by
    constructor
    · intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · exfalso; have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp h; omega
      · exact h
    · intro h; exact Dvd.dvd.mul_left h p
  simp only [hpm, hm.ne', ite_false, h3]

theorem coeff_Λ₁_mul (h5 : 5 ≤ p) (m : ℕ) : coeff (p * m) Λ₁ = coeff m Λ₁ := by
  rw [coeff_Λ₁, coeff_Λ₁]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hpm : p * m ≠ 0 := Nat.mul_ne_zero (by omega) hm.ne'
  simp only [hpm, hm.ne', ite_false]
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  rw [pow_succ, pow_succ, pow_mul, hodd.neg_one_pow]

theorem coeff_Λ₃_mul (h5 : 5 ≤ p) (m : ℕ) : coeff (p * m) Λ₃ = coeff m Λ₃ := by
  rw [coeff_Λ₃, coeff_Λ₃, qf_mul hp.out h5]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hpm : p * m ≠ 0 := Nat.mul_ne_zero (by omega) hm.ne'
  simp only [hpm, hm.ne', ite_false]

theorem coeff_Λ_mul (h5 : 5 ≤ p) (r : ℕ) (s : ℤ) (m : ℕ) :
    coeff (p * m) (Λ r s) = coeff m (Λ r s) := by
  simp only [Λ, map_add, coeff_C_mul, coeff_Λ₁_mul h5, coeff_Λ₃_mul h5]

theorem coeff_Qq_mul (h5 : 5 ≤ p) (m : ℕ) : coeff (p * m) Qq = coeff m Qq := by
  rw [coeff_Qq, coeff_Qq, qf_mul hp.out h5]

/-! ## `p`-integrality -/

theorem PI_Inv1 : PI p Inv1 := fun n => by
  simp only [Inv1, coeff_mk]
  rw [padicNorm_pow, padicNorm.neg, padicNorm.one, one_pow]

theorem PI_Λ₁ : PI p Λ₁ := PI.X.mul PI_Inv1

theorem PI_Qq : PI p Qq := PI.map_int _

theorem PI_Λ₃ : PI p Λ₃ := PI.one.sub PI_Qq

theorem PI_Λ (r : ℕ) (s : ℤ) : PI p (Λ r s) :=
  (PI.C_mul (padicNorm.of_int s) PI_Λ₁).add
    (PI.C_mul (by exact_mod_cast padicNorm.of_nat (p := p) r) PI_Λ₃)

theorem PI_Gq_pow (r : ℕ) (s : ℤ) (N : ℕ) : PI p ((Gq r s ^ N : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
  rw [Gq, ← map_pow, val_ιU]; exact PI.map_int _

/-! ## The Frobenius series -/

/-- $Z = \sum_{p \nmid n} \frac{\lambda_n}{n} X^n$, where $\Lambda = \sum \lambda_n X^n$. -/
def Zs (p : ℕ) (r : ℕ) (s : ℤ) : ℚ⟦X⟧ := Vof p (Λ r s)

theorem theta_Zs (h5 : 5 ≤ p) (r : ℕ) (s : ℤ) :
    theta (Zs p r s) = Λ r s - expand p hp0 (Λ r s) :=
  theta_Vof p hp0 _ (coeff_Λ_mul h5 r s)

theorem PI_Zs (r : ℕ) (s : ℤ) : PI p (Zs p r s) := (PI_Λ r s).Vof

/-- $E = G^{pM} / G(X^p)^M$. -/
def Eu (p : ℕ) [Fact p.Prime] (r : ℕ) (s : ℤ) (M : ℕ) : ℚ⟦X⟧ˣ :=
  Gq r s ^ (p * M) * (exU p hp0 (Gq r s))⁻¹ ^ M

theorem Gq_pow_eq (r : ℕ) (s : ℤ) (M : ℕ) :
    Gq r s ^ (p * M) = exU p hp0 (Gq r s ^ M) * Eu p r s M := by
  rw [Eu, map_pow, inv_pow, mul_left_comm, mul_inv_cancel, mul_one]

theorem hasLD_Eu (h5 : 5 ≤ p) (r : ℕ) (s : ℤ) (M : ℕ) :
    HasLD (Eu p r s M) (C ((p : ℚ) * M) * theta (Zs p r s)) := by
  refine (((hasLD_Gq r s).pow (p * M)).mul (((hasLD_Gq r s).expand p hp0).inv.pow M)).congr ?_
  rw [theta_Zs h5, map_mul, map_natCast, map_natCast, Nat.cast_mul]
  ring

theorem constantCoeff_Eu (r : ℕ) (s : ℤ) (M : ℕ) :
    constantCoeff ((Eu p r s M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 := by
  have h1 : cU (exU p hp0 (Gq r s)) = 1 := by
    apply Units.ext
    rw [val_cU, val_exU, constantCoeff_expand, ← val_cU, cU_Gq]
  have : cU (Eu p r s M) = 1 := by
    rw [Eu, map_mul, map_pow, map_pow, map_inv, cU_Gq, h1]; simp
  rw [← val_cU, this]; rfl

/-- $S_t = \sum_{i + j = rM} [X^i]G^M \, [X^{pj}](Q Z^t)$. -/
def Sx (p : ℕ) [Fact p.Prime] (r : ℕ) (s : ℤ) (M t : ℕ) : ℚ :=
  ∑ x ∈ antidiagonal (r * M),
    coeff x.1 ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * coeff (p * x.2) (Qq * Zs p r s ^ t)

/-- **The exponential expansion.** $a(pM) = \sum_{t \le prM} \frac{(pM)^t}{t!} S_t$. -/
theorem expansion (h5 : 5 ≤ p) (r : ℕ) (s : ℤ) (M : ℕ) (hr : 1 ≤ r) (hM : 1 ≤ M) :
    (a r s (p * M) : ℚ) = ∑ t ∈ range (p * (r * M) + 1),
      ((p : ℚ) * M) ^ t / t.factorial * Sx p r s M t := by
  have hpM : 1 ≤ p * M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp0 (by omega))
  rw [a_eq_coeff_Qq r s (p * M) hr hpM, Gq_pow_eq, Units.val_mul, val_exU,
    show r * (p * M) = p * (r * M) by ring, ← mul_assoc Qq]
  have hdvd := X_pow_dvd_sub_expTrunc (p * (r * M)) (X_dvd_Vof p (Λ r s))
    (hasLD_Eu h5 r s M) (constantCoeff_Eu r s M)
  rw [coeff_mul_eq_of_X_pow_dvd _ hdvd, expTrunc, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show Qq * expand p hp0 ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * (C (((p : ℚ) * M) ^ t / t.factorial) *
      Vof p (Λ r s) ^ t) = C (((p : ℚ) * M) ^ t / t.factorial) *
      (expand p hp0 ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * (Qq * Zs p r s ^ t)) by rw [Zs]; ring,
    coeff_C_mul, coeff_p_mul_expand_mul]
  rfl

/-- The term $t = 0$ is $a(M)$. -/
theorem Sx_zero (h5 : 5 ≤ p) (r : ℕ) (s : ℤ) (M : ℕ) (hr : 1 ≤ r) (hM : 1 ≤ M) :
    Sx p r s M 0 = a r s M := by
  rw [a_eq_coeff_Qq r s M hr hM, Sx, mul_comm Qq ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧), coeff_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pow_zero, mul_one, coeff_Qq_mul h5]

end

end

/-! ## Lemma B and the main estimate -/

section

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-- $V_1 = \sum_{p \nmid n} (-1)^{n+1} X^n / n$. -/
def V₁ (p : ℕ) : ℚ⟦X⟧ := Vof p Λ₁

/-- $V_3 = -\sum_{p \nmid n} q_n X^n / n$. -/
def V₃ (p : ℕ) : ℚ⟦X⟧ := Vof p Λ₃

omit hp in
theorem Zs_eq (r : ℕ) (s : ℤ) : Zs p r s = C (s : ℚ) * V₁ p + C (r : ℚ) * V₃ p := by
  rw [Zs, Λ, Vof_add, Vof_C_mul, Vof_C_mul]; rfl

theorem theta_V₃ (h5 : 5 ≤ p) : theta (V₃ p) = expand p hp0 Qq - Qq := by
  rw [V₃, theta_Vof p hp0 _ (coeff_Λ₃_mul h5), Λ₃, map_sub, map_one]; ring

/-- **Lemma B.** $[X^{pj}](Q V_3) = -\frac{pj}{2} [X^{pj}] V_3^2$. -/
theorem coeff_Qq_V₃ (h5 : 5 ≤ p) (j : ℕ) :
    coeff (p * j) (Qq * V₃ p) = -((p : ℚ) * j / 2) * coeff (p * j) (V₃ p ^ 2) := by
  have hQ : Qq = expand p hp0 Qq - theta (V₃ p) := by rw [theta_V₃ h5]; ring
  have h2 : theta (V₃ p ^ 2) = 2 * V₃ p * theta (V₃ p) := by
    rw [show V₃ p ^ 2 = V₃ p ^ (1 + 1) by ring, theta_pow]; push_cast; ring
  have h12 : C (1 / 2 : ℚ) * (2 : ℚ⟦X⟧) = 1 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, ← map_mul]; norm_num
  have e : Qq * V₃ p = expand p hp0 Qq * V₃ p - C (1 / 2 : ℚ) * theta (V₃ p ^ 2) := by
    conv_lhs => rw [hQ]
    rw [h2]
    linear_combination (V₃ p * theta (V₃ p)) * h12
  rw [e, map_sub, V₃, coeff_p_mul_expand_mul_Vof, ← V₃, coeff_C_mul, coeff_theta]
  push_cast; ring

theorem padicNorm_half (h5 : 5 ≤ p) : padicNorm p ((2 : ℚ)⁻¹) = 1 := by
  have := padicNorm_inv_nat_of_not_dvd (p := p) (n := 2) (by
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
  simpa using this

theorem norm_coeff_Qq_V₃ (h5 : 5 ≤ p) (j : ℕ) :
    padicNorm p (coeff (p * j) (Qq * V₃ p)) ≤ padicNorm p p * padicNorm p j := by
  rw [coeff_Qq_V₃ h5, padicNorm.mul, padicNorm.neg, div_eq_mul_inv, padicNorm.mul,
    padicNorm.mul, padicNorm_half h5, mul_one]
  have h1 : padicNorm p (coeff (p * j) (V₃ p ^ 2)) ≤ 1 := ((PI_Λ₃.Vof).pow 2) _
  have h0 : 0 ≤ padicNorm p p * padicNorm p j :=
    mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)
  calc padicNorm p p * padicNorm p j * padicNorm p (coeff (p * j) (V₃ p ^ 2))
      ≤ padicNorm p p * padicNorm p j * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = _ := mul_one _

/-- The bound $|[X^{pj}](QZ)|_p \le |p|_p\,|j|_p$, given Lemma A. -/
theorem norm_coeff_Qq_Zs (h5 : 5 ≤ p)
    (hA : ∀ j : ℕ, padicNorm p (coeff (p * j) (Qq * V₁ p)) ≤ padicNorm p p * padicNorm p j)
    (r : ℕ) (s : ℤ) (j : ℕ) :
    padicNorm p (coeff (p * j) (Qq * Zs p r s)) ≤ padicNorm p p * padicNorm p j := by
  rw [Zs_eq, mul_add, mul_left_comm, mul_left_comm Qq, map_add, coeff_C_mul, coeff_C_mul]
  refine padicNorm.nonarchimedean.trans (max_le ?_ ?_)
  · rw [padicNorm.mul]
    calc padicNorm p (s : ℚ) * padicNorm p (coeff (p * j) (Qq * V₁ p))
        ≤ 1 * (padicNorm p p * padicNorm p j) :=
          mul_le_mul (padicNorm.of_int s) (hA j) (padicNorm.nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [padicNorm.mul]
    calc padicNorm p (r : ℚ) * padicNorm p (coeff (p * j) (Qq * V₃ p))
        ≤ 1 * (padicNorm p p * padicNorm p j) :=
          mul_le_mul (padicNorm.of_nat r) (norm_coeff_Qq_V₃ h5 j) (padicNorm.nonneg _)
            zero_le_one
      _ = _ := one_mul _

/-- The Gauss-type bound $|g_i|_p\,|i|_p \le |M|_p$ for the coefficients of $G^M$. -/
theorem norm_coeff_Gq_pow (r : ℕ) (s : ℤ) (M i : ℕ) :
    padicNorm p (coeff i ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) * padicNorm p i ≤ padicNorm p M := by
  have h := congrArg (coeff i) ((hasLD_Gq r s).pow M)
  rw [coeff_theta, mul_assoc, ← map_natCast (C (R := ℚ)), coeff_C_mul] at h
  have h2 := congrArg (padicNorm p) h
  rw [padicNorm.mul, padicNorm.mul] at h2
  have h3 : padicNorm p (coeff i (Λ r s * ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧))) ≤ 1 :=
    ((PI_Λ r s).mul (PI_Gq_pow r s M)) i
  rw [mul_comm, h2]
  calc padicNorm p M * padicNorm p (coeff i (Λ r s * ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)))
      ≤ padicNorm p M * 1 := mul_le_mul_of_nonneg_left h3 (padicNorm.nonneg _)
    _ = _ := mul_one _

/-- The term $t = 1$: $|S_1|_p \le |p|_p\,|M|_p$. -/
theorem norm_Sx_one (h5 : 5 ≤ p)
    (hA : ∀ j : ℕ, padicNorm p (coeff (p * j) (Qq * V₁ p)) ≤ padicNorm p p * padicNorm p j)
    (r : ℕ) (s : ℤ) (M : ℕ) :
    padicNorm p (Sx p r s M 1) ≤ padicNorm p p * padicNorm p M := by
  refine padicNorm.sum_le' (fun x hx => ?_) (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _))
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [pow_one, padicNorm.mul]
  have hc := norm_coeff_Qq_Zs h5 hA r s x.2
  have hg := norm_coeff_Gq_pow (p := p) r s M x.1
  have hg1 : padicNorm p (coeff x.1 ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) ≤ 1 := PI_Gq_pow r s M x.1
  have hpp := padicNorm.nonneg (p := p) (p : ℚ)
  by_cases hj : padicNorm p (x.2 : ℚ) ≤ padicNorm p M
  · calc padicNorm p (coeff x.1 ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) *
          padicNorm p (coeff (p * x.2) (Qq * Zs p r s))
        ≤ 1 * (padicNorm p p * padicNorm p x.2) :=
          mul_le_mul hg1 hc (padicNorm.nonneg _) zero_le_one
      _ ≤ padicNorm p p * padicNorm p M := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hj hpp
  · replace hj := lt_of_not_ge hj
    have hrM : padicNorm p ((r : ℚ) * M) < padicNorm p (x.2 : ℚ) := by
      rw [padicNorm.mul]
      calc padicNorm p (r : ℚ) * padicNorm p M ≤ 1 * padicNorm p M :=
            mul_le_mul_of_nonneg_right (padicNorm.of_nat r) (padicNorm.nonneg _)
        _ < _ := by rw [one_mul]; exact hj
    have hi : padicNorm p (x.1 : ℚ) = padicNorm p (x.2 : ℚ) := by
      have e : (x.1 : ℚ) = (r : ℚ) * M + -(x.2 : ℚ) := by
        have : ((x.1 + x.2 : ℕ) : ℚ) = ((r * M : ℕ) : ℚ) := by rw [hx']
        push_cast at this; linarith
      rw [e, padicNorm.add_eq_max_of_ne (by rw [padicNorm.neg]; exact hrM.ne), padicNorm.neg,
        max_eq_right hrM.le]
    calc padicNorm p (coeff x.1 ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) *
          padicNorm p (coeff (p * x.2) (Qq * Zs p r s))
        ≤ padicNorm p (coeff x.1 ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) *
            (padicNorm p p * padicNorm p x.2) :=
          mul_le_mul_of_nonneg_left hc (padicNorm.nonneg _)
      _ = padicNorm p p *
            (padicNorm p (coeff x.1 ((Gq r s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) * padicNorm p x.1) := by
          rw [hi]; ring
      _ ≤ padicNorm p p * padicNorm p M := mul_le_mul_of_nonneg_left hg hpp

/-- The terms $t \ge 2$: $|S_t|_p \le 1$. -/
theorem norm_Sx_le_one (r : ℕ) (s : ℤ) (M t : ℕ) : padicNorm p (Sx p r s M t) ≤ 1 := by
  refine padicNorm.sum_le' (fun x _ => ?_) zero_le_one
  rw [padicNorm.mul]
  exact mul_le_one_of_le (PI_Gq_pow r s M x.1) (padicNorm.nonneg _)
    ((PI_Qq.mul ((PI_Zs r s).pow t)) _)

/-- $|c^t / t!|_p \le |c|_p^2$ for $t \ge 2$ when $|c|_p \le |p|_p$. -/
theorem norm_pow_div_factorial (h5 : 5 ≤ p) {c : ℚ} (hc : padicNorm p c ≤ padicNorm p p) (t : ℕ) :
    padicNorm p (c ^ (t + 2) / (t + 2).factorial) ≤ padicNorm p c ^ 2 := by
  have hf := norm_p_pow_le_norm_factorial (p := p) h5 (t := t + 2) (by omega)
  rw [show t + 2 - 2 = t by omega] at hf
  have hfpos : 0 < padicNorm p ((t + 2).factorial : ℚ) := by
    have : ((t + 2).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero this).symm
  rw [padicNorm.div, padicNorm_pow, div_le_iff₀ hfpos, pow_add]
  have h1 : padicNorm p c ^ t ≤ padicNorm p p ^ t :=
    pow_le_pow_left₀ (padicNorm.nonneg _) hc t
  calc padicNorm p c ^ t * padicNorm p c ^ 2 ≤ padicNorm p p ^ t * padicNorm p c ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ padicNorm p ((t + 2).factorial : ℚ) * padicNorm p c ^ 2 :=
        mul_le_mul_of_nonneg_right hf (by positivity)
    _ = _ := by ring

/-- **The main estimate.** $|a(pM) - a(M)|_p \le |pM|_p^2$. -/
theorem main_estimate (h5 : 5 ≤ p)
    (hA : ∀ j : ℕ, padicNorm p (coeff (p * j) (Qq * V₁ p)) ≤ padicNorm p p * padicNorm p j)
    (r : ℕ) (s : ℤ) (M : ℕ) (hr : 1 ≤ r) (hM : 1 ≤ M) :
    padicNorm p (((a r s (p * M) - a r s M : ℤ)) : ℚ) ≤ padicNorm p ((p : ℚ) * M) ^ 2 := by
  push_cast
  rw [expansion h5 r s M hr hM, Finset.sum_range_succ', Sx_zero h5 r s M hr hM]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, add_sub_cancel_right]
  have hc : padicNorm p ((p : ℚ) * M) ≤ padicNorm p p := by
    rw [padicNorm.mul]
    calc padicNorm p (p : ℚ) * padicNorm p (M : ℚ) ≤ padicNorm p p * 1 :=
          mul_le_mul_of_nonneg_left (padicNorm.of_nat M) (padicNorm.nonneg _)
      _ = _ := mul_one _
  refine padicNorm.sum_le' (fun t _ => ?_) (by positivity)
  rcases t with _ | t
  · rw [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one, padicNorm.mul, sq]
    refine mul_le_mul_of_nonneg_left ?_ (padicNorm.nonneg _)
    rw [padicNorm.mul]; exact norm_Sx_one h5 hA r s M
  · rw [padicNorm.mul]
    calc padicNorm p (((p : ℚ) * M) ^ (t + 1 + 1) / ((t + 1 + 1).factorial : ℚ)) *
          padicNorm p (Sx p r s M (t + 1 + 1))
        ≤ padicNorm p ((p : ℚ) * M) ^ 2 * 1 :=
          mul_le_mul (norm_pow_div_factorial h5 hc t) (norm_Sx_le_one r s M _)
            (padicNorm.nonneg _) (by positivity)
      _ = _ := mul_one _

end

end

/-! ## The polynomial $W_1$ and degree bounds -/

section

noncomputable section

/-! ## The polynomial $W_1 = ((1+X)^p - 1 - X^p)/p$ and its factor $\Phi$ -/

theorem phi_dvd_aux {A : Type*} [CommRing A] (x : A) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (1 + x + x ^ 2) ∣ (1 + x) ^ p - 1 - x ^ p := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h1 : (1 + x + x ^ 2) ∣ (1 + x) ^ p - (-x ^ 2) ^ p := by
    have := sub_dvd_pow_sub_pow (1 + x) (-x ^ 2) p
    rwa [sub_neg_eq_add] at this
  have h3 : ∀ k : ℕ, (1 + x + x ^ 2) ∣ (x ^ 3) ^ k - 1 := by
    intro k
    have := sub_dvd_pow_sub_pow (x ^ 3) 1 k
    rw [one_pow] at this
    exact (Dvd.intro (x - 1) (by ring)).trans this
  rw [hodd.neg_pow] at h1
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h; omega
  have h3' : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
  have hmod : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rcases hmod with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, p = 6 * m + 1 := ⟨p / 6, by omega⟩
    have e : (1 + x) ^ (6 * m + 1) - 1 - x ^ (6 * m + 1) =
        ((1 + x) ^ (6 * m + 1) - -(x ^ 2) ^ (6 * m + 1)) - x ^ 2 * ((x ^ 3) ^ (4 * m) - 1)
          - x * ((x ^ 3) ^ (2 * m) - 1) - (1 + x + x ^ 2) := by ring
    rw [e]
    exact ((h1.sub (Dvd.dvd.mul_left (h3 _) _)).sub (Dvd.dvd.mul_left (h3 _) _)).sub dvd_rfl
  · obtain ⟨m, rfl⟩ : ∃ m, p = 6 * m + 5 := ⟨p / 6, by omega⟩
    have e : (1 + x) ^ (6 * m + 5) - 1 - x ^ (6 * m + 5) =
        ((1 + x) ^ (6 * m + 5) - -(x ^ 2) ^ (6 * m + 5)) - x * ((x ^ 3) ^ (4 * m + 3) - 1)
          - x ^ 2 * ((x ^ 3) ^ (2 * m + 1) - 1) - (1 + x + x ^ 2) := by ring
    rw [e]
    exact ((h1.sub (Dvd.dvd.mul_left (h3 _) _)).sub (Dvd.dvd.mul_left (h3 _) _)).sub dvd_rfl

theorem exists_W_K {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ∃ W K : Polynomial ℤ,
    (1 + Polynomial.X) ^ p - 1 - Polynomial.X ^ p = Polynomial.C (p : ℤ) * W ∧
    (1 + Polynomial.X) ^ p - 1 - Polynomial.X ^ p =
      (1 + Polynomial.X + Polynomial.X ^ 2) * K ∧
    W.coeff 0 = 0 ∧ W.natDegree ≤ p - 1 ∧ K.natDegree ≤ p - 3 := by
  set f : Polynomial ℤ := (1 + Polynomial.X) ^ p - 1 - Polynomial.X ^ p with hf
  have hfc : ∀ i, f.coeff i = (p.choose i : ℤ) - (if i = 0 then 1 else 0) -
      (if i = p then 1 else 0) := by
    intro i
    rw [hf, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow,
      Polynomial.coeff_one, Polynomial.coeff_X_pow]
  have hp0 : p ≠ 0 := hp.ne_zero
  have hfc0 : f.coeff 0 = 0 := by
    rw [hfc]; simp [Ne.symm hp0]
  have hfhi : ∀ i, p ≤ i → f.coeff i = 0 := by
    intro i hi
    rw [hfc]
    rcases Nat.lt_or_ge p i with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; simp [show i ≠ 0 by omega, show i ≠ p by omega]
    · obtain rfl : i = p := le_antisymm h hi
      simp [hp0]
  have hdvd : Polynomial.C (p : ℤ) ∣ f := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hfc0]; exact dvd_zero _
    rcases Nat.lt_or_ge i p with hip | hip
    · rw [hfc]
      simp only [show i ≠ 0 by omega, show i ≠ p by omega, ite_false, sub_zero]
      exact_mod_cast Nat.Prime.dvd_choose_self hp hi.ne' hip
    · rw [hfhi i hip]; exact dvd_zero _
  obtain ⟨W, hW⟩ := hdvd
  obtain ⟨K, hK⟩ := phi_dvd_aux (Polynomial.X : Polynomial ℤ) hp h5
  refine ⟨W, K, hW, hK, ?_, ?_, ?_⟩
  · have := congrArg (fun P : Polynomial ℤ => P.coeff 0) hW
    simp only [Polynomial.coeff_C_mul, hfc0] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h (by exact_mod_cast hp0)
    · exact h
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have := congrArg (fun P : Polynomial ℤ => P.coeff N) hW
    simp only [Polynomial.coeff_C_mul, hfhi N (by omega)] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h (by exact_mod_cast hp0)
    · exact h
  · by_cases hK0 : K = 0
    · simp [hK0]
    have hmon : (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ).Monic := by monicity!
    have hdeg : (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ).natDegree = 2 := by
      compute_degree!
    have hfdeg : f.natDegree ≤ p - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN; exact hfhi N (by omega)
    rw [hf, hK, hmon.natDegree_mul' hK0, hdeg] at hfdeg
    omega

/-! ## Degree bounds for power series -/

/-- `A` has no monomial beyond degree `d`. -/
def DegLE (A : ℚ⟦X⟧) (d : ℕ) : Prop := ∀ n, d < n → coeff n A = 0

theorem DegLE.mul {A B : ℚ⟦X⟧} {a b : ℕ} (hA : DegLE A a) (hB : DegLE B b) :
    DegLE (A * B) (a + b) := by
  intro n hn
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rcases Nat.lt_or_ge a x.1 with h | h
  · rw [hA _ h, zero_mul]
  · rw [hB _ (by omega), mul_zero]

theorem DegLE.pow {A : ℚ⟦X⟧} {a : ℕ} (hA : DegLE A a) (n : ℕ) : DegLE (A ^ n) (n * a) := by
  induction n with
  | zero =>
    intro m hm; rw [pow_zero, coeff_one]; simp; omega
  | succ n ih =>
    rw [pow_succ, show (n + 1) * a = n * a + a by ring]; exact ih.mul hA

theorem DegLE.mono {A : ℚ⟦X⟧} {a b : ℕ} (hA : DegLE A a) (h : a ≤ b) : DegLE A b :=
  fun n hn => hA n (by omega)

theorem degLE_one_sub_X_sq : DegLE (1 - X ^ 2 : ℚ⟦X⟧) 2 := by
  intro n hn
  rw [map_sub, coeff_one, coeff_X_pow]
  simp [show n ≠ 0 by omega, show n ≠ 2 by omega]

/-! ## The series $W_1$ and $D = W_1 / \Phi$ over `ℚ` -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- The ring hom `ℤ[X] → ℚ⟦X⟧`. -/
abbrev φZ : Polynomial ℤ →+* ℚ⟦X⟧ := ι.comp Polynomial.coeToPowerSeries.ringHom

theorem φZ_X : φZ (Polynomial.X) = X := by simp

theorem coeff_φZ (P : Polynomial ℤ) (n : ℕ) : coeff n (φZ P) = (P.coeff n : ℚ) := by
  simp [coeff_map]

/-- The data $W_1$, $K$ with $(1+X)^p - 1 - X^p = pW_1 = \Phi K$. -/
theorem exists_series (h5 : 5 ≤ p) : ∃ W D : ℚ⟦X⟧,
    (1 + X) ^ p = 1 + X ^ p + C (p : ℚ) * W ∧ W = (1 + X + X ^ 2) * D ∧ X ∣ W ∧
    PI p W ∧ PI p D ∧ DegLE D (p - 3) := by
  obtain ⟨W, K, hW, hK, hW0, hWd, hKd⟩ := exists_W_K hp.out h5
  have hW' := congrArg φZ hW
  have hK' := congrArg φZ hK
  simp only [map_sub, map_pow, map_add, map_one, φZ_X, map_mul] at hW' hK'
  have hC : φZ (Polynomial.C (p : ℤ)) = C (p : ℚ) := by
    ext n; rw [coeff_φZ, Polynomial.coeff_C, coeff_C]; split_ifs <;> simp
  rw [hC] at hW'
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hCC : C (p : ℚ) * C (p : ℚ)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hp0, map_one]
  set Dq := C (p : ℚ)⁻¹ * φZ K with hDq
  have hWD : φZ W = (1 + X + X ^ 2) * Dq := by
    have : C (p : ℚ) * φZ W = C (p : ℚ) * ((1 + X + X ^ 2) * Dq) := by
      rw [← hW', hK', hDq]; linear_combination (-(1 + X + X ^ 2) * φZ K) * hCC
    exact mul_left_cancel₀ (by intro h; have := congrArg (coeff 0) h; simp [hp0] at this) this
  -- Φ is invertible over ℚ with integer inverse
  have hΦinv : (1 + X + X ^ 2 : ℚ⟦X⟧) * ι (invOfUnit Φ 1) = 1 := by
    have h := congrArg ι (mul_invOfUnit Φ 1 (by simp))
    have e : ι Φ = 1 + X + X ^ 2 := by simp [Φ]
    rw [map_mul, map_one, e] at h
    exact h
  have hD : Dq = φZ W * ι (invOfUnit Φ 1) := by
    rw [hWD, mul_comm (1 + X + X ^ 2 : ℚ⟦X⟧), mul_assoc, hΦinv, mul_one]
  have hPIW : PI p (φZ W) := fun n => by rw [coeff_φZ]; exact padicNorm.of_int _
  refine ⟨φZ W, Dq, ?_, hWD, ?_, hPIW, ?_, ?_⟩
  · linear_combination hW'
  · rw [← pow_one X, X_pow_dvd_iff]
    intro m hm; obtain rfl : m = 0 := by omega
    rw [coeff_φZ, hW0]; simp
  · rw [hD]; exact hPIW.mul (PI.map_int _)
  · intro n hn
    rw [hDq, coeff_C_mul, coeff_φZ, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

end

end

/-! ## The truncated logarithm -/

section

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

theorem Inv1_eq_rescale : Inv1 = rescale (-1 : ℚ) (mk 1) := by
  ext n; simp [Inv1, coeff_rescale]

theorem coeff_Inv1_pow (h k : ℕ) :
    coeff k (Inv1 ^ (h + 1)) = (-1 : ℚ) ^ k * ((h + k).choose h : ℚ) := by
  rw [Inv1_eq_rescale, ← map_pow, mk_one_pow_eq_mk_choose_add, coeff_rescale, coeff_mk]

theorem PI_coeff_le_of_dvd {m j : ℕ} (h : j ∣ m) :
    padicNorm p (m : ℚ) ≤ padicNorm p (j : ℚ) := by
  obtain ⟨q, rfl⟩ := h
  push_cast
  rw [padicNorm.mul]
  calc padicNorm p (j : ℚ) * padicNorm p (q : ℚ) ≤ padicNorm p (j : ℚ) * 1 :=
        mul_le_mul_of_nonneg_left (padicNorm.of_nat q) (padicNorm.nonneg _)
    _ = _ := mul_one _

/-- $j \mid h!\binom{h+k}{h}$ when $j = k + i$ with $1 \le i \le h$. -/
theorem dvd_factorial_mul_choose {h k i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) :
    (k + i) ∣ h.factorial * (h + k).choose h := by
  have e : (h + k).choose h * h.factorial * k.factorial = (h + k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := h + k) (k := h) (by omega)
    rwa [show h + k - h = k by omega] at this
  have d1 : (k + i) * k.factorial ∣ (k + i).factorial := by
    obtain ⟨m, hm⟩ : ∃ m, k + i = m + 1 := ⟨k + i - 1, by omega⟩
    rw [hm, Nat.factorial_succ]
    exact Nat.mul_dvd_mul_left _ (Nat.factorial_dvd_factorial (by omega))
  have d2 : (k + i).factorial ∣ (h + k).factorial := Nat.factorial_dvd_factorial (by omega)
  have d3 : (k + i) * k.factorial ∣ (h.factorial * (h + k).choose h) * k.factorial := by
    rw [show h.factorial * (h + k).choose h * k.factorial = (h + k).factorial by rw [← e]; ring]
    exact d1.trans d2
  exact Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos k) d3

section LemmaA

variable {W D : ℚ⟦X⟧}

/-- $Y = W_1 / (1 + X^p)$. -/
def Yof (p : ℕ) [Fact p.Prime] (W : ℚ⟦X⟧) : ℚ⟦X⟧ := W * expand p hp0 Inv1

/-- $(1+X)^p / (1+X^p)$ as a unit. -/
def EY (p : ℕ) [Fact p.Prime] : ℚ⟦X⟧ˣ := ιU onePlusXu ^ p * exU p hp0 (ιU onePlusXu)⁻¹

theorem expand_one_add_X_mul_Inv1 : (1 + X ^ p) * expand p hp0 Inv1 = 1 := by
  have := congrArg (expand p hp0) one_add_X_mul_Inv1
  rwa [map_mul, map_add, map_one, expand_X] at this

theorem val_EY (hW1 : (1 + X) ^ p = 1 + X ^ p + C (p : ℚ) * W) :
    (EY p : ℚ⟦X⟧) = 1 + C (p : ℚ) * Yof p W := by
  rw [EY, Units.val_mul, Units.val_pow_eq_pow_val, val_onePlusXq, val_exU, ← map_inv,
    val_onePlusXq_inv, hW1, Yof]
  linear_combination (expand_one_add_X_mul_Inv1 (p := p))

theorem theta_V₁ (h5 : 5 ≤ p) : theta (V₁ p) = Λ₁ - expand p hp0 Λ₁ :=
  theta_Vof p hp0 _ (coeff_Λ₁_mul h5)

theorem hasLD_EY (h5 : 5 ≤ p) : HasLD (EY p) (C (p : ℚ) * theta (V₁ p)) := by
  refine ((hasLD_onePlusXq.pow p).mul (hasLD_onePlusXq.inv.expand p hp0)).congr ?_
  rw [theta_V₁ h5, map_neg, map_natCast]; ring

theorem theta_Yof (h5 : 5 ≤ p) (hW1 : (1 + X) ^ p = 1 + X ^ p + C (p : ℚ) * W) :
    theta (Yof p W) = theta (V₁ p) * (1 + C (p : ℚ) * Yof p W) := by
  have h := hasLD_EY (p := p) h5
  unfold HasLD at h
  rw [val_EY hW1, theta_add, theta_one, zero_add, theta_C_mul] at h
  have hp0' : (C (p : ℚ) : ℚ⟦X⟧) ≠ 0 := by
    intro h0; have := congrArg (coeff 0) h0
    simp [hp.out.ne_zero] at this
  apply mul_left_cancel₀ hp0'
  rw [h]; ring

/-- The truncated logarithm $L_H = \sum_{h < H} \frac{(-1)^h p^h}{h+1} Y^{h+1}$. -/
def LH (p : ℕ) [Fact p.Prime] (W : ℚ⟦X⟧) (H : ℕ) : ℚ⟦X⟧ :=
  ∑ h ∈ range H, C ((-1 : ℚ) ^ h * (p : ℚ) ^ h / ((h + 1 : ℕ) : ℚ)) * Yof p W ^ (h + 1)

theorem theta_LH (H : ℕ) :
    theta (LH p W H) = theta (Yof p W) * ∑ h ∈ range H, (-(C (p : ℚ)) * Yof p W) ^ h := by
  rw [LH, theta_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [theta_C_mul, theta_pow]
  have e1 : (-(C (p : ℚ)) * Yof p W) ^ h = C ((-1 : ℚ) ^ h * (p : ℚ) ^ h) * Yof p W ^ h := by
    rw [mul_pow, map_mul, map_pow, map_pow, map_neg, map_one, neg_pow]
  have e : C ((-1 : ℚ) ^ h * (p : ℚ) ^ h / ((h + 1 : ℕ) : ℚ)) * ((h + 1 : ℕ) : ℚ⟦X⟧) =
      C ((-1 : ℚ) ^ h * (p : ℚ) ^ h) := by
    rw [← map_natCast (C (R := ℚ)), ← map_mul]; congr 1; field_simp
  rw [e1]
  linear_combination (Yof p W ^ h * theta (Yof p W)) * e

theorem X_dvd_Yof (hX : X ∣ W) : X ∣ Yof p W := Dvd.dvd.mul_right hX _

theorem X_pow_dvd_V₁_sub_LH (h5 : 5 ≤ p) (hW1 : (1 + X) ^ p = 1 + X ^ p + C (p : ℚ) * W)
    (hX : X ∣ W) (H : ℕ) : X ^ (H + 1) ∣ V₁ p - LH p W H := by
  have hEY := val_EY (p := p) hW1
  have hinv : (EY p : ℚ⟦X⟧) * ((EY p)⁻¹ : ℚ⟦X⟧ˣ) = 1 := Units.mul_inv _
  have hgeom := geom_sum_mul_neg (-(C (p : ℚ)) * Yof p W) H
  have hθ : theta (V₁ p - LH p W H) =
      0 * (V₁ p - LH p W H) +
        theta (Yof p W) * (-(C (p : ℚ)) * Yof p W) ^ H * ((EY p)⁻¹ : ℚ⟦X⟧ˣ) := by
    rw [theta_sub, theta_LH, zero_mul, zero_add]
    have hY := theta_Yof h5 hW1
    rw [hEY] at hinv
    linear_combination (-(∑ h ∈ range H, (-(C (p : ℚ)) * Yof p W) ^ h +
        (-(C (p : ℚ)) * Yof p W) ^ H * ((EY p)⁻¹ : ℚ⟦X⟧ˣ).val)) * hY
      + (-theta (V₁ p)) * hgeom + (-theta (V₁ p) * (-(C (p : ℚ)) * Yof p W) ^ H) * hinv
  apply X_pow_dvd_of_theta hθ (dvd_zero _)
  · rw [pow_succ']
    apply Dvd.dvd.mul_right
    exact mul_dvd_mul (X_dvd_theta _) (pow_dvd_pow_of_dvd (Dvd.dvd.mul_left (X_dvd_Yof hX) _) H)
  · have h1 : X ∣ V₁ p := X_dvd_Vof p Λ₁
    have h2 : X ∣ LH p W H := Finset.dvd_sum fun h _ =>
      Dvd.dvd.mul_left (dvd_pow (X_dvd_Yof hX) (by omega)) _
    obtain ⟨u, hu⟩ := dvd_sub h1 h2
    rw [hu]; simp

end LemmaA

end

end

/-! ## Lemma A -/

section

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

theorem degLE_Φq : DegLE (1 + X + X ^ 2 : ℚ⟦X⟧) 2 := by
  intro n hn
  rw [map_add, map_add, coeff_one, coeff_X, coeff_X_pow]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega]

/-- The bound for one term of the double sum in Lemma A. -/
theorem lemmaA_term (h5 : 5 ≤ p) {h k i : ℕ} {c : ℚ} (hc : padicNorm p c ≤ 1)
    (hi1 : 1 ≤ i) (hih : i ≤ h) :
    padicNorm p ((-1 : ℚ) ^ h * (p : ℚ) ^ h / ((h + 1 : ℕ) : ℚ) *
      (((-1 : ℚ) ^ k * ((h + k).choose h : ℚ)) * c)) ≤
      padicNorm p (p : ℚ) * padicNorm p ((k + i : ℕ) : ℚ) := by
  set A := padicNorm p (p : ℚ)
  set N1 := padicNorm p ((h + 1 : ℕ) : ℚ)
  set Fh := padicNorm p (h.factorial : ℚ)
  set B := padicNorm p ((h + k).choose h : ℚ)
  set J := padicNorm p ((k + i : ℕ) : ℚ)
  have hm1 : ∀ n : ℕ, padicNorm p ((-1 : ℚ) ^ n) = 1 := fun n => by
    rw [padicNorm_pow, padicNorm.neg, padicNorm.one, one_pow]
  have hA0 : 0 ≤ A := padicNorm.nonneg _
  have hB0 : 0 ≤ B := padicNorm.nonneg _
  have hN1 : 0 < N1 := by
    have : ((h + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero h)
    exact lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero this).symm
  have hFB : Fh * B ≤ J := by
    have := PI_coeff_le_of_dvd (p := p) (dvd_factorial_mul_choose (k := k) hi1 hih)
    rwa [Nat.cast_mul, padicNorm.mul] at this
  have hF : A ^ (h - 1) ≤ N1 * Fh := by
    have := norm_p_pow_le_norm_factorial (p := p) h5 (t := h + 1) (by omega)
    rwa [show h + 1 - 2 = h - 1 by omega, Nat.factorial_succ, Nat.cast_mul,
      padicNorm.mul] at this
  rw [padicNorm.mul, padicNorm.div, padicNorm.mul, hm1, one_mul, padicNorm_pow, padicNorm.mul,
    padicNorm.mul, hm1, one_mul]
  have hAh : A ^ h = A * A ^ (h - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc A ^ h / N1 * (B * padicNorm p c) ≤ A ^ h / N1 * B :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hB0 hc) (by positivity)
    _ = A * A ^ (h - 1) / N1 * B := by rw [hAh]
    _ ≤ A * (N1 * Fh) / N1 * B := by gcongr
    _ = A * (Fh * B) := by field_simp
    _ ≤ A * J := mul_le_mul_of_nonneg_left hFB hA0

/-- **Lemma A.** $|[X^{pj}](Q V_1)|_p \le |p|_p\,|j|_p$. -/
theorem lemmaA (h5 : 5 ≤ p) (j : ℕ) :
    padicNorm p (coeff (p * j) (Qq * V₁ p)) ≤ padicNorm p p * padicNorm p j := by
  obtain ⟨W, D, hW1, hWD, hX, hPW, hPD, hDd⟩ := exists_series (p := p) h5
  have h0 : 0 ≤ padicNorm p (p : ℚ) * padicNorm p (j : ℚ) :=
    mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)
  have hWdeg : DegLE W (p - 1) := by
    rw [hWD]; exact (degLE_Φq.mul hDd).mono (by omega)
  have htr := X_pow_dvd_V₁_sub_LH h5 hW1 hX (p * j)
  rw [coeff_mul_eq_of_X_pow_dvd _ htr, LH, Finset.mul_sum, map_sum]
  refine padicNorm.sum_le' (fun h _ => ?_) h0
  set a : ℚ := (-1 : ℚ) ^ h * (p : ℚ) ^ h / ((h + 1 : ℕ) : ℚ)
  have hterm : coeff (p * j) (Qq * (C a * Yof p W ^ (h + 1))) =
      a * ∑ x ∈ antidiagonal j,
        coeff x.1 (Inv1 ^ (h + 1)) * coeff (p * x.2) (Qq * W ^ (h + 1)) := by
    rw [show Qq * (C a * Yof p W ^ (h + 1)) =
        C a * (expand p hp0 (Inv1 ^ (h + 1)) * (Qq * W ^ (h + 1))) by
          rw [Yof, mul_pow, map_pow]; ring,
      coeff_C_mul, coeff_p_mul_expand_mul]
  rw [hterm, Finset.mul_sum]
  refine padicNorm.sum_le' (fun x hx => ?_) h0
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  -- the polynomial `P = Q W^(h+1)`
  have hPeq : Qq * W ^ (h + 1) = (1 - X ^ 2) * D * W ^ h := by
    rw [pow_succ', ← mul_assoc, hWD, ← mul_assoc, Qq_mul_Φq, ← hWD]
  have hPdeg : DegLE (Qq * W ^ (h + 1)) (2 + (p - 3) + h * (p - 1)) := by
    rw [hPeq]; exact (degLE_one_sub_X_sq.mul hDd).mul (hWdeg.pow h)
  have hPX : X ∣ Qq * W ^ (h + 1) := Dvd.dvd.mul_left (dvd_pow hX (by omega)) _
  have hPI : PI p (Qq * W ^ (h + 1)) := PI_Qq.mul (hPW.pow _)
  rw [coeff_Inv1_pow, ← hx']
  by_cases hi : x.2 = 0 ∨ h + 1 ≤ x.2
  · have hz : coeff (p * x.2) (Qq * W ^ (h + 1)) = 0 := by
      rcases hi with hi | hi
      · rw [hi, mul_zero]; exact coeff_eq_zero_of_X_pow_dvd (k := 1) (by simpa using hPX) one_pos
      · apply hPdeg
        have h1 : p * (h + 1) ≤ p * x.2 := Nat.mul_le_mul_left p hi
        have h2 : h * (p - 1) ≤ h * p := Nat.mul_le_mul_left h (by omega)
        have h3 : h * p = p * h := mul_comm _ _
        have h4 : p * (h + 1) = p * h + p := by ring
        omega
    rw [hz, mul_zero, mul_zero, padicNorm.zero]
    exact mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)
  · rw [not_or, not_le] at hi
    exact lemmaA_term h5 (hPI _) (by omega) (by omega)

end

end

/-! ## The tower -/

/-- **Bala's general clause.** For every prime $p \ge 5$, every positive integer $r$, every
integer $s$ and all positive integers $n$ and $k$:
$a(r,s;np^k) \equiv a(r,s;np^{k-1}) \pmod{p^{2k}}$. -/
theorem a_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (2 * k) ∣ a r s (n * p ^ k) - a r s (n * p ^ (k - 1)) := by
  have := Fact.mk hp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set M := n * p ^ k'
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
    (pow_ne_zero _ hp.ne_zero))
  have hNk : n * p ^ (k' + 1) = p * M := by simp only [M]; ring
  rw [hNk, show k' + 1 - 1 = k' by omega]
  have h := main_estimate h5 (lemmaA h5) r s M (by omega) hM
  have hM' : padicNorm p (M : ℚ) ≤ padicNorm p p ^ k' := by
    simp only [M]; push_cast
    rw [padicNorm.mul, padicNorm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (padicNorm.nonneg _) _) (padicNorm.of_nat n)
  have hle : padicNorm p ((a r s (p * M) - a r s M : ℤ) : ℚ) ≤
      (p : ℚ) ^ (-((2 * (k' + 1) : ℕ) : ℤ)) := by
    calc _ ≤ padicNorm p ((p : ℚ) * M) ^ 2 := h
      _ = (padicNorm p p * padicNorm p M) ^ 2 := by rw [padicNorm.mul]
      _ ≤ (padicNorm p p * padicNorm p p ^ k') ^ 2 := by
          have h0 : 0 ≤ padicNorm p (p : ℚ) * padicNorm p (M : ℚ) :=
            mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)
          exact pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left hM' (padicNorm.nonneg _)) 2
      _ = padicNorm p p ^ (2 * (k' + 1)) := by rw [← pow_succ', ← pow_mul]; ring_nf
      _ = (p : ℚ) ^ (-((2 * (k' + 1) : ℕ) : ℤ)) := by
          rw [padicNorm.padicNorm_p_of_prime, zpow_neg, zpow_natCast, inv_pow]
  have := (padicNorm.dvd_iff_norm_le (p := p) (n := 2 * (k' + 1))).mpr hle
  exact_mod_cast this

/-- A333472 is the case $r = s = 1$. -/
theorem A333472_eq (m : ℕ) : A333472 m = a 1 1 m := by
  simp [A333472, a, Fzpow]

/-- **Bala's conjecture on A333472.** For every prime $p \ge 5$ and all positive integers $n$
and $k$: $a(np^k) \equiv a(np^{k-1}) \pmod{p^{2k}}$. -/
theorem a333472_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (2 * k) ∣ A333472 (n * p ^ k) - A333472 (n * p ^ (k - 1)) := by
  rw [A333472_eq, A333472_eq]
  exact a_tower p hp h5 1 one_pos 1 n k hn hk

/-! ## Sanity checks: the first terms $1, 1, 3, 13$ of A333472 -/

/-- $a(m+1) = [W^{m+1}]\,(1 - W^2)(1+W)^{m+1}\Phi^m$, from the Lagrange formula. -/
theorem A333472_eq_coeff (m : ℕ) :
    A333472 (m + 1) = coeff (m + 1) ((1 - X ^ 2) * (1 + X) ^ (m + 1) * (1 + X + X ^ 2) ^ m) := by
  rw [A333472_eq, a_eq_coeff_Qz 1 1 (m + 1) le_rfl (by omega), Qz, Gz, one_mul]
  congr 1
  rw [mul_pow, Units.val_mul, ← zpow_natCast, ← zpow_mul, one_mul, zpow_natCast, pow_one,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  simp only [onePlusXu, Φu, Units.val_mk]
  rw [pow_succ (1 + X + X ^ 2 : ℤ⟦X⟧) m]
  have h := mul_invOfUnit Φ 1 (by simp)
  linear_combination (1 - X ^ 2) * (1 + X) ^ (m + 1) * (1 + X + X ^ 2) ^ m * h

theorem A333472_zero : A333472 0 = 1 := by
  simp [A333472]

theorem A333472_one : A333472 1 = 1 := by
  rw [A333472_eq_coeff 0]
  rw [show (1 - X ^ 2) * (1 + X) ^ (0 + 1) * (1 + X + X ^ 2) ^ 0 =
    (1 + X - X ^ 2 - X ^ 3 : ℤ⟦X⟧) by ring]
  simp [coeff_X_pow, coeff_X, coeff_one]

theorem A333472_two : A333472 2 = 3 := by
  rw [A333472_eq_coeff 1]
  rw [show (1 - X ^ 2) * (1 + X) ^ (1 + 1) * (1 + X + X ^ 2) ^ 1 =
    (1 + C 3 * X + C 3 * X ^ 2 - C 3 * X ^ 4 - C 3 * X ^ 5 - X ^ 6 : ℤ⟦X⟧) by
      simp only [map_ofNat]; ring]
  simp [coeff_X_pow, coeff_X, coeff_one]

theorem A333472_three : A333472 3 = 13 := by
  rw [A333472_eq_coeff 2]
  rw [show (1 - X ^ 2) * (1 + X) ^ (2 + 1) * (1 + X + X ^ 2) ^ 2 =
    (1 + C 5 * X + C 11 * X ^ 2 + C 13 * X ^ 3 + C 6 * X ^ 4 - C 6 * X ^ 5 - C 13 * X ^ 6
      - C 11 * X ^ 7 - C 5 * X ^ 8 - X ^ 9 : ℤ⟦X⟧) by
      simp only [map_ofNat]; ring]
  simp [coeff_X_pow, coeff_X, coeff_one]

end OeisA333472

end
