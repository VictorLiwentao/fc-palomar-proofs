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
# Hanna's power-coefficient parity conjectures (OEIS A292877 and seven relatives)

For $m \in \mathbb{Z}$ let $T_m \in \mathbb{Z}[[x]]$ be the Fuss–Catalan series,
$T_m = 1 + x T_m^m$. This file proves that the families `IsFamilyI` and `IsFamilyII` have
exactly one solution, whose coefficients are integers congruent to those of $T_m$ modulo $2$
(`familyI_integral_mod_two`, `familyII_integral_mod_two`; family (II) needs $2E_N \mid R_N$).
It then proves the parity conjectures of Paul D. Hanna for A292877 (all three), A303562,
A303563, A171791, A230218, A263075, A263190 (conjecture (3)) and A371673, with existence,
uniqueness and integrality of each sequence. Write $\theta = x\,d/dx$.

1. **Formula (1)** (`coeff_U1_zpow`). For $A(0) = 1$, $N \ge 1$ and $E \in \mathbb{Z}$,
   $[x^N] A^E = [x^N] (A \bmod x^N)^E + E\, a(N)$. Write $A = u(1 + y)$ with $y = x^N D/u$;
   then $(1 + y)^E \equiv 1 + E y$ modulo $y^2$, by induction on $E$ (`dvd_zpow_one_add`).
2. **Existence and uniqueness** (`existsUnique`). Since $E_N \ne 0$ for $N \ge 2$, formula (1)
   turns the conditions into a causal fixed-point equation, which has exactly one solution.
3. **Integrality** (`integral`). From $\theta(B^E) = E\,(\theta B/B)\,B^E$ we get
   $N\,[x^N] B^E = E\,[x^N](\theta B/B)\,B^E$, so $E \mid [x^N] B^E$ for every
   $B \in 1 + x\mathbb{Z}[[x]]$ when $\gcd(E, N) = 1$ (`dvd_coeff_zpow`). In both families
   $E_N \equiv \pm 1 \pmod N$, and $E_N \mid R_N$. Formula (1) and induction on $N$ give
   $a(N) \in \mathbb{Z}$.
4. **Comparison modulo 2** (`parity`). If $B \equiv T \pmod 2$ and $E = 2^s w$ with $w$ odd,
   then $B^E \equiv T^E \pmod{2^{s+1}}$ (`two_pow_dvd_zpow_sub`). Apply formula (1) to $A$ and to
   the series $B$ that agrees with $A$ below $N$ and with $T$ from $N$ on. By induction on $N$,
   $a(N) \equiv t(N) \pmod 2$ follows from (H2): $2E_N$ divides
   $M_N([x^N] T^{E_N} - R_N)$ for some odd $M_N$.
5. **Lagrange inversion** (`lagrange`, `coeff_Tm_zpow`). $T_m = 1 + W$, where $W$ is the
   compositional inverse (Mathlib's `substInvOfIsUnit`) of $f(w) = w(1 + w)^{-m}$, so
   $T_m(f(w)) = 1 + w$ and $T_m = 1 + x T_m^m$ (`Tm_eq`). For every $P$,
   $[x^N] P = [w^N]\, P(f(w))\,(1 - (m-1)w)(1 + w)^{mN - 1}$. The residues vanish by the
   absorption identity $j\,[w^j](1 - (m-1)w)(1+w)^{r-1} = (r - mj)\,[w^{j-1}](1+w)^{r-1}$
   (`absorb`), which follows from $\theta (1+w)^r = r w (1+w)^{r-1}$. Hence
   $N\,[x^N] T_m^E = E\,[w^{N-1}](1 + w)^{E + mN - 1}$. The coefficients of $(1+w)^q$ are
   `Ring.choose q n`, through Mathlib's `binomialSeries`.
6. **(H2)** (`H2`, `hT_EI`, `hT_EII`). In family (I), $E + mN - 1 = -(N^2 - N + 2)$; in family
   (II), $E + mN - 1 = N^2$. In both cases $[w^{N-1}](1+w)^{E+mN-1} = \pm\binom{N^2}{N-1}$. With
   $(N^2 - N + 1)\binom{N^2}{N-1} = N\binom{N^2}{N}$ and Lucas' theorem, which makes
   $\binom{N^2}{N}$ even for $N \ge 2$ (`two_dvd_choose_sq`), this gives
   $2E \mid (N^2 - N + 1)\,[x^N] T_m^E$. In family (II) also $2E_N \mid R_N$.
7. **$T_m$ modulo 2** (`coeff_Tm_mod_two`). The equation $\sigma = 1 + x\sigma^m$ has at most one
   solution over every ring (`eq_of_funEq`). Over $\mathbb{F}_2$ the Frobenius identity
   $G(x)^2 = G(x^2)$ checks the solutions: $\sum_k x^{2^k - 1}$ for $m = 2$; the Fibbinary
   series $F$, from $F = F^2 + xF^4$, for $m = 3$; $\sum_k x^{(4^k-1)/3}$ for $m = 4$;
   $1 + \sum_k x^{2^k}$, from $\sigma^2 = \sigma + x$, for $m = -1$; and $1 + xF^2$, from
   $\sigma^2(\sigma - 1) = x$, for $m = -2$.
8. **The entries.** With $N = n - 1$ where Hanna writes $[x^{n-1}]$, A303563, A292877 and A303562
   are family (I) with $m = 2, 3, 4$, A230218 is family (II) with $m = -1$, and A171791,
   A263075, A263190 and A371673 are family (II) with $m = -2$. For the last three,
   $2(N+1)^2 \mid R_N$; for A371673 this uses that the Catalan number $C_N$ is even for even
   $N \ge 2$. For A292877 (3), the number $c(n)$ of Fibbinary numbers below $2^n$ satisfies
   $c(n+2) = c(n+1) + c(n)$, so $c(n) = F(n+2)$ and $F(n+3) - F(n+2) = F(n+1)$.

The method combines Lagrange inversion, Lucas' theorem and the Frobenius map of
$\mathbb{F}_2[[x]]$.

*References:*
- Paul D. Hanna, [A292877](https://oeis.org/A292877), September 25, 2017.
- Paul D. Hanna, [A303562](https://oeis.org/A303562) and [A303563](https://oeis.org/A303563),
  April 27, 2018.
- Paul D. Hanna, [A171791](https://oeis.org/A171791), January 24, 2010 (conjecture of
  October 9, 2013).
- Paul D. Hanna, [A230218](https://oeis.org/A230218), October 11, 2013.
- Paul D. Hanna, [A263075](https://oeis.org/A263075), October 8, 2015, and
  [A263190](https://oeis.org/A263190), October 12, 2015.
- Paul D. Hanna, [A371673](https://oeis.org/A371673), April 2, 2024.
- [A003714](https://oeis.org/A003714), the Fibbinary numbers.
- I. M. Gessel, *Lagrange inversion*, J. Combin. Theory Ser. A 144 (2016).
- É. Lucas, *Théorie des fonctions numériques simplement périodiques*, Amer. J. Math. 1 (1878).
-/

@[expose] public section

namespace OeisA292877

open PowerSeries

/-- Fibbinary numbers (OEIS A003714): no two adjacent `1`s in binary. -/
def Fibbinary (n : ℕ) : Prop := n &&& (n >>> 1) = 0

/-- Integer powers in `ℚ⟦X⟧`: `A^k` for `k ≥ 0` and `(A^{-k})⁻¹` for `k < 0`. For `A(0) = 1`
this is the power in the group of units. -/
noncomputable def zpowQ (A : ℚ⟦X⟧) (k : ℤ) : ℚ⟦X⟧ :=
  if 0 ≤ k then A ^ k.toNat else (A ^ k.natAbs)⁻¹

/-- Integer powers in `ℤ⟦X⟧`: `T^k` for `k ≥ 0` and `(T^{-1})^{-k}` for `k < 0`, where
`invOfUnit T 1` is the inverse of `T` when `T(0) = 1`. -/
noncomputable def zpowZ (T : ℤ⟦X⟧) (k : ℤ) : ℤ⟦X⟧ :=
  if 0 ≤ k then T ^ k.toNat else invOfUnit T 1 ^ k.natAbs

/-- `T` is the Fuss–Catalan series $T_m$: $T(0) = 1$ and $T = 1 + x T^m$. -/
def IsFussCatalan (m : ℤ) (T : ℤ⟦X⟧) : Prop :=
  constantCoeff T = 1 ∧ T = 1 + X * zpowZ T m

/-- Family (I): $a(0) = a(1) = 1$ and $[x^N] A^{-(N^2 + (m-1)N + 1)} = 0$ for $N \ge 2$. -/
def IsFamilyI (m : ℤ) (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ coeff 1 A = 1 ∧
    ∀ N : ℕ, 2 ≤ N → coeff N (zpowQ A (-((N : ℤ) ^ 2 + (m - 1) * N + 1))) = 0

/-- Family (II): $a(0) = a(1) = 1$ and $[x^N] A^{N^2 - mN + 1} = R_N$ for $N \ge 2$. -/
def IsFamilyII (m : ℤ) (R : ℕ → ℤ) (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ coeff 1 A = 1 ∧
    ∀ N : ℕ, 2 ≤ N → coeff N (zpowQ A ((N : ℤ) ^ 2 - m * N + 1)) = R N

/-- OEIS A292877: $a(0) = a(1) = 1$ and $[x^{n-1}]\, 1/A(x)^{n^2} = 0$ for $n > 2$. -/
def IsA292877 (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ coeff 1 A = 1 ∧ ∀ n : ℕ, 2 < n → coeff (n - 1) ((A ^ (n ^ 2))⁻¹) = 0

/-- OEIS A303562: $a(0) = a(1) = 1$ and $[x^{n-1}]\, 1/A(x)^{n^2+n-1} = 0$ for $n > 2$. -/
def IsA303562 (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ coeff 1 A = 1 ∧
    ∀ n : ℕ, 2 < n → coeff (n - 1) ((A ^ (n ^ 2 + n - 1))⁻¹) = 0

/-- OEIS A303563: $a(0) = a(1) = 1$ and $[x^{n-1}]\, 1/A(x)^{n^2-n+1} = 0$ for $n > 2$. -/
def IsA303563 (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ coeff 1 A = 1 ∧
    ∀ n : ℕ, 2 < n → coeff (n - 1) ((A ^ (n ^ 2 - n + 1))⁻¹) = 0

/-- OEIS A171791: $a(0) = a(1) = 1$ and $[x^n]\, A(x)^{(n+1)^2} = 0$ for $n > 1$. -/
def IsA171791 (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ coeff 1 A = 1 ∧ ∀ n : ℕ, 1 < n → coeff n (A ^ ((n + 1) ^ 2)) = 0

/-- OEIS A230218: $a(0) = a(1) = 1$ and $[x^n]\, A(x)^{n^2+n+1} = 0$ for $n > 1$. -/
def IsA230218 (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ coeff 1 A = 1 ∧ ∀ n : ℕ, 1 < n → coeff n (A ^ (n ^ 2 + n + 1)) = 0

/-- OEIS A263075: $[x^{n-1}]\, A(x)^{n^2} = n^n (n-1)!$ for $n \ge 1$. -/
def IsA263075 (A : ℚ⟦X⟧) : Prop :=
  ∀ n : ℕ, 1 ≤ n → coeff (n - 1) (A ^ (n ^ 2)) = ((n ^ n * (n - 1).factorial : ℕ) : ℚ)

/-- OEIS A263190: $[x^{n-1}]\, A(x)^{n^2} = (n!)^2$ for $n \ge 1$. -/
def IsA263190 (A : ℚ⟦X⟧) : Prop :=
  ∀ n : ℕ, 1 ≤ n → coeff (n - 1) (A ^ (n ^ 2)) = ((n.factorial ^ 2 : ℕ) : ℚ)

/-- OEIS A371673: $[x^{n-1}]\, A(x)^{n^2} = C_{n-1}\, n^n$ for $n \ge 1$, with $C_k$ the
Catalan numbers (OEIS A000108). -/
def IsA371673 (A : ℚ⟦X⟧) : Prop :=
  ∀ n : ℕ, 1 ≤ n → coeff (n - 1) (A ^ (n ^ 2)) = ((catalan (n - 1) * n ^ n : ℕ) : ℚ)

end OeisA292877

namespace OeisA292877

open PowerSeries

/-! ## The Euler operator and logarithmic derivatives

Adapted from this repository's A333472 package, generalized from `ℚ` to any commutative ring. -/

section Theta

variable {R : Type*} [CommRing R]

/-- The Euler operator $\theta = X \frac{d}{dX}$. -/
noncomputable def theta (A : R⟦X⟧) : R⟦X⟧ := mk fun n => (n : R) * coeff n A

@[simp] theorem coeff_theta (A : R⟦X⟧) (n : ℕ) : coeff n (theta A) = n * coeff n A := by
  simp [theta]

theorem theta_one : theta (1 : R⟦X⟧) = 0 := by
  ext n; simp only [coeff_theta, coeff_one, map_zero]; split_ifs with h <;> simp [h]

theorem theta_X : theta (X : R⟦X⟧) = X := by
  ext n; simp only [coeff_theta, coeff_X]; split_ifs with h <;> simp [h]

theorem theta_add (A B : R⟦X⟧) : theta (A + B) = theta A + theta B := by
  ext n; simp [mul_add]

theorem theta_mul (A B : R⟦X⟧) : theta (A * B) = theta A * B + A * theta B := by
  ext n
  simp only [coeff_theta, map_add, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx]; push_cast; ring

/-- Logarithmic derivative: `θ u = L * u`. -/
def HasLD (u : R⟦X⟧ˣ) (L : R⟦X⟧) : Prop := theta (u : R⟦X⟧) = L * u

theorem HasLD.mul {u v : R⟦X⟧ˣ} {L M : R⟦X⟧} (hu : HasLD u L) (hv : HasLD v M) :
    HasLD (u * v) (L + M) := by
  unfold HasLD at *
  rw [Units.val_mul, theta_mul, hu, hv]; ring

theorem HasLD.inv {u : R⟦X⟧ˣ} {L : R⟦X⟧} (hu : HasLD u L) : HasLD u⁻¹ (-L) := by
  unfold HasLD at *
  set i : R⟦X⟧ := ↑u⁻¹ with hi_def
  have hu1 : (u : R⟦X⟧) * i = 1 := Units.mul_inv u
  have hi : i * (u : R⟦X⟧) = 1 := Units.inv_mul u
  have h1 : theta ((u : R⟦X⟧) * i) = 0 := by rw [hu1, theta_one]
  rw [theta_mul, hu] at h1
  linear_combination i * h1 - theta i * hi - L * i * hu1

theorem HasLD.pow {u : R⟦X⟧ˣ} {L : R⟦X⟧} (hu : HasLD u L) (n : ℕ) :
    HasLD (u ^ n) ((n : R⟦X⟧) * L) := by
  induction n with
  | zero => unfold HasLD; simp [theta_one]
  | succ n ih =>
    have := ih.mul hu
    rw [← pow_succ] at this
    unfold HasLD at *
    rw [this]; push_cast; ring

theorem HasLD.zpow {u : R⟦X⟧ˣ} {L : R⟦X⟧} (hu : HasLD u L) (k : ℤ) :
    HasLD (u ^ k) ((k : R⟦X⟧) * L) := by
  rcases k with n | n
  · simpa using hu.pow n
  · rw [zpow_negSucc]
    have := (hu.pow (n + 1)).inv
    unfold HasLD at *
    rw [this, Int.cast_negSucc]; push_cast; ring

/-- Every unit has a logarithmic derivative. -/
theorem hasLD_self (u : R⟦X⟧ˣ) : HasLD u (theta (u : R⟦X⟧) * ↑u⁻¹) := by
  unfold HasLD
  rw [mul_assoc, Units.inv_mul, mul_one]

end Theta

/-! ## Units with constant term `1` and the perturbation formula -/

section Units

variable {R : Type*} [CommRing R]

/-- The series `f` with its constant coefficient replaced by `1`. -/
noncomputable def one1 (f : R⟦X⟧) : R⟦X⟧ := 1 + (f - C (constantCoeff f))

@[simp] theorem constantCoeff_one1 (f : R⟦X⟧) : constantCoeff (one1 f) = 1 := by
  simp [one1]

theorem coeff_one1 (f : R⟦X⟧) {n : ℕ} (hn : n ≠ 0) : coeff n (one1 f) = coeff n f := by
  simp [one1, coeff_one, coeff_C, hn]

theorem one1_eq (f : R⟦X⟧) (h : constantCoeff f = 1) : one1 f = f := by
  simp [one1, h]

/-- The unit `one1 f`. -/
noncomputable def U1 (f : R⟦X⟧) : R⟦X⟧ˣ :=
  ⟨one1 f, invOfUnit (one1 f) 1, mul_invOfUnit _ _ (by simp), invOfUnit_mul _ _ (by simp)⟩

@[simp] theorem val_U1 (f : R⟦X⟧) : (U1 f : R⟦X⟧) = one1 f := rfl

theorem constantCoeff_zpow_of_one (u : R⟦X⟧ˣ) (hu : constantCoeff (u : R⟦X⟧) = 1) (k : ℤ) :
    constantCoeff ((u ^ k : R⟦X⟧ˣ) : R⟦X⟧) = 1 := by
  have h1 : Units.map (constantCoeff (R := R)).toMonoidHom u = 1 := by
    ext; simpa using hu
  have := congrArg (fun w : Rˣ => (w : R)) (congrArg (· ^ k) h1)
  simpa [← map_zpow] using this

theorem map_U1 {S : Type*} [CommRing S] (φ : R →+* S) (f : R⟦X⟧) :
    Units.map (map φ).toMonoidHom (U1 f) = U1 (map φ f) := by
  ext n
  rcases n with _ | n
  · simp [one1, ← coeff_zero_eq_constantCoeff_apply, -coeff_zero_eq_constantCoeff, coeff_map]
  · simp [one1, coeff_one, coeff_map]

theorem coeff_U1_zpow_map {S : Type*} [CommRing S] (φ : R →+* S) (f : R⟦X⟧) (k : ℤ) (n : ℕ) :
    coeff n ((U1 (map φ f) ^ k : S⟦X⟧ˣ) : S⟦X⟧) = φ (coeff n ((U1 f ^ k : R⟦X⟧ˣ) : R⟦X⟧)) := by
  rw [← map_U1, ← map_zpow, Units.coe_map]
  simp [coeff_map]

/-- Congruences modulo `d` pass to integer powers of units. -/
theorem dvd_zpow_sub {S : Type*} [CommRing S] {d : S} {u v : Sˣ} (h : d ∣ (u : S) - v) (k : ℤ) :
    d ∣ ((u ^ k : Sˣ) : S) - ((v ^ k : Sˣ) : S) := by
  set q := Ideal.Quotient.mk (Ideal.span {d})
  have key : Units.map q.toMonoidHom u = Units.map q.toMonoidHom v := by
    ext
    simp only [Units.coe_map]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)
  have := congrArg (fun w => ((w ^ k : (S ⧸ Ideal.span {d})ˣ) : S ⧸ Ideal.span {d})) key
  simp only [← map_zpow, Units.coe_map] at this
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp this)

/-- If `d ∣ y ^ 2` and `w = 1 + y`, then `w ^ k ≡ 1 + k y` modulo `d`. -/
theorem dvd_zpow_one_add {S : Type*} [CommRing S] {d y : S} (hy : d ∣ y ^ 2) (w : Sˣ)
    (hw : (w : S) = 1 + y) (k : ℤ) : d ∣ ((w ^ k : Sˣ) : S) - (1 + k * y) := by
  have hi : ((w⁻¹ : Sˣ) : S) * (1 + y) = 1 := by rw [← hw, Units.inv_mul]
  have step_up : ∀ k : ℤ, d ∣ ((w ^ k : Sˣ) : S) - (1 + k * y) →
      d ∣ ((w ^ (k + 1) : Sˣ) : S) - (1 + (k + 1 : ℤ) * y) := by
    intro k ih
    have e : ((w ^ (k + 1) : Sˣ) : S) - (1 + (k + 1 : ℤ) * y) =
        (((w ^ k : Sˣ) : S) - (1 + k * y)) * (1 + y) + k * y ^ 2 := by
      rw [zpow_add_one, Units.val_mul, hw]; push_cast; ring
    rw [e]
    exact dvd_add (Dvd.dvd.mul_right ih _) (Dvd.dvd.mul_left hy _)
  have step_down : ∀ k : ℤ, d ∣ ((w ^ k : Sˣ) : S) - (1 + k * y) →
      d ∣ ((w ^ (k - 1) : Sˣ) : S) - (1 + (k - 1 : ℤ) * y) := by
    intro k ih
    set i : S := ((w⁻¹ : Sˣ) : S)
    have e : ((w ^ (k - 1) : Sˣ) : S) - (1 + (k - 1 : ℤ) * y) =
        (((w ^ k : Sˣ) : S) - (1 + k * y)) * i + y ^ 2 * (i - k + k * y * i) := by
      rw [zpow_sub_one, Units.val_mul]
      push_cast
      linear_combination (1 + ((k : S) - 1) * y - (k : S) * y ^ 2) * hi
    rw [e]
    exact dvd_add (Dvd.dvd.mul_right ih _) (Dvd.dvd.mul_right hy _)
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => exact step_up _ ih
  | pred n ih => exact step_down _ ih

theorem coeff_X_pow_mul_self (N : ℕ) (F : R⟦X⟧) : coeff N (X ^ N * F) = constantCoeff F := by
  rw [coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]

theorem coeff_eq_zero_of_X_pow_dvd {n k : ℕ} {A : R⟦X⟧} (h : X ^ k ∣ A) (hn : n < k) :
    coeff n A = 0 :=
  X_pow_dvd_iff.mp h n hn

/-- **Perturbation.** If `v = u + X^N D` with `u(0) = 1` and `N ≥ 1`, then
`[X^N] v^k = [X^N] u^k + k D(0)` for every `k ∈ ℤ`. -/
theorem coeff_zpow_perturb {N : ℕ} (hN : 1 ≤ N) (u v : R⟦X⟧ˣ)
    (hu : constantCoeff (u : R⟦X⟧) = 1) (D : R⟦X⟧) (hv : (v : R⟦X⟧) = (u : R⟦X⟧) + X ^ N * D)
    (k : ℤ) :
    coeff N ((v ^ k : R⟦X⟧ˣ) : R⟦X⟧) =
      coeff N ((u ^ k : R⟦X⟧ˣ) : R⟦X⟧) + k * constantCoeff D := by
  set i : R⟦X⟧ := ((u⁻¹ : R⟦X⟧ˣ) : R⟦X⟧)
  set y : R⟦X⟧ := X ^ N * (D * i)
  have hw : ((u⁻¹ * v : R⟦X⟧ˣ) : R⟦X⟧) = 1 + y := by
    rw [Units.val_mul, hv]
    simp only [y, i]
    rw [mul_add, Units.inv_mul]; ring
  have hy : (X : R⟦X⟧) ^ (N + 1) ∣ y ^ 2 := by
    refine ⟨X ^ (N - 1) * (D * i) ^ 2, ?_⟩
    simp only [y]
    rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
    congr 2; omega
  obtain ⟨Z, hZ⟩ := dvd_zpow_one_add hy _ hw k
  have hvk : ((v ^ k : R⟦X⟧ˣ) : R⟦X⟧) =
      ((u ^ k : R⟦X⟧ˣ) : R⟦X⟧) * (1 + (k : R⟦X⟧) * y + X ^ (N + 1) * Z) := by
    have e : v ^ k = u ^ k * (u⁻¹ * v) ^ k := by rw [← mul_zpow, mul_inv_cancel_left]
    rw [e, Units.val_mul]; congr 1; linear_combination hZ
  have hik : constantCoeff i = 1 := by
    have := constantCoeff_zpow_of_one u hu (-1)
    simpa [i] using this
  rw [hvk]
  have e : ((u ^ k : R⟦X⟧ˣ) : R⟦X⟧) * (1 + (k : R⟦X⟧) * y + X ^ (N + 1) * Z) =
      ((u ^ k : R⟦X⟧ˣ) : R⟦X⟧) + C (k : R) * (X ^ N * (((u ^ k : R⟦X⟧ˣ) : R⟦X⟧) * D * i)) +
        X ^ (N + 1) * (((u ^ k : R⟦X⟧ˣ) : R⟦X⟧) * Z) := by
    simp only [y, map_intCast]; ring
  rw [e, map_add, map_add, coeff_C_mul, coeff_X_pow_mul_self,
    coeff_eq_zero_of_X_pow_dvd (dvd_mul_right _ _) (Nat.lt_succ_self N), add_zero]
  simp [constantCoeff_zpow_of_one u hu k, hik]

/-- Formula (1): `[X^N] f^k = [X^N] (f mod X^N)^k + k [X^N] f`, after normalizing `f(0) = 1`. -/
theorem coeff_U1_zpow (f : R⟦X⟧) {N : ℕ} (hN : 1 ≤ N) (k : ℤ) :
    coeff N ((U1 f ^ k : R⟦X⟧ˣ) : R⟦X⟧) =
      coeff N ((U1 (trunc N f : R⟦X⟧) ^ k : R⟦X⟧ˣ) : R⟦X⟧) + k * coeff N f := by
  have hv : ((U1 f : R⟦X⟧ˣ) : R⟦X⟧) =
      ((U1 (trunc N f : R⟦X⟧) : R⟦X⟧ˣ) : R⟦X⟧) + X ^ N * mk fun j => coeff (N + j) f := by
    ext n
    simp only [val_U1, map_add, coeff_X_pow_mul', coeff_mk]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [coeff_zero_eq_constantCoeff_apply, show ¬ N ≤ 0 by omega]
    · rw [coeff_one1 _ hn.ne', coeff_one1 _ hn.ne', Polynomial.coeff_coe, coeff_trunc]
      by_cases h : n < N
      · simp [h, show ¬ N ≤ n by omega]
      · simp [h, show N ≤ n by omega, show N + (n - N) = n by omega]
  rw [coeff_zpow_perturb hN _ _ (by simp) _ hv k]
  simp

/-- Truncations below `N` agree when the coefficients below `N` agree. -/
theorem trunc_congr {f g : R⟦X⟧} {N : ℕ} (h : ∀ k < N, coeff k f = coeff k g) :
    trunc N f = trunc N g := by
  ext k
  simp only [coeff_trunc]
  split_ifs with hk
  · exact h k hk
  · rfl

end Units

section Fix

variable {R : Type*} [CommRing R]

/-! The causal fixed-point construction below is copied from this repository's A318008
package. -/

/-- Coefficient `n` of `T f` depends only on the coefficients of `f` below `n`. -/
def Causal (T : R⟦X⟧ → R⟦X⟧) : Prop :=
  ∀ n f g, (∀ k < n, coeff k f = coeff k g) → coeff n (T f) = coeff n (T g)

theorem Causal.eq {T : R⟦X⟧ → R⟦X⟧} (hT : Causal T) {f g : R⟦X⟧} (hf : T f = f)
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

theorem Causal.fix_eq {T : R⟦X⟧ → R⟦X⟧} (hT : Causal T) : T (fix T) = fix T := by
  ext n
  conv_rhs => rw [fix, coeff_mk, fixSeq]
  apply hT
  intro k hk
  simp [fix, hk]

end Fix

/-! ## Existence, uniqueness, integrality and the comparison modulo `2` -/

section Engine

/-- The condition `a(0) = a(1) = 1` and `[x^N] A^{E_N} = R_N` for `N ≥ 2`. -/
def Sat (E R : ℕ → ℤ) (A : ℚ⟦X⟧) : Prop :=
  coeff 0 A = 1 ∧ coeff 1 A = 1 ∧ ∀ N, 2 ≤ N → coeff N ((U1 A ^ E N : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = R N

/-- The operator whose fixed points are the solutions of `Sat E R`. -/
noncomputable def Op (E R : ℕ → ℤ) (f : ℚ⟦X⟧) : ℚ⟦X⟧ := mk fun N =>
  if N < 2 then 1 else
    ((R N : ℚ) - coeff N ((U1 (trunc N f : ℚ⟦X⟧) ^ E N : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) / E N

theorem Op_causal (E R : ℕ → ℤ) : Causal (Op E R) := by
  intro n f g h
  simp only [Op, coeff_mk, trunc_congr h]

variable {E R : ℕ → ℤ}

theorem sat_iff (hE : ∀ N, 2 ≤ N → E N ≠ 0) (A : ℚ⟦X⟧) : Sat E R A ↔ Op E R A = A := by
  constructor
  · rintro ⟨h0, h1, h⟩
    ext N
    simp only [Op, coeff_mk]
    split_ifs with hN
    · interval_cases N <;> simp_all
    · have := h N (by omega)
      rw [coeff_U1_zpow A (by omega)] at this
      have hE' : (E N : ℚ) ≠ 0 := by exact_mod_cast hE N (by omega)
      rw [div_eq_iff hE']
      linear_combination -this
  · intro hA
    have hc : ∀ N, coeff N A = coeff N (Op E R A) := fun N => by rw [hA]
    refine ⟨by simpa [Op] using hc 0, by simpa [Op] using hc 1, fun N hN => ?_⟩
    have := hc N
    simp only [Op, coeff_mk, show ¬ N < 2 by omega, ↓reduceIte] at this
    rw [coeff_U1_zpow A (by omega)]
    have hE' : (E N : ℚ) ≠ 0 := by exact_mod_cast hE N (by omega)
    rw [this]
    field_simp
    ring

theorem existsUnique (hE : ∀ N, 2 ≤ N → E N ≠ 0) : ∃! A : ℚ⟦X⟧, Sat E R A :=
  ⟨fix (Op E R), (sat_iff hE _).mpr (Op_causal E R).fix_eq,
    fun _ hA => (Op_causal E R).eq ((sat_iff hE _).mp hA) (Op_causal E R).fix_eq⟩

/-- `k ∣ [X^N] B^k` when `k` and `N` are coprime, by `N [X^N] B^k = k [X^N] (θB/B) B^k`. -/
theorem dvd_coeff_zpow (B : ℤ⟦X⟧ˣ) (k : ℤ) (N : ℕ) (h : IsCoprime k N) :
    k ∣ coeff N ((B ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  have hL := (hasLD_self B).zpow k
  unfold HasLD at hL
  have := congrArg (coeff N) hL
  rw [coeff_theta, ← map_intCast (C (R := ℤ)), mul_assoc, coeff_C_mul] at this
  exact h.dvd_of_dvd_mul_left ⟨_, this⟩

/-- The cast `ℤ → ℚ`. -/
abbrev ιq : ℤ →+* ℚ := Int.castRingHom ℚ

theorem integral (hE : ∀ N, 2 ≤ N → IsCoprime (E N) (N : ℤ) ∧ E N ∣ R N) {A : ℚ⟦X⟧}
    (hA : Sat E R A) (n : ℕ) : ∃ z : ℤ, coeff n A = z := by
  induction n using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 2 with hN | hN
    · interval_cases N
      · exact ⟨1, by simp [hA.1]⟩
      · exact ⟨1, by simp [hA.2.1]⟩
    classical
    set b : ℕ → ℤ := fun k => if h : k < N then (ih k h).choose else 0
    have hb : map ιq (mk b) = (trunc N A : ℚ⟦X⟧) := by
      ext k
      simp only [coeff_map, coeff_mk, Polynomial.coeff_coe, coeff_trunc, b]
      split_ifs with hk
      · exact (ih k hk).choose_spec.symm
      · simp
    have h1 := hA.2.2 N hN
    rw [coeff_U1_zpow A (by omega), ← hb, coeff_U1_zpow_map] at h1
    obtain ⟨hcop, hdvd⟩ := hE N hN
    obtain ⟨q, hq⟩ := dvd_coeff_zpow (U1 (mk b)) (E N) N hcop
    obtain ⟨r, hr⟩ := hdvd
    refine ⟨r - q, ?_⟩
    have hE0 : (E N : ℚ) ≠ 0 := by
      have : E N ≠ 0 := by
        rintro h0
        rw [h0, isCoprime_zero_left, Int.isUnit_iff] at hcop
        omega
      exact_mod_cast this
    rw [hq, hr] at h1
    simp only [map_mul, eq_intCast] at h1
    apply mul_left_cancel₀ hE0
    push_cast at h1 ⊢
    linear_combination h1

theorem two_pow_dvd_pow_sub {S : Type*} [CommRing S] {x y : S} (h : (2 : S) ∣ x - y) (s : ℕ) :
    (2 : S) ^ (s + 1) ∣ x ^ (2 ^ s) - y ^ (2 ^ s) := by
  induction s with
  | zero => simpa using h
  | succ s ih =>
    have e : x ^ 2 ^ (s + 1) - y ^ 2 ^ (s + 1) =
        (x ^ 2 ^ s - y ^ 2 ^ s) * ((x ^ 2 ^ s - y ^ 2 ^ s) + 2 * y ^ 2 ^ s) := by
      rw [pow_succ, pow_mul, pow_mul]; ring
    rw [e, pow_succ]
    refine mul_dvd_mul ih (dvd_add ((dvd_pow_self 2 (by omega)).trans ih) (dvd_mul_right _ _))

/-- Lemma 2: if `u ≡ v (mod 2)`, then `u^{2^s w} ≡ v^{2^s w} (mod 2^{s+1})`. -/
theorem two_pow_dvd_zpow_sub {S : Type*} [CommRing S] {u v : Sˣ} (h : (2 : S) ∣ (u : S) - v)
    (s : ℕ) (w : ℤ) :
    (2 : S) ^ (s + 1) ∣ ((u ^ (2 ^ s * w) : Sˣ) : S) - ((v ^ (2 ^ s * w) : Sˣ) : S) := by
  have h1 := dvd_zpow_sub h w
  have e : ∀ x : Sˣ, x ^ (2 ^ s * w) = (x ^ w) ^ (2 ^ s : ℕ) := fun x => by
    rw [mul_comm, zpow_mul, ← zpow_natCast]; push_cast; rfl
  rw [e u, e v, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact two_pow_dvd_pow_sub h1 s

theorem dvd_coeff_of_C_dvd {c : ℤ} {F : ℤ⟦X⟧} (h : C c ∣ F) (n : ℕ) : c ∣ coeff n F := by
  obtain ⟨G, rfl⟩ := h
  rw [coeff_C_mul]; exact dvd_mul_right _ _

theorem C_dvd_of_dvd_coeff {c : ℤ} {F : ℤ⟦X⟧} (h : ∀ n, c ∣ coeff n F) : C c ∣ F := by
  classical
  refine ⟨mk fun n => (h n).choose, ?_⟩
  ext n
  rw [coeff_C_mul, coeff_mk]
  exact (h n).choose_spec

theorem isCoprime_two_of_odd {M : ℤ} (hM : Odd M) (s : ℕ) : IsCoprime ((2 : ℤ) ^ s) M := by
  obtain ⟨t, rfl⟩ := hM
  exact IsCoprime.pow_left ⟨-t, 1, by ring⟩

/-- Theorem 7: comparison with `T` modulo `2`. -/
theorem parity (hE : ∀ N, 2 ≤ N → E N ≠ 0) {A : ℚ⟦X⟧} (hA : Sat E R A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (T : ℤ⟦X⟧) (hT0 : constantCoeff T = 1) (hT1 : coeff 1 T = 1)
    (hT : ∀ N, 2 ≤ N → ∃ M : ℤ, Odd M ∧
      2 * E N ∣ M * (coeff N ((U1 T ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - R N)) (n : ℕ) :
    2 ∣ a n - coeff n T := by
  have ha0 : a 0 = 1 := by have := ha 0; rw [hA.1] at this; exact_mod_cast this.symm
  have ha1 : a 1 = 1 := by have := ha 1; rw [hA.2.1] at this; exact_mod_cast this.symm
  induction n using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 2 with hN | hN
    · interval_cases N
      · simp [ha0, coeff_zero_eq_constantCoeff_apply, hT0]
      · simp [ha1, hT1]
    have hAz : map ιq (mk a) = A := by ext k; simp [ha k]
    set B : ℤ⟦X⟧ := mk fun k => if k < N then a k else coeff k T
    have htr : trunc N (mk a) = trunc N B := trunc_congr fun k hk => by simp [B, hk]
    have e1 := coeff_U1_zpow (mk a) (show 1 ≤ N by omega) (E N)
    have e2 := coeff_U1_zpow B (show 1 ≤ N by omega) (E N)
    rw [htr] at e1
    have hR : coeff N ((U1 (mk a) ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = R N := by
      have := hA.2.2 N hN
      rw [← hAz, coeff_U1_zpow_map, eq_intCast] at this
      exact_mod_cast this
    have hBT : (2 : ℤ⟦X⟧) ∣ ((U1 B : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - ((U1 T : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
      have : (2 : ℤ⟦X⟧) = C 2 := by simp
      rw [this]
      refine C_dvd_of_dvd_coeff fun k => ?_
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [coeff_zero_eq_constantCoeff_apply]
      · rw [val_U1, val_U1, map_sub, coeff_one1 _ hk.ne', coeff_one1 _ hk.ne']
        simp only [B, coeff_mk]
        split_ifs with hkN
        · exact ih k hkN
        · simp
    obtain ⟨s, w, hw, hsw⟩ : ∃ s : ℕ, ∃ w : ℤ, Odd w ∧ E N = 2 ^ s * w := by
      obtain ⟨s, w', hw', h'⟩ := Nat.exists_eq_two_pow_mul_odd (n := (E N).natAbs)
        (by simpa using hE N hN)
      refine ⟨s, (E N).sign * w', ?_, ?_⟩
      · rcases Int.sign_trichotomy (E N) with h | h | h
        · rw [h, one_mul]; exact_mod_cast hw'.natCast
        · exact absurd (Int.sign_eq_zero_iff_zero.mp h) (hE N hN)
        · rw [h, neg_one_mul, odd_neg]; exact hw'.natCast
      · rw [mul_left_comm, ← Nat.cast_ofNat, ← Nat.cast_pow, ← Nat.cast_mul, ← h',
          Int.sign_mul_natAbs]
    have hL2' : (C ((2 : ℤ) ^ (s + 1)) : ℤ⟦X⟧) ∣
        ((U1 B ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - ((U1 T ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
      rw [hsw, map_pow, map_ofNat]
      exact two_pow_dvd_zpow_sub hBT s w
    have hL2 := dvd_coeff_of_C_dvd hL2' N
    rw [map_sub] at hL2
    obtain ⟨M, hM, hMd⟩ := hT N hN
    have hTR : (2 : ℤ) ^ (s + 1) ∣ coeff N ((U1 T ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - R N := by
      have h2 : (2 : ℤ) ^ (s + 1) ∣ M * (coeff N ((U1 T ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - R N) :=
        (show (2 : ℤ) ^ (s + 1) ∣ 2 * E N from ⟨w, by rw [hsw]; ring⟩).trans hMd
      exact (isCoprime_two_of_odd hM (s + 1)).dvd_of_dvd_mul_left h2
    have hmain : (2 : ℤ) ^ (s + 1) ∣ E N * (a N - coeff N T) := by
      have e3 : E N * (a N - coeff N T) =
          (coeff N ((U1 (mk a) ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - R N) -
            (coeff N ((U1 B ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) -
              coeff N ((U1 T ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)) -
            (coeff N ((U1 T ^ E N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - R N) := by
        rw [e1, e2]
        simp only [B, coeff_mk, lt_irrefl, ↓reduceIte, Int.cast_id]
        ring
      rw [e3, hR, sub_self, zero_sub]
      exact dvd_sub (dvd_neg.mpr hL2) hTR
    have h4 : (2 : ℤ) ^ s * 2 ∣ 2 ^ s * (w * (a N - coeff N T)) := by
      rw [← pow_succ, ← mul_assoc, ← hsw]; exact hmain
    have h5 := (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ s ≠ 0)).mp h4
    exact (by simpa using isCoprime_two_of_odd hw 1 : IsCoprime (2 : ℤ) w).dvd_of_dvd_mul_left h5

end Engine

end OeisA292877

namespace OeisA292877

open PowerSeries Finset

/-! ## The Fuss–Catalan series and Lagrange inversion

The Lagrange extraction follows the proof of `lagrange` in this repository's A333472
package. -/

section Lagrange

/-- `1 + X` as a unit of `ℤ⟦X⟧`. -/
noncomputable def u1 : ℤ⟦X⟧ˣ := U1 (1 + X)

@[simp] theorem val_u1 : (u1 : ℤ⟦X⟧) = 1 + X := one1_eq _ (by simp)

theorem binomialSeries_one : binomialSeries ℤ (1 : ℤ) = (1 + X : ℤ⟦X⟧) := by
  simpa using binomialSeries_nat (A := ℤ) (R := ℤ) 1

/-- `(1 + X)^q` is the binomial series. -/
theorem val_u1_zpow (q : ℤ) : ((u1 ^ q : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = binomialSeries ℤ q := by
  have up : ∀ q : ℤ, ((u1 ^ q : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = binomialSeries ℤ q →
      ((u1 ^ (q + 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = binomialSeries ℤ (q + 1) := by
    intro q h
    rw [zpow_add_one, Units.val_mul, h, val_u1, binomialSeries_add, binomialSeries_one]
  have down : ∀ q : ℤ, ((u1 ^ q : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = binomialSeries ℤ q →
      ((u1 ^ (q - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = binomialSeries ℤ (q - 1) := by
    intro q h
    have e : binomialSeries ℤ q = binomialSeries ℤ (q - 1) * (1 + X) := by
      rw [← binomialSeries_one, ← binomialSeries_add, sub_add_cancel]
    rw [zpow_sub_one, Units.val_mul, h, e, mul_assoc, ← val_u1, Units.mul_inv, mul_one]
  induction q using Int.induction_on with
  | zero => simp
  | succ n ih => exact up _ ih
  | pred n ih => exact down _ ih

theorem coeff_u1_zpow (q : ℤ) (n : ℕ) :
    coeff n ((u1 ^ q : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = Ring.choose q n := by
  rw [val_u1_zpow, binomialSeries_coeff, smul_eq_mul, mul_one]

theorem hasLD_u1 : HasLD u1 (X * ((u1⁻¹ : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)) := by
  unfold HasLD
  rw [mul_assoc, Units.inv_mul, mul_one, val_u1, theta_add, theta_one, theta_X, zero_add]

theorem theta_u1_zpow (r : ℤ) :
    theta ((u1 ^ r : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = C r * (X * ((u1 ^ (r - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)) := by
  have := hasLD_u1.zpow r
  unfold HasLD at this
  rw [this, zpow_sub_one, Units.val_mul,
    show (r : ℤ⟦X⟧) = C r by rw [← map_intCast (C (R := ℤ)) r, Int.cast_id]]
  ring

/-- Absorption: `j [X^j] (1 - (m-1)X)(1+X)^{r-1} = (r - m j) [X^{j-1}] (1+X)^{r-1}`. -/
theorem absorb (m r : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    (j : ℤ) * coeff j ((1 - C (m - 1) * X) * ((u1 ^ (r - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)) =
      (r - m * j) * coeff (j - 1) ((u1 ^ (r - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  have hr : ((u1 ^ r : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = ((u1 ^ (r - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) * (1 + X) := by
    rw [← val_u1, ← Units.val_mul, ← zpow_add_one, sub_add_cancel]
  have e : (1 - C (m - 1) * X) * ((u1 ^ (r - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) =
      ((u1 ^ r : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - C m * (X * ((u1 ^ (r - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)) := by
    rw [hr, map_sub, map_one]; ring
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 := congrArg (coeff (i + 1)) (theta_u1_zpow r)
  rw [coeff_theta, coeff_C_mul, coeff_succ_X_mul] at h1
  rw [e, map_sub, mul_sub, h1, coeff_C_mul, coeff_succ_X_mul, Nat.add_sub_cancel]
  push_cast; ring

variable (m : ℤ)

/-- `f(W) = W (1 + W)^{-m}`, the compositional inverse of `T_m - 1`. -/
noncomputable def fL : ℤ⟦X⟧ := X * ((u1 ^ (-m) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)

theorem constantCoeff_fL : constantCoeff (fL m) = 0 := by simp [fL]

theorem coeff_one_fL : coeff 1 (fL m) = 1 := by
  rw [fL, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_zpow_of_one _ (by simp)]

theorem isUnit_coeff_one_fL : IsUnit (coeff 1 (fL m)) := by
  rw [coeff_one_fL]; exact isUnit_one

theorem hasSubst_fL : HasSubst (fL m) := HasSubst.of_constantCoeff_zero' (constantCoeff_fL m)

/-- The compositional inverse of `fL m`. -/
noncomputable def Wm : ℤ⟦X⟧ := substInvOfIsUnit (fL m) (isUnit_coeff_one_fL m)

/-- The Fuss–Catalan series `T_m = 1 + W`, the solution of `T = 1 + X T^m`. -/
noncomputable def Tm : ℤ⟦X⟧ := 1 + Wm m

theorem hasSubst_Wm : HasSubst (Wm m) := HasSubst.substInvOfIsUnit (fL m) (isUnit_coeff_one_fL m)

theorem constantCoeff_Tm : constantCoeff (Tm m) = 1 := by
  simp [Tm, Wm]

theorem val_U1_Tm : ((U1 (Tm m) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = Tm m := one1_eq _ (constantCoeff_Tm m)

theorem Tm_subst : substAlgHom (hasSubst_fL m) (Tm m) = 1 + X := by
  rw [Tm, map_add, map_one, coe_substAlgHom, Wm,
    subst_substInvOfIsUnit_left _ (constantCoeff_fL m)]

/-- The functional equation `T_m = 1 + X T_m^m`. -/
theorem Tm_eq : Tm m = 1 + X * ((U1 (Tm m) ^ m : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  set σ : ℤ⟦X⟧ →ₐ[ℤ] ℤ⟦X⟧ := substAlgHom (hasSubst_Wm m)
  have hu : Units.map σ.toMonoidHom u1 = U1 (Tm m) := by
    ext1
    rw [Units.coe_map, val_U1_Tm, val_u1]
    change σ (1 + X) = Tm m
    rw [map_add, map_one, substAlgHom_X, Tm]
  have h := subst_substInvOfIsUnit_right (fL m) (constantCoeff_fL m) (isUnit_coeff_one_fL m)
  rw [← Wm, ← coe_substAlgHom (hasSubst_Wm m), fL, map_mul, substAlgHom_X] at h
  have h2 : σ ((u1 ^ (-m) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = ((U1 (Tm m) ^ (-m) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
    rw [← hu, ← map_zpow, Units.coe_map]; rfl
  rw [h2] at h
  have h3 : X * ((U1 (Tm m) ^ m : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = Wm m := by
    rw [← h, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      mul_one]
  rw [h3, Tm]

/-- The Lagrange kernel `K_N = (1 - (m-1)W)(1+W)^{mN - 1}`. -/
noncomputable def KL (N : ℕ) : ℤ⟦X⟧ := (1 - C (m - 1) * X) * ((u1 ^ (m * N - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)

theorem fL_pow_mul_KL {k N : ℕ} (hk : k ≤ N) :
    fL m ^ k * KL m N =
      X ^ k * ((1 - C (m - 1) * X) * ((u1 ^ (m * ((N - k : ℕ) : ℤ) - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)) := by
  have e : ((u1 ^ (-m) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) ^ k * ((u1 ^ (m * N - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) =
      ((u1 ^ (m * ((N - k : ℕ) : ℤ) - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, ← Units.val_mul, ← zpow_add]
    congr 2
    push_cast [hk]
    ring
  rw [fL, KL, mul_pow, ← e]
  ring

theorem coeff_fL_pow_mul_KL {k N : ℕ} (hk : k ≤ N) :
    coeff N (fL m ^ k * KL m N) = if k = N then 1 else 0 := by
  rw [fL_pow_mul_KL m hk, coeff_X_pow_mul', ite_eq_left hk]
  obtain ⟨j, hj⟩ : ∃ j, N - k = j := ⟨_, rfl⟩
  rw [hj]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [ite_eq_left (by omega), coeff_zero_eq_constantCoeff_apply, map_mul,
      constantCoeff_zpow_of_one _ (by simp)]
    simp
  · rw [ite_eq_right (by omega)]
    have h := absorb m (m * j) j hjpos
    rw [sub_self, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hjpos.ne')

/-- **Lagrange inversion** for `W = X (1 + W)^m`: for every power series `P`,
`[X^N] P = [W^N] P(f(W)) K_N(W)`. -/
theorem lagrange (N : ℕ) (P : ℤ⟦X⟧) :
    coeff N P = coeff N (substAlgHom (hasSubst_fL m) P * KL m N) := by
  set K : ℤ⟦X⟧ := KL m N
  set S : ℤ⟦X⟧ := ∑ k ∈ range (N + 1), coeff k P • X ^ k
  have hcS : ∀ i, i < N + 1 → coeff i S = coeff i P := by
    intro i hi
    simp only [S, map_sum, map_zsmul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [hi]
  obtain ⟨R, hR⟩ : X ^ (N + 1) ∣ P - S := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [map_sub, hcS i hi, sub_self]
  have hP : P = S + X ^ (N + 1) * R := by rw [← hR]; ring
  set φ : ℤ⟦X⟧ →ₐ[ℤ] ℤ⟦X⟧ := substAlgHom (hasSubst_fL m)
  have hφP : φ P = ∑ k ∈ range (N + 1), coeff k P • fL m ^ k + fL m ^ (N + 1) * φ R := by
    conv_lhs => rw [hP]
    simp [S, φ, map_sum, map_pow, substAlgHom_X]
  have htail : coeff N (fL m ^ (N + 1) * φ R * K) = 0 := by
    apply coeff_eq_zero_of_X_pow_dvd _ (Nat.lt_succ_self N)
    rw [fL, mul_pow, mul_assoc, mul_assoc]
    exact Dvd.intro _ rfl
  have hterm : ∀ k ∈ range (N + 1), coeff N (fL m ^ k * K) = if k = N then 1 else 0 := by
    intro k hk
    exact coeff_fL_pow_mul_KL m (by simpa [Nat.lt_succ_iff] using hk)
  rw [hφP, add_mul, map_add, htail, add_zero, Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, map_zsmul]
  rw [Finset.sum_congr rfl fun k hk => by rw [hterm k hk]]
  simp

/-- The coefficient formula `N [x^N] T_m^E = E [W^{N-1}] (1+W)^{E + mN - 1}`. -/
theorem coeff_Tm_zpow (E : ℤ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℤ) * coeff N ((U1 (Tm m) ^ E : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) =
      E * coeff (N - 1) ((u1 ^ (E + m * N - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  have hmap : Units.map (substAlgHom (hasSubst_fL m)).toMonoidHom (U1 (Tm m)) = u1 := by
    ext1
    rw [Units.coe_map, val_u1, val_U1_Tm]
    exact Tm_subst m
  have e : substAlgHom (hasSubst_fL m) ((U1 (Tm m) ^ E : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) =
      ((u1 ^ E : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
    rw [← hmap, ← map_zpow, Units.coe_map]; rfl
  have e2 : ((u1 ^ E : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) * KL m N =
      (1 - C (m - 1) * X) * ((u1 ^ (E + m * N - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
    rw [KL, mul_left_comm, ← Units.val_mul, ← zpow_add, add_sub_assoc]
  rw [lagrange m N, e, e2, absorb m (E + m * N) N hN]
  ring

end Lagrange

/-! ## Lucas' theorem and the parity of `C(N², N)` -/

section Binomial

/-- Lucas: if bit `i` of `k` is `1` and bit `i` of `n` is `0`, then `C(n, k)` is even. -/
theorem two_dvd_choose_of_bit (i : ℕ) : ∀ {n k : ℕ}, (k / 2 ^ i) % 2 = 1 →
    (n / 2 ^ i) % 2 = 0 → 2 ∣ n.choose k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction i with
  | zero =>
    intro n k hk hn
    simp only [pow_zero, Nat.div_one] at hk hn
    have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2)
    rw [hn, hk, Nat.choose_zero_succ, zero_mul] at this
    exact Nat.modEq_zero_iff_dvd.mp this
  | succ i ih =>
    intro n k hk hn
    have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2)
    have h2 : 2 ∣ (n / 2).choose (k / 2) := ih (by rwa [Nat.div_div_eq_div_mul, ← pow_succ'])
      (by rwa [Nat.div_div_eq_div_mul, ← pow_succ'])
    exact Nat.modEq_zero_iff_dvd.mp
      (this.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right h2 _)))

/-- (B1): `C(N², N)` is even for `N ≥ 2`. -/
theorem two_dvd_choose_sq {N : ℕ} (hN : 2 ≤ N) : 2 ∣ (N ^ 2).choose N := by
  rcases Nat.even_or_odd N with he | ho
  · obtain ⟨s, o, ho, hso⟩ := Nat.exists_eq_two_pow_mul_odd (n := N) (by omega)
    have hs : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with rfl | h
      · rw [pow_zero, one_mul] at hso; rw [hso] at he
        exact absurd he (Nat.not_even_iff_odd.mpr ho)
      · exact h
    have hpos : 0 < 2 ^ s := by positivity
    apply two_dvd_choose_of_bit s
    · rw [hso, Nat.mul_div_cancel_left _ hpos]; exact Nat.odd_iff.mp ho
    · rw [hso, show (2 ^ s * o) ^ 2 = 2 ^ s * (2 ^ s * o ^ 2) by ring,
        Nat.mul_div_cancel_left _ hpos]
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      rw [pow_succ]; simp [Nat.mul_mod]
  · obtain ⟨t, o, ho, hto⟩ := Nat.exists_eq_two_pow_mul_odd (n := N - 1) (by omega)
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · rw [pow_zero, one_mul] at hto
        obtain ⟨a, ha⟩ := ho; obtain ⟨b, hb⟩ := ‹Odd N›; omega
      · exact h
    have hpos : 0 < 2 ^ t := by positivity
    have h1 : 1 < 2 ^ t := Nat.one_lt_two_pow (by omega)
    have hNe : N = 2 ^ t * o + 1 := by omega
    apply two_dvd_choose_of_bit t
    · rw [hNe, Nat.mul_add_div hpos, Nat.div_eq_of_lt h1, add_zero]; exact Nat.odd_iff.mp ho
    · rw [hNe, show (2 ^ t * o + 1) ^ 2 = 2 ^ t * (2 ^ t * o ^ 2 + 2 * o) + 1 by ring,
        Nat.mul_add_div hpos, Nat.div_eq_of_lt h1, add_zero]
      obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      rw [pow_succ]; simp [Nat.add_mod, Nat.mul_mod]

end Binomial

/-! ## The comparison hypothesis (H2) -/

section H2

variable (m : ℤ)

/-- The comparison hypothesis (H2) for `T_m`: if `[W^{N-1}] (1+W)^{E+mN-1} = ±C(N², N-1)`, then
`2E` divides `(N² - N + 1) [x^N] T_m^E`. -/
theorem H2 (E : ℤ) {N : ℕ} (hN : 2 ≤ N) (ε : ℤ)
    (hc : coeff (N - 1) ((u1 ^ (E + m * N - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = ε * (N ^ 2).choose (N - 1)) :
    2 * E ∣ ((N : ℤ) ^ 2 - N + 1) * coeff N ((U1 (Tm m) ^ E : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  have h1 := coeff_Tm_zpow m E (show 1 ≤ N by omega)
  rw [hc] at h1
  have h2 := Nat.choose_succ_right_eq (N ^ 2) (N - 1)
  rw [show N - 1 + 1 = N by omega] at h2
  have h2' : ((N ^ 2).choose N : ℤ) * N = ((N ^ 2).choose (N - 1) : ℤ) * ((N : ℤ) ^ 2 - N + 1) := by
    have hle : N - 1 ≤ N ^ 2 := by have := Nat.le_self_pow (n := 2) (by norm_num) N; omega
    have := congrArg (fun x : ℕ => (x : ℤ)) h2
    push_cast [Nat.cast_sub hle, Nat.cast_sub (show 1 ≤ N by omega)] at this
    linear_combination this
  obtain ⟨t, ht⟩ := two_dvd_choose_sq hN
  refine ⟨ε * t, ?_⟩
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  apply mul_left_cancel₀ hN0
  have ht' : ((N ^ 2).choose N : ℤ) = 2 * t := by exact_mod_cast ht
  linear_combination ((N : ℤ) ^ 2 - N + 1) * h1 + E * ε * h2'.symm + E * ε * N * ht'
    - E * ε * N * ht' + E * ε * N * ht'

end H2

end OeisA292877

namespace OeisA292877

open PowerSeries

/-! ## Reduction of `T_m` modulo `2` -/

section Unique

variable {S : Type*} [CommRing S]

/-- The equation `T = 1 + X T^m` has at most one solution over every commutative ring. -/
theorem eq_of_funEq (m : ℤ) {σ σ' : S⟦X⟧} (h : σ = 1 + X * ((U1 σ ^ m : S⟦X⟧ˣ) : S⟦X⟧))
    (h' : σ' = 1 + X * ((U1 σ' ^ m : S⟦X⟧ˣ) : S⟦X⟧)) : σ = σ' := by
  have hc : constantCoeff σ = 1 := by rw [h]; simp
  have hc' : constantCoeff σ' = 1 := by rw [h']; simp
  have key : ∀ n, X ^ n ∣ σ - σ' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : X ^ n ∣ ((U1 σ : S⟦X⟧ˣ) : S⟦X⟧) - ((U1 σ' : S⟦X⟧ˣ) : S⟦X⟧) := by
        rw [val_U1, val_U1, one1_eq _ hc, one1_eq _ hc']; exact ih
      have h2 := dvd_zpow_sub h1 m
      have e : σ - σ' = X * (((U1 σ ^ m : S⟦X⟧ˣ) : S⟦X⟧) - ((U1 σ' ^ m : S⟦X⟧ˣ) : S⟦X⟧)) := by
        linear_combination h - h'
      rw [e, pow_succ']
      exact mul_dvd_mul_left X h2
  ext n
  have := coeff_eq_zero_of_X_pow_dvd (key (n + 1)) (Nat.lt_succ_self n)
  rwa [map_sub, sub_eq_zero] at this

theorem map_Tm_eq (φ : ℤ →+* S) (m : ℤ) :
    map φ (Tm m) = 1 + X * ((U1 (map φ (Tm m)) ^ m : S⟦X⟧ˣ) : S⟦X⟧) := by
  have h := congrArg (map φ) (Tm_eq m)
  rw [map_add, map_one, map_mul, map_X] at h
  rw [← map_U1, ← map_zpow, Units.coe_map]
  exact h

/-- Reduction of `T_m` modulo `2` is the unique solution of `σ = 1 + X σ^m` over `𝔽₂`. -/
theorem coeff_Tm_mod_two (m : ℤ) (σ : (ZMod 2)⟦X⟧)
    (hσ : σ = 1 + X * ((U1 σ ^ m : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧)) (n : ℕ) :
    ((coeff n (Tm m) : ℤ) : ZMod 2) = coeff n σ := by
  rw [← eq_of_funEq m (map_Tm_eq (Int.castRingHom (ZMod 2)) m) hσ, coeff_map]
  rfl

end Unique

/-! ## Explicit solutions over `𝔽₂`

The Frobenius lemma `coeff_sq` follows `coeff_U_sq` of this repository's A318008 package. -/

section F2

theorem two_eq_zero : (2 : (ZMod 2)⟦X⟧) = 0 := by
  rw [show (2 : (ZMod 2)⟦X⟧) = C (2 : ZMod 2) from (map_ofNat C 2).symm,
    show (2 : ZMod 2) = 0 from rfl, map_zero]

/-- Frobenius over `𝔽₂`: `G(x)² = G(x²)`. -/
theorem coeff_sq (G : (ZMod 2)⟦X⟧) (n : ℕ) :
    coeff n (G ^ 2) = if n % 2 = 0 then coeff (n / 2) G else 0 := by
  have h : coeff n (G ^ Fintype.card (ZMod 2)) =
      if Fintype.card (ZMod 2) ∣ n then coeff (n / Fintype.card (ZMod 2)) G else 0 := by
    rw [← FiniteField.PowerSeries.expand_card, coeff_expand]
  rw [ZMod.card] at h
  rw [h]
  simp only [Nat.dvd_iff_mod_eq_zero]

theorem coeff_four (G : (ZMod 2)⟦X⟧) (n : ℕ) :
    coeff n (G ^ 4) = if n % 4 = 0 then coeff (n / 4) G else 0 := by
  rw [show G ^ 4 = (G ^ 2) ^ 2 by ring, coeff_sq, coeff_sq]
  by_cases h : n % 4 = 0
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left h, Nat.div_div_eq_div_mul]
  · rw [ite_eq_right h]
    split_ifs with h1 h2 <;> first | rfl | omega

theorem val_U1_zpow_natCast {R : Type*} [CommRing R] (σ : R⟦X⟧) (hσ : constantCoeff σ = 1)
    (k : ℕ) : ((U1 σ ^ (k : ℤ) : R⟦X⟧ˣ) : R⟦X⟧) = σ ^ k := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val, val_U1, one1_eq _ hσ]

/-- An indicator series over `𝔽₂`. -/
noncomputable def ind (P : ℕ → Prop) : (ZMod 2)⟦X⟧ := by
  classical exact mk fun n => if P n then 1 else 0

theorem coeff_ind (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    coeff n (ind P) = if P n then 1 else 0 := by
  rw [ind, coeff_mk]; congr

theorem constantCoeff_ind {P : ℕ → Prop} (h : P 0) : constantCoeff (ind P) = 1 := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ind, ite_eq_left h]

/-! ### `m = 2`: the support is `{2^k - 1}`. -/

/-- `n = 2^k - 1` for some `k ≥ 0`. -/
def Mers (n : ℕ) : Prop := ∃ k, n = 2 ^ k - 1

theorem mers_zero : Mers 0 := ⟨0, rfl⟩

theorem mers_succ (n : ℕ) : Mers (n + 1) ↔ n % 2 = 0 ∧ Mers (n / 2) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by
      rcases k with _ | k
      · simp at hk
      · omega⟩
    have := Nat.one_le_two_pow (n := j)
    rw [pow_succ] at hk
    exact ⟨by omega, j, by omega⟩
  · rintro ⟨h2, k, hk⟩
    have := Nat.one_le_two_pow (n := k)
    exact ⟨k + 1, by rw [pow_succ]; omega⟩

theorem ind_mers_eq : ind Mers = 1 + X * ind Mers ^ 2 := by
  classical
  ext n
  rcases n with _ | n
  · simp [coeff_ind, mers_zero]
  · rw [map_add, coeff_one, ite_eq_right (by omega), zero_add, coeff_succ_X_mul, coeff_sq,
      coeff_ind, coeff_ind, mers_succ]
    by_cases h : n % 2 = 0 <;> simp [h]

theorem funEq_two :
    ind Mers = 1 + X * ((U1 (ind Mers) ^ (2 : ℤ) : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, val_U1_zpow_natCast _ (constantCoeff_ind mers_zero)]
  exact ind_mers_eq

/-! ### `m = 4`: the support is `{(4^k - 1)/3}`. -/

/-- `n = (4^k - 1)/3` for some `k ≥ 0`. -/
def Quat (n : ℕ) : Prop := ∃ k, n = (4 ^ k - 1) / 3

theorem three_mul_quat (k : ℕ) : 3 * ((4 ^ k - 1) / 3) + 1 = 4 ^ k := by
  have h1 : 3 ∣ 4 ^ k - 1 := by simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
  have h2 := Nat.one_le_pow k 4 (by norm_num)
  rw [Nat.mul_div_cancel' h1]; omega

theorem quat_iff (n : ℕ) : Quat n ↔ ∃ k, 3 * n + 1 = 4 ^ k := by
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k, three_mul_quat k⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := three_mul_quat k
    omega

theorem quat_zero : Quat 0 := ⟨0, rfl⟩

theorem quat_succ (n : ℕ) : Quat (n + 1) ↔ n % 4 = 0 ∧ Quat (n / 4) := by
  rw [quat_iff, quat_iff]
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · simp at hk
    · rw [pow_succ] at hk
      exact ⟨by omega, k, by omega⟩
  · rintro ⟨h4, k, hk⟩
    exact ⟨k + 1, by rw [pow_succ]; omega⟩

theorem funEq_four :
    ind Quat = 1 + X * ((U1 (ind Quat) ^ (4 : ℤ) : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) := by
  classical
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, val_U1_zpow_natCast _ (constantCoeff_ind quat_zero)]
  ext n
  rcases n with _ | n
  · simp [coeff_ind, quat_zero]
  · rw [map_add, coeff_one, ite_eq_right (by omega), zero_add, coeff_succ_X_mul, coeff_four,
      coeff_ind, coeff_ind, quat_succ]
    by_cases h : n % 4 = 0 <;> simp [h]

/-! ### `m = 3`: the support is the Fibbinary numbers. -/

instance : DecidablePred Fibbinary := fun _ => inferInstanceAs (Decidable (_ = _))

theorem fibbinary_iff_bits (n : ℕ) :
    Fibbinary n ↔ ∀ i, ¬ (n.testBit i = true ∧ n.testBit (i + 1) = true) := by
  unfold Fibbinary
  constructor
  · intro h i hi
    have := congrArg (fun x => Nat.testBit x i) h
    simp only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.zero_testBit] at this
    rw [add_comm 1 i, hi.1, hi.2] at this
    simp at this
  · intro h
    apply Nat.zero_of_testBit_eq_false
    intro i
    rw [Nat.testBit_land, Nat.testBit_shiftRight, add_comm 1 i]
    by_contra hc
    simp only [Bool.and_eq_true, Bool.not_eq_false] at hc
    exact h i ⟨by simpa using hc.1, by simpa using hc.2⟩

theorem fibbinary_iff (n : ℕ) : Fibbinary n ↔ n % 4 ≠ 3 ∧ Fibbinary (n / 2) := by
  rw [fibbinary_iff_bits, fibbinary_iff_bits]
  simp only [Nat.testBit_div_two]
  have h0 : n.testBit 0 = true ↔ n % 2 = 1 := by simp [Nat.testBit_zero]
  have h1 : n.testBit 1 = true ↔ (n / 2) % 2 = 1 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, ← Nat.testBit_div_two]; simp [Nat.testBit_zero]
  constructor
  · intro h
    refine ⟨fun h3 => h 0 ⟨h0.mpr (by omega), h1.mpr (by omega)⟩, fun i => h (i + 1)⟩
  · rintro ⟨h3, h⟩ i
    rcases i with _ | i
    · rintro ⟨ha, hb⟩
      have := h0.mp ha; have := h1.mp hb
      omega
    · exact h i

theorem fibbinary_zero : Fibbinary 0 := rfl

theorem fibbinary_two_mul (j : ℕ) : Fibbinary (2 * j) ↔ Fibbinary j := by
  rw [fibbinary_iff, Nat.mul_div_cancel_left j two_pos]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem fibbinary_four_mul_add_one (j : ℕ) : Fibbinary (4 * j + 1) ↔ Fibbinary j := by
  rw [fibbinary_iff, show (4 * j + 1) / 2 = 2 * j by omega, fibbinary_two_mul]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem not_fibbinary_four_mul_add_three (j : ℕ) : ¬ Fibbinary (4 * j + 3) := by
  rw [fibbinary_iff]; omega

theorem ind_fib_eq : ind Fibbinary = ind Fibbinary ^ 2 + X * ind Fibbinary ^ 4 := by
  ext n
  rw [map_add, coeff_sq, coeff_ind, coeff_ind]
  rcases n with _ | n
  · simp [fibbinary_zero]
  rw [coeff_succ_X_mul, coeff_four, coeff_ind]
  obtain ⟨j, hj | hj | hj | hj⟩ : ∃ j, n + 1 = 4 * j ∨ n + 1 = 4 * j + 1 ∨
      n + 1 = 4 * j + 2 ∨ n + 1 = 4 * j + 3 := ⟨(n + 1) / 4, by omega⟩
  · have e : Fibbinary (n + 1) ↔ Fibbinary ((n + 1) / 2) := by
      rw [show n + 1 = 2 * (2 * j) by omega, fibbinary_two_mul,
        show 2 * (2 * j) / 2 = 2 * j by omega]
    simp only [e, show (n + 1) % 2 = 0 by omega, show ¬ (n % 4 = 0) by omega, ↓reduceIte, add_zero]
  · have e : Fibbinary (n + 1) ↔ Fibbinary (n / 4) := by
      rw [show n + 1 = 4 * j + 1 by omega, fibbinary_four_mul_add_one, show n / 4 = j by omega]
    simp only [e, show ¬ ((n + 1) % 2 = 0) by omega, show n % 4 = 0 by omega, ↓reduceIte, zero_add]
  · have e : Fibbinary (n + 1) ↔ Fibbinary ((n + 1) / 2) := by
      rw [show n + 1 = 2 * (2 * j + 1) by omega, fibbinary_two_mul,
        show 2 * (2 * j + 1) / 2 = 2 * j + 1 by omega]
    simp only [e, show (n + 1) % 2 = 0 by omega, show ¬ (n % 4 = 0) by omega, ↓reduceIte, add_zero]
  · have e : ¬ Fibbinary (n + 1) := by
      rw [show n + 1 = 4 * j + 3 by omega]; exact not_fibbinary_four_mul_add_three j
    simp only [e, show ¬ ((n + 1) % 2 = 0) by omega, show ¬ (n % 4 = 0) by omega, ↓reduceIte,
      add_zero]

theorem ind_fib_unit : constantCoeff (ind Fibbinary) = 1 := constantCoeff_ind fibbinary_zero

theorem ind_fib_eq' : ind Fibbinary = 1 + X * ind Fibbinary ^ 3 := by
  set F := ind Fibbinary
  set i : (ZMod 2)⟦X⟧ := (((U1 F)⁻¹ : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧)
  have hinv : i * F = 1 := by
    have := Units.inv_mul (U1 F)
    rwa [val_U1, one1_eq _ ind_fib_unit] at this
  linear_combination (-i) * ind_fib_eq + (1 - F - X * F ^ 3) * hinv - X * F ^ 3 * two_eq_zero

theorem funEq_three :
    ind Fibbinary = 1 + X * ((U1 (ind Fibbinary) ^ (3 : ℤ) : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) := by
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, val_U1_zpow_natCast _ ind_fib_unit]
  exact ind_fib_eq'

/-! ### `m = -1`: the support is `{0} ∪ {2^k}`. -/

/-- `n = 0` or `n = 2^k` for some `k ≥ 0`. -/
def ZeroPow (n : ℕ) : Prop := n = 0 ∨ ∃ k, n = 2 ^ k

theorem zeroPow_two_mul (j : ℕ) : ZeroPow (2 * j) ↔ ZeroPow j := by
  constructor
  · rintro (h | ⟨k, hk⟩)
    · left; omega
    · rcases k with _ | k
      · rw [pow_zero] at hk; omega
      · right; exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro (h | ⟨k, hk⟩)
    · left; omega
    · right; exact ⟨k + 1, by rw [pow_succ]; omega⟩

theorem zeroPow_odd (j : ℕ) : ZeroPow (2 * j + 1) ↔ j = 0 := by
  constructor
  · rintro (h | ⟨k, hk⟩)
    · omega
    · rcases k with _ | k
      · rw [pow_zero] at hk; omega
      · rw [pow_succ] at hk; omega
  · rintro rfl; right; exact ⟨0, rfl⟩

theorem ind_zeroPow_sq : ind ZeroPow ^ 2 = ind ZeroPow + X := by
  classical
  ext n
  rw [coeff_sq, map_add, coeff_ind, coeff_ind, coeff_X]
  obtain ⟨j, hj | hj⟩ : ∃ j, n = 2 * j ∨ n = 2 * j + 1 := ⟨n / 2, by omega⟩
  · have e : ZeroPow n ↔ ZeroPow (n / 2) := by
      rw [hj, zeroPow_two_mul, show 2 * j / 2 = j by omega]
    simp only [e, show n % 2 = 0 by omega, show ¬ (n = 1) by omega, ↓reduceIte, add_zero]
  · have e : ZeroPow n ↔ n = 1 := by rw [hj, zeroPow_odd]; omega
    simp only [e, show ¬ (n % 2 = 0) by omega]
    by_cases h : n = 1
    · simp only [h, ↓reduceIte]; rfl
    · simp only [h, ↓reduceIte, add_zero]

theorem funEq_neg_one :
    ind ZeroPow = 1 + X * ((U1 (ind ZeroPow) ^ (-1 : ℤ) : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) := by
  set σ := ind ZeroPow
  have hc : constantCoeff σ = 1 := constantCoeff_ind (Or.inl rfl)
  set i : (ZMod 2)⟦X⟧ := ((U1 σ ^ (-1 : ℤ) : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧)
  have hinv : i * σ = 1 := by
    have := Units.inv_mul (U1 σ)
    rwa [val_U1, one1_eq _ hc, ← zpow_neg_one] at this
  linear_combination i * ind_zeroPow_sq - (σ - 1) * hinv

/-! ### `m = -2`: the support is `{0} ∪ {2f + 1 : f Fibbinary}`. -/

theorem funEq_neg_two :
    1 + X * ind Fibbinary ^ 2 = 1 + X * ((U1 (1 + X * ind Fibbinary ^ 2) ^ (-2 : ℤ) :
      (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) := by
  set F := ind Fibbinary
  set G : (ZMod 2)⟦X⟧ := 1 + X * F ^ 2
  have hc : constantCoeff G = 1 := by simp [G]
  set i : (ZMod 2)⟦X⟧ := ((U1 G ^ (-1 : ℤ) : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧)
  have hinv : i * G = 1 := by
    have := Units.inv_mul (U1 G)
    rwa [val_U1, one1_eq _ hc, ← zpow_neg_one] at this
  have hi2 : ((U1 G ^ (-2 : ℤ) : (ZMod 2)⟦X⟧ˣ) : (ZMod 2)⟦X⟧) = i ^ 2 := by
    rw [show (-2 : ℤ) = (-1) * 2 by norm_num, zpow_mul]
    simp [i]
  have hG3 : (G - 1) * G ^ 2 = X := by
    simp only [G]
    linear_combination (X * (2 + (F - 1 - X * F ^ 3) + 2 * X * F ^ 3)) * ind_fib_eq' +
      (X ^ 2 * F ^ 3 * (2 + (F - 1 - X * F ^ 3) + 2 * X * F ^ 3)) * two_eq_zero
  rw [hi2]
  linear_combination i ^ 2 * hG3 - (G - 1) * (i * G + 1) * hinv

end F2

end OeisA292877

namespace OeisA292877

open PowerSeries

/-! ## The two families -/

section Families

/-- Family (I): `E_N = -(N² + (m-1)N + 1)`. -/
def EI (m : ℤ) (N : ℕ) : ℤ := -((N : ℤ) ^ 2 + (m - 1) * N + 1)

/-- Family (II): `E_N = N² - mN + 1`. -/
def EII (m : ℤ) (N : ℕ) : ℤ := (N : ℤ) ^ 2 - m * N + 1

theorem isCoprime_EI (m : ℤ) (N : ℕ) : IsCoprime (EI m N) (N : ℤ) :=
  ⟨-1, -((N : ℤ) + m - 1), by simp only [EI]; ring⟩

theorem isCoprime_EII (m : ℤ) (N : ℕ) : IsCoprime (EII m N) (N : ℤ) :=
  ⟨1, m - N, by simp only [EII]; ring⟩

theorem ne_zero_of_isCoprime {e : ℤ} {N : ℕ} (hN : 2 ≤ N) (h : IsCoprime e (N : ℤ)) : e ≠ 0 := by
  rintro rfl
  rw [isCoprime_zero_left, Int.isUnit_iff] at h
  omega

theorem odd_M (N : ℕ) : Odd ((N : ℤ) ^ 2 - N + 1) := by
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self (N : ℤ)
  exact ⟨k, by linear_combination hk⟩

theorem coeff_EI (m : ℤ) {N : ℕ} (hN : 1 ≤ N) :
    coeff (N - 1) ((u1 ^ (EI m N + m * N - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) =
      ((Int.negOnePow ((N - 1 : ℕ) : ℤ) : ℤˣ) : ℤ) * ((N ^ 2).choose (N - 1) : ℤ) := by
  rw [coeff_u1_zpow, show EI m N + m * N - 1 = -((N : ℤ) ^ 2 - N + 2) by simp only [EI]; ring,
    Ring.choose_neg, Units.smul_def,
    show ((N : ℤ) ^ 2 - N + 2) + ((N - 1 : ℕ) : ℤ) - 1 = ((N ^ 2 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hN]; ring,
    Ring.choose_natCast, smul_eq_mul]

theorem coeff_EII (m : ℤ) (N : ℕ) :
    coeff (N - 1) ((u1 ^ (EII m N + m * N - 1) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) =
      1 * ((N ^ 2).choose (N - 1) : ℤ) := by
  rw [coeff_u1_zpow, show EII m N + m * N - 1 = ((N ^ 2 : ℕ) : ℤ) by push_cast [EII]; ring,
    Ring.choose_natCast, one_mul]

theorem hT_EI (m : ℤ) (N : ℕ) (hN : 2 ≤ N) : ∃ M : ℤ, Odd M ∧
    2 * EI m N ∣ M * (coeff N ((U1 (Tm m) ^ EI m N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - (0 : ℕ → ℤ) N) :=
  ⟨_, odd_M N, by simpa using H2 m (EI m N) hN _ (coeff_EI m (by omega))⟩

theorem hT_EII (m : ℤ) (R : ℕ → ℤ) (hR : ∀ N, 2 ≤ N → 2 * EII m N ∣ R N) (N : ℕ) (hN : 2 ≤ N) :
    ∃ M : ℤ, Odd M ∧
      2 * EII m N ∣ M * (coeff N ((U1 (Tm m) ^ EII m N : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) - R N) :=
  ⟨_, odd_M N, by
    rw [mul_sub]
    exact dvd_sub (H2 m (EII m N) hN _ (coeff_EII m N)) (Dvd.dvd.mul_left (hR N hN) _)⟩

theorem coeff_one_Tm (m : ℤ) : coeff 1 (Tm m) = 1 := by
  rw [Tm_eq, map_add, coeff_one, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_zpow_of_one _ (by rw [val_U1_Tm]; exact constantCoeff_Tm m)]
  simp

/-- Theorem 3 (I), parity part. -/
theorem famI_parity (m : ℤ) {A : ℚ⟦X⟧} (hA : Sat (EI m) 0 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (n : ℕ) : 2 ∣ a n - coeff n (Tm m) :=
  parity (fun N hN => ne_zero_of_isCoprime hN (isCoprime_EI m N)) hA a ha (Tm m)
    (constantCoeff_Tm m) (coeff_one_Tm m) (fun N hN => hT_EI m N hN) n

theorem famI_integral (m : ℤ) {A : ℚ⟦X⟧} (hA : Sat (EI m) 0 A) (n : ℕ) :
    ∃ z : ℤ, coeff n A = z :=
  integral (fun N _ => ⟨isCoprime_EI m N, dvd_zero _⟩) hA n

theorem famI_existsUnique (m : ℤ) : ∃! A : ℚ⟦X⟧, Sat (EI m) 0 A :=
  existsUnique fun N hN => ne_zero_of_isCoprime hN (isCoprime_EI m N)

/-- Theorem 3 (II), parity part. -/
theorem famII_parity (m : ℤ) (R : ℕ → ℤ) (hR : ∀ N, 2 ≤ N → 2 * EII m N ∣ R N) {A : ℚ⟦X⟧}
    (hA : Sat (EII m) R A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) (n : ℕ) :
    2 ∣ a n - coeff n (Tm m) :=
  parity (fun N hN => ne_zero_of_isCoprime hN (isCoprime_EII m N)) hA a ha (Tm m)
    (constantCoeff_Tm m) (coeff_one_Tm m) (hT_EII m R hR) n

theorem famII_integral (m : ℤ) (R : ℕ → ℤ) (hR : ∀ N, 2 ≤ N → 2 * EII m N ∣ R N) {A : ℚ⟦X⟧}
    (hA : Sat (EII m) R A) (n : ℕ) : ∃ z : ℤ, coeff n A = z :=
  integral (fun N hN => ⟨isCoprime_EII m N, (dvd_mul_left _ _).trans (hR N hN)⟩) hA n

theorem famII_existsUnique (m : ℤ) (R : ℕ → ℤ) : ∃! A : ℚ⟦X⟧, Sat (EII m) R A :=
  existsUnique fun N hN => ne_zero_of_isCoprime hN (isCoprime_EII m N)

/-- Parity from a congruence with `T_m` and its reduction `σ` modulo `2`. -/
theorem odd_iff_of_dvd {a t : ℤ} (h : 2 ∣ a - t) {s : ZMod 2} (ht : (t : ZMod 2) = s) :
    Odd a ↔ s = 1 := by
  rw [← ZMod.intCast_eq_one_iff_odd, ← ht]
  have : (t : ZMod 2) = a := (ZMod.intCast_eq_intCast_iff_dvd_sub t a 2).mpr (by exact_mod_cast h)
  rw [← this]

theorem ite_eq_one_iff {p : Prop} [Decidable p] : ((if p then 1 else 0 : ZMod 2) = 1) ↔ p := by
  by_cases h : p <;> simp [h]

end Families

/-! ## From the OEIS conditions to the families -/

section Bridges

theorem inv_pow_eq (A : ℚ⟦X⟧) (hA : constantCoeff A = 1) (k : ℕ) :
    (A ^ k)⁻¹ = ((U1 A ^ (-(k : ℤ)) : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp [hA]), ← val_U1_zpow_natCast A hA k,
    ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]

/-- Bridge for the entries with `[x^{n-1}] 1/A(x)^{e(n)} = 0` for `n > 2`. -/
theorem bridge_neg (e : ℕ → ℕ) (E : ℕ → ℤ) (hE : ∀ N, E N = -((e (N + 1) : ℕ) : ℤ))
    (A : ℚ⟦X⟧) :
    (constantCoeff A = 1 ∧ coeff 1 A = 1 ∧ ∀ n : ℕ, 2 < n → coeff (n - 1) ((A ^ e n)⁻¹) = 0) ↔
      Sat E 0 A := by
  constructor
  · rintro ⟨h0, h1, h⟩
    refine ⟨by simpa using h0, h1, fun N hN => ?_⟩
    have := h (N + 1) (by omega)
    rw [inv_pow_eq A h0, Nat.add_sub_cancel, ← hE] at this
    simpa using this
  · rintro ⟨h0, h1, h⟩
    have h0' : constantCoeff A = 1 := by simpa using h0
    refine ⟨h0', h1, fun n hn => ?_⟩
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    rw [inv_pow_eq A h0', Nat.add_sub_cancel, ← hE, h N (by omega)]
    simp

/-- Bridge for the entries with `[x^n] A(x)^{e(n)} = 0` for `n > 1`. -/
theorem bridge_pos (e : ℕ → ℕ) (E : ℕ → ℤ) (hE : ∀ N, E N = ((e N : ℕ) : ℤ)) (A : ℚ⟦X⟧) :
    (constantCoeff A = 1 ∧ coeff 1 A = 1 ∧ ∀ n : ℕ, 1 < n → coeff n (A ^ e n) = 0) ↔
      Sat E 0 A := by
  constructor
  · rintro ⟨h0, h1, h⟩
    refine ⟨by simpa using h0, h1, fun N hN => ?_⟩
    rw [hE, val_U1_zpow_natCast A h0, h N (by omega)]
    simp
  · rintro ⟨h0, h1, h⟩
    have h0' : constantCoeff A = 1 := by simpa using h0
    refine ⟨h0', h1, fun n hn => ?_⟩
    have := h n (by omega)
    rw [hE, val_U1_zpow_natCast A h0'] at this
    simpa using this

theorem coeff_one_pow (A : ℚ⟦X⟧) (hA : constantCoeff A = 1) (k : ℕ) :
    coeff 1 (A ^ k) = k * coeff 1 A := by
  have h := coeff_U1_zpow A (le_refl 1) (k : ℤ)
  have htr : (trunc 1 A : ℚ⟦X⟧) = 1 := by
    ext n
    rw [Polynomial.coeff_coe, coeff_trunc, coeff_one]
    rcases n with _ | n
    · simp [hA]
    · simp
  have h1 : U1 (1 : ℚ⟦X⟧) = 1 :=
    Units.ext (by rw [val_U1, Units.val_one]; exact one1_eq _ (by simp))
  rw [htr, val_U1_zpow_natCast A hA, h1] at h
  simpa using h

/-- Bridge for the entries with `[x^{n-1}] A(x)^{n²} = r(n)` for `n ≥ 1`. -/
theorem bridge_R (r : ℕ → ℕ) (h1 : r 1 = 1) (h2 : r 2 = 4) (A : ℚ⟦X⟧) :
    (∀ n : ℕ, 1 ≤ n → coeff (n - 1) (A ^ (n ^ 2)) = ((r n : ℕ) : ℚ)) ↔
      Sat (EII (-2)) (fun N => (r (N + 1) : ℤ)) A := by
  have hE : ∀ N : ℕ, EII (-2) N = (((N + 1) ^ 2 : ℕ) : ℤ) := fun N => by push_cast [EII]; ring
  constructor
  · intro h
    have h0 : coeff 0 A = 1 := by simpa [h1] using h 1 le_rfl
    have h0' : constantCoeff A = 1 := by simpa using h0
    have hA1 : coeff 1 A = 1 := by
      have := h 2 (by norm_num)
      rw [show 2 - 1 = 1 from rfl, coeff_one_pow A h0', h2] at this
      norm_num at this
      linarith
    refine ⟨h0, hA1, fun N hN => ?_⟩
    rw [hE, val_U1_zpow_natCast A h0']
    simpa using h (N + 1) (by omega)
  · rintro ⟨h0, hA1, h⟩ n hn
    have h0' : constantCoeff A = 1 := by simpa using h0
    rcases n with _ | _ | _ | n
    · omega
    · simp [h1, h0']
    · rw [show 1 + 1 - 1 = 1 from rfl, coeff_one_pow A h0', hA1, h2]; norm_num
    · have := h (n + 2) (by omega)
      rw [hE, val_U1_zpow_natCast A h0'] at this
      simpa using this

end Bridges

/-! ## Counting Fibbinary numbers -/

section Counting

theorem sum_range_two_mul (g : ℕ → ℕ) (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M), g k = ∑ j ∈ Finset.range M, (g (2 * j) + g (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- `c(n) = #{k < 2^n : k Fibbinary}`. -/
def fibCount (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ n), if Fibbinary k then 1 else 0

theorem fibCount_add_two (n : ℕ) : fibCount (n + 2) = fibCount (n + 1) + fibCount n := by
  unfold fibCount
  rw [show 2 ^ (n + 2) = 2 * 2 ^ (n + 1) by ring, sum_range_two_mul, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [fibbinary_two_mul]
  · rw [show 2 ^ (n + 1) = 2 * 2 ^ n by ring, sum_range_two_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 2 * (2 * j) + 1 = 4 * j + 1 by ring, show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring]
    simp only [fibbinary_four_mul_add_one, not_fibbinary_four_mul_add_three, ↓reduceIte, add_zero]

theorem fibCount_eq (n : ℕ) : fibCount n = Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · decide
    · decide
    · rw [fibCount_add_two, ih (n + 1) (by omega), ih n (by omega), Nat.fib_add_two (n := n + 2)]
      ring

/-- The number of Fibbinary numbers in `[2^n, 2^{n+1})` is `F(n+1)`. -/
theorem card_fibbinary_Icc (n : ℕ) :
    ((Finset.Icc (2 ^ n) (2 ^ (n + 1) - 1)).filter Fibbinary).card = Nat.fib (n + 1) := by
  have hIcc : Finset.Icc (2 ^ n) (2 ^ (n + 1) - 1) = Finset.Ico (2 ^ n) (2 ^ (n + 1)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    have := Nat.one_le_two_pow (n := n + 1)
    omega
  rw [hIcc, Finset.card_filter]
  have h : fibCount n + ∑ k ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), (if Fibbinary k then 1 else 0) =
      fibCount (n + 1) := by
    unfold fibCount
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))
  have h1 : fibCount n = Nat.fib (n + 2) := fibCount_eq n
  have h2 : fibCount (n + 1) = Nat.fib (n + 3) := fibCount_eq (n + 1)
  have h3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  omega

theorem fibbinary_two_pow (n : ℕ) : Fibbinary (2 ^ n) := by
  induction n with
  | zero => decide
  | succ n ih => rw [pow_succ, mul_comm, fibbinary_two_mul]; exact ih

end Counting

end OeisA292877

namespace OeisA292877

open PowerSeries

/-! ## The general form -/

theorem zpowQ_eq (A : ℚ⟦X⟧) (hA : constantCoeff A = 1) (k : ℤ) :
    zpowQ A k = ((U1 A ^ k : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
  unfold zpowQ
  split_ifs with h
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Int.toNat_natCast, val_U1_zpow_natCast A hA]
  · have hk : k = -((k.natAbs : ℕ) : ℤ) := by omega
    conv_rhs => rw [hk]
    rw [inv_pow_eq A hA]

theorem zpowZ_eq (T : ℤ⟦X⟧) (hT : constantCoeff T = 1) (k : ℤ) :
    zpowZ T k = ((U1 T ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  unfold zpowZ
  split_ifs with h
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Int.toNat_natCast, val_U1_zpow_natCast T hT]
  · have hk : k = -((k.natAbs : ℕ) : ℤ) := by omega
    conv_rhs => rw [hk, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    congr 1
    change invOfUnit T 1 = invOfUnit (one1 T) 1
    rw [one1_eq T hT]

theorem isFussCatalan_iff (m : ℤ) (T : ℤ⟦X⟧) :
    IsFussCatalan m T ↔ T = 1 + X * ((U1 T ^ m : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  constructor
  · rintro ⟨h0, h⟩
    rwa [zpowZ_eq T h0] at h
  · intro h
    have h0 : constantCoeff T = 1 := by rw [h]; simp
    exact ⟨h0, by rwa [zpowZ_eq T h0]⟩

/-- For every $m \in \mathbb{Z}$ there is exactly one Fuss–Catalan series $T_m$. -/
theorem fussCatalan_existsUnique (m : ℤ) : ∃! T : ℤ⟦X⟧, IsFussCatalan m T := by
  refine ⟨Tm m, (isFussCatalan_iff m _).mpr ?_, fun T hT =>
    eq_of_funEq m ((isFussCatalan_iff m T).mp hT) ?_⟩
  · exact Tm_eq m
  · exact Tm_eq m

theorem eq_Tm {m : ℤ} {T : ℤ⟦X⟧} (hT : IsFussCatalan m T) : T = Tm m :=
  eq_of_funEq m ((isFussCatalan_iff m T).mp hT) (Tm_eq m)

theorem isFamilyI_iff (m : ℤ) (A : ℚ⟦X⟧) : IsFamilyI m A ↔ Sat (EI m) 0 A := by
  constructor
  · rintro ⟨h0, h1, h⟩
    refine ⟨by simpa using h0, h1, fun N hN => ?_⟩
    have := h N hN
    rwa [zpowQ_eq A h0] at this
  · rintro ⟨h0, h1, h⟩
    have h0' : constantCoeff A = 1 := by simpa using h0
    refine ⟨h0', h1, fun N hN => ?_⟩
    rw [zpowQ_eq A h0']
    have := h N hN
    simp only [Pi.zero_apply, Int.cast_zero] at this
    exact this

theorem isFamilyII_iff (m : ℤ) (R : ℕ → ℤ) (A : ℚ⟦X⟧) :
    IsFamilyII m R A ↔ Sat (EII m) R A := by
  constructor
  · rintro ⟨h0, h1, h⟩
    refine ⟨by simpa using h0, h1, fun N hN => ?_⟩
    have := h N hN
    rwa [zpowQ_eq A h0] at this
  · rintro ⟨h0, h1, h⟩
    have h0' : constantCoeff A = 1 := by simpa using h0
    refine ⟨h0', h1, fun N hN => ?_⟩
    rw [zpowQ_eq A h0']
    exact h N hN

/-- Family (I) has exactly one solution in `ℚ⟦X⟧`. -/
theorem familyI_existsUnique (m : ℤ) : ∃! A : ℚ⟦X⟧, IsFamilyI m A := by
  simpa only [isFamilyI_iff] using famI_existsUnique m

/-- Family (II) has exactly one solution in `ℚ⟦X⟧`. -/
theorem familyII_existsUnique (m : ℤ) (R : ℕ → ℤ) : ∃! A : ℚ⟦X⟧, IsFamilyII m R A := by
  simpa only [isFamilyII_iff] using famII_existsUnique m R

/-- Family (I): every coefficient of $A$ is an integer, congruent modulo $2$ to the coefficient
of $T_m$. -/
theorem familyI_integral_mod_two (m : ℤ) (A : ℚ⟦X⟧) (hA : IsFamilyI m A) (T : ℤ⟦X⟧)
    (hT : IsFussCatalan m T) (n : ℕ) : ∃ a : ℤ, coeff n A = a ∧ 2 ∣ a - coeff n T := by
  classical
  have hS := (isFamilyI_iff m A).mp hA
  have hz := famI_integral m hS
  refine ⟨(hz n).choose, (hz n).choose_spec, ?_⟩
  rw [eq_Tm hT]
  exact famI_parity m hS (fun k => (hz k).choose) (fun k => (hz k).choose_spec) n

/-- Family (II), when $2(N^2 - mN + 1)$ divides $R_N$ for $N \ge 2$: every coefficient of $A$
is an integer, congruent modulo $2$ to the coefficient of $T_m$. -/
theorem familyII_integral_mod_two (m : ℤ) (R : ℕ → ℤ)
    (hR : ∀ N : ℕ, 2 ≤ N → 2 * ((N : ℤ) ^ 2 - m * N + 1) ∣ R N) (A : ℚ⟦X⟧)
    (hA : IsFamilyII m R A) (T : ℤ⟦X⟧) (hT : IsFussCatalan m T) (n : ℕ) :
    ∃ a : ℤ, coeff n A = a ∧ 2 ∣ a - coeff n T := by
  classical
  have hS := (isFamilyII_iff m R A).mp hA
  have hz := famII_integral m R hR hS
  refine ⟨(hz n).choose, (hz n).choose_spec, ?_⟩
  rw [eq_Tm hT]
  exact famII_parity m R hR hS (fun k => (hz k).choose) (fun k => (hz k).choose_spec) n

/-! ## The eight entries -/

theorem isA292877_iff (A : ℚ⟦X⟧) : IsA292877 A ↔ Sat (EI 3) 0 A :=
  bridge_neg (fun n => n ^ 2) (EI 3) (fun N => by push_cast [EI]; ring) A

theorem isA303562_iff (A : ℚ⟦X⟧) : IsA303562 A ↔ Sat (EI 4) 0 A :=
  bridge_neg (fun n => n ^ 2 + n - 1) (EI 4) (fun N => by
    simp only [EI]
    rw [Nat.cast_sub (by nlinarith)]
    push_cast; ring) A

theorem isA303563_iff (A : ℚ⟦X⟧) : IsA303563 A ↔ Sat (EI 2) 0 A :=
  bridge_neg (fun n => n ^ 2 - n + 1) (EI 2) (fun N => by
    simp only [EI]
    rw [Nat.cast_add, Nat.cast_sub (by nlinarith)]
    push_cast; ring) A

theorem isA171791_iff (A : ℚ⟦X⟧) : IsA171791 A ↔ Sat (EII (-2)) 0 A :=
  bridge_pos (fun n => (n + 1) ^ 2) (EII (-2)) (fun N => by push_cast [EII]; ring) A

theorem isA230218_iff (A : ℚ⟦X⟧) : IsA230218 A ↔ Sat (EII (-1)) 0 A :=
  bridge_pos (fun n => n ^ 2 + n + 1) (EII (-1)) (fun N => by push_cast [EII]; ring) A

/-- `R_N` for A263075. -/
def r263075 (n : ℕ) : ℕ := n ^ n * (n - 1).factorial

def r263190 (n : ℕ) : ℕ := n.factorial ^ 2

def r371673 (n : ℕ) : ℕ := catalan (n - 1) * n ^ n

theorem isA263075_iff (A : ℚ⟦X⟧) :
    IsA263075 A ↔ Sat (EII (-2)) (fun N => (r263075 (N + 1) : ℤ)) A :=
  bridge_R r263075 (by decide) (by decide) A

theorem isA263190_iff (A : ℚ⟦X⟧) :
    IsA263190 A ↔ Sat (EII (-2)) (fun N => (r263190 (N + 1) : ℤ)) A :=
  bridge_R r263190 (by decide) (by decide) A

theorem isA371673_iff (A : ℚ⟦X⟧) :
    IsA371673 A ↔ Sat (EII (-2)) (fun N => (r371673 (N + 1) : ℤ)) A :=
  bridge_R r371673 (by simp [r371673]) (by simp [r371673]) A

theorem EII_neg_two (N : ℕ) : 2 * EII (-2) N = ((2 * (N + 1) ^ 2 : ℕ) : ℤ) := by
  push_cast [EII]; ring

theorem two_dvd_factorial {N : ℕ} (hN : 2 ≤ N) : 2 ∣ N.factorial := Nat.dvd_factorial two_pos hN

theorem dvd_r263075 (N : ℕ) (hN : 2 ≤ N) : 2 * EII (-2) N ∣ (r263075 (N + 1) : ℤ) := by
  rw [EII_neg_two, Int.natCast_dvd_natCast, r263075, Nat.add_sub_cancel,
    show (N + 1) ^ (N + 1) = (N + 1) ^ 2 * (N + 1) ^ (N - 1) by rw [← pow_add]; congr 1; omega]
  rw [mul_comm 2, mul_assoc]
  exact mul_dvd_mul_left _ (Dvd.dvd.mul_left (two_dvd_factorial hN) _)

theorem dvd_r263190 (N : ℕ) (hN : 2 ≤ N) : 2 * EII (-2) N ∣ (r263190 (N + 1) : ℤ) := by
  rw [EII_neg_two, Int.natCast_dvd_natCast, r263190, Nat.factorial_succ, mul_pow, mul_comm 2]
  exact mul_dvd_mul_left _ (dvd_pow (two_dvd_factorial hN) two_ne_zero)

theorem two_dvd_catalan {N : ℕ} (hN : 2 ≤ N) (he : N % 2 = 0) : 2 ∣ catalan N := by
  have h := succ_mul_catalan_eq_centralBinom N
  have h2 := Nat.two_dvd_centralBinom_of_one_le (show 0 < N by omega)
  rw [← h] at h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h3 | h3
  · omega
  · exact h3

theorem dvd_r371673 (N : ℕ) (hN : 2 ≤ N) : 2 * EII (-2) N ∣ (r371673 (N + 1) : ℤ) := by
  rw [EII_neg_two, Int.natCast_dvd_natCast, r371673, Nat.add_sub_cancel,
    show (N + 1) ^ (N + 1) = (N + 1) ^ 2 * (N + 1) ^ (N - 1) by rw [← pow_add]; congr 1; omega]
  rcases Nat.mod_two_eq_zero_or_one N with he | ho
  · rw [show 2 * (N + 1) ^ 2 = 2 * ((N + 1) ^ 2) from rfl]
    exact mul_dvd_mul (two_dvd_catalan hN he) (dvd_mul_right _ _)
  · rw [mul_comm 2, mul_left_comm]
    refine mul_dvd_mul_left _ (Dvd.dvd.mul_left (dvd_pow ?_ (by omega)) _)
    omega

theorem coeff_neg_two_eq_one_iff {n : ℕ} (hn : 0 < n) :
    coeff n (1 + X * ind Fibbinary ^ 2) = 1 ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [map_add, coeff_one, ite_eq_right (by omega), zero_add, coeff_succ_X_mul, coeff_sq]
  constructor
  · intro h
    split_ifs at h with hj
    · rw [coeff_ind, ite_eq_one_iff] at h
      exact ⟨j / 2, h, by omega⟩
    · exact absurd h (by decide)
  · rintro ⟨f, hf, hjf⟩
    rw [ite_eq_left (by omega), coeff_ind, ite_eq_one_iff, show j / 2 = f by omega]
    exact hf

/-- Parity transfer for `m = -2`. -/
theorem odd_iff_neg_two {a : ℤ} {n : ℕ} (hn : 0 < n) (h : 2 ∣ a - coeff n (Tm (-2))) :
    Odd a ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 := by
  rw [odd_iff_of_dvd h (coeff_Tm_mod_two (-2) _ funEq_neg_two n), coeff_neg_two_eq_one_iff hn]

/-- The g.f. of A292877 exists and is unique. -/
theorem a292877_existsUnique : ∃! A : ℚ⟦X⟧, IsA292877 A := by
  simpa only [isA292877_iff] using famI_existsUnique 3

/-- A292877 has integer terms. -/
theorem a292877_integral (A : ℚ⟦X⟧) (hA : IsA292877 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n :=
  ⟨fun n => (famI_integral 3 ((isA292877_iff A).mp hA) n).choose,
    fun n => (famI_integral 3 ((isA292877_iff A).mp hA) n).choose_spec⟩

/-- A292877, conjecture (2): $a(n)$ is odd if and only if $n$ is a Fibbinary number. -/
theorem a292877_conj2 (A : ℚ⟦X⟧) (hA : IsA292877 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) : Odd (a n) ↔ Fibbinary n := by
  rw [odd_iff_of_dvd (famI_parity 3 ((isA292877_iff A).mp hA) a ha n)
    (coeff_Tm_mod_two 3 _ funEq_three n), coeff_ind, ite_eq_one_iff]

/-- A292877, conjecture (1): $a(2^n)$ is odd for $n \ge 0$. -/
theorem a292877_conj1 (A : ℚ⟦X⟧) (hA : IsA292877 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) : Odd (a (2 ^ n)) :=
  (a292877_conj2 A hA a ha _).mpr (fibbinary_two_pow n)

/-- A292877, conjecture (3): the number of odd terms among $a(2^n), \dots, a(2^{n+1}-1)$ is
$F(n+1)$, for $n \ge 0$. -/
theorem a292877_conj3 (A : ℚ⟦X⟧) (hA : IsA292877 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) :
    ((Finset.Icc (2 ^ n) (2 ^ (n + 1) - 1)).filter fun k => Odd (a k)).card = Nat.fib (n + 1) := by
  rw [Finset.filter_congr fun k _ => a292877_conj2 A hA a ha k]
  exact card_fibbinary_Icc n

/-- The g.f. of A303562 exists and is unique. -/
theorem a303562_existsUnique : ∃! A : ℚ⟦X⟧, IsA303562 A := by
  simpa only [isA303562_iff] using famI_existsUnique 4

/-- A303562 has integer terms. -/
theorem a303562_integral (A : ℚ⟦X⟧) (hA : IsA303562 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n :=
  ⟨fun n => (famI_integral 4 ((isA303562_iff A).mp hA) n).choose,
    fun n => (famI_integral 4 ((isA303562_iff A).mp hA) n).choose_spec⟩

/-- A303562: $a(n)$ is odd if and only if $n = (4^k - 1)/3$ for some $k \ge 0$. -/
theorem a303562_parity (A : ℚ⟦X⟧) (hA : IsA303562 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) : Odd (a n) ↔ ∃ k, n = (4 ^ k - 1) / 3 := by
  classical
  rw [odd_iff_of_dvd (famI_parity 4 ((isA303562_iff A).mp hA) a ha n)
    (coeff_Tm_mod_two 4 _ funEq_four n), coeff_ind, ite_eq_one_iff]
  rfl

/-- The g.f. of A303563 exists and is unique. -/
theorem a303563_existsUnique : ∃! A : ℚ⟦X⟧, IsA303563 A := by
  simpa only [isA303563_iff] using famI_existsUnique 2

/-- A303563 has integer terms. -/
theorem a303563_integral (A : ℚ⟦X⟧) (hA : IsA303563 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n :=
  ⟨fun n => (famI_integral 2 ((isA303563_iff A).mp hA) n).choose,
    fun n => (famI_integral 2 ((isA303563_iff A).mp hA) n).choose_spec⟩

/-- A303563: $a(n)$ is odd if and only if $n = 2^k - 1$ for some $k \ge 0$. -/
theorem a303563_parity (A : ℚ⟦X⟧) (hA : IsA303563 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) : Odd (a n) ↔ ∃ k, n = 2 ^ k - 1 := by
  classical
  rw [odd_iff_of_dvd (famI_parity 2 ((isA303563_iff A).mp hA) a ha n)
    (coeff_Tm_mod_two 2 _ funEq_two n), coeff_ind, ite_eq_one_iff]
  rfl

/-- The g.f. of A230218 exists and is unique. -/
theorem a230218_existsUnique : ∃! A : ℚ⟦X⟧, IsA230218 A := by
  simpa only [isA230218_iff] using famII_existsUnique (-1) 0

/-- A230218 has integer terms. -/
theorem a230218_integral (A : ℚ⟦X⟧) (hA : IsA230218 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n :=
  have h := famII_integral (-1) 0 (fun _ _ => dvd_zero _) ((isA230218_iff A).mp hA)
  ⟨fun n => (h n).choose, fun n => (h n).choose_spec⟩

/-- A230218: for $n > 0$, $a(n)$ is odd if and only if $n$ is a power of $2$. -/
theorem a230218_parity (A : ℚ⟦X⟧) (hA : IsA230218 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ k, n = 2 ^ k := by
  classical
  rw [odd_iff_of_dvd (famII_parity (-1) 0 (fun _ _ => dvd_zero _) ((isA230218_iff A).mp hA) a ha n)
    (coeff_Tm_mod_two (-1) _ funEq_neg_one n), coeff_ind, ite_eq_one_iff]
  exact ⟨fun h => h.resolve_left (by omega), Or.inr⟩

/-- The g.f. of A171791 exists and is unique. -/
theorem a171791_existsUnique : ∃! A : ℚ⟦X⟧, IsA171791 A := by
  simpa only [isA171791_iff] using famII_existsUnique (-2) 0

/-- A171791 has integer terms. -/
theorem a171791_integral (A : ℚ⟦X⟧) (hA : IsA171791 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n :=
  have h := famII_integral (-2) 0 (fun _ _ => dvd_zero _) ((isA171791_iff A).mp hA)
  ⟨fun n => (h n).choose, fun n => (h n).choose_spec⟩

/-- A171791: for $n > 0$, $a(n)$ is odd if and only if $n = 2f + 1$ with $f$ Fibbinary. -/
theorem a171791_parity (A : ℚ⟦X⟧) (hA : IsA171791 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 :=
  odd_iff_neg_two hn
    (famII_parity (-2) 0 (fun _ _ => dvd_zero _) ((isA171791_iff A).mp hA) a ha n)

/-- The g.f. of A263075 exists and is unique. -/
theorem a263075_existsUnique : ∃! A : ℚ⟦X⟧, IsA263075 A := by
  simpa only [isA263075_iff] using famII_existsUnique (-2) _

/-- A263075 has integer terms. -/
theorem a263075_integral (A : ℚ⟦X⟧) (hA : IsA263075 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n :=
  ⟨fun n => (famII_integral (-2) _ dvd_r263075 ((isA263075_iff A).mp hA) n).choose,
    fun n => (famII_integral (-2) _ dvd_r263075 ((isA263075_iff A).mp hA) n).choose_spec⟩

/-- A263075: for $n > 0$, $a(n)$ is odd if and only if $n = 2f + 1$ with $f$ Fibbinary. -/
theorem a263075_parity (A : ℚ⟦X⟧) (hA : IsA263075 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 :=
  odd_iff_neg_two hn (famII_parity (-2) _ dvd_r263075 ((isA263075_iff A).mp hA) a ha n)

/-- The g.f. of A263190 exists and is unique. -/
theorem a263190_existsUnique : ∃! A : ℚ⟦X⟧, IsA263190 A := by
  simpa only [isA263190_iff] using famII_existsUnique (-2) _

/-- A263190 has integer terms. -/
theorem a263190_integral (A : ℚ⟦X⟧) (hA : IsA263190 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n :=
  ⟨fun n => (famII_integral (-2) _ dvd_r263190 ((isA263190_iff A).mp hA) n).choose,
    fun n => (famII_integral (-2) _ dvd_r263190 ((isA263190_iff A).mp hA) n).choose_spec⟩

/-- A263190, conjecture (3): for $n > 0$, $a(n)$ is odd if and only if $n = 2f + 1$ with $f$
Fibbinary. -/
theorem a263190_conj3 (A : ℚ⟦X⟧) (hA : IsA263190 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 :=
  odd_iff_neg_two hn (famII_parity (-2) _ dvd_r263190 ((isA263190_iff A).mp hA) a ha n)

/-- The g.f. of A371673 exists and is unique. -/
theorem a371673_existsUnique : ∃! A : ℚ⟦X⟧, IsA371673 A := by
  simpa only [isA371673_iff] using famII_existsUnique (-2) _

/-- A371673 has integer terms. -/
theorem a371673_integral (A : ℚ⟦X⟧) (hA : IsA371673 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n :=
  ⟨fun n => (famII_integral (-2) _ dvd_r371673 ((isA371673_iff A).mp hA) n).choose,
    fun n => (famII_integral (-2) _ dvd_r371673 ((isA371673_iff A).mp hA) n).choose_spec⟩

/-- A371673: for $n > 0$, $a(n)$ is odd if and only if $n = 2f + 1$ with $f$ Fibbinary. -/
theorem a371673_parity (A : ℚ⟦X⟧) (hA : IsA371673 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 :=
  odd_iff_neg_two hn (famII_parity (-2) _ dvd_r371673 ((isA371673_iff A).mp hA) a ha n)

/-! ## Sanity checks -/

example : (Finset.range 22).filter Fibbinary = {0, 1, 2, 4, 5, 8, 9, 10, 16, 17, 18, 20, 21} := by
  decide

/-- The first nontrivial coefficient of A292877 is `a(2) = 5`. -/
example (A : ℚ⟦X⟧) (hA : IsA292877 A) : coeff 2 A = 5 := by
  have h := ((isA292877_iff A).mp hA).2.2 2 le_rfl
  rw [coeff_U1_zpow A (by norm_num)] at h
  have htr : (trunc 2 A : ℚ⟦X⟧) = map (Int.castRingHom ℚ) (1 + X) := by
    ext n
    rw [Polynomial.coeff_coe, coeff_trunc, coeff_map]
    rcases n with _ | _ | n
    · simp [hA.1]
    · simp [hA.2.1, coeff_X]
    · simp [coeff_X, coeff_one]
  rw [htr, coeff_U1_zpow_map, show U1 (1 + X : ℤ⟦X⟧) = u1 from rfl, coeff_u1_zpow,
    show EI 3 2 = -((9 : ℕ) : ℤ) by norm_num [EI], Ring.choose_neg, Units.smul_def,
    show ((9 : ℕ) : ℤ) + ((2 : ℕ) : ℤ) - 1 = ((10 : ℕ) : ℤ) by norm_num, Ring.choose_natCast] at h
  norm_num [EI, Nat.choose] at h
  linarith

end OeisA292877

end
