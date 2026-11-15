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
# OEIS A258377–A258381: Bala's 2-adic statements for Hanna's type-B series

For $N \in \mathbb{N}$, the type-B series $A$ solves
$A^{N+1} = \frac{1}{1-z} \mathrm{BINOMIAL}(\mathrm{BINOMIAL}(A))^N$ with $A(0) = 1$. This file
proves that $A$ exists and is unique, that $a(n) = [z^n] A(z)$ is an integer, that
$a(n + 2^{k-1}) \equiv a(n) \pmod{2^k}$, and that for $k \ge 3$ the least period modulo $2^k$ is
$2^{k-1}$ exactly when $N \equiv 1, 2 \pmod 4$. It proves all of Peter Bala's 2-adic statements
in A258377–A258381: residues, periods and example patterns.

Write $T_c(F)(z) = \frac{1}{1-cz} F(\frac{z}{1-cz})$, so that $\mathrm{BINOMIAL} = T_1$.
Composition is `PowerSeries.subst`.

*Pivot lemma.* Let $\Phi(f) = f^{N+1} - U f(g)^N$ with $U(0) = 1$, $g(0) = 0$ and
$g \equiv z \pmod{z^2}$. If $f(0) = f'(0) = 1$ and $z^n \mid f' - f$, then
$z^{n+1} \mid \Phi(f') - \Phi(f) - (f' - f)$: the pivot is $(N + 1) - N = 1$. Hence $\Phi = 0$
has at most one solution with constant term $1$, and a solution modulo $z^M$ agrees with it below
degree $M$. The operator $f \mapsto f - \Phi(f)$, with the constant term reset to $1$, is causal
over every commutative ring, so its fixed point is a solution. (The causal fixed point follows
the OeisA318008 package of this repository.)

*Type A over $\mathbb{Z}$.* With $U = (1-z)^{-N}$ and $g = \frac{z}{1-z}$, written with
$(1-z)^{-1} = \sum_j z^j$, the fixed point over $\mathbb{Z}$ is an integral series
$B(u) = \sum_m b(m) u^m$ with $B(0) = 1$ and $B^{N+1} = T_1(B)^N$.

*Bridge.* Over $\mathbb{Q}$, `subst` associativity and inverse identities give
$T_a \circ T_b = T_{a+b}$. Rescaling $z \mapsto 2z$ turns $T_1$ into $T_2$, so $D(z) = B(2z)$
satisfies $D^{N+1} = T_2(D)^N$. Then $A_0 = T_1(D)$ satisfies
$A_0^{N+1} = \frac{1}{1-z} T_1(T_2(D))^N = \frac{1}{1-z} T_3(D)^N
= \frac{1}{1-z} T_1(T_1(A_0))^N$. By uniqueness $A = A_0$, that is
$A(z) = \frac{1}{1-z} B(\frac{2z}{1-z})$. So $a(n) = \sum_m \binom{n}{m} 2^m b(m)$ is an integer.
This relation is implicit in Bala's formulas in OEIS A145901.

*2-adic part.* From $r \binom{2^t}{r} = 2^t \binom{2^t - 1}{r - 1}$ and Vandermonde's identity,
$2^{t+j} \mid 2^m (\binom{n + 2^t}{m} - \binom{n}{m})$ whenever $j + v \le m$ for every $v$ with
$2^v \le m$. With $j = 1$ this gives the period $2^{k-1}$ modulo $2^k$. With $j = 2$ the terms
$m \ge 3$ of $a(n + 2^{k-2}) - a(n)$ vanish modulo $2^k$. The terms $m = 1, 2$ use $b(1) = N$ and
$2 b(2) = 3N^2 + N$, read off degrees $1$ and $2$ of the type-A equation. The result is
$a(n + 2^{k-2}) - a(n) \equiv 2^{k-2} \cdot 3N(N+1) \pmod{2^k}$. The least periods follow from
`Function.minimalPeriod_eq_prime_pow`.

*Examples.* Modulo $2^k$, $a(n) \equiv \sum_{m < k} \binom{n}{m} 2^m b(m)$, and $a$ has period
$2^{k-1}$. So each pattern is a finite check over $n < 2^{k-1}$, given $b(0), \dots, b(k-1)$.
These values, for $k \le 5$, come from a check of the type-A equation below degree $5$ by
`decide +kernel`, together with the pivot lemma. The same values give the first terms of the data
as a sanity check.

*References:*
- Peter Bala, [A258377](https://oeis.org/A258377), [A258378](https://oeis.org/A258378),
  [A258379](https://oeis.org/A258379), [A258380](https://oeis.org/A258380) and
  [A258381](https://oeis.org/A258381), May 28 2015; 2-adic comments Dec 06 2017.
- Peter Bala, [A145901](https://oeis.org/A145901), formulas of May 28 2015 and Jan 12 2018.
-/

@[expose] public section

namespace OeisA258377

open PowerSeries

/-- The binomial transform $\mathrm{BINOMIAL}(F)(z) = \frac{1}{1-z} F(\frac{z}{1-z})$. -/
noncomputable def binomial (F : ℚ⟦X⟧) : ℚ⟦X⟧ := (1 - X)⁻¹ * F.subst (X * (1 - X)⁻¹ : ℚ⟦X⟧)

/-- Hanna's type-B equation
$A^{N+1} = \frac{1}{1-z} \mathrm{BINOMIAL}(\mathrm{BINOMIAL}(A))^N$, with $A(0) = 1$. -/
def IsSolution (N : ℕ) (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ A ^ (N + 1) = (1 - X)⁻¹ * binomial (binomial A) ^ N

/-- The least period of $a(n) \bmod m$: the least $p > 0$ with $a(n + p) \equiv a(n) \pmod m$
for all $n \ge 0$, or $0$ if there is none. It is the minimal period of the sequence of residues
under the shift. So a positive value says that $a(n) \bmod m$ is purely periodic. -/
noncomputable def leastPeriodMod (a : ℕ → ℤ) (m : ℕ) : ℕ :=
  Function.minimalPeriod (fun s : ℕ → ZMod m => fun n => s (n + 1)) fun n => (a n : ZMod m)

/-! ## Substitution tools and causal fixed points

Copied from the OeisA318008 package of this repository (same author, Apache-2.0), except
`subst_one'`. -/

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

lemma subst_one' {g : R⟦X⟧} (hg : constantCoeff g = 0) : (1 : R⟦X⟧).subst g = 1 := by
  simpa using subst_C' hg 1

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

end General

section Fix
variable {R : Type*} [CommRing R]

/-- Coefficient `n` of `T f` depends only on the coefficients of `f` below `n`. -/
def Causal (T : R⟦X⟧ → R⟦X⟧) : Prop :=
  ∀ n f g, (∀ k < n, coeff k f = coeff k g) → coeff n (T f) = coeff n (T g)

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

end Fix

/-! ## The pivot lemma for Hanna's equations -/

section Hanna
variable {R : Type*} [CommRing R]

lemma X_dvd_sub_one {f : R⟦X⟧} (hf : constantCoeff f = 1) : X ∣ f - 1 :=
  X_dvd_iff.mpr (by simp [hf])

lemma pow_sub_pow_sub {n : ℕ} {f g : R⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (h : X ^ n ∣ f - g) (e : ℕ) :
    X ^ (n + 1) ∣ f ^ e - g ^ e - (e : R⟦X⟧) * (f - g) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 := X_dvd_sub_one hf
    have h2 : X ∣ g ^ e - 1 := X_dvd_sub_one (by simp [hg])
    have key : f ^ (e + 1) - g ^ (e + 1) - ((e + 1 : ℕ) : R⟦X⟧) * (f - g) =
        f * (f ^ e - g ^ e - (e : R⟦X⟧) * (f - g)) + (e : R⟦X⟧) * ((f - g) * (f - 1)) +
          (f - g) * (g ^ e - 1) := by
      push_cast; ring
    rw [key]
    refine dvd_add (dvd_add (Dvd.dvd.mul_left ih _) (Dvd.dvd.mul_left ?_ _)) ?_
    · rw [pow_succ]; exact mul_dvd_mul h h1
    · rw [pow_succ]; exact mul_dvd_mul h h2

lemma subst_sub_self {n : ℕ} {g : R⟦X⟧} (hg0 : constantCoeff g = 0) (hg : X ^ 2 ∣ g - X)
    {d : R⟦X⟧} (hd : X ^ n ∣ d) : X ^ (n + 1) ∣ d.subst g - d := by
  obtain ⟨h, rfl⟩ := hd
  rw [subst_mul (hs hg0), subst_pow (hs hg0), subst_X (hs hg0)]
  have h1 : X ^ (n + 1) ∣ g ^ n - X ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := X_pow_dvd_pow_sub_pow (m := 2) (j := n) hn hg (dvd_refl X)
        (X_dvd_iff.mpr hg0)
      rwa [show 2 + n - 1 = n + 1 by omega] at this
  have h2 : X ∣ h.subst g - h := X_dvd_iff.mpr (by rw [map_sub, cc_subst hg0, sub_self])
  have : g ^ n * h.subst g - X ^ n * h = (g ^ n - X ^ n) * h.subst g + X ^ n * (h.subst g - h) := by
    ring
  rw [this, pow_succ]
  exact dvd_add (Dvd.dvd.mul_right (by rw [← pow_succ]; exact h1) _) (mul_dvd_mul_left _ h2)

/-- Hanna's operator `f ↦ f^(N+1) - U f(g)^N`; its zeros are the solutions of
`f^(N+1) = U f(g)^N`. -/
noncomputable def Φ (N : ℕ) (U g f : R⟦X⟧) : R⟦X⟧ := f ^ (N + 1) - U * (f.subst g) ^ N

/-- The pivot of `Φ` is `(N + 1) - N = 1`: a change of `f` in degree `n` changes `Φ f` by the
same amount in degree `n`. -/
lemma Φ_perturb {N n : ℕ} {U g : R⟦X⟧} (hU : constantCoeff U = 1) (hg0 : constantCoeff g = 0)
    (hg : X ^ 2 ∣ g - X) {f f' : R⟦X⟧} (hf : constantCoeff f = 1) (hf' : constantCoeff f' = 1)
    (h : X ^ n ∣ f' - f) : X ^ (n + 1) ∣ Φ N U g f' - Φ N U g f - (f' - f) := by
  have hs1 : constantCoeff (f.subst g) = 1 := by rw [cc_subst hg0, hf]
  have hs1' : constantCoeff (f'.subst g) = 1 := by rw [cc_subst hg0, hf']
  have hss : f'.subst g - f.subst g = (f' - f).subst g := by rw [subst_sub (hs hg0)]
  have hT : X ^ (n + 1) ∣ (f' - f).subst g - (f' - f) := subst_sub_self hg0 hg h
  have hsn : X ^ n ∣ f'.subst g - f.subst g := by
    have := dvd_add ((pow_dvd_pow X (Nat.le_succ n)).trans hT) h
    rw [hss]; simpa using this
  have e1 := pow_sub_pow_sub hf' hf h (N + 1)
  have e2 := pow_sub_pow_sub hs1' hs1 hsn N
  have hU1 := X_dvd_sub_one hU
  have key : Φ N U g f' - Φ N U g f - (f' - f) =
      (f' ^ (N + 1) - f ^ (N + 1) - ((N + 1 : ℕ) : R⟦X⟧) * (f' - f)) -
      U * ((f'.subst g) ^ N - (f.subst g) ^ N - (N : R⟦X⟧) * (f'.subst g - f.subst g)) -
      U * (N : R⟦X⟧) * ((f' - f).subst g - (f' - f)) - (N : R⟦X⟧) * ((U - 1) * (f' - f)) := by
    simp only [Φ]; rw [← hss]; push_cast; ring
  rw [key]
  refine dvd_sub (dvd_sub (dvd_sub e1 (Dvd.dvd.mul_left e2 _)) (Dvd.dvd.mul_left hT _))
    (Dvd.dvd.mul_left ?_ _)
  rw [pow_succ']
  exact mul_dvd_mul hU1 h

/-- Solutions of `Φ = 0` agree to every order to which a second series solves it. -/
lemma Φ_dvd {N : ℕ} {U g : R⟦X⟧} (hU : constantCoeff U = 1) (hg0 : constantCoeff g = 0)
    (hg : X ^ 2 ∣ g - X) {B P : R⟦X⟧} (hB : constantCoeff B = 1) (hP : constantCoeff P = 1)
    (hB0 : Φ N U g B = 0) {M : ℕ} (hPM : X ^ M ∣ Φ N U g P) : X ^ M ∣ P - B := by
  induction M with
  | zero => simp
  | succ M ih =>
    have ih' := ih ((pow_dvd_pow X (Nat.le_succ M)).trans hPM)
    have := Φ_perturb hU hg0 hg hB hP ih' (N := N)
    rw [hB0, sub_zero] at this
    have := dvd_sub hPM this
    simpa using this

lemma Φ_unique {N : ℕ} {U g : R⟦X⟧} (hU : constantCoeff U = 1) (hg0 : constantCoeff g = 0)
    (hg : X ^ 2 ∣ g - X) {B P : R⟦X⟧} (hB : constantCoeff B = 1) (hP : constantCoeff P = 1)
    (hB0 : Φ N U g B = 0) (hP0 : Φ N U g P = 0) : P = B := by
  rw [← sub_eq_zero]
  ext n
  have := Φ_dvd hU hg0 hg hB hP hB0 (M := n + 1) (by rw [hP0]; exact dvd_zero _)
  rw [map_zero]
  exact X_pow_dvd_iff.mp this n (Nat.lt_succ_self n)

/-- Replace the constant coefficient by `1`. -/
noncomputable def nrm (f : R⟦X⟧) : R⟦X⟧ := f + C (1 - constantCoeff f)

lemma cc_nrm (f : R⟦X⟧) : constantCoeff (nrm f) = 1 := by simp [nrm]

lemma coeff_nrm (f : R⟦X⟧) {n : ℕ} (hn : n ≠ 0) : coeff n (nrm f) = coeff n f := by
  simp [nrm, coeff_C, hn]

/-- The operator whose fixed point solves `Φ = 0` with constant coefficient `1`. -/
noncomputable def T (N : ℕ) (U g f : R⟦X⟧) : R⟦X⟧ :=
  mk fun n => if n = 0 then 1 else coeff n (nrm f - Φ N U g (nrm f))

lemma T_causal {N : ℕ} {U g : R⟦X⟧} (hU : constantCoeff U = 1) (hg0 : constantCoeff g = 0)
    (hg : X ^ 2 ∣ g - X) : Causal (T N U g) := by
  intro n f f' hff
  simp only [T, coeff_mk]
  split_ifs with hn
  · rfl
  have hX : X ^ n ∣ nrm f' - nrm f := by
    rw [X_pow_dvd_iff]
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [cc_nrm]
    · rw [map_sub, coeff_nrm _ hi0.ne', coeff_nrm _ hi0.ne', hff i hi, sub_self]
  have h := X_pow_dvd_iff.mp (Φ_perturb hU hg0 hg (cc_nrm f) (cc_nrm f') hX (N := N)) n
    (Nat.lt_succ_self n)
  simp only [map_sub] at h ⊢
  linear_combination h

lemma exists_Φ_eq_zero (N : ℕ) {U g : R⟦X⟧} (hU : constantCoeff U = 1)
    (hg0 : constantCoeff g = 0) (hg : X ^ 2 ∣ g - X) :
    ∃ B : R⟦X⟧, constantCoeff B = 1 ∧ Φ N U g B = 0 := by
  have hB := (T_causal hU hg0 hg (N := N)).fix_eq
  have h0 : constantCoeff (fix (T N U g)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← hB]
    simp [T]
  refine ⟨_, h0, ?_⟩
  have hnB : nrm (fix (T N U g)) = fix (T N U g) := by simp [nrm, h0]
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Φ, h0, hU, cc_subst hg0]
  · have := congrArg (coeff n) hB
    simp only [T, coeff_mk, hn.ne', ite_false, hnB, map_sub] at this
    simp only [map_zero]
    linear_combination -this

end Hanna

/-! ## The type-A series over `ℤ` -/

section TypeA
variable {R : Type*} [CommRing R]

lemma cc_mk_one : constantCoeff (mk 1 : R⟦X⟧) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, Pi.one_apply]

lemma cc_X_mul_mk_one : constantCoeff (X * mk 1 : R⟦X⟧) = 0 := by simp

lemma X_sq_dvd_X_mul_sub {v : R⟦X⟧} (hv : constantCoeff v = 1) : X ^ 2 ∣ X * v - X := by
  rw [show X * v - X = X * (v - 1) by ring, pow_two]
  exact mul_dvd_mul_left X (X_dvd_sub_one hv)

/-- Hanna's type-A series over `ℤ`: `B^(N+1) = BINOMIAL(B)^N`, `B(0) = 1`. -/
noncomputable def typeA (N : ℕ) : ℤ⟦X⟧ := fix (T N ((mk 1) ^ N) (X * mk 1))

lemma typeA_spec (N : ℕ) :
    constantCoeff (typeA N) = 1 ∧ Φ N ((mk 1) ^ N) (X * mk 1) (typeA N) = 0 := by
  have hU : constantCoeff ((mk 1 : ℤ⟦X⟧) ^ N) = 1 := by simp
  have hB := (T_causal hU cc_X_mul_mk_one (X_sq_dvd_X_mul_sub cc_mk_one) (N := N)).fix_eq
  have h0 : constantCoeff (typeA N) = 1 := by
    rw [typeA, ← coeff_zero_eq_constantCoeff_apply, ← hB]
    simp [T]
  refine ⟨h0, ?_⟩
  have hnB : nrm (typeA N) = typeA N := by simp [nrm, h0]
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Φ, h0, hU, cc_subst cc_X_mul_mk_one]
  · have := congrArg (coeff n) hB
    simp only [T, coeff_mk, hn.ne', ite_false, map_sub] at this
    rw [← typeA, hnB] at this
    simp only [map_zero]
    linear_combination -this

/-- The coefficients of `BINOMIAL(F) = (1 - X)⁻¹ F(X/(1 - X))`, written with `mk 1 = (1 - X)⁻¹`. -/
lemma coeff_binA (F : R⟦X⟧) (n : ℕ) :
    coeff n (mk 1 * F.subst (X * mk 1 : R⟦X⟧)) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : R) * coeff j F := by
  rw [subst_eq_sum cc_X_mul_mk_one F (n + 1), mul_add, map_add, Finset.mul_sum, map_sum]
  have hz : coeff n (mk 1 * ((X * mk 1 : R⟦X⟧) ^ (n + 1) *
      (mk fun i => coeff (i + (n + 1)) F).subst (X * mk 1 : R⟦X⟧))) = 0 := by
    have : X ^ (n + 1) ∣ mk 1 * ((X * mk 1 : R⟦X⟧) ^ (n + 1) *
        (mk fun i => coeff (i + (n + 1)) F).subst (X * mk 1 : R⟦X⟧)) := by
      rw [mul_pow]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _) _
    exact X_pow_dvd_iff.mp this n (Nat.lt_succ_self n)
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e : mk 1 * (C (coeff j F) * (X * mk 1 : R⟦X⟧) ^ j) =
      C (coeff j F) * (X ^ j * (mk 1) ^ (j + 1)) := by ring
  rw [e, coeff_C_mul, coeff_X_pow_mul']
  simp only [hjn, ↓reduceIte]
  rw [mk_one_pow_eq_mk_choose_add, coeff_mk, Nat.add_sub_cancel' hjn, mul_comm]

end TypeA

/-! ## Binomial transforms over `ℚ` and the bridge -/

section Rat

/-- `(1 - c X)⁻¹`. -/
noncomputable def ginv (c : ℚ) : ℚ⟦X⟧ := (1 - C c * X)⁻¹

lemma lin_mul_ginv (c : ℚ) : (1 - C c * X) * ginv c = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp)

lemma cc_ginv (c : ℚ) : constantCoeff (ginv c) = 1 := by simp [ginv]

lemma cc_g (c : ℚ) : constantCoeff (X * ginv c) = 0 := by simp

lemma mk_one_eq_ginv : (mk 1 : ℚ⟦X⟧) = ginv 1 := by
  rw [ginv, map_one, one_mul, PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  exact mk_one_mul_one_sub_eq_one ℚ

lemma subst_inv {g : ℚ⟦X⟧} (hg : constantCoeff g = 0) {u : ℚ⟦X⟧} (hu : constantCoeff u ≠ 0) :
    (u⁻¹).subst g = (u.subst g)⁻¹ := by
  symm
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by rwa [cc_subst hg]), ← subst_mul (hs hg),
    PowerSeries.inv_mul_cancel _ hu, subst_one' hg]

lemma subst_ginv (a b : ℚ) : (ginv b).subst (X * ginv a) = (1 - C a * X) * ginv (a + b) := by
  have hg := cc_g a
  rw [show ginv b = (1 - C b * X)⁻¹ from rfl, subst_inv hg (by simp), subst_sub (hs hg),
    subst_one' hg, subst_mul (hs hg), subst_C' hg, subst_X (hs hg),
    PowerSeries.inv_eq_iff_mul_eq_one (by simp)]
  have h1 := lin_mul_ginv a
  have h2 := lin_mul_ginv (a + b)
  rw [map_add] at h2
  linear_combination h2 + (-(C b) * X * ginv (a + b)) * h1

lemma subst_g (a b : ℚ) : (X * ginv b).subst (X * ginv a) = X * ginv (a + b) := by
  rw [subst_mul (hs (cc_g a)), subst_X (hs (cc_g a)), subst_ginv]
  linear_combination (X * ginv (a + b)) * lin_mul_ginv a

/-- The iterated binomial transform `F ↦ (1 - c X)⁻¹ F(X/(1 - c X))`. -/
noncomputable def binc (c : ℚ) (F : ℚ⟦X⟧) : ℚ⟦X⟧ := ginv c * F.subst (X * ginv c)

lemma binc_binc (a b : ℚ) (F : ℚ⟦X⟧) : binc a (binc b F) = binc (a + b) F := by
  simp only [binc]
  rw [subst_mul (hs (cc_g a)), subst_ginv, subst_assoc (cc_g b) (cc_g a), subst_g]
  linear_combination (ginv (a + b) * F.subst (X * ginv (a + b))) * lin_mul_ginv a

lemma cc_binc (c : ℚ) (F : ℚ⟦X⟧) : constantCoeff (binc c F) = constantCoeff F := by
  rw [binc, map_mul, cc_ginv, cc_subst (cc_g c), one_mul]

lemma coeff_binc_one (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (binc 1 F) = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℚ) * coeff j F := by
  rw [binc, ← mk_one_eq_ginv, coeff_binA]

lemma rescale_inv {u : ℚ⟦X⟧} (hu : constantCoeff u ≠ 0) (r : ℚ) :
    rescale r (u⁻¹) = (rescale r u)⁻¹ := by
  symm
  have hc : constantCoeff (rescale r u) = constantCoeff u := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by rwa [hc]), ← map_mul,
    PowerSeries.inv_mul_cancel _ hu, map_one]

lemma rescale_ginv : rescale 2 (ginv 1) = ginv 2 := by
  rw [ginv, rescale_inv (by simp), map_sub, map_one, map_mul, rescale_X, ginv]
  simp

lemma rescale_subst {g : ℚ⟦X⟧} (hg : constantCoeff g = 0) (F : ℚ⟦X⟧) :
    rescale 2 (F.subst g) = F.subst (rescale 2 g) := by
  rw [rescale_eq_subst, rescale_eq_subst 2 g, subst_assoc hg (by simp)]

lemma rescale_binc (F : ℚ⟦X⟧) : rescale 2 (binc 1 F) = binc 2 (rescale 2 F) := by
  simp only [binc]
  rw [map_mul, rescale_ginv, rescale_subst (cc_g 1), map_mul, rescale_X, rescale_ginv,
    rescale_eq_subst 2 F, subst_assoc (by simp) (cc_g 2), smul_eq_C_mul,
    subst_mul (hs (cc_g 2)), subst_C' (cc_g 2), subst_X (hs (cc_g 2)), mul_assoc]

/-- The type-B equation for `binc 1 D` from the scaled type-A equation for `D`. -/
lemma bridge (N : ℕ) {D : ℚ⟦X⟧} (hD : D ^ (N + 1) = (binc 2 D) ^ N) :
    (binc 1 D) ^ (N + 1) = ginv 1 * (binc 1 (binc 1 (binc 1 D))) ^ N := by
  have h3 : binc 1 (binc 1 (binc 1 D)) = binc 1 (binc 2 D) := by
    rw [binc_binc, binc_binc, binc_binc]; norm_num
  rw [h3]
  show (ginv 1 * D.subst (X * ginv 1)) ^ (N + 1) =
    ginv 1 * (ginv 1 * (binc 2 D).subst (X * ginv 1)) ^ N
  rw [mul_pow, mul_pow, ← subst_pow (hs (cc_g 1)), hD, subst_pow (hs (cc_g 1))]
  ring

end Rat

/-! ## Existence, uniqueness and integrality -/

section Main

lemma binomial_eq : binomial = binc 1 := by
  funext F; simp [binomial, binc, ginv]

lemma ginv_one : ginv 1 = (1 - X)⁻¹ := by simp [ginv]

lemma ginv_two : ginv 2 = (1 - 2 * X)⁻¹ := by
  rw [ginv, show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]

lemma binomial_binomial (A : ℚ⟦X⟧) : binomial (binomial A) = binc 2 A := by
  rw [binomial_eq, binc_binc]; norm_num

/-- The two forms of the equation in the entries agree:
$\mathrm{BINOMIAL}(\mathrm{BINOMIAL}(A))^N = \frac{1}{(1-2z)^N} A^N(\frac{z}{1-2z})$. -/
theorem isSolution_iff (N : ℕ) (A : ℚ⟦X⟧) : IsSolution N A ↔ constantCoeff A = 1 ∧
    A ^ (N + 1) = (1 - X)⁻¹ * (1 - 2 * X)⁻¹ ^ N * (A ^ N).subst (X * (1 - 2 * X)⁻¹ : ℚ⟦X⟧) := by
  rw [IsSolution, binomial_binomial, binc, mul_pow, ← subst_pow (hs (cc_g 2)), ginv_two,
    mul_assoc]

lemma isSolution_iff_Φ (N : ℕ) (A : ℚ⟦X⟧) : IsSolution N A ↔
    constantCoeff A = 1 ∧ Φ N (ginv 1 * ginv 2 ^ N) (X * ginv 2) A = 0 := by
  rw [IsSolution, binomial_binomial, Φ, sub_eq_zero, binc, mul_pow, ginv_one, mul_assoc]

lemma Φ_hyps (N : ℕ) : constantCoeff (ginv 1 * ginv 2 ^ N) = 1 ∧
    constantCoeff (X * ginv 2) = 0 ∧ X ^ 2 ∣ X * ginv 2 - X :=
  ⟨by simp [cc_ginv], cc_g 2, X_sq_dvd_X_mul_sub (cc_ginv 2)⟩

lemma map_mk_one : map (Int.castRingHom ℚ) (mk 1 : ℤ⟦X⟧) = mk 1 := by
  ext n; simp [coeff_map]

lemma map_subst' {g : ℤ⟦X⟧} (hg : constantCoeff g = 0) (f : ℤ⟦X⟧) :
    map (Int.castRingHom ℚ) (f.subst g) =
      (map (Int.castRingHom ℚ) f).subst (map (Int.castRingHom ℚ) g) :=
  map_subst (hs hg) f

/-- The type-A series over `ℚ`. -/
noncomputable def typeAQ (N : ℕ) : ℚ⟦X⟧ := map (Int.castRingHom ℚ) (typeA N)

lemma cc_typeAQ (N : ℕ) : constantCoeff (typeAQ N) = 1 := by
  rw [typeAQ, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
    (typeA_spec N).1, map_one]

lemma typeAQ_eq (N : ℕ) : typeAQ N ^ (N + 1) = (binc 1 (typeAQ N)) ^ N := by
  have h := congrArg (map (Int.castRingHom ℚ)) (typeA_spec N).2
  rw [Φ, map_sub, map_mul, map_pow, map_pow, map_pow, map_subst' cc_X_mul_mk_one, map_zero,
    sub_eq_zero, map_mul, map_X, map_mk_one, mk_one_eq_ginv] at h
  rw [binc, mul_pow]
  exact h

/-- The solution: `binc 1 (B(2z))` with `B` the type-A series. -/
noncomputable def sol (N : ℕ) : ℚ⟦X⟧ := binc 1 (rescale 2 (typeAQ N))

lemma isSolution_sol (N : ℕ) : IsSolution N (sol N) := by
  refine ⟨?_, ?_⟩
  · rw [sol, cc_binc, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply, cc_typeAQ]
  · have hD : (rescale 2 (typeAQ N)) ^ (N + 1) = (binc 2 (rescale 2 (typeAQ N))) ^ N := by
      rw [← map_pow, typeAQ_eq, map_pow, rescale_binc]
    rw [sol, bridge N hD, binomial_eq, ginv_one]

/-- For every $N$, exactly one $A \in \mathbb{Q}[[z]]$ with $A(0) = 1$ satisfies the type-B
equation. -/
theorem existsUnique (N : ℕ) : ∃! A : ℚ⟦X⟧, IsSolution N A := by
  refine ⟨sol N, isSolution_sol N, fun A hA => ?_⟩
  obtain ⟨hU, hg0, hg⟩ := Φ_hyps N
  have h1 := (isSolution_iff_Φ N A).mp hA
  have h2 := (isSolution_iff_Φ N (sol N)).mp (isSolution_sol N)
  exact Φ_unique hU hg0 hg h2.1 h1.1 h2.2 h1.2

/-- The type-A coefficients. -/
noncomputable def bZ (N m : ℕ) : ℤ := coeff m (typeA N)

/-- The type-B coefficients, `a(n) = ∑ C(n, m) 2^m b(m)`. -/
noncomputable def aZ (N n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), (n.choose m : ℤ) * 2 ^ m * bZ N m

lemma coeff_sol (N n : ℕ) : coeff n (sol N) = (aZ N n : ℚ) := by
  rw [sol, coeff_binc_one, aZ]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rescale, typeAQ, coeff_map, bZ]
  simp; ring

lemma coeff_of_isSolution {N : ℕ} {A : ℚ⟦X⟧} (hA : IsSolution N A) (n : ℕ) :
    coeff n A = (aZ N n : ℚ) := by
  rw [(existsUnique N).unique hA (isSolution_sol N), coeff_sol]

lemma eq_aZ {N : ℕ} {A : ℚ⟦X⟧} (hA : IsSolution N A) {a : ℕ → ℤ} (ha : ∀ n, coeff n A = a n) :
    a = aZ N := by
  funext n
  exact_mod_cast (ha n).symm.trans (coeff_of_isSolution hA n)

/-- The coefficients $a(n)$ are integers. -/
theorem exists_int_coeff (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) :
    ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n :=
  ⟨aZ N, coeff_of_isSolution hA⟩

end Main

/-! ## The coefficients `b(1) = N` and `2 b(2) = 3N² + N` -/

section SmallCoeff
variable {R : Type*} [CommRing R]

lemma coeff_one_mul' (f g : R⟦X⟧) :
    coeff 1 (f * g) = constantCoeff f * coeff 1 g + coeff 1 f * constantCoeff g := by
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]

lemma coeff_two_mul' (f g : R⟦X⟧) : coeff 2 (f * g) =
    constantCoeff f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * constantCoeff g := by
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]
  ring

lemma coeff_one_pow' {f : R⟦X⟧} (hf : constantCoeff f = 1) (k : ℕ) :
    coeff 1 (f ^ k) = k * coeff 1 f := by
  induction k with
  | zero => simp [coeff_one]
  | succ k ih =>
    rw [pow_succ, coeff_one_mul', ih, hf, map_pow, hf, one_pow]
    push_cast; ring

lemma coeff_two_pow' {f : R⟦X⟧} (hf : constantCoeff f = 1) (k : ℕ) :
    coeff 2 (f ^ k) = k * coeff 2 f + (k.choose 2 : R) * coeff 1 f ^ 2 := by
  induction k with
  | zero => simp [coeff_one]
  | succ k ih =>
    rw [pow_succ, coeff_two_mul', ih, coeff_one_pow' hf, hf, map_pow, hf, one_pow,
      Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast; ring

end SmallCoeff

section SmallB

lemma typeA_eq (N : ℕ) :
    typeA N ^ (N + 1) = (mk 1 * (typeA N).subst (X * mk 1 : ℤ⟦X⟧)) ^ N := by
  have h := (typeA_spec N).2
  rw [Φ, sub_eq_zero] at h
  rw [h, mul_pow]

lemma cc_binA (N : ℕ) : constantCoeff (mk 1 * (typeA N).subst (X * mk 1 : ℤ⟦X⟧)) = 1 := by
  rw [map_mul, cc_mk_one, cc_subst cc_X_mul_mk_one, (typeA_spec N).1, one_mul]

lemma bZ_zero (N : ℕ) : bZ N 0 = 1 := by
  rw [bZ, coeff_zero_eq_constantCoeff_apply, (typeA_spec N).1]

lemma bZ_one (N : ℕ) : bZ N 1 = N := by
  have h := congrArg (coeff 1) (typeA_eq N)
  rw [coeff_one_pow' (typeA_spec N).1, coeff_one_pow' (cc_binA N), coeff_binA] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul, coeff_zero_eq_constantCoeff_apply,
    (typeA_spec N).1] at h
  rw [bZ]
  push_cast at h
  linear_combination h

lemma choose_two_mul (x : ℕ) : ((x.choose 2 : ℕ) : ℤ) * 2 = x * ((x : ℤ) - 1) := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

lemma bZ_two (N : ℕ) : 2 * bZ N 2 = 3 * (N : ℤ) ^ 2 + N := by
  have h := congrArg (coeff 2) (typeA_eq N)
  rw [coeff_two_pow' (typeA_spec N).1, coeff_two_pow' (cc_binA N), coeff_binA, coeff_binA] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul, coeff_zero_eq_constantCoeff_apply,
    (typeA_spec N).1, Nat.choose_one_right] at h
  have h1 := bZ_one N
  rw [bZ] at h1
  rw [h1, Nat.choose_succ_succ', Nat.choose_one_right] at h
  have hc := choose_two_mul N
  rw [bZ]
  push_cast at h
  linear_combination 2 * h + (1 + 2 * (N : ℤ)) * hc

end SmallB

/-! ## Periodicity modulo powers of `2` -/

section TwoAdic

lemma two_pow_dvd_mul_choose (t : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ∃ v, 2 ^ v ≤ r ∧ 2 ^ t ∣ 2 ^ v * (2 ^ t).choose r := by
  obtain ⟨v, o, ho, hro⟩ := Nat.exists_eq_two_pow_mul_odd (n := r) (by omega)
  refine ⟨v, ?_, ?_⟩
  · rw [hro]; exact Nat.le_mul_of_pos_right _ ho.pos
  · have key := Nat.add_one_mul_choose_eq (2 ^ t - 1) (r - 1)
    rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.sub_add_cancel hr] at key
    have h1 : 2 ^ t ∣ (2 ^ v * (2 ^ t).choose r) * o := by
      refine ⟨(2 ^ t - 1).choose (r - 1), ?_⟩
      calc 2 ^ v * (2 ^ t).choose r * o = (2 ^ t).choose r * (2 ^ v * o) := by ring
        _ = (2 ^ t).choose r * r := by rw [← hro]
        _ = _ := key.symm
    exact (Nat.Coprime.pow_left t (Nat.coprime_two_left.mpr ho)).dvd_of_dvd_mul_right h1

lemma dvd_two_pow_mul_choose {t m j r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m)
    (hj : ∀ v, 2 ^ v ≤ m → j + v ≤ m) : 2 ^ (t + j) ∣ 2 ^ m * (2 ^ t).choose r := by
  obtain ⟨v, hv, hdvd⟩ := two_pow_dvd_mul_choose t hr
  have hjv := hj v (hv.trans hrm)
  have : 2 ^ m * (2 ^ t).choose r = 2 ^ (m - v) * (2 ^ v * (2 ^ t).choose r) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
  rw [this, pow_add, mul_comm (2 ^ t)]
  exact mul_dvd_mul (pow_dvd_pow 2 (by omega)) hdvd

/-- The Vandermonde–Kummer bound: `2^(t+j)` divides `2^m (C(n + 2^t, m) - C(n, m))` when
`j + v ≤ m` for every `v` with `2^v ≤ m`. -/
lemma choose_shift (t m n : ℕ) {j : ℕ} (hj : ∀ v, 2 ^ v ≤ m → j + v ≤ m) :
    (2 : ℤ) ^ (t + j) ∣ 2 ^ m * (((n + 2 ^ t).choose m : ℤ) - n.choose m) := by
  have hV : (n + 2 ^ t).choose m = n.choose m +
      ∑ k ∈ Finset.range m, (2 ^ t).choose (k + 1) * n.choose (m - (k + 1)) := by
    rw [add_comm n, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ']
    simp [add_comm]
  rw [hV]
  push_cast
  rw [add_sub_cancel_left, Finset.mul_sum]
  apply Finset.dvd_sum
  intro k hk
  have hkm : k + 1 ≤ m := Finset.mem_range.mp hk
  have := dvd_two_pow_mul_choose (t := t) (by omega : 1 ≤ k + 1) hkm hj
  rw [← mul_assoc]
  exact Dvd.dvd.mul_right (by exact_mod_cast this) _

lemma aZ_eq_sum (N : ℕ) {n M : ℕ} (hM : n < M) :
    aZ N n = ∑ m ∈ Finset.range M, (n.choose m : ℤ) * 2 ^ m * bZ N m := by
  rw [aZ]
  apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
  intro m _ hm'
  simp only [Finset.mem_range, not_lt] at hm'
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

lemma aZ_sub (N n P : ℕ) : aZ N (n + P) - aZ N n = ∑ m ∈ Finset.range (n + P + 1),
    2 ^ m * (((n + P).choose m : ℤ) - n.choose m) * bZ N m := by
  rw [aZ_eq_sum N (Nat.lt_succ_self (n + P)), aZ_eq_sum N (M := n + P + 1) (by omega),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- Theorem 4: period `2^(k-1)` modulo `2^k`. -/
theorem aZ_periodic (N k n : ℕ) (hk : 1 ≤ k) :
    (2 : ℤ) ^ k ∣ aZ N (n + 2 ^ (k - 1)) - aZ N n := by
  rw [aZ_sub]
  apply Finset.dvd_sum
  intro m _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have := choose_shift (k - 1) m n (j := 1)
      (fun v hv => by have := Nat.lt_two_pow_self (n := v); omega)
    rw [show k - 1 + 1 = k by omega] at this
    exact Dvd.dvd.mul_right this _

lemma two_pow_le_aux {m v : ℕ} (hm : 3 ≤ m) (hv : 2 ^ v ≤ m) : 2 + v ≤ m := by
  by_contra h
  have h1 : m - 1 ≤ v := by omega
  have h2 : 2 ^ (m - 1) ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) h1
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 3 := ⟨m - 3, by omega⟩
  have h3 : 2 ^ (q + 2) = 4 * 2 ^ q := by ring
  have h4 := Nat.lt_two_pow_self (n := q)
  rw [show q + 3 - 1 = q + 2 by omega, h3] at h2
  omega

/-- Theorem 5: the shift by `2^(k-2)` modulo `2^k`. -/
theorem aZ_shift (N k n : ℕ) (hk : 3 ≤ k) :
    (2 : ℤ) ^ k ∣ aZ N (n + 2 ^ (k - 2)) - aZ N n - 2 ^ (k - 2) * (3 * N * (N + 1)) := by
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 3 := ⟨k - 3, by omega⟩
  have hP : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
  rw [show s + 3 - 2 = s + 1 by omega, aZ_sub,
    ← Finset.sum_range_add_sum_Ico _ (show 3 ≤ n + 2 ^ (s + 1) + 1 by omega)]
  have hrest : (2 : ℤ) ^ (s + 3) ∣ ∑ m ∈ Finset.Ico 3 (n + 2 ^ (s + 1) + 1),
      2 ^ m * (((n + 2 ^ (s + 1)).choose m : ℤ) - n.choose m) * bZ N m := by
    apply Finset.dvd_sum
    intro m hm
    have hm3 : 3 ≤ m := (Finset.mem_Ico.mp hm).1
    have := choose_shift (s + 1) m n (j := 2) (fun v hv => two_pow_le_aux hm3 hv)
    rw [show s + 1 + 2 = s + 3 by omega] at this
    exact Dvd.dvd.mul_right this _
  have hfirst : (2 : ℤ) ^ (s + 3) ∣ ∑ m ∈ Finset.range 3,
      2 ^ m * (((n + 2 ^ (s + 1)).choose m : ℤ) - n.choose m) * bZ N m -
        2 ^ (s + 1) * (3 * N * (N + 1)) := by
    have hcA := choose_two_mul (n + 2 ^ (s + 1))
    have hcB := choose_two_mul n
    have hb1 := bZ_one N
    have hb2 := bZ_two N
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
      Nat.choose_one_right]
    push_cast at hcA ⊢
    refine ⟨bZ N 2 * n + bZ N 2 * 2 ^ s - bZ N 2, ?_⟩
    linear_combination (4 * 2 ^ s) * hb1 + (2 * bZ N 2) * hcA - (2 * bZ N 2) * hcB +
      (2 * 2 ^ s) * hb2
  have := dvd_add hfirst hrest
  convert this using 1
  ring

end TwoAdic

/-! ## Least periods -/

section Period

lemma iterate_shift {β : Type*} (s : ℕ → β) (p : ℕ) :
    (fun t : ℕ → β => fun n => t (n + 1))^[p] s = fun n => s (n + p) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [Function.iterate_succ_apply', ih]
    funext n
    exact congrArg s (by omega)

lemma isPeriodicPt_shift_iff (a : ℕ → ℤ) (m p : ℕ) :
    Function.IsPeriodicPt (fun s : ℕ → ZMod m => fun n => s (n + 1)) p
      (fun n => (a n : ZMod m)) ↔ ∀ n, a (n + p) ≡ a n [ZMOD m] := by
  rw [Function.IsPeriodicPt, Function.IsFixedPt, iterate_shift, funext_iff]
  simp only [ZMod.intCast_eq_intCast_iff]

lemma leastPeriodMod_dvd_of {a : ℕ → ℤ} {m p : ℕ} (h : ∀ n, a (n + p) ≡ a n [ZMOD m]) :
    leastPeriodMod a m ∣ p :=
  ((isPeriodicPt_shift_iff a m p).mpr h).minimalPeriod_dvd

lemma leastPeriodMod_eq_two_pow {a : ℕ → ℤ} {m j : ℕ}
    (h1 : ∀ n, a (n + 2 ^ (j + 1)) ≡ a n [ZMOD m]) (h2 : ¬ ∀ n, a (n + 2 ^ j) ≡ a n [ZMOD m]) :
    leastPeriodMod a m = 2 ^ (j + 1) :=
  Function.minimalPeriod_eq_prime_pow (hp := Nat.fact_prime_two)
    (by rwa [isPeriodicPt_shift_iff]) (by rwa [isPeriodicPt_shift_iff])

lemma modEq_mod {a : ℕ → ℤ} {m P : ℕ} (h : ∀ n, a (n + P) ≡ a n [ZMOD m]) (n : ℕ) :
    a n ≡ a (n % P) [ZMOD m] := by
  conv_lhs => rw [← Nat.mod_add_div n P]
  generalize n / P = q
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc]; exact (h _).trans ih

/-- A pattern of length `2^(j+1)` whose two halves start differently has least period
`2^(j+1)`. -/
lemma leastPeriodMod_of_pattern {a : ℕ → ℤ} {m q j : ℕ} [NeZero q] (hq : q = 2 ^ (j + 1))
    (v : Fin q → ZMod m) (h : ∀ n, (a n : ZMod m) = v (Fin.ofNat q n))
    (hne : v (Fin.ofNat q 0) ≠ v (Fin.ofNat q (2 ^ j))) : leastPeriodMod a m = q := by
  have hof : ∀ n, Fin.ofNat q (n + q) = Fin.ofNat q n := fun n => by
    ext; simp
  subst hq
  refine leastPeriodMod_eq_two_pow (fun n => ?_) (fun hall => hne ?_)
  · rw [← ZMod.intCast_eq_intCast_iff, h, h, hof]
  · have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hall 0)
    rw [h, h, zero_add] at this
    exact this.symm

end Period

section Results

/-- For $k \ge 1$ and all $n \ge 0$: $a(n + 2^{k-1}) \equiv a(n) \pmod{2^k}$. -/
theorem periodic (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    a (n + 2 ^ (k - 1)) ≡ a n [ZMOD 2 ^ k] := by
  rw [eq_aZ hA ha]
  exact (Int.modEq_iff_dvd.mpr (aZ_periodic N k n hk)).symm

/-- For $k \ge 1$, $a(n) \bmod 2^k$ is purely periodic with least period dividing $2^{k-1}$. -/
theorem leastPeriodMod_dvd (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (k : ℕ) (hk : 1 ≤ k) :
    leastPeriodMod a (2 ^ k) ∣ 2 ^ (k - 1) :=
  leastPeriodMod_dvd_of fun n => by push_cast; exact periodic N A hA a ha k hk n

/-- For $k \ge 3$ and all $n \ge 0$:
$a(n + 2^{k-2}) - a(n) \equiv 2^{k-2} \cdot 3N(N+1) \pmod{2^k}$. -/
theorem shift_sub (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (k : ℕ) (hk : 3 ≤ k) (n : ℕ) :
    a (n + 2 ^ (k - 2)) - a n ≡ 2 ^ (k - 2) * (3 * N * (N + 1)) [ZMOD 2 ^ k] := by
  rw [eq_aZ hA ha]
  exact (Int.modEq_iff_dvd.mpr (by simpa using aZ_shift N k n hk)).symm

lemma four_dvd_iff (N : ℕ) : (4 : ℤ) ∣ 3 * N * (N + 1) ↔ ¬ (N % 4 = 1 ∨ N % 4 = 2) := by
  have : (4 : ℤ) ∣ 3 * N * (N + 1) ↔ 4 ∣ 3 * N * (N + 1) := by exact_mod_cast Iff.rfl
  rw [this, Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mul_mod 3, Nat.add_mod N]
  have h := Nat.mod_lt N (show 4 > 0 by norm_num)
  interval_cases N % 4 <;> simp

/-- For $k \ge 3$, the least period of $a(n) \bmod 2^k$ is exactly $2^{k-1}$ if and only if
$N \equiv 1, 2 \pmod 4$. (For $k = 2$ it is $2$ for every odd $N$.) -/
theorem leastPeriodMod_eq_iff (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (k : ℕ) (hk : 3 ≤ k) :
    leastPeriodMod a (2 ^ k) = 2 ^ (k - 1) ↔ N % 4 = 1 ∨ N % 4 = 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have hsh := shift_sub N A hA a ha (j + 3) hk
  simp only [show j + 3 - 2 = j + 1 by omega, show j + 3 - 1 = j + 2 by omega] at hsh ⊢
  constructor
  · intro h
    by_contra hN
    obtain ⟨c, hc⟩ := (four_dvd_iff N).mpr hN
    have hper : ∀ n, a (n + 2 ^ (j + 1)) ≡ a n [ZMOD ((2 ^ (j + 3) : ℕ) : ℤ)] := by
      intro n
      have h1 := hsh n
      have h2 : (2 : ℤ) ^ (j + 1) * (3 * N * (N + 1)) ≡ 0 [ZMOD 2 ^ (j + 3)] := by
        rw [hc, Int.modEq_zero_iff_dvd]
        exact ⟨c, by ring⟩
      push_cast
      exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by
        have := Int.ModEq.trans h1 h2
        simpa using (Int.modEq_iff_dvd.mp this.symm)))
    have hle := Nat.le_of_dvd (by positivity) (leastPeriodMod_dvd_of hper)
    rw [h] at hle
    have : 2 ^ (j + 1) < 2 ^ (j + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · intro hN
    refine leastPeriodMod_eq_two_pow (j := j + 1) (fun n => ?_) (fun hall => ?_)
    · push_cast; exact periodic N A hA a ha (j + 3) (by omega) n
    · have h0 := hsh 0
      have h1 := hall 0
      push_cast at h1
      have h3 : (2 : ℤ) ^ (j + 1) * (3 * N * (N + 1)) ≡ 0 [ZMOD 2 ^ (j + 3)] :=
        h0.symm.trans (Int.modEq_iff_dvd.mpr (by
          have := Int.modEq_iff_dvd.mp h1.symm; simpa using this)).symm
      rw [Int.modEq_zero_iff_dvd, show j + 3 = (j + 1) + 2 by omega, pow_add] at h3
      have h4 := (Int.dvd_of_mul_dvd_mul_left (by positivity) h3)
      exact (four_dvd_iff N).mp (by simpa using h4) hN

end Results

section Residues

lemma aZ_trunc (N n k : ℕ) :
    aZ N n ≡ ∑ m ∈ Finset.range k, (n.choose m : ℤ) * 2 ^ m * bZ N m [ZMOD 2 ^ k] := by
  rw [aZ_eq_sum N (M := k + (n + 1)) (by omega),
    ← Finset.sum_range_add_sum_Ico _ (by omega : k ≤ k + (n + 1))]
  refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ?_)
  rw [add_sub_cancel_left]
  apply Finset.dvd_sum
  intro m hm
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow 2 (Finset.mem_Ico.mp hm).1) _) _

lemma aZ_mod_two (N n : ℕ) : aZ N n ≡ 1 [ZMOD 2] := by
  simpa [bZ_zero] using aZ_trunc N n 1

lemma aZ_mod_four (N n : ℕ) : aZ N n ≡ 1 + 2 * n * N [ZMOD 4] := by
  have h := aZ_trunc N n 2
  have e : ∑ m ∈ Finset.range 2, (n.choose m : ℤ) * 2 ^ m * bZ N m = 1 + 2 * n * N := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
      Nat.choose_one_right, bZ_zero, bZ_one]
    push_cast; ring
  rw [e] at h
  norm_num at h
  exact h

/-- Every $a(n)$ is odd. -/
theorem odd (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (n : ℕ) : Odd (a n) := by
  rw [eq_aZ hA ha, Int.odd_iff]
  exact aZ_mod_two N n

lemma leastPeriodMod_two (N : ℕ) : leastPeriodMod (aZ N) 2 = 1 :=
  Nat.dvd_one.mp (leastPeriodMod_dvd_of fun n => by
    push_cast; exact (aZ_mod_two N _).trans (aZ_mod_two N n).symm)

lemma leastPeriodMod_four (N : ℕ) (hN : N % 2 = 1) : leastPeriodMod (aZ N) 4 = 2 := by
  refine leastPeriodMod_eq_two_pow (j := 0) (fun n => ?_) (fun hall => ?_)
  · have := (Int.modEq_iff_dvd.mpr (aZ_periodic N 2 n (by norm_num))).symm
    norm_num at this ⊢
    exact this
  · have h0 := hall 0
    have h1 := aZ_mod_four N 1
    have h2 := aZ_mod_four N 0
    norm_num at h0 h1 h2
    have := (h1.symm.trans h0).trans h2
    unfold Int.ModEq at this
    omega

end Residues

/-! ## Small type-A coefficients by a finite check -/

section Values

/-- Coefficient `n` of the `k`-th power of the series with coefficients `f`. -/
def cpow (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ i ∈ Finset.range (n + 1), cpow f k i * f (n - i)

/-- The binomial transform of a sequence. -/
def binS (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * f j

lemma coeff_pow_cpow (F : ℤ⟦X⟧) (k n : ℕ) :
    coeff n (F ^ k) = cpow (fun i => coeff i F) k n := by
  induction k generalizing n with
  | zero => simp [cpow, coeff_one]
  | succ k ih =>
    rw [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, cpow]
    simp only [ih]

/-- The first `M` type-A coefficients from a finite check of the equation below degree `M`. -/
lemma bZ_eq_of_check (N M : ℕ) (p : ℕ → ℤ) (hp0 : p 0 = 1)
    (h : ∀ n < M, cpow p (N + 1) n = cpow (binS p) N n) : ∀ m < M, bZ N m = p m := by
  have hP : constantCoeff (mk p) = 1 := by rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, hp0]
  have hU : constantCoeff ((mk 1 : ℤ⟦X⟧) ^ N) = 1 := by simp
  have hdvd : X ^ M ∣ Φ N ((mk 1) ^ N) (X * mk 1) (mk p) := by
    rw [X_pow_dvd_iff]
    intro n hn
    have hb : (fun i => coeff i (mk 1 * (mk p).subst (X * mk 1 : ℤ⟦X⟧))) = binS p := by
      funext i; rw [coeff_binA]; simp [binS]
    rw [Φ, ← mul_pow, map_sub, coeff_pow_cpow, coeff_pow_cpow, hb]
    simp only [coeff_mk]
    rw [h n hn, sub_self]
  have h2 := Φ_dvd hU cc_X_mul_mk_one (X_sq_dvd_X_mul_sub cc_mk_one) (typeA_spec N).1 hP
    (typeA_spec N).2 hdvd
  intro m hm
  have := X_pow_dvd_iff.mp h2 m hm
  rw [map_sub, sub_eq_zero, coeff_mk] at this
  rw [bZ, this]

lemma bZ_vals_one : ∀ m < 4, bZ 1 m = [1, 1, 2, 6].getD m 0 :=
  bZ_eq_of_check 1 4 _ rfl (by decide +kernel)

lemma bZ_vals_two : ∀ m < 4, bZ 2 m = [1, 2, 7, 36].getD m 0 :=
  bZ_eq_of_check 2 4 _ rfl (by decide +kernel)

lemma bZ_vals_three : ∀ m < 4, bZ 3 m = [1, 3, 15, 109].getD m 0 :=
  bZ_eq_of_check 3 4 _ rfl (by decide +kernel)

lemma bZ_vals_four : ∀ m < 5, bZ 4 m = [1, 4, 26, 244, 3131].getD m 0 :=
  bZ_eq_of_check 4 5 _ rfl (by decide +kernel)

lemma bZ_vals_five : ∀ m < 4, bZ 5 m = [1, 5, 40, 460].getD m 0 :=
  bZ_eq_of_check 5 4 _ rfl (by decide +kernel)

/-- A residue pattern from a finite check over one period `2^(k-1)`. -/
lemma pattern_of_check {N k m : ℕ} (hm : m = 2 ^ k) (hk : 1 ≤ k) (p : ℕ → ℤ)
    (hb : ∀ i < k, bZ N i = p i) {q : ℕ} [NeZero q] (hq : q ∣ 2 ^ (k - 1))
    (v : Fin q → ZMod m) (hchk : ∀ r < 2 ^ (k - 1),
      ((∑ i ∈ Finset.range k, (r.choose i : ℤ) * 2 ^ i * p i : ℤ) : ZMod m) = v (Fin.ofNat q r))
    (n : ℕ) : (aZ N n : ZMod m) = v (Fin.ofNat q n) := by
  subst hm
  have hper : ∀ n, aZ N (n + 2 ^ (k - 1)) ≡ aZ N n [ZMOD ((2 ^ k : ℕ) : ℤ)] := fun n => by
    push_cast; exact (Int.modEq_iff_dvd.mpr (aZ_periodic N k n hk)).symm
  have h2 : aZ N (n % 2 ^ (k - 1)) ≡ ∑ i ∈ Finset.range k,
      ((n % 2 ^ (k - 1)).choose i : ℤ) * 2 ^ i * p i [ZMOD ((2 ^ k : ℕ) : ℤ)] := by
    push_cast
    have := aZ_trunc N (n % 2 ^ (k - 1)) k
    rwa [Finset.sum_congr rfl fun i hi => by rw [hb i (Finset.mem_range.mp hi)]] at this
  rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr ((modEq_mod hper n).trans h2),
    hchk _ (Nat.mod_lt _ (by positivity))]
  congr 1
  ext
  simp [Nat.mod_mod_of_dvd n hq]

end Values

/-! ## Bala's statements for A258377–A258381 -/

section Entries

lemma leastPeriodMod_of_one_mod_four (A : ℚ⟦X⟧) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) {N : ℕ}
    (hA : IsSolution N A) (hN : N % 4 = 1) :
    ∀ k ≥ 1, leastPeriodMod a (2 ^ k) = 2 ^ (k - 1) := by
  have := eq_aZ hA ha; subst this
  intro k hk
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
  · simpa using leastPeriodMod_two N
  · simpa using leastPeriodMod_four N (by omega)
  · exact (leastPeriodMod_eq_iff N A hA _ ha k hk3).mpr (Or.inl hN)

/-- OEIS A258377 ($N = 1$), Peter Bala: $a(n)$ is odd, and for $k = 1, 2, 3, \dots$ the
sequence $a(n) \bmod 2^k$ is purely periodic with (least) period $2^{k-1}$. -/
theorem a258377 (A : ℚ⟦X⟧) (hA : IsSolution 1 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, Odd (a n)) ∧ ∀ k ≥ 1, leastPeriodMod a (2 ^ k) = 2 ^ (k - 1) :=
  ⟨odd 1 A hA a ha, leastPeriodMod_of_one_mod_four A a ha hA rfl⟩

/-- Bala's examples for A258377: $a(n) \bmod 4 = (1, 3, 1, 3, \dots)$ with period $2$, and
$a(n) \bmod 8 = (1, 3, 5, 7, 1, 3, 5, 7, \dots)$ with period $4$. -/
theorem a258377_examples (A : ℚ⟦X⟧) (hA : IsSolution 1 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 4) = ![1, 3] (Fin.ofNat 2 n)) ∧ leastPeriodMod a 4 = 2) ∧
    ((∀ n, (a n : ZMod 8) = ![1, 3, 5, 7] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 8 = 4) := by
  have := eq_aZ hA ha; subst this
  have hb : ∀ i < 3, bZ 1 i = [1, 1, 2, 6].getD i 0 := fun i hi => bZ_vals_one i (by omega)
  have h4 := pattern_of_check (N := 1) (k := 2) (m := 4) rfl (by norm_num) _
    (fun i hi => hb i (by omega)) (q := 2) (by norm_num) ![1, 3] (by decide +kernel)
  have h8 := pattern_of_check (N := 1) (k := 3) (m := 8) rfl (by norm_num) _ hb (q := 4)
    (by norm_num) ![1, 3, 5, 7] (by decide +kernel)
  exact ⟨⟨h4, leastPeriodMod_of_pattern (j := 0) rfl _ h4 (by decide)⟩,
    ⟨h8, leastPeriodMod_of_pattern (j := 1) rfl _ h8 (by decide)⟩⟩

/-- OEIS A258378 ($N = 2$), Peter Bala: $a(n) \equiv 1 \pmod 4$, and for $k = 1, 2, 3, \dots$
the sequence $a(n) \bmod 2^k$ is purely periodic with period length a divisor of $2^{k-1}$.
Sharper: for $k \ge 3$ the least period is exactly $2^{k-1}$. -/
theorem a258378 (A : ℚ⟦X⟧) (hA : IsSolution 2 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, a n ≡ 1 [ZMOD 4]) ∧ (∀ k ≥ 1, leastPeriodMod a (2 ^ k) ∣ 2 ^ (k - 1)) ∧
      ∀ k ≥ 3, leastPeriodMod a (2 ^ k) = 2 ^ (k - 1) := by
  refine ⟨fun n => ?_, leastPeriodMod_dvd 2 A hA a ha,
    fun k hk => (leastPeriodMod_eq_iff 2 A hA a ha k hk).mpr (Or.inr rfl)⟩
  rw [eq_aZ hA ha]
  exact (aZ_mod_four 2 n).trans (Int.modEq_iff_dvd.mpr ⟨-n, by push_cast; ring⟩)

/-- Bala's examples for A258378: $a(n) \bmod 8 = (1, 5, 5, 1, \dots)$ with period $4$, and
$a(n) \bmod 16 = (1, 5, 5, 1, 9, 13, 13, 9, \dots)$ with period $8$. -/
theorem a258378_examples (A : ℚ⟦X⟧) (hA : IsSolution 2 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 8) = ![1, 5, 5, 1] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 8 = 4) ∧
    ((∀ n, (a n : ZMod 16) = ![1, 5, 5, 1, 9, 13, 13, 9] (Fin.ofNat 8 n)) ∧
      leastPeriodMod a 16 = 8) := by
  have := eq_aZ hA ha; subst this
  have h8 := pattern_of_check (N := 2) (k := 3) (m := 8) rfl (by norm_num) _
    (fun i hi => bZ_vals_two i (by omega)) (q := 4) (by norm_num) ![1, 5, 5, 1]
    (by decide +kernel)
  have h16 := pattern_of_check (N := 2) (k := 4) (m := 16) rfl (by norm_num) _ bZ_vals_two
    (q := 8) (by norm_num) ![1, 5, 5, 1, 9, 13, 13, 9] (by decide +kernel)
  exact ⟨⟨h8, leastPeriodMod_of_pattern (j := 1) rfl _ h8 (by decide)⟩,
    ⟨h16, leastPeriodMod_of_pattern (j := 2) rfl _ h16 (by decide)⟩⟩

/-- OEIS A258379 ($N = 3$), Peter Bala: $a(n)$ is odd, and for $k = 1, 2, 3, \dots$ the
sequence $a(n) \bmod 2^k$ is purely periodic with period length a divisor of $2^{k-1}$. -/
theorem a258379 (A : ℚ⟦X⟧) (hA : IsSolution 3 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, Odd (a n)) ∧ ∀ k ≥ 1, leastPeriodMod a (2 ^ k) ∣ 2 ^ (k - 1) :=
  ⟨odd 3 A hA a ha, leastPeriodMod_dvd 3 A hA a ha⟩

/-- Bala's examples for A258379: $a(n) \bmod 4 = (1, 3, \dots)$ with period $2$,
$a(n) \bmod 8 = (1, 7, \dots)$ with period $2$, and $a(n) \bmod 16 = (1, 7, 9, 15, \dots)$ with
period $4$. -/
theorem a258379_examples (A : ℚ⟦X⟧) (hA : IsSolution 3 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 4) = ![1, 3] (Fin.ofNat 2 n)) ∧ leastPeriodMod a 4 = 2) ∧
    ((∀ n, (a n : ZMod 8) = ![1, 7] (Fin.ofNat 2 n)) ∧ leastPeriodMod a 8 = 2) ∧
    ((∀ n, (a n : ZMod 16) = ![1, 7, 9, 15] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 16 = 4) := by
  have := eq_aZ hA ha; subst this
  have h4 := pattern_of_check (N := 3) (k := 2) (m := 4) rfl (by norm_num) _
    (fun i hi => bZ_vals_three i (by omega)) (q := 2) (by norm_num) ![1, 3] (by decide +kernel)
  have h8 := pattern_of_check (N := 3) (k := 3) (m := 8) rfl (by norm_num) _
    (fun i hi => bZ_vals_three i (by omega)) (q := 2) (by norm_num) ![1, 7] (by decide +kernel)
  have h16 := pattern_of_check (N := 3) (k := 4) (m := 16) rfl (by norm_num) _ bZ_vals_three
    (q := 4) (by norm_num) ![1, 7, 9, 15] (by decide +kernel)
  exact ⟨⟨h4, leastPeriodMod_of_pattern (j := 0) rfl _ h4 (by decide)⟩,
    ⟨h8, leastPeriodMod_of_pattern (j := 0) rfl _ h8 (by decide)⟩,
    ⟨h16, leastPeriodMod_of_pattern (j := 1) rfl _ h16 (by decide)⟩⟩

/-- OEIS A258380 ($N = 4$), Peter Bala: $a(n) \equiv 1 \pmod 8$, and for $k = 1, 2, 3, \dots$
the sequence $a(n) \bmod 2^k$ is purely periodic with period length a divisor of $2^{k-1}$. -/
theorem a258380 (A : ℚ⟦X⟧) (hA : IsSolution 4 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, a n ≡ 1 [ZMOD 8]) ∧ ∀ k ≥ 1, leastPeriodMod a (2 ^ k) ∣ 2 ^ (k - 1) := by
  refine ⟨fun n => ?_, leastPeriodMod_dvd 4 A hA a ha⟩
  rw [eq_aZ hA ha]
  have h := aZ_trunc 4 n 3
  have hb1 : bZ 4 1 = 4 := bZ_vals_four 1 (by norm_num)
  have hb2 : bZ 4 2 = 26 := bZ_vals_four 2 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right, bZ_zero, hb1, hb2] at h
  norm_num at h
  exact h.trans (Int.modEq_iff_dvd.mpr ⟨-(n + 13 * (n.choose 2 : ℤ)), by ring⟩)

/-- Bala's examples for A258380: $a(n) \bmod 16 = (1, 9, 9, 1, \dots)$ with period $4$, and
$a(n) \bmod 32 = (1, 9, 25, 17, \dots)$ with period $4$. -/
theorem a258380_examples (A : ℚ⟦X⟧) (hA : IsSolution 4 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 16) = ![1, 9, 9, 1] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 16 = 4) ∧
    ((∀ n, (a n : ZMod 32) = ![1, 9, 25, 17] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 32 = 4) := by
  have := eq_aZ hA ha; subst this
  have h16 := pattern_of_check (N := 4) (k := 4) (m := 16) rfl (by norm_num) _
    (fun i hi => bZ_vals_four i (by omega)) (q := 4) (by norm_num) ![1, 9, 9, 1]
    (by decide +kernel)
  have h32 := pattern_of_check (N := 4) (k := 5) (m := 32) rfl (by norm_num) _ bZ_vals_four
    (q := 4) (by norm_num) ![1, 9, 25, 17] (by decide +kernel)
  exact ⟨⟨h16, leastPeriodMod_of_pattern (j := 1) rfl _ h16 (by decide)⟩,
    ⟨h32, leastPeriodMod_of_pattern (j := 1) rfl _ h32 (by decide)⟩⟩

/-- OEIS A258381 ($N = 5$), Peter Bala: $a(n)$ is odd, and for $k = 1, 2, 3, \dots$ the
sequence $a(n) \bmod 2^k$ is purely periodic with (least) period $2^{k-1}$. -/
theorem a258381 (A : ℚ⟦X⟧) (hA : IsSolution 5 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, Odd (a n)) ∧ ∀ k ≥ 1, leastPeriodMod a (2 ^ k) = 2 ^ (k - 1) :=
  ⟨odd 5 A hA a ha, leastPeriodMod_of_one_mod_four A a ha hA rfl⟩

/-- Bala's examples for A258381: $a(n) \bmod 4 = (1, 3, 1, 3, \dots)$ with period $2$, and
$a(n) \bmod 8 = (1, 3, 5, 7, 1, 3, 5, 7, \dots)$ with period $4$. -/
theorem a258381_examples (A : ℚ⟦X⟧) (hA : IsSolution 5 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 4) = ![1, 3] (Fin.ofNat 2 n)) ∧ leastPeriodMod a 4 = 2) ∧
    ((∀ n, (a n : ZMod 8) = ![1, 3, 5, 7] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 8 = 4) := by
  have := eq_aZ hA ha; subst this
  have hb : ∀ i < 3, bZ 5 i = [1, 5, 40, 460].getD i 0 := fun i hi => bZ_vals_five i (by omega)
  have h4 := pattern_of_check (N := 5) (k := 2) (m := 4) rfl (by norm_num) _
    (fun i hi => hb i (by omega)) (q := 2) (by norm_num) ![1, 3] (by decide +kernel)
  have h8 := pattern_of_check (N := 5) (k := 3) (m := 8) rfl (by norm_num) _ hb (q := 4)
    (by norm_num) ![1, 3, 5, 7] (by decide +kernel)
  exact ⟨⟨h4, leastPeriodMod_of_pattern (j := 0) rfl _ h4 (by decide)⟩,
    ⟨h8, leastPeriodMod_of_pattern (j := 1) rfl _ h8 (by decide)⟩⟩

end Entries

/-! ## Sanity checks: the first terms of the data -/

section Data

lemma aZ_eq_of_vals {N M : ℕ} {p : ℕ → ℤ} (hb : ∀ m < M, bZ N m = p m) {n : ℕ} (hn : n < M) :
    aZ N n = ∑ m ∈ Finset.range (n + 1), (n.choose m : ℤ) * 2 ^ m * p m :=
  Finset.sum_congr rfl fun m hm => by rw [hb m (by simp at hm; omega)]

/-- Sanity check against the data: `a(1), a(2), a(3)` of A258377–A258381. -/
lemma aZ_data :
    (aZ 1 1, aZ 1 2, aZ 1 3) = (3, 13, 79) ∧ (aZ 2 1, aZ 2 2, aZ 2 3) = (5, 37, 385) ∧
    (aZ 3 1, aZ 3 2, aZ 3 3) = (7, 73, 1071) ∧ (aZ 4 1, aZ 4 2, aZ 4 3) = (9, 121, 2289) ∧
    (aZ 5 1, aZ 5 2, aZ 5 3) = (11, 181, 4191) := by
  simp only [aZ_eq_of_vals bZ_vals_one (show 1 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_one (show 2 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_one (show 3 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_two (show 1 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_two (show 2 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_two (show 3 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_three (show 1 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_three (show 2 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_three (show 3 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_four (show 1 < 5 by norm_num),
    aZ_eq_of_vals bZ_vals_four (show 2 < 5 by norm_num),
    aZ_eq_of_vals bZ_vals_four (show 3 < 5 by norm_num),
    aZ_eq_of_vals bZ_vals_five (show 1 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_five (show 2 < 4 by norm_num),
    aZ_eq_of_vals bZ_vals_five (show 3 < 4 by norm_num)]
  decide +kernel

end Data

end OeisA258377

end
