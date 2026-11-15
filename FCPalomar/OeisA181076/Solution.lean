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
# OEIS A183128 and A183129: Hanna's binomial-power exponentials

Paul D. Hanna (2010) conjectured that the series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} f(n,k) x^k] x^n/n\bigr)$ has integer coefficients for
$f(n,k) = \binom{n+k-1}{k}^{e(n,k)}$ with $e = k^2+1$ (A183128), $k^2+k$ (A183129), $n$ (A181076)
and $n+k-1$ (A181078), and for $f(n,k) = \binom{n}{k}^{e(n,k)}$, $0 \le k \le n$, with $e = n+k$
(A181082) and $n+k+1$ (A181084). This file proves all six, and Hanna's notes that the exponents
$k^2$ (A183128), $k^2+k-1$ (A183129) and $k$ for $\binom{n}{k}$ (A181070) do not give integer
series. It also proves the general criterion (Theorem 1), its Corollary 2 and the obstruction
at $k = 1$ (Theorem 4), for the diagonal series of any $U \in 1 + z\mathbb{Z}[[z]]$.

Write $B(n,k) = [z^k]\,U(z)^n$ with $U \in 1 + z\mathbb{Z}[[z]]$, $f(n,k) = B(n,k)^{e(n,k)}$ and
$c(m) = \sum_{n=1}^{m} \frac{m}{n} f(n, m-n)$, so that the series is
$\exp\bigl(\sum_{m \ge 1} c(m) x^m/m\bigr)$. Call $c$ a *Gauss sequence* if
$p^r \mid c(pM) - c(M)$ whenever $p$ is prime and $p^r \mid pM$.

*Step 1 (Dold's criterion; `exists_coeff_eq_intCast_of_gauss`).* If $c$ is a Gauss sequence,
then $\exp\bigl(\sum c(m) x^m/m\bigr)$ has integer coefficients. Möbius inversion writes
$c(m) = \sum_{d \mid m} d\,a(d)$ with integers $a(d)$, and the series agrees up to degree $N$
with the finite product $\prod_{d \le N} (1 - x^d)^{-a(d)}$, which has integer coefficients. This
step, and the Euler product used in Step 8, are copied from the package
`FCPalomar/OeisA181316`.

*Step 2 (Lemma 1).* $n \mid k\,B(n,k)$, from the derivative of $U^n$ (`dvd_mul_coeff_pow`).
If $p^j \mid n$, then $B(pn,pk) \equiv B(n,k) \pmod{p^{j+1}}$
(`prime_pow_dvd_coeff_pow_sub`): in $(\mathbb{Z}/p)[[z]]$ we have $U^p = U(z^p)$
(`map_frobenius_expand`), so $p \mid U^p - U(z^p)$; lifting gives
$p^{j+1} \mid U^{p^{j+1}} - U(z^p)^{p^j}$, and we raise to the power $n/p^j$ and compare the
coefficients of $z^{pk}$.

*Step 3 (the diagonal pairing; `diagSum_gauss`).* Let $n \mid k f(n,k)$, and let
$p^{j+1} \mid f(pn,pk) - f(n,k)$ whenever $p^j \mid n$. Then each $c(m)$ is an integer
(`hannaLog_eq_ofInt`) and $c$ is a Gauss sequence. Split $c(pM) - c(M)$ with $p^r \mid pM$
(`diagSum_mul_sub`):
- a term $T = \frac{pM}{n} f(n,k)$ with $p \nmid n$ satisfies $nT = pM f(n,k)$, so $p^r \mid T$
  (`prime_pow_dvd_unpaired`);
- a term with $p \mid n$ has $n = pn_0$ and $k = pk_0$. It pairs with the term $(n_0, k_0)$ of
  $c(M)$. Their difference $X$ satisfies $n_0 X = M\,(f(pn_0,pk_0) - f(n_0,k_0))$, and
  comparing powers of $p$ gives $p^r \mid X$ (`prime_pow_dvd_paired`).

*Step 4 (Theorem 1, diagonal form; `integral_of_criterion`).* The hypotheses of Step 3 hold
under (E1) and (E2) (`pair_congr`). For $k = 0$ both terms are $1$. If $p \nmid b = B(n,k)$,
(E1) and Euler's theorem give $b'^{e'} \equiv b^e \pmod{p^{1+v_p(n)}}$. If $p \mid b$, either
$e' = e$ and $b' - b \mid b'^e - b^e$, or both powers vanish modulo $p^{1+v_p(n)}$.

*Step 5 (Corollary 2).* (a) A constant exponent satisfies (E2) by its first alternative.
(b) For a polynomial $P \in \mathbb{Z}[n,k]$, $(p-1)g \mid P(pn,pk) - P(n,k)$ whenever
$g \mid n$ and $g \mid k$, by induction on $P$ (`eval_mul_sub_eval_dvd`). If $p \nmid b$, then
$n \mid kb$ gives $p^{v_p(n)} \mid k$, which is (E1) (`exponent_modEq`). If $p \mid b$ and
$p^j \mid n$, condition (M) gives $p^{j+1} \mid b^e$ (`prime_pow_succ_dvd_pow`). In the case
$e \ge n$ this holds because $n > j$. In the case $e \ge i+1$ with $n \mid ib$, it holds because
$v_p(i) < i$. Applied at $(n,k)$ and at $(pn,pk)$, this gives the second alternative of (E2).

*Step 6 (the six entries).* $U = 1/(1-z)$ (`mk 1`) gives $B(n,k) = \binom{n+k-1}{k}$
(`coeff_mk_one_pow`), and $U = 1 + z$ gives $\binom{n}{k}$ (`coeff_one_add_X_pow`); for $k > n$
the term $\binom{n}{k}^{e} = 0$ matches the inner sum over $k \le n$. In each case (M) holds
with $j = k$: $k^2+1 \ge k+1$ and $k^2+k \ge k+1$ for $k \ge 1$, and $e \ge n$ for the other
four exponents.

*Step 7 (the notes).* The recurrence $(m+1)\,a(m+1) = \sum_{i=0}^{m} (i+1)\,\ell(i+1)\,a(m-i)$
for the coefficients $a$ of $\exp L$ and $\ell$ of $L$ (`coeff_exp_subst_six`) gives
$a(6) = 153254825495/2$ for $k^2$, $19140157244799/2$ for $k^2+k-1$ and $45/2$ for
$\binom{n}{k}^k$. These are not integers.

*Step 8 (Theorem 4, diagonal form; `not_integral_of_exponent`).* If the series has integer
coefficients, then $p \mid c(pM) - c(M)$ for $p \nmid M$: the integers $a(d)$ of an Euler
product that agrees with the series up to degree $pM$ give $c(n) = \sum_{d \mid n} d\,a(d)$,
and every divisor of $pM$ that does not divide $M$ is a multiple of $p$
(`prime_dvd_mul_sub_of_integral`). Take $M = p + 1$ in the split of Step 3. The unpaired terms
and the pairs with $n_0 \ne p$ vanish modulo $p$ (`pair_congr_prime`: $p - 1$ divides
$e(pn,pk) - e(n,k)$, and both powers vanish if $p \mid B(n,k)$). For $n_0 = p$, $k_0 = 1$ we
have $B(p,1) = p\,u_1$ with $u_1 = [z]\,U$ (`coeff_one_pow`), $e(p,1) = 1$, $p \mid B(p^2,p)$
and $e(p^2,p) \ge 2$, so the pair is $\equiv -(p+1)\,u_1 \pmod p$. Hence $p \mid u_1$, a
contradiction.

The file ends with the first seven terms of each of the six sequences, which match the OEIS
data.

*References:*
- Paul D. Hanna, [A183128](https://oeis.org/A183128), [A183129](https://oeis.org/A183129),
  [A181076](https://oeis.org/A181076), [A181078](https://oeis.org/A181078),
  [A181082](https://oeis.org/A181082), [A181084](https://oeis.org/A181084) and
  [A181070](https://oeis.org/A181070), 2010.
- A. Dold, *Fixed point indices of iterated maps*, Invent. Math. 74 (1983), 419–435.
- R. P. Stanley, *Enumerative Combinatorics*, Vol. 2, Cambridge Univ. Press, 1999,
  Exercise 5.2(a).
-/

@[expose] public section

namespace OeisA181076

open PowerSeries Finset
open scoped ArithmeticFunction.Moebius Pointwise

/-! ## Definitions -/

/-- Hanna's logarithm $\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr] \frac{x^n}{n}$ over
$\mathbb{Q}$: its coefficient of $x^m$ is $\sum_{n=1}^{m} f(n, m-n)/n$. -/
noncomputable def hannaLog (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ :=
  mk fun m => ∑ n ∈ Finset.Icc 1 m, (f n (m - n) : ℚ) / n

/-- Hanna's series $\exp\Bigl(\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr]
\frac{x^n}{n}\Bigr)$ over $\mathbb{Q}$. -/
noncomputable def hannaExp (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ := subst (hannaLog f) (exp ℚ)

/-- OEIS A183128: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+1} x^k] x^n/n\bigr)$. -/
noncomputable def a183128 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + 1))

/-- OEIS A183129: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+k} x^k] x^n/n\bigr)$. -/
noncomputable def a183129 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k))

/-- OEIS A181076: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{n} x^k] x^n/n\bigr)$. -/
noncomputable def a181076 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ n)

/-- OEIS A181078: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{n+k-1} x^k] x^n/n\bigr)$. -/
noncomputable def a181078 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1))

/-- OEIS A181082: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k=0}^{n} \binom{n}{k}^{n+k} x^k] x^n/n\bigr)$. -/
noncomputable def a181082 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k) else 0)

/-- OEIS A181084: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k=0}^{n} \binom{n}{k}^{n+k+1} x^k] x^n/n\bigr)$. -/
noncomputable def a181084 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k + 1) else 0)

/-! ## Dold's criterion

Everything from here to the section "Hanna's logarithm" is copied from the package
`FCPalomar/OeisA181316` (Apache-2.0, Wentao Li): Euler's theorem for prime powers, the
sufficiency half of Dold's criterion (`exists_coeff_eq_intCast_of_gauss`), which that package
takes from `FCPalomar/A158110`, and the Euler product of an integral series
(`exists_eulerProduct`). -/

/-! ### Fermat and Euler -/

theorem prime_pow_dvd_pow_totient_sub_one {p : ℕ} (hp : p.Prime) {y : ℤ} (hy : ¬(p : ℤ) ∣ y)
    {k : ℕ} (hk : 0 < k) : (p : ℤ) ^ k ∣ y ^ Nat.totient (p ^ k) - 1 := by
  have hcop : IsCoprime y p :=
    ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hy).symm
  have hf : (p : ℤ) ∣ y ^ (p - 1) - 1 :=
    (Int.ModEq.pow_card_sub_one_eq_one hp hcop).symm.dvd
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := dvd_sub_pow_of_dvd_sub hf j
  rw [one_pow, ← pow_mul] at h
  rwa [Nat.totient_prime_pow hp (by omega : 0 < j + 1), Nat.add_sub_cancel, mul_comm]

theorem isCoprime_of_not_dvd {p : ℕ} (hp : p.Prime) {y : ℤ} (hy : ¬(p : ℤ) ∣ y) (k : ℕ) :
    IsCoprime ((p : ℤ) ^ k) y :=
  IsCoprime.pow_left ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hy)

theorem prime_pow_dvd_pow_sub_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) {x y : ℤ}
    (hxy : (p : ℤ) ^ k ∣ x - y) (hy : ¬(p : ℤ) ∣ y) {a b : ℕ}
    (hab : a ≡ b [MOD Nat.totient (p ^ k)]) : (p : ℤ) ^ k ∣ x ^ a - y ^ b := by
  set T := Nat.totient (p ^ k)
  have hT := prime_pow_dvd_pow_totient_sub_one hp hy hk
  have h1 : (p : ℤ) ^ k ∣ x ^ a - y ^ a := hxy.trans (sub_dvd_pow_sub_pow x y a)
  have hpow : ∀ s, (p : ℤ) ^ k ∣ (y ^ T) ^ s - 1 := fun s => by
    simpa using hT.trans (sub_dvd_pow_sub_pow (y ^ T) 1 s)
  have h2 : (p : ℤ) ^ k ∣ y ^ a - y ^ b := by
    have ea : y ^ a = (y ^ T) ^ (a / T) * y ^ (a % T) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have eb : y ^ b = (y ^ T) ^ (b / T) * y ^ (b % T) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [ea, eb, ← hab]
    have : (y ^ T) ^ (a / T) * y ^ (a % T) - (y ^ T) ^ (b / T) * y ^ (a % T) =
        (((y ^ T) ^ (a / T) - 1) - ((y ^ T) ^ (b / T) - 1)) * y ^ (a % T) := by ring
    rw [this]
    exact dvd_mul_of_dvd_left (dvd_sub (hpow _) (hpow _)) _
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-! ### Logarithmic derivatives -/

section LogDeriv

/-- Two series with equal constant terms whose logarithmic derivatives agree below degree `N`
agree up to degree `N`. -/
theorem coeff_eq_of_derivative_eq_mul {F G f g : ℚ⟦X⟧} (hF : d⁄dX F = f * F)
    (hG : d⁄dX G = g * G) (h0 : constantCoeff F = constantCoeff G) {N : ℕ}
    (hfg : ∀ i < N, coeff i f = coeff i g) : ∀ i ≤ N, coeff i F = coeff i G := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | j
    · simpa using h0
    · have e1 := congrArg (coeff j) hF
      have e2 := congrArg (coeff j) hG
      rw [coeff_derivative, coeff_mul] at e1 e2
      have hsum : ∑ x ∈ antidiagonal j, coeff x.1 f * coeff x.2 F =
          ∑ x ∈ antidiagonal j, coeff x.1 g * coeff x.2 G := by
        refine sum_congr rfl fun x hx => ?_
        have hx' := mem_antidiagonal.mp hx
        rw [hfg x.1 (by omega), ih x.2 (by omega) (by omega)]
      have hne : (j : ℚ) + 1 ≠ 0 := by positivity
      exact mul_right_cancel₀ hne (e1.trans (hsum.trans e2.symm))

theorem derivative_mul_of {F G f g : ℚ⟦X⟧} (hF : d⁄dX F = f * F)
    (hG : d⁄dX G = g * G) : d⁄dX (F * G) = (f + g) * (F * G) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hF, hG]
  ring

theorem derivative_pow_of {F f : ℚ⟦X⟧} (hF : d⁄dX F = f * F) (n : ℕ) :
    d⁄dX (F ^ n) = (n * f) * F ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, derivative_mul_of ih hF]
    push_cast
    ring

theorem derivative_prod_of {ι : Type*} (s : Finset ι) {F f : ι → ℚ⟦X⟧}
    (hF : ∀ i ∈ s, d⁄dX (F i) = f i * F i) :
    d⁄dX (∏ i ∈ s, F i) = (∑ i ∈ s, f i) * ∏ i ∈ s, F i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact derivative_mul_of (hF a (mem_insert_self a s))
      (ih fun i hi => hF i (mem_insert_of_mem hi))

/-- The chain rule for $\exp \circ L$. -/
theorem derivative_exp_subst {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) :
    d⁄dX (subst L (exp ℚ)) = d⁄dX L * subst L (exp ℚ) := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hL), derivative_exp, mul_comm]

theorem constantCoeff_exp_subst {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) :
    constantCoeff (subst L (exp ℚ)) = 1 := by
  have ha := HasSubst.of_constantCoeff_zero' hL
  have h1 : subst L (exp ℚ) = subst L (exp ℚ - 1) + 1 := by
    rw [← coe_substAlgHom ha, map_sub, map_one, sub_add_cancel]
  have h2 : constantCoeff (subst L (exp ℚ - 1)) = 0 :=
    constantCoeff_subst_eq_zero hL _ (by simp)
  rw [h1, map_add, map_one, h2, zero_add]

end LogDeriv

/-! ### Finite Euler products -/

section EulerProduct

/-- The power series over `ℚ` with integer coefficients. -/
noncomputable abbrev intSeries : Subring ℚ⟦X⟧ := (map (Int.castRingHom ℚ)).range

/-- The series $1 / (1 - x^d) = \sum_{k \ge 0} x^{dk}$. -/
noncomputable def geom (d : ℕ) : ℚ⟦X⟧ := mk fun n => if d ∣ n then 1 else 0

/-- The logarithmic derivative $d x^{d-1} / (1 - x^d)$ of $1 / (1 - x^d)$. -/
noncomputable def geomLogDeriv (d : ℕ) : ℚ⟦X⟧ := (d : ℚ⟦X⟧) * X ^ (d - 1) * geom d

/-- The factor $(1 - x^d)^{-c}$, written with natural exponents. -/
noncomputable def factor (d : ℕ) (c : ℤ) : ℚ⟦X⟧ := geom d ^ c.toNat * (1 - X ^ d) ^ (-c).toNat

/-- The finite product $\prod_{d=1}^{N} (1 - x^d)^{-c(d)}$. -/
noncomputable def eulerProduct (c : ℕ → ℤ) (N : ℕ) : ℚ⟦X⟧ := ∏ d ∈ Icc 1 N, factor d (c d)

theorem geom_mul_one_sub {d : ℕ} (hd : 0 < d) : geom d * (1 - X ^ d) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one, geom, coeff_mk, coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.not_le.mpr hd]
  · rcases le_or_gt d n with h | h
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
      simp [Nat.dvd_add_right (dvd_refl d), hd.ne']
    · have hnd : ¬d ∣ n := fun hdn => absurd (Nat.le_of_dvd hn hdn) (by omega)
      simp [hnd, Nat.not_le.mpr h, hn.ne']

theorem derivative_one_sub_X_pow {d : ℕ} (hd : 0 < d) :
    d⁄dX (1 - X ^ d) = -geomLogDeriv d * (1 - X ^ d) := by
  have h := geom_mul_one_sub hd
  rw [map_sub, derivative_one, derivative_pow, derivative_X, geomLogDeriv]
  linear_combination ((d : ℚ⟦X⟧) * X ^ (d - 1)) * h

theorem derivative_geom {d : ℕ} (hd : 0 < d) :
    d⁄dX (geom d) = geomLogDeriv d * geom d := by
  have h := geom_mul_one_sub hd
  have h' := congrArg (d⁄dX) h
  rw [Derivation.leibniz, derivative_one_sub_X_pow hd, derivative_one, smul_eq_mul,
    smul_eq_mul] at h'
  linear_combination geom d * h' - (d⁄dX (geom d) - geomLogDeriv d * geom d) * h

theorem derivative_factor {d : ℕ} (hd : 0 < d) (c : ℤ) :
    d⁄dX (factor d c) = ((c : ℚ⟦X⟧) * geomLogDeriv d) * factor d c := by
  rw [factor, derivative_mul_of (derivative_pow_of (derivative_geom hd) _)
    (derivative_pow_of (derivative_one_sub_X_pow hd) _)]
  have key : ((c.toNat : ℤ) : ℚ⟦X⟧) - (((-c).toNat : ℤ) : ℚ⟦X⟧) = (c : ℚ⟦X⟧) := by
    rw [← Int.cast_sub, Int.toNat_sub_toNat_neg]
  simp only [Int.cast_natCast] at key
  rw [← key]
  ring

theorem derivative_eulerProduct (c : ℕ → ℤ) (N : ℕ) :
    d⁄dX (eulerProduct c N) =
      (∑ d ∈ Icc 1 N, (c d : ℚ⟦X⟧) * geomLogDeriv d) * eulerProduct c N :=
  derivative_prod_of _ fun d hd => derivative_factor (mem_Icc.mp hd).1 (c d)

theorem constantCoeff_eulerProduct (c : ℕ → ℤ) (N : ℕ) :
    constantCoeff (eulerProduct c N) = 1 := by
  rw [eulerProduct, map_prod]
  refine prod_eq_one fun d hd => ?_
  have hd0 : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
  rw [factor, map_mul, map_pow, map_pow, ← coeff_zero_eq_constantCoeff_apply, geom, coeff_mk]
  simp [hd0]

theorem geom_mem (d : ℕ) : geom d ∈ intSeries :=
  ⟨mk fun n => if d ∣ n then 1 else 0, by
    ext n
    simp only [coeff_map, coeff_mk, geom]
    split_ifs <;> simp⟩

theorem one_sub_X_pow_mem (d : ℕ) : (1 - X ^ d : ℚ⟦X⟧) ∈ intSeries :=
  Subring.sub_mem _ (Subring.one_mem _) (Subring.pow_mem _ (RingHom.mem_range.mpr ⟨X, map_X _⟩) d)

theorem eulerProduct_mem (c : ℕ → ℤ) (N : ℕ) : eulerProduct c N ∈ intSeries :=
  Subring.prod_mem _ fun d _ => Subring.mul_mem _ (Subring.pow_mem _ (geom_mem d) _)
    (Subring.pow_mem _ (one_sub_X_pow_mem d) _)

theorem coeff_geomLogDeriv {d : ℕ} (hd : 0 < d) (j : ℕ) :
    coeff j (geomLogDeriv d) = if d ∣ j + 1 then (d : ℚ) else 0 := by
  rw [geomLogDeriv, mul_assoc, ← map_natCast (C (R := ℚ)) d, coeff_C_mul, coeff_X_pow_mul',
    geom]
  rcases le_or_gt d (j + 1) with h | h
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
    have hj : j - (d - 1) = t := by omega
    rw [ite_eq_left (by omega), coeff_mk, hj, ht]
    by_cases hdt : d ∣ t
    · simp [hdt, Nat.dvd_add_right (dvd_refl d)]
    · simp [hdt, Nat.dvd_add_right (dvd_refl d)]
  · have hnd : ¬d ∣ j + 1 := fun hdj => absurd (Nat.le_of_dvd (by omega) hdj) (by omega)
    rw [ite_eq_right (by omega), ite_eq_right hnd, mul_zero]

theorem coeff_logDeriv_eulerProduct (c : ℕ → ℤ) {N j : ℕ} (hj : j < N) :
    coeff j (∑ d ∈ Icc 1 N, (c d : ℚ⟦X⟧) * geomLogDeriv d) =
      ∑ d ∈ (j + 1).divisors, (d : ℚ) * c d := by
  rw [map_sum]
  have hfilter : (Icc 1 N).filter (· ∣ j + 1) = (j + 1).divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨h, by omega⟩
    · rintro ⟨h, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hj⟩, h⟩
  rw [← hfilter, sum_filter]
  refine sum_congr rfl fun d hd => ?_
  rw [← map_intCast (C (R := ℚ)), coeff_C_mul, coeff_geomLogDeriv (mem_Icc.mp hd).1 j]
  split_ifs <;> ring

end EulerProduct

/-! ### The integrality criterion -/

/-- If $n \mid \sum_{d \mid n} \mu(d) b(n/d)$ for all $n \ge 1$, then
$\exp\left(\sum_{n \ge 1} b(n) x^n / n\right)$ has integer coefficients. -/
theorem exists_coeff_eq_intCast_of_dvd (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * b x.2) (N : ℕ) :
    ∃ z : ℤ, coeff N (subst (mk fun n => if n = 0 then 0 else (b n : ℚ) / n) (exp ℚ)) = z := by
  set L : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else (b n : ℚ) / n with hLdef
  set c : ℕ → ℤ := fun n : ℕ => (∑ x ∈ n.divisorsAntidiagonal, μ x.1 * b x.2) / (n : ℤ)
    with hc
  have hinv : ∀ n : ℕ, 0 < n → ∑ i ∈ n.divisors, (i : ℤ) * c i = b n := by
    refine ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr fun n hn => ?_
    simp only [Int.cast_id, hc]
    exact (Int.mul_ediv_cancel' (hb n hn)).symm
  have hL0 : constantCoeff L = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hLdef, coeff_mk, ite_eq_left rfl]
  have heq := coeff_eq_of_derivative_eq_mul (derivative_exp_subst hL0)
    (derivative_eulerProduct c N)
    (by rw [constantCoeff_exp_subst hL0, constantCoeff_eulerProduct]) (N := N)
    (fun i hi => by
      rw [coeff_derivative, coeff_logDeriv_eulerProduct c hi, hLdef, coeff_mk,
        ite_eq_right (by omega)]
      have h := hinv (i + 1) (by omega)
      have h' : ∑ d ∈ (i + 1).divisors, (d : ℚ) * c d = b (i + 1) := by exact_mod_cast h
      rw [h']
      field_simp
      push_cast
      ring) N le_rfl
  obtain ⟨G, hG⟩ := RingHom.mem_range.mp (eulerProduct_mem c N)
  exact ⟨coeff N G, by rw [heq, ← hG, coeff_map]; simp⟩

theorem sum_divisors_prime_pow_mul {p k N : ℕ} (hp : p.Prime) (hN : ¬p ∣ N) (F : ℕ → ℤ) :
    ∑ d ∈ (p ^ k * N).divisors, F d =
      ∑ i ∈ range (k + 1), ∑ e ∈ N.divisors, F (p ^ i * e) := by
  have hcop : (p ^ k).Coprime N :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hN)
  rw [Nat.divisors_mul, Finset.mul_def, sum_image hcop.mul_injOn_divisors, sum_product]
  simp only [Nat.sum_divisors_prime_pow hp]

/-! ### Gauss sequences

The Möbius pairing is adapted from `prime_pow_dvd_sum_moebius` and `dvd_sum_moebius` in
`FCPalomar/A158110`, with a general Gauss sequence in place of $q^{n^m}$. -/

/-- The Gauss congruences $b(pM) \equiv b(M) \pmod{p^k}$ whenever $p^k \mid pM$. -/
def Gauss (b : ℕ → ℤ) : Prop :=
  ∀ p k M : ℕ, p.Prime → p ^ k ∣ p * M → (p : ℤ) ^ k ∣ b (p * M) - b M

/-- Under the Gauss congruences, $p^k$ divides the Möbius sum at $p^k N$ when $p \nmid N$. -/
theorem prime_pow_dvd_sum_moebius {b : ℕ → ℤ} (hb : Gauss b) {p : ℕ} (hp : p.Prime) {k N : ℕ}
    (hk : 0 < k) (hN : ¬p ∣ N) :
    (p : ℤ) ^ k ∣ ∑ x ∈ (p ^ k * N).divisorsAntidiagonal, μ x.1 * b x.2 := by
  rw [Nat.sum_divisorsAntidiagonal (fun a c => μ a * b c),
    sum_divisors_prime_pow_mul hp hN, sum_comm]
  refine dvd_sum fun e he => ?_
  have hed : e ∣ N := (Nat.mem_divisors.mp he).1
  have hN0 : N ≠ 0 := (Nat.mem_divisors.mp he).2
  have hce : ∀ i, (p ^ i).Coprime e := fun i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hN (h.trans hed))
  have he0 : e ≠ 0 := fun h => hN0 (Nat.eq_zero_of_zero_dvd (h ▸ hed))
  obtain ⟨M, rfl⟩ := hed
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hmu : ∀ i, μ (p ^ i * e) = μ (p ^ i) * μ e := fun i =>
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hce i)
  rw [sum_range_succ', sum_range_succ', sum_eq_zero fun i _ => ?_]
  · have q0 : p ^ (j + 1) * (e * M) / (p ^ 0 * e) = p ^ (j + 1) * M := by
      rw [pow_zero, one_mul, show p ^ (j + 1) * (e * M) = e * (p ^ (j + 1) * M) by ring,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)]
    have q1 : p ^ (j + 1) * (e * M) / (p ^ (0 + 1) * e) = p ^ j * M := by
      rw [zero_add, pow_one,
        show p ^ (j + 1) * (e * M) = (p * e) * (p ^ j * M) by ring,
        Nat.mul_div_cancel_left _ (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero he0))]
    rw [q0, q1, hmu, hmu, pow_zero, ArithmeticFunction.moebius_apply_one, zero_add, pow_one,
      ArithmeticFunction.moebius_apply_prime hp]
    have ht := hb p (j + 1) (p ^ j * M) hp ⟨M, by ring⟩
    rw [show p * (p ^ j * M) = p ^ (j + 1) * M by ring] at ht
    obtain ⟨t, ht⟩ := ht
    exact ⟨μ e * t, by linear_combination (μ e) * ht⟩
  · rw [hmu, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
    simp

/-- Dold's congruence $n \mid \sum_{d \mid n} \mu(d) b(n/d)$ for a Gauss sequence. -/
theorem dvd_sum_moebius {b : ℕ → ℤ} (hb : Gauss b) {n : ℕ} (hn : 0 < n) :
    (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * b x.2 := by
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hv : k ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn.ne').mp hpk
  have hdecomp := Nat.ordProj_mul_ordCompl_eq_self n p
  have hdiv := prime_pow_dvd_sum_moebius hb hp (k := n.factorization p) (by omega)
    (Nat.not_dvd_ordCompl hp hn.ne')
  rw [hdecomp] at hdiv
  rw [← Int.natCast_dvd]
  push_cast
  exact (pow_dvd_pow _ hv).trans hdiv

/-- The series $\sum_{n \ge 1} b(n) x^n / n$ over $\mathbb{Q}$. -/
noncomputable def ofInt (b : ℕ → ℤ) : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else (b n : ℚ) / n

/-- **Dold's criterion, (⇐).** For a Gauss sequence $b$,
$\exp\left(\sum_{n \ge 1} b(n) x^n / n\right)$ has integer coefficients. -/
theorem exists_coeff_eq_intCast_of_gauss {b : ℕ → ℤ} (hb : Gauss b) (N : ℕ) :
    ∃ z : ℤ, coeff N (subst (ofInt b) (exp ℚ)) = z :=
  exists_coeff_eq_intCast_of_dvd b (fun _ hn => dvd_sum_moebius hb hn) N

/-! ### The converse at degree `N` -/

theorem constantCoeff_ofInt (b : ℕ → ℤ) : constantCoeff (ofInt b) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ofInt, coeff_mk, ite_eq_left rfl]

theorem coeff_derivative_ofInt (b : ℕ → ℤ) (j : ℕ) :
    coeff j (d⁄dX (ofInt b)) = b (j + 1) := by
  rw [coeff_derivative, ofInt, coeff_mk, ite_eq_right (Nat.succ_ne_zero j)]
  field_simp
  push_cast
  ring

/-- Two series with constant term `1` that agree up to degree `N` have logarithmic derivatives
that agree below degree `N`. -/
theorem coeff_logDeriv_eq {F G f g : ℚ⟦X⟧} (hF : d⁄dX F = f * F) (hG : d⁄dX G = g * G)
    (hF0 : constantCoeff F = 1) (hG0 : constantCoeff G = 1) {N : ℕ}
    (hFG : ∀ i ≤ N, coeff i F = coeff i G) : ∀ j < N, coeff j f = coeff j g := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have e1 := congrArg (coeff j) hF
    have e2 := congrArg (coeff j) hG
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a f * coeff b F), sum_range_succ, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, hF0, mul_one] at e1
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff a g * coeff b G), sum_range_succ, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, hG0, mul_one] at e2
    have hsum : ∑ x ∈ range j, coeff x f * coeff (j - x) F =
        ∑ x ∈ range j, coeff x g * coeff (j - x) G := by
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.mp hx
      rw [ih x hx' (by omega), hFG (j - x) (by omega)]
    rw [hFG (j + 1) hj] at e1
    linarith

/-- `X ^ (d + 1)` divides `F - 1 - a X ^ d`: the series is $1 + a x^d$ up to degree `d`. -/
def Near (d : ℕ) (a : ℤ) (F : ℚ⟦X⟧) : Prop := X ^ (d + 1) ∣ F - 1 - (a : ℚ⟦X⟧) * X ^ d

theorem Near.mul {d : ℕ} (hd : 0 < d) {a b : ℤ} {F G : ℚ⟦X⟧} (hF : Near d a F) (hG : Near d b G) :
    Near d (a + b) (F * G) := by
  obtain ⟨R, hR⟩ := hF
  obtain ⟨S, hS⟩ := hG
  have hF' : F = 1 + (a : ℚ⟦X⟧) * X ^ d + X ^ (d + 1) * R := by rw [← hR]; ring
  have hG' : G = 1 + (b : ℚ⟦X⟧) * X ^ d + X ^ (d + 1) * S := by rw [← hS]; ring
  have hXX : (X : ℚ⟦X⟧) ^ d * X ^ d = X ^ (d + 1) * X ^ (d - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  refine ⟨R + S + (a : ℚ⟦X⟧) * X ^ d * S + (b : ℚ⟦X⟧) * X ^ d * R + X ^ (d + 1) * R * S +
    (a : ℚ⟦X⟧) * (b : ℚ⟦X⟧) * X ^ (d - 1), ?_⟩
  rw [hF', hG']
  push_cast
  linear_combination (a : ℚ⟦X⟧) * (b : ℚ⟦X⟧) * hXX

theorem near_one (d : ℕ) : Near d 0 1 := ⟨0, by simp⟩

theorem Near.pow {d : ℕ} (hd : 0 < d) {a : ℤ} {F : ℚ⟦X⟧} (hF : Near d a F) (n : ℕ) :
    Near d (n * a) (F ^ n) := by
  induction n with
  | zero => simpa using near_one d
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hd hF using 1
    push_cast
    ring

theorem near_geom {d : ℕ} (hd : 0 < d) : Near d 1 (geom d) := by
  have h := geom_mul_one_sub hd
  have h1 : geom d = 1 + geom d * X ^ d := by linear_combination h
  refine ⟨X ^ (d - 1) * geom d, ?_⟩
  have hXX : (X : ℚ⟦X⟧) ^ (d + 1) * X ^ (d - 1) = X ^ d * X ^ d := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  push_cast
  linear_combination (1 + X ^ d) * h1 - geom d * hXX

theorem near_one_sub {d : ℕ} : Near d (-1) (1 - X ^ d) := ⟨0, by push_cast; ring⟩

theorem near_factor {d : ℕ} (hd : 0 < d) (c : ℤ) : Near d c (factor d c) := by
  have h := ((near_geom hd).pow hd c.toNat).mul hd (near_one_sub.pow hd (-c).toNat)
  have key : (c.toNat : ℤ) * 1 + ((-c).toNat : ℤ) * (-1) = c := by
    have := Int.toNat_sub_toNat_neg c
    linarith
  rwa [key] at h

theorem coeff_mul_of_near {d : ℕ} {a : ℤ} {F : ℚ⟦X⟧} (hF : Near d a F) (E : ℚ⟦X⟧) {i : ℕ}
    (hi : i ≤ d) : coeff i (E * F) = coeff i E + if i = d then a * coeff 0 E else 0 := by
  obtain ⟨R, hR⟩ := hF
  have hF' : E * F = E + (a : ℚ⟦X⟧) * (X ^ d * E) + X ^ (d + 1) * (E * R) := by
    rw [show F = 1 + (a : ℚ⟦X⟧) * X ^ d + X ^ (d + 1) * R by rw [← hR]; ring]
    ring
  rw [hF', map_add, map_add, ← map_intCast (C (R := ℚ)), coeff_C_mul, coeff_X_pow_mul',
    coeff_X_pow_mul', ite_eq_right (show ¬d + 1 ≤ i by omega), add_zero]
  by_cases h : i = d
  · subst h
    simp
  · rw [ite_eq_right (show ¬d ≤ i by omega), ite_eq_right h]
    simp

theorem eulerProduct_succ (c : ℕ → ℤ) (N : ℕ) :
    eulerProduct c (N + 1) = eulerProduct c N * factor (N + 1) (c (N + 1)) := by
  rw [eulerProduct, eulerProduct, prod_Icc_succ_top (by omega)]

theorem eulerProduct_congr {c c' : ℕ → ℤ} {N : ℕ} (h : ∀ d ∈ Icc 1 N, c d = c' d) :
    eulerProduct c N = eulerProduct c' N :=
  prod_congr rfl fun d hd => by rw [h d hd]

/-- A series with integer coefficients and constant term `1` agrees with a finite Euler
product up to degree `N`. -/
theorem exists_eulerProduct {G : ℚ⟦X⟧} (hG : ∀ n, ∃ z : ℤ, coeff n G = z)
    (hG0 : constantCoeff G = 1) (N : ℕ) :
    ∃ c : ℕ → ℤ, ∀ i ≤ N, coeff i G = coeff i (eulerProduct c N) := by
  induction N with
  | zero =>
    refine ⟨0, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    simp [eulerProduct, hG0]
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨z, hz⟩ := hG (N + 1)
    obtain ⟨E, hE⟩ := RingHom.mem_range.mp (eulerProduct_mem c N)
    set D : ℤ := z - coeff (N + 1) E
    set c' := Function.update c (N + 1) D
    have hcc : eulerProduct c' N = eulerProduct c N :=
      eulerProduct_congr fun d hd => by
        simp only [c']
        rw [Function.update_of_ne (by have := (mem_Icc.mp hd).2; omega)]
    have hc'N : c' (N + 1) = D := Function.update_self _ _ _
    refine ⟨c', fun i hi => ?_⟩
    rw [eulerProduct_succ, hcc, hc'N,
      coeff_mul_of_near (near_factor (Nat.succ_pos N) D) _ hi]
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · rw [ite_eq_right (by omega), add_zero]
      exact hc i (by omega)
    · rw [ite_eq_left rfl, coeff_zero_eq_constantCoeff_apply, constantCoeff_eulerProduct, hz, ← hE,
        coeff_map]
      simp [D]

/-! ## Hanna's logarithm as a Gauss sequence -/

/-- $m$ times the coefficient of $x^m$ in `hannaLog f`, as an integer:
$\sum_{n=1}^{m} m f(n, m-n) / n$. -/
def diagSum (f : ℕ → ℕ → ℤ) (m : ℕ) : ℤ := ∑ n ∈ Icc 1 m, (m * f n (m - n)) / n

theorem dvd_add_mul {n k : ℕ} {g : ℤ} (h : (n : ℤ) ∣ k * g) :
    (n : ℤ) ∣ ((n + k : ℕ) : ℤ) * g := by
  push_cast
  rw [add_mul]
  exact dvd_add (dvd_mul_right _ _) h

theorem dvd_mul_of_le {f : ℕ → ℕ → ℤ} (hf : ∀ n k : ℕ, 0 < n → (n : ℤ) ∣ k * f n k)
    {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m) : (n : ℤ) ∣ m * f n (m - n) := by
  have h := dvd_add_mul (hf n (m - n) hn)
  rwa [Nat.add_sub_cancel' hnm] at h

theorem hannaLog_eq_ofInt {f : ℕ → ℕ → ℤ} (hf : ∀ n k : ℕ, 0 < n → (n : ℤ) ∣ k * f n k) :
    hannaLog f = ofInt (diagSum f) := by
  ext m
  rw [hannaLog, ofInt, coeff_mk, coeff_mk]
  split_ifs with hm
  · subst hm
    simp
  rw [diagSum, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnm⟩ := Finset.mem_Icc.mp hn
  rw [Int.cast_div (dvd_mul_of_le hf hn1 hnm) (by exact_mod_cast (show n ≠ 0 by omega))]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp

theorem prime_pow_dvd_of_mul_eq {p : ℕ} (hp : p.Prime) {r n : ℕ} (hn : ¬p ∣ n) {x y : ℤ}
    (h : (n : ℤ) * x = y) (hy : (p : ℤ) ^ r ∣ y) : (p : ℤ) ^ r ∣ x := by
  have hcop := isCoprime_of_not_dvd hp (y := (n : ℤ)) (by exact_mod_cast hn) r
  rw [← h, mul_comm] at hy
  exact hcop.dvd_of_dvd_mul_right hy

/-- If $a x = b D$, $p^{j+1} \mid D$ whenever $p^j \mid a$, and $p^s \mid b$, then
$p^{s+1} \mid x$. -/
theorem prime_pow_succ_dvd_of_mul_eq {p : ℕ} (hp : p.Prime) {a b : ℕ} (ha : a ≠ 0) {x D : ℤ}
    (h : (a : ℤ) * x = b * D) (hD : ∀ j, p ^ j ∣ a → (p : ℤ) ^ (j + 1) ∣ D) {s : ℕ}
    (hs : p ^ s ∣ b) : (p : ℤ) ^ (s + 1) ∣ x := by
  obtain ⟨v, u, hu, rfl⟩ : ∃ v u, ¬p ∣ u ∧ a = p ^ v * u :=
    ⟨_, _, Nat.not_dvd_ordCompl hp ha, (Nat.ordProj_mul_ordCompl_eq_self a p).symm⟩
  have h1 : (p : ℤ) ^ s * (p : ℤ) ^ (v + 1) ∣ b * D :=
    mul_dvd_mul (by exact_mod_cast hs) (hD v (dvd_mul_right _ _))
  rw [← h] at h1
  have h2 : (p : ℤ) ^ v * (p : ℤ) ^ (s + 1) ∣ (p : ℤ) ^ v * ((u : ℤ) * x) := by
    have e1 : (p : ℤ) ^ s * (p : ℤ) ^ (v + 1) = (p : ℤ) ^ v * (p : ℤ) ^ (s + 1) := by ring
    have e2 : ((p ^ v * u : ℕ) : ℤ) * x = (p : ℤ) ^ v * ((u : ℤ) * x) := by push_cast; ring
    rwa [e1, e2] at h1
  have h3 := (mul_dvd_mul_iff_left (pow_ne_zero v (by exact_mod_cast hp.ne_zero))).mp h2
  exact prime_pow_dvd_of_mul_eq hp hu rfl h3

/-- The split of $c(pM) - c(M)$: the terms with $p \nmid n$, and the differences of the paired
terms $(pn_0, pk_0)$ and $(n_0, k_0)$. -/
theorem diagSum_mul_sub (f : ℕ → ℕ → ℤ) {p : ℕ} (hp : p.Prime) (M : ℕ) :
    diagSum f (p * M) - diagSum f M =
      ∑ n ∈ (Icc 1 (p * M)).filter (¬p ∣ ·), ((p * M : ℕ) : ℤ) * f n (p * M - n) / n +
        ∑ n0 ∈ Icc 1 M, ((M : ℤ) * f (p * n0) (p * (M - n0)) / n0 -
          M * f n0 (M - n0) / n0) := by
  have hfilt : (Icc 1 (p * M)).filter (p ∣ ·) = (Icc 1 M).image (p * ·) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨n0, rfl⟩⟩
      refine ⟨n0, ⟨?_, Nat.le_of_mul_le_mul_left h2 hp.pos⟩, rfl⟩
      rcases Nat.eq_zero_or_pos n0 with rfl | h
      · omega
      · exact h
    · rintro ⟨n0, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hp.pos h1, Nat.mul_le_mul_left p h2⟩, dvd_mul_right p n0⟩
  have hsplit : diagSum f (p * M) =
      ∑ n ∈ (Icc 1 (p * M)).filter (¬p ∣ ·), ((p * M : ℕ) : ℤ) * f n (p * M - n) / n +
        ∑ n0 ∈ Icc 1 M, (M : ℤ) * f (p * n0) (p * (M - n0)) / n0 := by
    rw [diagSum, ← sum_filter_add_sum_filter_not (Icc 1 (p * M)) (p ∣ ·), hfilt,
      sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h, add_comm]
    congr 1
    refine sum_congr rfl fun n0 _ => ?_
    rw [← Nat.mul_sub,
      show ((p * M : ℕ) : ℤ) * f (p * n0) (p * (M - n0)) =
        (p : ℤ) * (M * f (p * n0) (p * (M - n0))) by push_cast; ring,
      Nat.cast_mul, Int.mul_ediv_mul_of_pos _ _ (by exact_mod_cast hp.pos)]
  rw [hsplit, diagSum, add_sub_assoc, ← sum_sub_distrib]

/-- An unpaired term: if $p \nmid n$ and $p^r \mid pM$, then $p^r \mid pM f(n, pM-n)/n$. -/
theorem prime_pow_dvd_unpaired {f : ℕ → ℕ → ℤ} (hf : ∀ n k : ℕ, 0 < n → (n : ℤ) ∣ k * f n k)
    {p r M n : ℕ} (hp : p.Prime) (hr : p ^ r ∣ p * M)
    (hn : n ∈ (Icc 1 (p * M)).filter (¬p ∣ ·)) :
    (p : ℤ) ^ r ∣ ((p * M : ℕ) : ℤ) * f n (p * M - n) / n := by
  obtain ⟨hn1, hn2⟩ := mem_Icc.mp (mem_filter.mp hn).1
  refine prime_pow_dvd_of_mul_eq hp (mem_filter.mp hn).2
    (Int.mul_ediv_cancel' (dvd_mul_of_le hf hn1 hn2)) ?_
  exact dvd_mul_of_dvd_left (by exact_mod_cast hr) _

/-- A paired term: if $p^{j+1} \mid f(pn_0,pk_0) - f(n_0,k_0)$ whenever $p^j \mid n_0$, and
$p^s \mid M$, then $p^{s+1}$ divides the difference of the two terms. -/
theorem prime_pow_dvd_paired {f : ℕ → ℕ → ℤ} (hf : ∀ n k : ℕ, 0 < n → (n : ℤ) ∣ k * f n k)
    {p s M n0 : ℕ} (hp : p.Prime) (hsM : p ^ s ∣ M) (hn0 : n0 ∈ Icc 1 M)
    (hD : ∀ j, p ^ j ∣ n0 → (p : ℤ) ^ (j + 1) ∣ f (p * n0) (p * (M - n0)) - f n0 (M - n0)) :
    (p : ℤ) ^ (s + 1) ∣
      (M : ℤ) * f (p * n0) (p * (M - n0)) / n0 - M * f n0 (M - n0) / n0 := by
  obtain ⟨hn1, hn2⟩ := mem_Icc.mp hn0
  have hd1 : (n0 : ℤ) ∣ M * f (p * n0) (p * (M - n0)) := by
    have h := hf (p * n0) (p * (M - n0)) (Nat.mul_pos hp.pos hn1)
    push_cast at h
    rw [mul_assoc] at h
    have h' := Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hp.ne_zero) h
    have h'' := dvd_add_mul (n := n0) (k := M - n0) (by exact_mod_cast h')
    rwa [Nat.add_sub_cancel' hn2] at h''
  have hd2 := dvd_mul_of_le hf hn1 hn2
  refine prime_pow_succ_dvd_of_mul_eq hp (a := n0) (b := M) (by omega)
    (D := f (p * n0) (p * (M - n0)) - f n0 (M - n0)) ?_ hD hsM
  rw [mul_sub, Int.mul_ediv_cancel' hd1, Int.mul_ediv_cancel' hd2, mul_sub]

/-- **The diagonal pairing.** If $n \mid k f(n,k)$ and $p^{j+1} \mid f(pn,pk) - f(n,k)$
whenever $p^j \mid n$, then $m \mapsto m\,[x^m]$ `hannaLog f` is a Gauss sequence. -/
theorem diagSum_gauss {f : ℕ → ℕ → ℤ} (hf : ∀ n k : ℕ, 0 < n → (n : ℤ) ∣ k * f n k)
    (hpair : ∀ p j n k : ℕ, p.Prime → 0 < n → p ^ j ∣ n →
      (p : ℤ) ^ (j + 1) ∣ f (p * n) (p * k) - f n k) : Gauss (diagSum f) := by
  intro p r M hp hr
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hsM : p ^ s ∣ M := by
    rw [pow_succ'] at hr
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos hr
  rw [diagSum_mul_sub f hp M]
  exact dvd_add (dvd_sum fun n hn => prime_pow_dvd_unpaired hf hp hr hn)
    (dvd_sum fun n0 hn0 => prime_pow_dvd_paired hf hp hsM hn0
      fun j hj => hpair p j n0 (M - n0) hp (mem_Icc.mp hn0).1 hj)

/-! ## Coefficients of $U^n$ -/

section Coefficients

variable (U : ℤ⟦X⟧)

theorem coeff_zero_pow (hU : constantCoeff U = 1) (n : ℕ) : coeff 0 (U ^ n) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, map_pow, hU, one_pow]

/-- **Lemma 1(b).** $n \mid k\,[z^k]\,U^n$. -/
theorem dvd_mul_coeff_pow (n k : ℕ) : (n : ℤ) ∣ k * coeff k (U ^ n) := by
  rcases k with _ | i
  · simp
  have h := congrArg (coeff i) (Derivation.leibniz_pow (derivative (R := ℤ)) U n)
  rw [coeff_derivative, nsmul_eq_mul, smul_eq_mul, ← map_natCast (C (R := ℤ)), coeff_C_mul] at h
  exact ⟨coeff i (U ^ (n - 1) * d⁄dX U), by push_cast; linear_combination h⟩

theorem C_dvd_of_forall_coeff {a : ℤ} {F : ℤ⟦X⟧} (h : ∀ i, a ∣ coeff i F) : C a ∣ F :=
  ⟨mk fun i => coeff i F / a, by
    ext i
    rw [coeff_C_mul, coeff_mk, Int.mul_ediv_cancel' (h i)]⟩

theorem dvd_coeff_of_C_dvd {a : ℤ} {F : ℤ⟦X⟧} (h : C a ∣ F) (i : ℕ) : a ∣ coeff i F := by
  obtain ⟨G, rfl⟩ := h
  rw [coeff_C_mul]
  exact dvd_mul_right _ _

/-- Frobenius: $U^p \equiv U(z^p) \pmod p$. -/
theorem prime_dvd_pow_sub_expand {p : ℕ} (hp : p.Prime) :
    (p : ℤ⟦X⟧) ∣ U ^ p - expand p hp.ne_zero U := by
  have := Fact.mk hp
  have hmap : map (Int.castRingHom (ZMod p)) (U ^ p - expand p hp.ne_zero U) = 0 := by
    rw [map_sub, map_pow, map_expand, ← map_frobenius_expand p hp.ne_zero, ZMod.frobenius_zmod,
      map_id, id, sub_self]
  rw [← map_natCast (C (R := ℤ))]
  refine C_dvd_of_forall_coeff fun i => ?_
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have := congrArg (coeff i) hmap
  rwa [coeff_map, map_zero] at this

/-- **Lemma 1(a).** If $p^j \mid n$, then $[z^{pk}]\,U^{pn} \equiv [z^k]\,U^n \pmod{p^{j+1}}$. -/
theorem prime_pow_dvd_coeff_pow_sub {p : ℕ} (hp : p.Prime) {j n : ℕ} (hn : p ^ j ∣ n) (k : ℕ) :
    (p : ℤ) ^ (j + 1) ∣ coeff (p * k) (U ^ (p * n)) - coeff k (U ^ n) := by
  obtain ⟨t, rfl⟩ := hn
  have h1 := (dvd_sub_pow_of_dvd_sub (prime_dvd_pow_sub_expand U hp) j).trans
    (sub_dvd_pow_sub_pow _ _ t)
  have e1 : ((U ^ p) ^ p ^ j) ^ t = U ^ (p * (p ^ j * t)) := by
    simp only [← pow_mul, mul_assoc]
  have e2 : ((expand p hp.ne_zero U) ^ p ^ j) ^ t = expand p hp.ne_zero (U ^ (p ^ j * t)) := by
    rw [← map_pow, ← map_pow, ← pow_mul]
  rw [e1, e2, ← map_natCast (C (R := ℤ)), ← map_pow] at h1
  have := dvd_coeff_of_C_dvd h1 (p * k)
  rwa [map_sub, coeff_expand_mul] at this

end Coefficients

/-! ## Theorem 1 (diagonal form) -/

section Criterion

variable (U : ℤ⟦X⟧)

/-- **The pair congruence.** Under (E1) and (E2), if $p^j \mid n$ then
$B(pn,pk)^{e(pn,pk)} \equiv B(n,k)^{e(n,k)} \pmod{p^{j+1}}$. -/
theorem pair_congr (hU : constantCoeff U = 1) {e : ℕ → ℕ → ℕ}
    (hE1 : ∀ p n k : ℕ, p.Prime → 0 < n → 0 < k → ¬(p : ℤ) ∣ coeff k (U ^ n) →
      e (p * n) (p * k) ≡ e n k [MOD (p - 1) * p ^ padicValNat p n])
    (hE2 : ∀ p n k : ℕ, p.Prime → 0 < n → 0 < k → (p : ℤ) ∣ coeff k (U ^ n) →
      e (p * n) (p * k) = e n k ∨
        ((p : ℤ) ^ (padicValNat p n + 1) ∣ coeff k (U ^ n) ^ e n k ∧
          (p : ℤ) ^ (padicValNat p n + 1) ∣ coeff (p * k) (U ^ (p * n)) ^ e (p * n) (p * k)))
    {p j n : ℕ} (k : ℕ) (hp : p.Prime) (hn : 0 < n) (hj : p ^ j ∣ n) :
    (p : ℤ) ^ (j + 1) ∣
      coeff (p * k) (U ^ (p * n)) ^ e (p * n) (p * k) - coeff k (U ^ n) ^ e n k := by
  have := Fact.mk hp
  have hjv : j ≤ padicValNat p n := (padicValNat_dvd_iff_le hn.ne').mp hj
  refine (pow_dvd_pow (p : ℤ) (by omega : j + 1 ≤ padicValNat p n + 1)).trans ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [coeff_zero_pow U hU]
  have hB := prime_pow_dvd_coeff_pow_sub U hp (pow_padicValNat_dvd (n := n)) k
  by_cases hpB : (p : ℤ) ∣ coeff k (U ^ n)
  · rcases hE2 p n k hp hn hk hpB with h | ⟨h1, h2⟩
    · rw [h]
      exact hB.trans (sub_dvd_pow_sub_pow _ _ _)
    · exact dvd_sub h2 h1
  · have he := hE1 p n k hp hn hk hpB
    rw [Nat.mul_comm (p - 1), ← Nat.totient_prime_pow_succ hp] at he
    exact prime_pow_dvd_pow_sub_pow hp (Nat.succ_pos _) hB hpB he

end Criterion

/-- **The criterion (Theorem 1), diagonal form.** Let $U \in 1 + z\mathbb{Z}[[z]]$,
$B(n,k) = [z^k]\,U^n$, and let $e(n,k) \ge 1$ for $n, k \ge 1$. Suppose that for every prime $p$
and all $n, k \ge 1$, with $b = B(n,k)$, $b' = B(pn,pk)$, $e = e(n,k)$, $e' = e(pn,pk)$ and
$r = 1 + v_p(n)$:
- (E1) if $p \nmid b$, then $e' \equiv e \pmod{(p-1)p^{v_p(n)}}$;
- (E2) if $p \mid b$, then $e' = e$, or both $p^r \mid b^e$ and $p^r \mid b'^{e'}$.

Then $\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} B(n,k)^{e(n,k)} x^k] x^n/n\bigr)$ has integer
coefficients. -/
theorem integral_of_criterion (U : ℤ⟦X⟧) (hU : constantCoeff U = 1) (e : ℕ → ℕ → ℕ)
    (he : ∀ n k : ℕ, 0 < n → 0 < k → 0 < e n k)
    (hE1 : ∀ p n k : ℕ, p.Prime → 0 < n → 0 < k → ¬(p : ℤ) ∣ coeff k (U ^ n) →
      e (p * n) (p * k) ≡ e n k [MOD (p - 1) * p ^ padicValNat p n])
    (hE2 : ∀ p n k : ℕ, p.Prime → 0 < n → 0 < k → (p : ℤ) ∣ coeff k (U ^ n) →
      e (p * n) (p * k) = e n k ∨
        ((p : ℤ) ^ (padicValNat p n + 1) ∣ coeff k (U ^ n) ^ e n k ∧
          (p : ℤ) ^ (padicValNat p n + 1) ∣ coeff (p * k) (U ^ (p * n)) ^ e (p * n) (p * k)))
    (m : ℕ) : ∃ z : ℤ, coeff m (hannaExp fun n k => coeff k (U ^ n) ^ e n k) = z := by
  have hf : ∀ n k : ℕ, 0 < n → (n : ℤ) ∣ k * coeff k (U ^ n) ^ e n k := by
    intro n k hn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    obtain ⟨d, hd⟩ : ∃ d, e n k = d + 1 := ⟨e n k - 1, by have := he n k hn hk; omega⟩
    rw [hd, pow_succ', ← mul_assoc]
    exact dvd_mul_of_dvd_left (dvd_mul_coeff_pow U n k) _
  rw [hannaExp, hannaLog_eq_ofInt hf]
  exact exists_coeff_eq_intCast_of_gauss
    (diagSum_gauss hf fun p j n k hp hn hj => pair_congr U hU hE1 hE2 k hp hn hj) m

/-- **Corollary 2(a), diagonal form.** For $U \in 1 + z\mathbb{Z}[[z]]$ and a constant exponent
$c \ge 1$, $\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} B(n,k)^{c} x^k] x^n/n\bigr)$ has integer
coefficients. -/
theorem integral_of_const_exponent (U : ℤ⟦X⟧) (hU : constantCoeff U = 1) {c : ℕ} (hc : 0 < c)
    (m : ℕ) : ∃ z : ℤ, coeff m (hannaExp fun n k => coeff k (U ^ n) ^ c) = z :=
  integral_of_criterion U hU (fun _ _ => c) (fun _ _ _ _ => hc)
    (fun _ _ _ _ _ _ _ => Nat.ModEq.refl _) (fun _ _ _ _ _ _ _ => Or.inl rfl) m

/-! ## Corollary 2(b): polynomial exponents -/

/-- $P(pz) \equiv P(z) \pmod{(p-1)g}$ when $g$ divides both coordinates of $z$. -/
theorem eval_mul_sub_eval_dvd (P : MvPolynomial (Fin 2) ℤ) {p g : ℤ} {z : Fin 2 → ℤ}
    (hz : ∀ i, g ∣ z i) :
    (p - 1) * g ∣ MvPolynomial.eval (fun i => p * z i) P - MvPolynomial.eval z P := by
  refine MvPolynomial.induction_on
    (motive := fun Q => (p - 1) * g ∣ MvPolynomial.eval (fun i => p * z i) Q - MvPolynomial.eval z Q)
    P (fun a => by simp) (fun P Q hP hQ => ?_) (fun P i hP => ?_)
  · rw [map_add, map_add, add_sub_add_comm]
    exact dvd_add hP hQ
  · rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
    have : MvPolynomial.eval (fun i => p * z i) P * (p * z i) - MvPolynomial.eval z P * z i =
        (MvPolynomial.eval (fun i => p * z i) P - MvPolynomial.eval z P) * (p * z i) +
          MvPolynomial.eval z P * ((p - 1) * z i) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left hP _)
      (dvd_mul_of_dvd_right (mul_dvd_mul_left _ (hz i)) _)

/-- (E1) for an exponent that agrees with a polynomial in $\mathbb{Z}[n,k]$. -/
theorem exponent_modEq {e : ℕ → ℕ → ℕ} {P : MvPolynomial (Fin 2) ℤ}
    (hP : ∀ n k : ℕ, 0 < n → (e n k : ℤ) = MvPolynomial.eval ![(n : ℤ), k] P)
    {p v n k : ℕ} (hp : p.Prime) (hn : 0 < n) (hvn : p ^ v ∣ n) (hvk : p ^ v ∣ k) :
    e (p * n) (p * k) ≡ e n k [MOD (p - 1) * p ^ v] := by
  rw [Nat.modEq_iff_dvd, hP _ _ hn, hP _ _ (Nat.mul_pos hp.pos hn)]
  have h := eval_mul_sub_eval_dvd P (p := (p : ℤ)) (g := (p : ℤ) ^ v) (z := ![(n : ℤ), k])
    (fun i => by
      fin_cases i
      · simpa using (Int.natCast_dvd_natCast.mpr hvn)
      · simpa using (Int.natCast_dvd_natCast.mpr hvk))
  have hz : (fun i => (p : ℤ) * ![(n : ℤ), (k : ℤ)] i) =
      ![((p * n : ℕ) : ℤ), ((p * k : ℕ) : ℤ)] := by
    funext i
    fin_cases i <;> simp
  rw [hz] at h
  rw [Nat.cast_mul (p - 1), Nat.cast_sub hp.one_le, Nat.cast_pow, Nat.cast_one]
  have := dvd_neg.mpr h
  rwa [neg_sub] at this

/-- The claim in the proof of Corollary 2(b): if $p \mid b$, $p^j \mid n$ and (M) holds, then
$p^{j+1} \mid b^e$. -/
theorem prime_pow_succ_dvd_pow {p : ℕ} (hp : p.Prime) {n j e : ℕ} {b : ℤ} (hn : 0 < n)
    (hjn : p ^ j ∣ n) (hpb : (p : ℤ) ∣ b) (he : 0 < e)
    (hM : 2 ≤ |b| → ∃ i : ℕ, 0 < i ∧ (n : ℤ) ∣ i * b ∧ min n (i + 1) ≤ e) :
    (p : ℤ) ^ (j + 1) ∣ b ^ e := by
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [zero_pow he.ne']
    exact dvd_zero _
  have hb2 : 2 ≤ |b| := by
    have h1 := Int.le_of_dvd (abs_pos.mpr hb0) ((dvd_abs _ _).mpr hpb)
    have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  obtain ⟨i, hi, hib, hie⟩ := hM hb2
  rcases min_le_iff.mp hie with h | h
  · have hjn' : j + 1 ≤ n := (Nat.lt_pow_self hp.one_lt).trans_le (Nat.le_of_dvd hn hjn)
    exact (pow_dvd_pow (p : ℤ) (hjn'.trans h)).trans (pow_dvd_pow_of_dvd hpb e)
  · obtain ⟨s, u, hu, rfl⟩ : ∃ s u, ¬p ∣ u ∧ i = p ^ s * u :=
      ⟨_, _, Nat.not_dvd_ordCompl hp hi.ne', (Nat.ordProj_mul_ordCompl_eq_self i p).symm⟩
    have h1 : (p : ℤ) ^ j ∣ (p : ℤ) ^ s * b := by
      have h0 := (Int.natCast_dvd_natCast.mpr hjn).trans hib
      have h0' : (p : ℤ) ^ j ∣ (u : ℤ) * ((p : ℤ) ^ s * b) := by
        push_cast at h0
        rw [show (u : ℤ) * ((p : ℤ) ^ s * b) = (p : ℤ) ^ s * u * b by ring]
        exact h0
      exact (isCoprime_of_not_dvd hp (by exact_mod_cast hu) j).dvd_of_dvd_mul_left h0'
    have hsi : s + 1 ≤ p ^ s * u :=
      (Nat.lt_pow_self hp.one_lt).trans_le (Nat.le_of_dvd hi (dvd_mul_right _ _))
    have h2 : (p : ℤ) ^ (s + 1) ∣ b ^ (p ^ s * u) :=
      (pow_dvd_pow _ hsi).trans (pow_dvd_pow_of_dvd hpb _)
    have h3 : (p : ℤ) ^ s * (p : ℤ) ^ (j + 1) ∣ (p : ℤ) ^ s * b ^ (p ^ s * u + 1) :=
      calc (p : ℤ) ^ s * (p : ℤ) ^ (j + 1) = (p : ℤ) ^ j * (p : ℤ) ^ (s + 1) := by ring
        _ ∣ (p : ℤ) ^ s * b * b ^ (p ^ s * u) := mul_dvd_mul h1 h2
        _ = (p : ℤ) ^ s * b ^ (p ^ s * u + 1) := by ring
    have h4 := (mul_dvd_mul_iff_left (pow_ne_zero s (by exact_mod_cast hp.ne_zero))).mp h3
    exact h4.trans (pow_dvd_pow b h)

/-- **Corollary 2(b), diagonal form.** Let $U \in 1 + z\mathbb{Z}[[z]]$ and
$B(n,k) = [z^k]\,U^n$. Let $e(n,k)$ agree for $n \ge 1$ with a polynomial $P \in \mathbb{Z}[n,k]$,
with $e(n,k) \ge 1$ for $n, k \ge 1$. Assume (M): for all $n, k \ge 1$ with $|B(n,k)| \ge 2$
there is $j \ge 1$ with $n \mid j\,B(n,k)$ and $e(n,k) \ge \min(n, j+1)$. Then
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} B(n,k)^{e(n,k)} x^k] x^n/n\bigr)$ has integer
coefficients. -/
theorem integral_of_polynomial_exponent (U : ℤ⟦X⟧) (hU : constantCoeff U = 1)
    (e : ℕ → ℕ → ℕ) (P : MvPolynomial (Fin 2) ℤ)
    (hP : ∀ n k : ℕ, 0 < n → (e n k : ℤ) = MvPolynomial.eval ![(n : ℤ), k] P)
    (he : ∀ n k : ℕ, 0 < n → 0 < k → 0 < e n k)
    (hM : ∀ n k : ℕ, 0 < n → 0 < k → 2 ≤ |coeff k (U ^ n)| →
      ∃ j : ℕ, 0 < j ∧ (n : ℤ) ∣ j * coeff k (U ^ n) ∧ min n (j + 1) ≤ e n k)
    (m : ℕ) : ∃ z : ℤ, coeff m (hannaExp fun n k => coeff k (U ^ n) ^ e n k) = z := by
  refine integral_of_criterion U hU e he (fun p n k hp hn hk hpB => ?_)
    (fun p n k hp hn hk hpB => Or.inr ⟨?_, ?_⟩) m
  · have hv : p ^ padicValNat p n ∣ n := pow_padicValNat_dvd
    have hvk : p ^ padicValNat p n ∣ k := by
      have h := (Int.natCast_dvd_natCast.mpr hv).trans (dvd_mul_coeff_pow U n k)
      push_cast at h
      exact_mod_cast (isCoprime_of_not_dvd hp hpB _).dvd_of_dvd_mul_right h
    exact exponent_modEq hP hp hn hv hvk
  · exact prime_pow_succ_dvd_pow hp hn pow_padicValNat_dvd hpB (he n k hn hk) (hM n k hn hk)
  · have hpB' : (p : ℤ) ∣ coeff (p * k) (U ^ (p * n)) := by
      have h := prime_pow_dvd_coeff_pow_sub U hp (j := 0) (n := n) (by simp) k
      rw [zero_add, pow_one] at h
      simpa using dvd_add h hpB
    have hpn : 0 < p * n := Nat.mul_pos hp.pos hn
    have hpk : 0 < p * k := Nat.mul_pos hp.pos hk
    have hdiv : p ^ (padicValNat p n + 1) ∣ p * n := by
      rw [pow_succ']
      exact Nat.mul_dvd_mul_left p pow_padicValNat_dvd
    exact (pow_dvd_pow _ (Nat.le_succ _)).trans
      (prime_pow_succ_dvd_pow hp hpn hdiv hpB' (he _ _ hpn hpk) (hM _ _ hpn hpk))

/-! ## The two binomial families -/

theorem coeff_mk_one_pow (n k : ℕ) :
    coeff k ((mk 1 : ℤ⟦X⟧) ^ n) = ((n + k - 1).choose k : ℤ) := by
  rcases n with _ | d
  · rcases k with _ | k
    · simp
    · simp [coeff_one]
  · rw [mk_one_pow_eq_mk_choose_add, coeff_mk, show d + 1 + k - 1 = d + k by omega,
      Nat.choose_symm_add]

theorem constantCoeff_mk_one : constantCoeff (mk 1 : ℤ⟦X⟧) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  rfl

theorem coeff_one_add_X_pow (n k : ℕ) :
    coeff k ((1 + X : ℤ⟦X⟧) ^ n) = (n.choose k : ℤ) := by
  have : (1 + X : ℤ⟦X⟧) ^ n = (((Polynomial.X + 1 : Polynomial ℤ) ^ n : Polynomial ℤ) : ℤ⟦X⟧) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_one, add_comm]
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow]

theorem constantCoeff_one_add_X : constantCoeff (1 + X : ℤ⟦X⟧) = 1 := by simp

theorem dvd_mul_choose_add (n k : ℕ) : (n : ℤ) ∣ k * ((n + k - 1).choose k : ℤ) := by
  have h := dvd_mul_coeff_pow (mk 1) n k
  rwa [coeff_mk_one_pow] at h

theorem dvd_mul_choose (n k : ℕ) : (n : ℤ) ∣ k * (n.choose k : ℤ) := by
  have h := dvd_mul_coeff_pow (1 + X) n k
  rwa [coeff_one_add_X_pow] at h


/-! ## Theorem 4: the obstruction at $k = 1$ -/

/-- **Dold's criterion, (⇒).** If $\exp\left(\sum b(n) x^n/n\right)$ has integer
coefficients, $p$ is prime and $p \nmid M$, then $p \mid b(pM) - b(M)$. -/
theorem prime_dvd_mul_sub_of_integral {b : ℕ → ℤ}
    (h : ∀ n, ∃ z : ℤ, coeff n (subst (ofInt b) (exp ℚ)) = z) {p M : ℕ} (hp : p.Prime)
    (hM : 0 < M) (hpM : ¬p ∣ M) : (p : ℤ) ∣ b (p * M) - b M := by
  have hL0 := constantCoeff_ofInt b
  obtain ⟨c, hc⟩ := exists_eulerProduct h (constantCoeff_exp_subst hL0) (p * M)
  have key := coeff_logDeriv_eq (derivative_exp_subst hL0) (derivative_eulerProduct c (p * M))
    (constantCoeff_exp_subst hL0) (constantCoeff_eulerProduct c (p * M)) hc
  have hb : ∀ n, 0 < n → n ≤ p * M → b n = ∑ d ∈ n.divisors, (d : ℤ) * c d := fun n hn hnN => by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have h1 : (b (j + 1) : ℚ) = ∑ d ∈ (j + 1).divisors, (d : ℚ) * c d := by
      rw [← coeff_derivative_ofInt, key j (by omega), coeff_logDeriv_eulerProduct c (by omega)]
    exact_mod_cast h1
  have hpMpos : 0 < p * M := Nat.mul_pos hp.pos hM
  rw [hb _ hpMpos le_rfl, hb M hM (Nat.le_mul_of_pos_left M hp.pos),
    show p * M = p ^ 1 * M by rw [pow_one],
    sum_divisors_prime_pow_mul hp hpM (fun d => (d : ℤ) * c d), sum_range_succ, sum_range_one]
  simp only [pow_zero, one_mul, pow_one, add_sub_cancel_left]
  exact dvd_sum fun d _ => by push_cast; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

/-- $[z]\,U^n = n\,[z]\,U$ when $U(0) = 1$. -/
theorem coeff_one_pow (U : ℤ⟦X⟧) (hU : constantCoeff U = 1) (n : ℕ) :
    coeff 1 (U ^ n) = n * coeff 1 U := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ, sum_cons, Finset.Nat.antidiagonal_zero,
      sum_map, sum_singleton]
    simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map,
      Nat.succ_eq_add_one, zero_add, ih, coeff_zero_eq_constantCoeff_apply, map_pow, hU,
      one_pow, Function.Embedding.refl_apply]
    push_cast
    ring

/-- The pair congruence modulo $p$ for a polynomial exponent. -/
theorem pair_congr_prime (U : ℤ⟦X⟧) (hU : constantCoeff U = 1) {e : ℕ → ℕ → ℕ}
    {P : MvPolynomial (Fin 2) ℤ}
    (hP : ∀ n k : ℕ, 0 < n → (e n k : ℤ) = MvPolynomial.eval ![(n : ℤ), k] P)
    (he : ∀ n k : ℕ, 0 < n → 0 < k → 0 < e n k) {p n : ℕ} (k : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (p : ℤ) ∣ coeff (p * k) (U ^ (p * n)) ^ e (p * n) (p * k) - coeff k (U ^ n) ^ e n k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [coeff_zero_pow U hU]
  have hB := prime_pow_dvd_coeff_pow_sub U hp (j := 0) (n := n) (by simp) k
  rw [zero_add, pow_one] at hB
  by_cases hpB : (p : ℤ) ∣ coeff k (U ^ n)
  · have hpB' : (p : ℤ) ∣ coeff (p * k) (U ^ (p * n)) := by simpa using dvd_add hB hpB
    have hpn : 0 < p * n := Nat.mul_pos hp.pos hn
    have hpk : 0 < p * k := Nat.mul_pos hp.pos hk
    exact dvd_sub (hpB'.trans (dvd_pow_self _ (he _ _ hpn hpk).ne'))
      (hpB.trans (dvd_pow_self _ (he _ _ hn hk).ne'))
  · have he' := exponent_modEq hP hp hn (v := 0) (k := k) (by simp) (by simp)
    rw [pow_zero, mul_one] at he'
    have := prime_pow_dvd_pow_sub_pow hp (k := 1) (a := e (p * n) (p * k)) (b := e n k) one_pos
      (by simpa using hB) hpB (by rw [pow_one, Nat.totient_prime hp]; exact he')
    simpa using this

/-- **The obstruction at $k = 1$ (Theorem 4), diagonal form.** Let $U \in 1 + z\mathbb{Z}[[z]]$
and $B(n,k) = [z^k]\,U^n$. Let $e(n,k)$ agree for $n \ge 1$ with a polynomial
$P \in \mathbb{Z}[n,k]$, with $e(n,k) \ge 1$ for $n, k \ge 1$. If a prime $p \nmid [z]\,U$ has
$e(p,1) = 1$ and $e(p^2,p) \ne 1$, then
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} B(n,k)^{e(n,k)} x^k] x^n/n\bigr)$ does not have integer
coefficients. -/
theorem not_integral_of_exponent (U : ℤ⟦X⟧) (hU : constantCoeff U = 1) (e : ℕ → ℕ → ℕ)
    (P : MvPolynomial (Fin 2) ℤ)
    (hP : ∀ n k : ℕ, 0 < n → (e n k : ℤ) = MvPolynomial.eval ![(n : ℤ), k] P)
    (he : ∀ n k : ℕ, 0 < n → 0 < k → 0 < e n k) {p : ℕ} (hp : p.Prime)
    (hu : ¬(p : ℤ) ∣ coeff 1 U) (h1 : e p 1 = 1) (h2 : e (p ^ 2) p ≠ 1) :
    ¬∀ m, ∃ z : ℤ, coeff m (hannaExp fun n k => coeff k (U ^ n) ^ e n k) = z := by
  intro hint
  set f : ℕ → ℕ → ℤ := fun n k => coeff k (U ^ n) ^ e n k with hfdef
  have hf : ∀ n k : ℕ, 0 < n → (n : ℤ) ∣ k * f n k := by
    intro n k hn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    obtain ⟨d, hd⟩ : ∃ d, e n k = d + 1 := ⟨e n k - 1, by have := he n k hn hk; omega⟩
    rw [hfdef]
    dsimp only
    rw [hd, pow_succ', ← mul_assoc]
    exact dvd_mul_of_dvd_left (dvd_mul_coeff_pow U n k) _
  rw [hannaExp, hannaLog_eq_ofInt hf] at hint
  have hpM : ¬p ∣ p + 1 := fun h => hp.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_add_right (dvd_refl p)).mp h))
  have hdiff := prime_dvd_mul_sub_of_integral hint hp (Nat.succ_pos p) hpM
  rw [diagSum_mul_sub f hp (p + 1)] at hdiff
  have hA : (p : ℤ) ∣ ∑ n ∈ (Icc 1 (p * (p + 1))).filter (¬p ∣ ·),
      ((p * (p + 1) : ℕ) : ℤ) * f n (p * (p + 1) - n) / n :=
    dvd_sum fun n hn => by
      simpa using prime_pow_dvd_unpaired hf hp (r := 1) (by simp) hn
  have hpmem : p ∈ Icc 1 (p + 1) := mem_Icc.mpr ⟨hp.one_lt.le, Nat.le_succ p⟩
  rw [← add_sum_erase _ _ hpmem] at hdiff
  have hB : (p : ℤ) ∣ ∑ n0 ∈ (Icc 1 (p + 1)).erase p,
      (((p + 1 : ℕ) : ℤ) * f (p * n0) (p * (p + 1 - n0)) / n0 -
        (p + 1 : ℕ) * f n0 (p + 1 - n0) / n0) :=
    dvd_sum fun n0 hn0 => by
      have hn0' := mem_of_mem_erase hn0
      have hne := ne_of_mem_erase hn0
      have hpn0 : ¬p ∣ n0 := by
        intro h
        obtain ⟨hn1, hn2⟩ := mem_Icc.mp hn0'
        have := Nat.le_of_dvd hn1 h
        obtain ⟨t, rfl⟩ := h
        rcases t with _ | _ | t
        · omega
        · exact hne (mul_one p)
        · nlinarith [hp.two_le]
      have := prime_pow_dvd_paired hf hp (s := 0) (by simp) hn0' fun j hj => by
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simpa using pair_congr_prime U hU hP he (p + 1 - n0) hp (mem_Icc.mp hn0').1
        · exact absurd ((dvd_pow_self p hj0.ne').trans hj) hpn0
      simpa using this
  -- The term `n₀ = p`.
  have hB1 : coeff 1 (U ^ p) = p * coeff 1 U := coeff_one_pow U hU p
  have hpp : p * p = p ^ 2 := by ring
  have hfp : f p 1 = p * coeff 1 U := by
    rw [hfdef]
    dsimp only
    rw [h1, pow_one, hB1]
  have hp2 : (p : ℤ) ^ 2 ∣ f (p * p) (p * 1) := by
    have hc := prime_pow_dvd_coeff_pow_sub U hp (j := 1) (n := p) (by simp) 1
    have hb' : (p : ℤ) ∣ coeff (p * 1) (U ^ (p * p)) := by
      have := (dvd_pow_self (p : ℤ) (by norm_num : 1 + 1 ≠ 0)).trans hc
      rw [hB1] at this
      simpa using dvd_add this (dvd_mul_right (p : ℤ) (coeff 1 U))
    have he2 : 2 ≤ e (p * p) (p * 1) := by
      have := he (p * p) (p * 1) (Nat.mul_pos hp.pos hp.pos) (by simpa using hp.pos)
      rw [mul_one, hpp] at this ⊢
      omega
    rw [hfdef]
    exact (pow_dvd_pow_of_dvd hb' 2).trans (pow_dvd_pow _ he2)
  obtain ⟨t, ht⟩ := hp2
  have hX : ((p + 1 : ℕ) : ℤ) * f (p * p) (p * (p + 1 - p)) / p -
      (p + 1 : ℕ) * f p (p + 1 - p) / p = p * ((p + 1) * t) - (p + 1) * coeff 1 U := by
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    rw [show p + 1 - p = 1 by omega, ht, hfp]
    push_cast
    rw [show ((p : ℤ) + 1) * ((p : ℤ) ^ 2 * t) = p * (p * ((p + 1) * t)) by ring,
      show ((p : ℤ) + 1) * ((p : ℤ) * coeff 1 U) = p * ((p + 1) * coeff 1 U) by ring,
      Int.mul_ediv_cancel_left _ hp0.ne', Int.mul_ediv_cancel_left _ hp0.ne']
  rw [hX] at hdiff
  have hfinal : (p : ℤ) ∣ (p + 1) * coeff 1 U := by
    have := dvd_sub (dvd_sub (dvd_sub hdiff hA) hB) (dvd_mul_right (p : ℤ) ((p + 1) * t))
    have e : ∑ n ∈ (Icc 1 (p * (p + 1))).filter (¬p ∣ ·),
          ((p * (p + 1) : ℕ) : ℤ) * f n (p * (p + 1) - n) / n +
        ((p * ((p + 1) * t) - (p + 1) * coeff 1 U) +
          ∑ n0 ∈ (Icc 1 (p + 1)).erase p,
            (((p + 1 : ℕ) : ℤ) * f (p * n0) (p * (p + 1 - n0)) / n0 -
              (p + 1 : ℕ) * f n0 (p + 1 - n0) / n0)) -
        ∑ n ∈ (Icc 1 (p * (p + 1))).filter (¬p ∣ ·),
          ((p * (p + 1) : ℕ) : ℤ) * f n (p * (p + 1) - n) / n -
        ∑ n0 ∈ (Icc 1 (p + 1)).erase p,
            (((p + 1 : ℕ) : ℤ) * f (p * n0) (p * (p + 1 - n0)) / n0 -
              (p + 1 : ℕ) * f n0 (p + 1 - n0) / n0) -
        p * ((p + 1) * t) = -((p + 1) * coeff 1 U) := by ring
    rw [e] at this
    exact (dvd_neg).mp this
  have hpZ := Nat.prime_iff_prime_int.mp hp
  rcases hpZ.dvd_or_dvd hfinal with h | h
  · have : (p : ℤ) ∣ 1 := by simpa using dvd_sub h (dvd_refl (p : ℤ))
    exact hpZ.not_dvd_one this
  · exact hu h

/-! ## Hanna's six conjectures -/

/-- **Hanna's conjecture in A183128.** Every term of A183128 is an integer. -/
theorem a183128_integral (m : ℕ) : ∃ z : ℤ, a183128 m = z := by
  unfold a183128
  simp_rw [← coeff_mk_one_pow]
  refine integral_of_polynomial_exponent (mk 1) constantCoeff_mk_one (fun _ k => k ^ 2 + 1)
    (MvPolynomial.X 1 ^ 2 + 1) (fun n k _ => by simp) (fun _ _ _ _ => by positivity)
    (fun n k hn hk _ => ⟨k, hk, dvd_mul_coeff_pow _ n k, ?_⟩) m
  exact (min_le_right _ _).trans (by nlinarith)

/-- **Hanna's conjecture in A183129.** Every term of A183129 is an integer. -/
theorem a183129_integral (m : ℕ) : ∃ z : ℤ, a183129 m = z := by
  unfold a183129
  simp_rw [← coeff_mk_one_pow]
  refine integral_of_polynomial_exponent (mk 1) constantCoeff_mk_one (fun _ k => k ^ 2 + k)
    (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1) (fun n k _ => by simp)
    (fun _ _ _ hk => by positivity)
    (fun n k hn hk _ => ⟨k, hk, dvd_mul_coeff_pow _ n k, ?_⟩) m
  exact (min_le_right _ _).trans (by nlinarith)

/-- **Hanna's conjecture in A181076.** Every term of A181076 is an integer. -/
theorem a181076_integral (m : ℕ) : ∃ z : ℤ, a181076 m = z := by
  unfold a181076
  simp_rw [← coeff_mk_one_pow]
  exact integral_of_polynomial_exponent (mk 1) constantCoeff_mk_one (fun n _ => n)
    (MvPolynomial.X 0) (fun n k _ => by simp) (fun _ _ hn _ => hn)
    (fun n k hn hk _ => ⟨k, hk, dvd_mul_coeff_pow _ n k, min_le_left _ _⟩) m

/-- **Hanna's conjecture in A181078.** Every term of A181078 is an integer. -/
theorem a181078_integral (m : ℕ) : ∃ z : ℤ, a181078 m = z := by
  unfold a181078
  simp_rw [← coeff_mk_one_pow]
  exact integral_of_polynomial_exponent (mk 1) constantCoeff_mk_one (fun n k => n + k - 1)
    (MvPolynomial.X 0 + MvPolynomial.X 1 - 1)
    (fun n k hn => by simp [Nat.cast_sub (show 1 ≤ n + k by omega)]) (fun _ _ _ hk => by omega)
    (fun n k hn hk _ => ⟨k, hk, dvd_mul_coeff_pow _ n k, (min_le_left _ _).trans (by omega)⟩) m

theorem choose_pow_eq (n k e : ℕ) (he : 0 < e) :
    (if k ≤ n then (n.choose k : ℤ) ^ e else 0) = coeff k ((1 + X : ℤ⟦X⟧) ^ n) ^ e := by
  rw [coeff_one_add_X_pow]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_pow he.ne']

/-- **Hanna's conjecture in A181082.** Every term of A181082 is an integer. -/
theorem a181082_integral (m : ℕ) : ∃ z : ℤ, a181082 m = z := by
  have h : (fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k) else 0) =
      fun n k => coeff k ((1 + X : ℤ⟦X⟧) ^ n) ^ (n + k) := by
    funext n k
    rcases Nat.eq_zero_or_pos (n + k) with h0 | h0
    · obtain ⟨rfl, rfl⟩ : n = 0 ∧ k = 0 := by omega
      simp
    · exact choose_pow_eq n k _ h0
  rw [a181082, h]
  exact integral_of_polynomial_exponent (1 + X) constantCoeff_one_add_X (fun n k => n + k)
    (MvPolynomial.X 0 + MvPolynomial.X 1) (fun n k _ => by simp) (fun _ _ _ hk => by omega)
    (fun n k hn hk _ => ⟨k, hk, dvd_mul_coeff_pow _ n k, (min_le_left _ _).trans (by omega)⟩) m

/-- **Hanna's conjecture in A181084.** Every term of A181084 is an integer. -/
theorem a181084_integral (m : ℕ) : ∃ z : ℤ, a181084 m = z := by
  have h : (fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k + 1) else 0) =
      fun n k => coeff k ((1 + X : ℤ⟦X⟧) ^ n) ^ (n + k + 1) := by
    funext n k
    exact choose_pow_eq n k _ (Nat.succ_pos _)
  rw [a181084, h]
  exact integral_of_polynomial_exponent (1 + X) constantCoeff_one_add_X (fun n k => n + k + 1)
    (MvPolynomial.X 0 + MvPolynomial.X 1 + 1) (fun n k _ => by simp) (fun _ _ _ _ => by omega)
    (fun n k hn hk _ => ⟨k, hk, dvd_mul_coeff_pow _ n k, (min_le_left _ _).trans (by omega)⟩) m

/-! ## Computing coefficients -/

theorem coeff_hannaLog (f : ℕ → ℕ → ℤ) (m : ℕ) :
    coeff m (hannaLog f) = ∑ n ∈ Icc 1 m, (f n (m - n) : ℚ) / n := by
  rw [hannaLog, coeff_mk]

theorem constantCoeff_hannaLog (f : ℕ → ℕ → ℤ) : constantCoeff (hannaLog f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_hannaLog]
  simp

/-- The recurrence $(n+1)\,a(n+1) = \sum_{i=0}^{n} (i+1)\,\ell(i+1)\,a(n-i)$ for the
coefficients $a$ of $\exp L$ and $\ell$ of $L$. -/
theorem coeff_exp_subst_succ {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) (n : ℕ) :
    coeff (n + 1) (subst L (exp ℚ)) * (n + 1) =
      ∑ i ∈ range (n + 1), coeff (i + 1) L * (i + 1) * coeff (n - i) (subst L (exp ℚ)) := by
  have h := congrArg (coeff n) (derivative_exp_subst hL)
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (d⁄dX L) * coeff j (subst L (exp ℚ)))] at h
  simpa only [coeff_derivative] using h

/-- The coefficients $a(1), \dots, a(6)$ of $\exp L$ in terms of those of $L$. -/
theorem coeff_exp_subst_six {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) :
    coeff 1 (subst L (exp ℚ)) = coeff 1 L ∧
    coeff 2 (subst L (exp ℚ)) * 2 = coeff 1 L * coeff 1 (subst L (exp ℚ)) + coeff 2 L * 2 ∧
    coeff 3 (subst L (exp ℚ)) * 3 = coeff 1 L * coeff 2 (subst L (exp ℚ)) +
      coeff 2 L * 2 * coeff 1 (subst L (exp ℚ)) + coeff 3 L * 3 ∧
    coeff 4 (subst L (exp ℚ)) * 4 = coeff 1 L * coeff 3 (subst L (exp ℚ)) +
      coeff 2 L * 2 * coeff 2 (subst L (exp ℚ)) + coeff 3 L * 3 * coeff 1 (subst L (exp ℚ)) +
      coeff 4 L * 4 ∧
    coeff 5 (subst L (exp ℚ)) * 5 = coeff 1 L * coeff 4 (subst L (exp ℚ)) +
      coeff 2 L * 2 * coeff 3 (subst L (exp ℚ)) + coeff 3 L * 3 * coeff 2 (subst L (exp ℚ)) +
      coeff 4 L * 4 * coeff 1 (subst L (exp ℚ)) + coeff 5 L * 5 ∧
    coeff 6 (subst L (exp ℚ)) * 6 = coeff 1 L * coeff 5 (subst L (exp ℚ)) +
      coeff 2 L * 2 * coeff 4 (subst L (exp ℚ)) + coeff 3 L * 3 * coeff 3 (subst L (exp ℚ)) +
      coeff 4 L * 4 * coeff 2 (subst L (exp ℚ)) + coeff 5 L * 5 * coeff 1 (subst L (exp ℚ)) +
      coeff 6 L * 6 := by
  have h0 : coeff 0 (subst L (exp ℚ)) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_exp_subst hL]
  have r := coeff_exp_subst_succ hL
  have r0 := r 0
  have r1 := r 1
  have r2 := r 2
  have r3 := r 3
  have r4 := r 4
  have r5 := r 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0] at r0 r1 r2 r3 r4 r5
  norm_num at r0 r1 r2 r3 r4 r5
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-! ## Hanna's non-integrality notes -/

/-- If the coefficient of $x^6$ is $c/2$ with $c$ odd, the series is not integral. -/
theorem not_integral_of_coeff_eq_half {F : ℚ⟦X⟧} {c : ℤ} (hc : c % 2 = 1)
    (h : coeff 6 F = c / 2) : ¬∀ m, ∃ z : ℤ, coeff m F = z := by
  intro hF
  obtain ⟨z, hz⟩ := hF 6
  rw [h] at hz
  have : (c : ℚ) = z * 2 := by
    rw [← hz]
    ring
  have : c = z * 2 := by exact_mod_cast this
  omega

/-- **Hanna's note in A183128.** The series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2} x^k] x^n/n\bigr)$ does not have
integer coefficients. -/
theorem a183128_note :
    ¬∀ m, ∃ z : ℤ, coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2)) = z := by
  refine not_integral_of_coeff_eq_half (c := 153254825495) (by norm_num) ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := coeff_exp_subst_six (constantCoeff_hannaLog
    fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2))
  simp only [coeff_hannaLog] at h1 h2 h3 h4 h5 h6
  simp [Finset.sum_Icc_succ_top, Nat.choose] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  rw [hannaExp]
  push_cast
  linarith

/-- **Hanna's note in A183129.** The series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+k-1} x^k] x^n/n\bigr)$ does not
have integer coefficients. -/
theorem a183129_note :
    ¬∀ m, ∃ z : ℤ,
      coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k - 1)) = z := by
  refine not_integral_of_coeff_eq_half (c := 19140157244799) (by norm_num) ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := coeff_exp_subst_six (constantCoeff_hannaLog
    fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k - 1))
  simp only [coeff_hannaLog] at h1 h2 h3 h4 h5 h6
  simp [Finset.sum_Icc_succ_top, Nat.choose] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  rw [hannaExp]
  push_cast
  linarith

/-- **Hanna's note in A181070.** The series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k=0}^{n} \binom{n}{k}^{k} x^k] x^n/n\bigr)$ does not have
integer coefficients. -/
theorem a181070_note :
    ¬∀ m, ∃ z : ℤ,
      coeff m (hannaExp fun n k => if k ≤ n then (n.choose k : ℤ) ^ k else 0) = z := by
  refine not_integral_of_coeff_eq_half (c := 45) (by norm_num) ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := coeff_exp_subst_six (constantCoeff_hannaLog
    fun n k => if k ≤ n then (n.choose k : ℤ) ^ k else 0)
  simp only [coeff_hannaLog] at h1 h2 h3 h4 h5 h6
  simp [Finset.sum_Icc_succ_top, Nat.choose] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  rw [hannaExp]
  push_cast
  linarith

/-! ## Sanity checks: the first terms of the six sequences -/

theorem a183128_first_terms :
    a183128 0 = 1 ∧ a183128 1 = 1 ∧ a183128 2 = 2 ∧ a183128 3 = 5 ∧ a183128 4 = 131 ∧
      a183128 5 = 527019 ∧ a183128 6 = 384803612051 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := coeff_exp_subst_six (constantCoeff_hannaLog
    fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + 1))
  simp only [coeff_hannaLog] at h1 h2 h3 h4 h5 h6
  simp [Finset.sum_Icc_succ_top, Nat.choose] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  simp only [a183128, hannaExp, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_exp_subst (constantCoeff_hannaLog _)]
  exact ⟨trivial, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem a183129_first_terms :
    a183129 0 = 1 ∧ a183129 1 = 1 ∧ a183129 2 = 2 ∧ a183129 3 = 5 ∧ a183129 4 = 374 ∧
      a183129 5 = 8404542 ∧ a183129 6 = 48017057808567 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := coeff_exp_subst_six (constantCoeff_hannaLog
    fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k))
  simp only [coeff_hannaLog] at h1 h2 h3 h4 h5 h6
  simp [Finset.sum_Icc_succ_top, Nat.choose] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  simp only [a183129, hannaExp, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_exp_subst (constantCoeff_hannaLog _)]
  exact ⟨trivial, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem a181076_first_terms :
    a181076 0 = 1 ∧ a181076 1 = 1 ∧ a181076 2 = 2 ∧ a181076 3 = 5 ∧ a181076 4 = 20 ∧
      a181076 5 = 168 ∧ a181076 6 = 3659 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := coeff_exp_subst_six (constantCoeff_hannaLog
    fun n k => ((n + k - 1).choose k : ℤ) ^ n)
  simp only [coeff_hannaLog] at h1 h2 h3 h4 h5 h6
  simp [Finset.sum_Icc_succ_top, Nat.choose] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  simp only [a181076, hannaExp, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_exp_subst (constantCoeff_hannaLog _)]
  exact ⟨trivial, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem a181078_first_terms :
    a181078 0 = 1 ∧ a181078 1 = 1 ∧ a181078 2 = 2 ∧ a181078 3 = 5 ∧ a181078 4 = 29 ∧
      a181078 5 = 657 ∧ a181078 6 = 61207 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := coeff_exp_subst_six (constantCoeff_hannaLog
    fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1))
  simp only [coeff_hannaLog] at h1 h2 h3 h4 h5 h6
  simp [Finset.sum_Icc_succ_top, Nat.choose] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  simp only [a181078, hannaExp, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_exp_subst (constantCoeff_hannaLog _)]
  exact ⟨trivial, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem a181082_first_terms :
    a181082 0 = 1 ∧ a181082 1 = 1 ∧ a181082 2 = 2 ∧ a181082 3 = 6 ∧ a181082 4 = 34 ∧
      a181082 5 = 375 ∧ a181082 6 = 15200 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := coeff_exp_subst_six (constantCoeff_hannaLog
    fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k) else 0)
  simp only [coeff_hannaLog] at h1 h2 h3 h4 h5 h6
  simp [Finset.sum_Icc_succ_top, Nat.choose] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  simp only [a181082, hannaExp, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_exp_subst (constantCoeff_hannaLog _)]
  exact ⟨trivial, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem a181084_first_terms :
    a181084 0 = 1 ∧ a181084 1 = 1 ∧ a181084 2 = 2 ∧ a181084 3 = 10 ∧ a181084 4 = 92 ∧
      a181084 5 = 1367 ∧ a181084 6 = 87090 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := coeff_exp_subst_six (constantCoeff_hannaLog
    fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k + 1) else 0)
  simp only [coeff_hannaLog] at h1 h2 h3 h4 h5 h6
  simp [Finset.sum_Icc_succ_top, Nat.choose] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  simp only [a181084, hannaExp, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_exp_subst (constantCoeff_hannaLog _)]
  exact ⟨trivial, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end OeisA181076

end
