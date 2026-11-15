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
# Bala's $p^{3k}$ supercongruences for $[x^{rn}]\, f(x)^{sn}$, $f = (1-x^m)^m/((1-x^a)^a(1-x^b)^b)$

Let $a, b \ge 1$, $m = a + b$, $f = (1-x^m)^m/((1-x^a)^a(1-x^b)^b)$ and
$u(N) = u_{r,s}(N) = [x^{rN}]\, f(x)^{sN}$ for $r \ge 1$ and $s \in \mathbb{Z}$. This file proves
`OeisA372211.u_tower`: for every prime $p \ge 5$ with $p \nmid abm$ and all $n, k \ge 1$,
$$u(np^k) \equiv u(np^{k-1}) \pmod{p^{3k}}.$$
It proves the same for Bala's variant $f^- = (1-x^m)^m/((1+x^a)^a(1+x^b)^b)$ (`um_tower`). The
corollaries are Bala's conjectures on A372211 for $p \ge 7$, on A372212 and A372213, and on
A351859, each for $a(n) = [x^n]\, f(x)^n$ and for $u_{r,s}$, and Bala's general clauses on
A372211 for $f$ and $f^-$ in the form "for all primes $p$ beyond a bound depending on $m$"
(`general_tower`, `general_variant_tower`, with the bound $m + 5$).

Write $\theta = x\, d/dx$ (`theta`). Steps 2–4 are a criterion for any unit $F$ of `ℤ⟦X⟧` with
constant term $1$ (`CubicHyp`, `uF_tower`): if $\theta F/F = \Lambda$ has $p$-integral
coefficients with $[x^{pn}]\Lambda = [x^n]\Lambda$, and the reduced logarithm
$V = \sum_{p \nmid n} [x^n]\Lambda\, x^n/n$ satisfies $|[x^{pj}] V^2|_p \le |pj|_p$, then
$u_F(r,s;N) = [x^{rN}]\, F^{sN}$ has the $p^{3k}$ towers for $p \ge 5$. It suffices to show
$|u_F(pM) - u_F(M)|_p \le |pM|_p^3$ for every $M$ (`main_estimate`) and to take $M = np^{k-1}$.

1. **Logarithmic derivative** (`hasLD_fU`). Over $\mathbb{Q}$,
   $\theta f / f = \Lambda = \sum_{n \ge 1} c(n) x^n$ with
   $c(n) = a^2 [a \mid n] + b^2 [b \mid n] - m^2 [m \mid n]$ (`cf`), because
   $\theta(1 - x^e) = L_e\,(1 - x^e)$ with $L_e = -e \sum_{k \ge 1} x^{ek}$.
   Since $p \nmid abm$, $c(pn) = c(n)$ (`cf_mul`).
2. **Exponential expansion** (`expansion`). Let $G = F^s$ and $Z = sV$ (`ZF`), so
   $\theta Z = s\Lambda - s\Lambda(x^p)$. The unit $E = G^{pM}/G(x^p)^M$ satisfies
   $\theta E = pM\, \theta Z \cdot E$, so a uniqueness argument for $\theta D = KD + R$ gives
   $E \equiv \sum_{t \le T} (pM)^t Z^t / t!$ modulo $x^{T+1}$. The extraction
   $[x^{pN}]\, A(x^p) B = \sum_{i+j=N} [x^i]A\, [x^{pj}]B$ then gives
   $u_F(pM) = \sum_t \frac{(pM)^t}{t!} S_t$ with $S_t = \sum_{i+j=rM} [x^i]G^M\, [x^{pj}] Z^t$.
   Here $S_0 = u_F(M)$, and $S_1 = 0$ because $Z$ has no monomial $x^{pj}$.
3. **Terms $t \ge 3$** (`norm_pow_div_factorial_three`). Legendre's formula gives
   $v_p((t+3)!) \le t$ for $p \ge 5$, so $|(pM)^{t+3}/(t+3)!|_p \le |pM|_p^3$, and $|S_t|_p \le 1$.
4. **Term $t = 2$** (`norm_Sx_two`). From $\theta G^M = M s\Lambda G^M$,
   $|i\,[x^i]G^M|_p \le |M|_p$. With the quadratic estimate, $|[x^{pj}] Z^2|_p \le |p|_p |j|_p$,
   and each term of $S_2$ is at most $|p|_p |M|_p$: use $|j|_p \le |M|_p$, or else
   $|i|_p = |j|_p$ for $i = rM - j$. So $|(pM)^2 S_2 / 2|_p \le |pM|_p^3$.
5. **Theorem 2** (`norm_coeff_Mred_sq`): $|[x^T] M_p^2|_p \le |T|_p$ for $T \ge 1$, where
   $M_p = \sum_{p \nmid n} c(n) x^n/n$ (`Mred`).
   - A common factor $g = \gcd(a, b)$ is removed by $M_{(ga,gb)}(x) = g\, M_{(a,b)}(x^g)$
     (`Vof_gmul`, `norm_coeff_Vof_sq_gmul`), so $a$ and $b$ may be taken coprime.
   - Let $P = p^{v_p(T)}$. The coefficients $c(i)/i$ lie in $\mathbb{Z}_p$ (`μP`); their image
     under `PadicInt.toZModPow` is $c(i)\, i^{-1}$ in `ZMod P`, with `Ring.inverse` giving $0$
     on multiples of $p$. Since the kernel of `toZModPow` is $(p^{v_p(T)})$, it suffices that
     $\sum_{i + i' = T} c(i) i^{-1}\, c(i') i'^{-1} = 0$ in `ZMod P`
     (`norm_coeff_Vof_sq_of_core`, `core_sum`).
   - In `ZMod P`, $i' = T - i \equiv -i$, so the sum is $-\sum_{i < T} c(i)c(T-i)\, i^{-2}$.
     Expanding $c$ gives the nine pair sums
     $Y(e, e') = \sum_{i < T,\ e \mid i,\ e' \mid T - i} i^{-2}$ (`sum_cZ_mul`).
   - Let $\zeta(x) = \sum_{t < x} t^{-2}$ on `ZMod P` (`zeta`). The units of `ZMod P` satisfy
     $\sum u^{-2} = 0$, since $u \mapsto 2u$ permutes them and $3$ is a unit
     (`sum_inverse_sq`). Hence $\zeta(x + 1) = \zeta(x) + x^{-2}$ for every $x$ (`zeta_succ`),
     and so $\zeta(1 - x) = -\zeta(x)$ (`zeta_one_sub`).
   - A sum of $i^{-2}$ over $i < U$ in one class modulo $d$ is
     $d^{-2}[\zeta(E/d) - \zeta(\beta/d)]$, where $\beta$ is the class and $E$ its first element
     $\ge U$ (`sum_class`, `sum_class_nat`).
   - For coprime $e, e'$ and $P \mid T$ this gives the pair formula
     $e^2 e'^2\, Y(e, e') = -[Z_e(T/e') + Z_{e'}(T/e)]$, where $Z_d(z) = \zeta(z/d)$ for
     $z \in \mathbb{Z}/d$ (`pair_sum`, `Zf`, `pt`); the class is found by the Chinese
     remainder theorem. The diagonal sums $Y(e, e)$ vanish (`diag_sum`), and $Z_d$ is odd
     (`Zf_neg`).
   - Since $m \equiv b \pmod a$, $m \equiv a \pmod b$ and $b \equiv -a \pmod m$, the six cross
     terms cancel (`Ycomb_eq_zero`).
6. **Corollaries** (`cubicHyp_f`, `u_tower`). The series of A372211, A372212 and A372213 are
   $f_{2,3}$, $f_{2,5}$ and $f_{3,4}$ by definition, and $G_3 = f_{1,3}$ because
   $(1 + x + x^2 + x^3)(1 - x) = 1 - x^4$ and $(1 + x + x^2)(1 - x) = 1 - x^3$ (`G3_eq`). The
   primes in Bala's ranges do not divide $abm$. As a check of the definitions,
   $f_{1,1} = (1 + x)^2$ and $u_{1,1}(n) = \binom{2n}{n}$ (`u_one_one`), the case A000984 named
   in A372211, and $f^-_{1,1} = (1 - x)^2$ (`fm_one_one`).
7. **Theorem 4: the variant** (`cubicHyp_fm`, `um_tower`). Since
   $1 + x^e = (1 - x^{2e})/(1 - x^e)$ (`onePlusU_eq`), $\theta f^- / f^- = \sum c^-(n) x^n$ with
   $c^-(n) = -a^2[a \mid n] + 2a^2[2a \mid n] - b^2[b \mid n] + 2b^2[2b \mid n] - m^2[m \mid n]$
   (`cm`), and $c^-(pn) = c^-(n)$ for $p \ge 5$. The quadratic estimate for
   $M^-_p = \sum_{p \nmid n} c^-(n) x^n/n$ is `norm_coeff_Mm_sq`:
   - the common factor $g$ is removed as in step 5 (`cm_gmul`);
   - for $a, b$ both odd, $c^-(n) = (-1)^n c(n)$ (`cm_odd`), so
     $[x^T](M^-_p)^2 = (-1)^T [x^T] M_p^2$ and Theorem 2 applies;
   - for $a$ odd and $b = 2\beta$ even (the other case by the symmetry `cm_comm`), the
     25 pair sums over the support $\{a, 2a, b, 2b, m\}$ are evaluated (`sum_cmZ_mul`,
     `core_var`). Pairs with common factor $2$ reduce to $T/2$ (`Ysum_gmul`, `pair_two`), and
     the pairs $(e, 2e)$ vanish because $Z_2 = 0$ (`Zf_two`). For $T$ even the terms cancel
     after halving the denominators (`Zf_scale`, `pt_half`). For $T$ odd they cancel by the
     distribution relation $\zeta(x/2) + \zeta((x+1)/2) = 4\zeta(x)$ (`zeta_half`), applied to
     the two halves of $T/b \bmod a$ and of $T/a \bmod b$ (`zeta_halves`, `halves_a`,
     `halves_b`).

The sign of $s$ is never used, so negative $s$ needs no separate case. The decomposition of
$f^p / f(x^p)$ as $\exp(pM_p)$ is the Dwork–Cartier method; the reduction to the quadratic
estimate follows rbajaj5's informal proof for $(a, b) = (1, 2)$ (OEIS A351858). Theorem 2 for
general $(a, b)$, through the odd function $\zeta$ and the cancellation, and Theorem 4 are due
to Wentao Li. The Lean proof was written for this package; the framework (`theta`, `HasLD`,
`Vof`, `expTrunc`, `PI` and the exponential expansion) is adapted from the package
`OeisA333472`, and `sum_inverse_sq` from `MosN8`.

*References:*
- Peter Bala, [A372211](https://oeis.org/A372211), [A372212](https://oeis.org/A372212) and
  [A372213](https://oeis.org/A372213), April 22, 2024.
- Peter Bala, [A351859](https://oeis.org/A351859), March 1, 2022.
-/

@[expose] public section

namespace OeisA372211

open PowerSeries

/-- The integer power $F^k$ of a power series $F$ with constant term $1$, for $k \in \mathbb{Z}$.
For $k < 0$ it is $(F^{-1})^{-k}$, where $F^{-1}$ = `invOfUnit F 1`. -/
noncomputable def zpowSeries (F : PowerSeries ℤ) (k : ℤ) : PowerSeries ℤ :=
  if 0 ≤ k then F ^ k.toNat else invOfUnit F 1 ^ k.natAbs

/-- $f_{a,b}(x) = (1 - x^m)^m / ((1 - x^a)^a\,(1 - x^b)^b)$ with $m = a + b$. For $a, b \ge 1$,
`invOfUnit (1 - X ^ e) 1` is the inverse of $1 - x^e$. -/
noncomputable def f (a b : ℕ) : PowerSeries ℤ :=
  (1 - X ^ (a + b)) ^ (a + b) * invOfUnit (1 - X ^ a) 1 ^ a * invOfUnit (1 - X ^ b) 1 ^ b

/-- $u_{r,s}(n) = [x^{rn}]\, f_{a,b}(x)^{sn}$. -/
noncomputable def u (a b r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (zpowSeries (f a b) (s * n))

/-- Bala's variant $f^-_{a,b}(x) = (1 - x^m)^m / ((1 + x^a)^a\,(1 + x^b)^b)$ with $m = a + b$.
For $a, b \ge 1$, `invOfUnit (1 + X ^ e) 1` is the inverse of $1 + x^e$. -/
noncomputable def fm (a b : ℕ) : PowerSeries ℤ :=
  (1 - X ^ (a + b)) ^ (a + b) * invOfUnit (1 + X ^ a) 1 ^ a * invOfUnit (1 + X ^ b) 1 ^ b

/-- $u^-_{r,s}(n) = [x^{rn}]\, f^-_{a,b}(x)^{sn}$. -/
noncomputable def um (a b r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries (fm a b) (s * n))

/-- The series of A372211: $f(x) = (1 - x^5)^5 / ((1 - x^2)^2\,(1 - x^3)^3)$. -/
noncomputable def f372211 : PowerSeries ℤ :=
  (1 - X ^ 5) ^ 5 * invOfUnit (1 - X ^ 2) 1 ^ 2 * invOfUnit (1 - X ^ 3) 1 ^ 3

/-- OEIS A372211: $a(n) = [x^n]\, f(x)^n$. -/
noncomputable def A372211 (n : ℕ) : ℤ := coeff n (f372211 ^ n)

/-- Bala's $u(r,s;n) = [x^{rn}]\, f(x)^{sn}$ for A372211. -/
noncomputable def u372211 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f372211 (s * n))

/-- The series of A372212: $f(x) = (1 - x^7)^7 / ((1 - x^2)^2\,(1 - x^5)^5)$. -/
noncomputable def f372212 : PowerSeries ℤ :=
  (1 - X ^ 7) ^ 7 * invOfUnit (1 - X ^ 2) 1 ^ 2 * invOfUnit (1 - X ^ 5) 1 ^ 5

/-- OEIS A372212: $a(n) = [x^n]\, f(x)^n$. -/
noncomputable def A372212 (n : ℕ) : ℤ := coeff n (f372212 ^ n)

/-- Bala's $u(r,s;n) = [x^{rn}]\, f(x)^{sn}$ for A372212. -/
noncomputable def u372212 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f372212 (s * n))

/-- The series of A372213: $f(x) = (1 - x^7)^7 / ((1 - x^3)^3\,(1 - x^4)^4)$. -/
noncomputable def f372213 : PowerSeries ℤ :=
  (1 - X ^ 7) ^ 7 * invOfUnit (1 - X ^ 3) 1 ^ 3 * invOfUnit (1 - X ^ 4) 1 ^ 4

/-- OEIS A372213: $a(n) = [x^n]\, f(x)^n$. -/
noncomputable def A372213 (n : ℕ) : ℤ := coeff n (f372213 ^ n)

/-- Bala's $u(r,s;n) = [x^{rn}]\, f(x)^{sn}$ for A372213. -/
noncomputable def u372213 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f372213 (s * n))

/-- $G_3(x) = (1 + x + x^2 + x^3)^4 / (1 + x + x^2)^3$. -/
noncomputable def G3 : PowerSeries ℤ :=
  (1 + X + X ^ 2 + X ^ 3) ^ 4 * invOfUnit (1 + X + X ^ 2) 1 ^ 3

/-- OEIS A351859: $a(n) = [x^n]\, (1 + x + x^2 + x^3)^{4n} / (1 + x + x^2)^{3n}$. -/
noncomputable def A351859 (n : ℕ) : ℤ :=
  coeff n ((1 + X + X ^ 2 + X ^ 3) ^ (4 * n) * invOfUnit (1 + X + X ^ 2) 1 ^ (3 * n))

/-- Bala's $a(r,s;n) = [x^{rn}]\, G_3(x)^{sn}$ for A351859. -/
noncomputable def a351859 (r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (zpowSeries G3 (s * n))

end OeisA372211

namespace OeisA372211

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


/-! ## The series `f` over `ℤ` and `ℚ` -/

section

noncomputable section

/-- The coefficient map `ℤ⟦X⟧ → ℚ⟦X⟧`. -/
abbrev ι : ℤ⟦X⟧ →+* ℚ⟦X⟧ := PowerSeries.map (Int.castRingHom ℚ)

/-- The units map of `ι`. -/
def ιU : ℤ⟦X⟧ˣ →* ℚ⟦X⟧ˣ := Units.map ι.toMonoidHom

@[simp] theorem val_ιU (u : ℤ⟦X⟧ˣ) : ((ιU u : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = ι u := rfl

theorem constantCoeff_f (a b : ℕ) : constantCoeff (f a b) = 1 := by
  unfold f
  simp only [map_mul, map_pow, constantCoeff_invOfUnit, map_sub, map_one, constantCoeff_X,
    inv_one, Units.val_one, one_pow, mul_one]
  rcases Nat.eq_zero_or_pos (a + b) with h | h
  · rw [h]; simp
  · rw [zero_pow h.ne']; simp

/-- `f` as a unit of `ℤ⟦X⟧`. -/
def fU (a b : ℕ) : ℤ⟦X⟧ˣ :=
  ⟨f a b, invOfUnit (f a b) 1, mul_invOfUnit _ 1 (by simp [constantCoeff_f]),
    invOfUnit_mul _ 1 (by simp [constantCoeff_f])⟩

theorem zpowSeries_eq (U : ℤ⟦X⟧ˣ) (hinv : invOfUnit (U : ℤ⟦X⟧) 1 = ((U⁻¹ : ℤ⟦X⟧ˣ) : ℤ⟦X⟧))
    (k : ℤ) : zpowSeries (U : ℤ⟦X⟧) k = ((U ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) := by
  unfold zpowSeries
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp
  · have hk : k = -((k.natAbs : ℕ) : ℤ) := by omega
    rw [hk, zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, hinv, ← inv_pow,
      Units.val_pow_eq_pow_val]

theorem zpowSeries_f (a b : ℕ) (k : ℤ) :
    zpowSeries (f a b) k = ((fU a b ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) :=
  zpowSeries_eq (fU a b) rfl k

/-- `1 - X ^ e` as a unit, for `e ≥ 1`. -/
def oneSubU (e : ℕ) (he : 0 < e) : ℤ⟦X⟧ˣ :=
  ⟨1 - X ^ e, invOfUnit (1 - X ^ e) 1, mul_invOfUnit _ 1 (by simp [zero_pow he.ne']),
    invOfUnit_mul _ 1 (by simp [zero_pow he.ne'])⟩

theorem fU_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    fU a b = oneSubU (a + b) (by omega) ^ (a + b) * (oneSubU a ha)⁻¹ ^ a *
      (oneSubU b hb)⁻¹ ^ b := by
  apply Units.ext
  simp [fU, oneSubU, f]

/-- $L_e = \theta(1 - X^e)/(1 - X^e) = -e \sum_{k \ge 1} X^{ek}$. -/
def Le (e : ℕ) : ℚ⟦X⟧ := mk fun n => if n ≠ 0 ∧ e ∣ n then -(e : ℚ) else 0

theorem theta_one_sub_X_pow {e : ℕ} (he : 0 < e) :
    theta (1 - X ^ e : ℚ⟦X⟧) = Le e * (1 - X ^ e) := by
  ext n
  rw [coeff_theta, mul_sub, mul_one, map_sub, map_sub, coeff_one, coeff_X_pow,
    coeff_mul_X_pow', Le, coeff_mk]
  by_cases h0 : n = 0
  · subst h0; simp [show ¬ e ≤ 0 by omega]
  by_cases hne : n = e
  · subst hne
    rw [ite_eq_right h0, ite_eq_left rfl, ite_eq_left ⟨h0, dvd_refl n⟩, ite_eq_left le_rfl,
      Nat.sub_self, coeff_mk, ite_eq_right (fun h => h.1 rfl)]
    ring
  by_cases hlt : n < e
  · have hnd : ¬ e ∣ n := fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) (by omega)
    simp [hnd, show ¬ e ≤ n by omega, hne, h0]
  · have hdv : e ∣ n ↔ e ∣ n - e := by
      conv_lhs => rw [show n = n - e + e by omega]
      exact Nat.dvd_add_self_right
    rw [ite_eq_right h0, ite_eq_right hne, ite_eq_left (show e ≤ n by omega), coeff_mk]
    by_cases hd : e ∣ n
    · rw [ite_eq_left ⟨h0, hd⟩, ite_eq_left ⟨by omega, hdv.1 hd⟩]; ring
    · rw [ite_eq_right (fun h => hd h.2), ite_eq_right (fun h => hd (hdv.2 h.2))]; ring

theorem hasLD_oneSubU {e : ℕ} (he : 0 < e) : HasLD (ιU (oneSubU e he)) (Le e) := by
  unfold HasLD
  rw [val_ιU]
  have : ι ((oneSubU e he : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) = 1 - X ^ e := by simp [oneSubU]
  rw [this]; exact theta_one_sub_X_pow he

/-- The weights $c(n) = a^2 [a \mid n] + b^2 [b \mid n] - m^2 [m \mid n]$ for $n \ge 1$, where
$m = a + b$, and $c(0) = 0$: $\theta f / f = \sum_n c(n) X^n$. -/
def cf (a b n : ℕ) : ℤ :=
  if n = 0 then 0 else
    (if a ∣ n then (a : ℤ) ^ 2 else 0) + (if b ∣ n then (b : ℤ) ^ 2 else 0) -
      (if a + b ∣ n then ((a + b : ℕ) : ℤ) ^ 2 else 0)

/-- $\Lambda = \theta f / f = \sum_n c(n) X^n$ over `ℚ`. -/
def Λq (a b : ℕ) : ℚ⟦X⟧ := mk fun n => (cf a b n : ℚ)

theorem coeff_natCast_mul (k : ℕ) (L : ℚ⟦X⟧) (n : ℕ) :
    coeff n ((k : ℚ⟦X⟧) * L) = k * coeff n L := by
  rw [← map_natCast (C (R := ℚ)), coeff_C_mul]

theorem hasLD_fU {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : HasLD (ιU (fU a b)) (Λq a b) := by
  rw [fU_eq ha hb, map_mul, map_mul, map_pow, map_pow, map_pow, map_inv, map_inv]
  refine ((((hasLD_oneSubU (by omega : 0 < a + b)).pow (a + b)).mul
    (((hasLD_oneSubU ha).inv).pow a)).mul (((hasLD_oneSubU hb).inv).pow b)).congr ?_
  ext n
  simp only [map_add, coeff_natCast_mul, map_neg, Le, coeff_mk, Λq, cf]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [hn.ne', ne_eq, not_false_eq_true, true_and, ite_false]
    split_ifs <;> push_cast <;> ring

/-- The constant-coefficient map on units. -/
def cU : ℚ⟦X⟧ˣ →* ℚˣ := Units.map (constantCoeff (R := ℚ)).toMonoidHom

@[simp] theorem val_cU (u : ℚ⟦X⟧ˣ) : ((cU u : ℚˣ) : ℚ) = constantCoeff (u : ℚ⟦X⟧) := rfl

end

end

/-! ## Periodicity and integrality of $\Lambda$ -/

section

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

theorem hp0 : p ≠ 0 := hp.out.ne_zero

theorem dvd_mul_iff_of_not_dvd {e : ℕ} (he : ¬ p ∣ e) (m : ℕ) : e ∣ p * m ↔ e ∣ m :=
  Nat.Coprime.dvd_mul_left (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 he))

theorem cf_mul {a b : ℕ} (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) (m : ℕ) :
    cf a b (p * m) = cf a b m := by
  unfold cf
  simp only [mul_eq_zero, hp0, false_or, dvd_mul_iff_of_not_dvd hpa,
    dvd_mul_iff_of_not_dvd hpb, dvd_mul_iff_of_not_dvd hpm]

theorem coeff_Λq_mul {a b : ℕ} (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) (m : ℕ) :
    coeff (p * m) (Λq a b) = coeff m (Λq a b) := by
  simp only [Λq, coeff_mk, cf_mul hpa hpb hpm]

theorem PI_Λq (a b : ℕ) : PI p (Λq a b) := fun n => by
  simp only [Λq, coeff_mk]; exact padicNorm.of_int _

/-- The reduced logarithm $M = \sum_{p \nmid n} \frac{c(n)}{n} X^n$. -/
def Mred (p : ℕ) (a b : ℕ) : ℚ⟦X⟧ := Vof p (Λq a b)

theorem PI_Mred (a b : ℕ) : PI p (Mred p a b) := (PI_Λq a b).Vof

end

end


/-! ## The cubic tower criterion

For a unit $F$ of `ℤ⟦X⟧` with constant term $1$ and $\theta F / F = \Lambda$, put
$u_F(r,s;N) = [x^{rN}]\, F^{sN}$. If $\Lambda$ has $p$-integral coefficients with
$[x^{pn}]\Lambda = [x^n]\Lambda$, and the reduced logarithm $V = \sum_{p \nmid n} [x^n]\Lambda\,
x^n/n$ satisfies $|[x^{pj}] V^2|_p \le |pj|_p$, then $u_F(r,s;np^k) \equiv u_F(r,s;np^{k-1})
\pmod{p^{3k}}$ for $p \ge 5$ (`uF_tower`). -/

section

noncomputable section

/-- $u_F(r,s;N) = [x^{rN}]\, F^{sN}$ for a unit $F$ of `ℤ⟦X⟧`. -/
def uF (F : ℤ⟦X⟧ˣ) (r : ℕ) (s : ℤ) (N : ℕ) : ℤ := coeff (r * N) ((F ^ (s * N) : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)

/-- $G = F^s$ over `ℚ`. -/
def GF (F : ℤ⟦X⟧ˣ) (s : ℤ) : ℚ⟦X⟧ˣ := ιU (F ^ s)

theorem uF_eq_coeff_GF (F : ℤ⟦X⟧ˣ) (r : ℕ) (s : ℤ) (N : ℕ) :
    (uF F r s N : ℚ) = coeff (r * N) ((GF F s ^ N : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
  rw [uF, GF, ← map_pow, ← zpow_natCast, ← zpow_mul, val_ιU, coeff_map]
  rfl

theorem cU_GF {F : ℤ⟦X⟧ˣ} (hF : constantCoeff (F : ℤ⟦X⟧) = 1) (s : ℤ) : cU (GF F s) = 1 := by
  have h1 : cU (ιU F) = 1 := Units.ext (by
    rw [val_cU, val_ιU, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, hF]
    simp)
  rw [GF, map_zpow, map_zpow, h1, one_zpow]

/-- The hypotheses of the cubic tower criterion for `F` with `θF/F = Λ`. -/
structure CubicHyp (p : ℕ) (F : ℤ⟦X⟧ˣ) (Λ : ℚ⟦X⟧) : Prop where
  const : constantCoeff (F : ℤ⟦X⟧) = 1
  hasLD : HasLD (ιU F) Λ
  pint : PI p Λ
  per : ∀ m, coeff (p * m) Λ = coeff m Λ
  quad : ∀ j, padicNorm p (coeff (p * j) (Vof p Λ ^ 2)) ≤ padicNorm p p * padicNorm p j

variable {p : ℕ} [hp : Fact p.Prime] {F : ℤ⟦X⟧ˣ} {Λ : ℚ⟦X⟧}

omit hp in
theorem hasLD_GF (H : CubicHyp p F Λ) (s : ℤ) : HasLD (GF F s) (C (s : ℚ) * Λ) := by
  rw [GF, map_zpow]
  exact (H.hasLD.zpow s).congr (by rw [map_intCast])

theorem PI_GF_pow (F : ℤ⟦X⟧ˣ) (s : ℤ) (N : ℕ) : PI p ((GF F s ^ N : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
  rw [GF, ← map_pow, val_ιU]; exact PI.map_int _

/-- $Z = \sum_{p \nmid n} \frac{s\,\lambda_n}{n} X^n = s V$. -/
def ZF (p : ℕ) (Λ : ℚ⟦X⟧) (s : ℤ) : ℚ⟦X⟧ := Vof p (C (s : ℚ) * Λ)

omit hp in
theorem ZF_eq (Λ : ℚ⟦X⟧) (s : ℤ) : ZF p Λ s = C (s : ℚ) * Vof p Λ := by
  rw [ZF, Vof_C_mul]

theorem theta_ZF (H : CubicHyp p F Λ) (s : ℤ) :
    theta (ZF p Λ s) = C (s : ℚ) * Λ - expand p hp0 (C (s : ℚ) * Λ) :=
  theta_Vof p hp0 _ (fun m => by simp only [coeff_C_mul, H.per])

theorem PI_ZF (H : CubicHyp p F Λ) (s : ℤ) : PI p (ZF p Λ s) :=
  (PI.C_mul (padicNorm.of_int s) H.pint).Vof

/-- $E = G^{pM} / G(X^p)^M$. -/
def Eu (p : ℕ) [Fact p.Prime] (F : ℤ⟦X⟧ˣ) (s : ℤ) (M : ℕ) : ℚ⟦X⟧ˣ :=
  GF F s ^ (p * M) * (exU p hp0 (GF F s))⁻¹ ^ M

theorem GF_pow_eq (F : ℤ⟦X⟧ˣ) (s : ℤ) (M : ℕ) :
    GF F s ^ (p * M) = exU p hp0 (GF F s ^ M) * Eu p F s M := by
  rw [Eu, map_pow, inv_pow, mul_left_comm, mul_inv_cancel, mul_one]

theorem hasLD_Eu (H : CubicHyp p F Λ) (s : ℤ) (M : ℕ) :
    HasLD (Eu p F s M) (C ((p : ℚ) * M) * theta (ZF p Λ s)) := by
  refine ((((hasLD_GF H s).pow (p * M)).mul
    (((hasLD_GF H s).expand p hp0).inv.pow M))).congr ?_
  rw [theta_ZF H, map_mul (C (R := ℚ)), map_natCast (C (R := ℚ)), map_natCast (C (R := ℚ)),
    Nat.cast_mul]
  ring

theorem constantCoeff_Eu (H : CubicHyp p F Λ) (s : ℤ) (M : ℕ) :
    constantCoeff ((Eu p F s M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 := by
  have h1 : cU (exU p hp0 (GF F s)) = 1 := by
    apply Units.ext
    rw [val_cU, val_exU, constantCoeff_expand, ← val_cU, cU_GF H.const]
  have : cU (Eu p F s M) = 1 := by
    rw [Eu, map_mul, map_pow, map_pow, map_inv, cU_GF H.const, h1]; simp
  rw [← val_cU, this]; rfl

/-- $S_t = \sum_{i + j = rM} [X^i]G^M \, [X^{pj}] Z^t$. -/
def Sx (p : ℕ) (F : ℤ⟦X⟧ˣ) (Λ : ℚ⟦X⟧) (r : ℕ) (s : ℤ) (M t : ℕ) : ℚ :=
  ∑ x ∈ antidiagonal (r * M),
    coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * coeff (p * x.2) (ZF p Λ s ^ t)

/-- **The exponential expansion.** $u_F(pM) = \sum_{t \le prM} \frac{(pM)^t}{t!} S_t$. -/
theorem expansion (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (M : ℕ) :
    (uF F r s (p * M) : ℚ) = ∑ t ∈ range (p * (r * M) + 1),
      ((p : ℚ) * M) ^ t / t.factorial * Sx p F Λ r s M t := by
  rw [uF_eq_coeff_GF, GF_pow_eq, Units.val_mul, val_exU, show r * (p * M) = p * (r * M) by ring]
  have hdvd := X_pow_dvd_sub_expTrunc (p * (r * M)) (X_dvd_Vof p (C (s : ℚ) * Λ))
    (hasLD_Eu H s M) (constantCoeff_Eu H s M)
  rw [coeff_mul_eq_of_X_pow_dvd _ hdvd, expTrunc, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show expand p hp0 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * (C (((p : ℚ) * M) ^ t / t.factorial) *
      Vof p (C (s : ℚ) * Λ) ^ t) = C (((p : ℚ) * M) ^ t / t.factorial) *
      (expand p hp0 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) * ZF p Λ s ^ t) by rw [ZF]; ring,
    coeff_C_mul, coeff_p_mul_expand_mul]
  rfl

/-- The term $t = 0$ is $u_F(M)$. -/
theorem Sx_zero (F : ℤ⟦X⟧ˣ) (Λ : ℚ⟦X⟧) (r : ℕ) (s : ℤ) (M : ℕ) :
    Sx p F Λ r s M 0 = uF F r s M := by
  rw [uF_eq_coeff_GF, Sx, ← mul_one ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧), coeff_mul, mul_one]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pow_zero, coeff_one, coeff_one]
  simp [hp0]

omit hp in
/-- The term $t = 1$ vanishes: $Z$ has no monomial $X^{pj}$. -/
theorem Sx_one (F : ℤ⟦X⟧ˣ) (Λ : ℚ⟦X⟧) (r : ℕ) (s : ℤ) (M : ℕ) : Sx p F Λ r s M 1 = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [pow_one, ZF, coeff_p_mul_Vof, mul_zero]

/-- The Gauss-type bound $|g_i|_p\,|i|_p \le |M|_p$ for the coefficients of $G^M$. -/
theorem norm_coeff_GF_pow (H : CubicHyp p F Λ) (s : ℤ) (M i : ℕ) :
    padicNorm p (coeff i ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) * padicNorm p i ≤ padicNorm p M := by
  have h := congrArg (coeff i) ((hasLD_GF H s).pow M)
  rw [coeff_theta, mul_assoc, ← map_natCast (C (R := ℚ)), coeff_C_mul] at h
  have h2 := congrArg (padicNorm p) h
  rw [padicNorm.mul, padicNorm.mul] at h2
  have h3 : padicNorm p (coeff i (C (s : ℚ) * Λ * ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧))) ≤ 1 :=
    ((PI.C_mul (padicNorm.of_int s) H.pint).mul (PI_GF_pow F s M)) i
  rw [mul_comm, h2]
  calc padicNorm p M * padicNorm p (coeff i (C (s : ℚ) * Λ * ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)))
      ≤ padicNorm p M * 1 := mul_le_mul_of_nonneg_left h3 (padicNorm.nonneg _)
    _ = _ := mul_one _

/-- The bound $|[X^{pj}] Z^2|_p \le |p|_p\,|j|_p$, from the quadratic estimate. -/
theorem norm_coeff_ZF_sq (H : CubicHyp p F Λ) (s : ℤ) (j : ℕ) :
    padicNorm p (coeff (p * j) (ZF p Λ s ^ 2)) ≤ padicNorm p p * padicNorm p j := by
  rw [ZF_eq, mul_pow, ← map_pow, coeff_C_mul, padicNorm.mul]
  calc padicNorm p ((s : ℚ) ^ 2) * padicNorm p (coeff (p * j) (Vof p Λ ^ 2))
      ≤ 1 * (padicNorm p p * padicNorm p j) :=
        mul_le_mul (by rw [padicNorm_pow]; exact pow_le_one₀ (padicNorm.nonneg _) (padicNorm.of_int s))
          (H.quad j) (padicNorm.nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The term $t = 2$: $|S_2|_p \le |p|_p\,|M|_p$. -/
theorem norm_Sx_two (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (M : ℕ) :
    padicNorm p (Sx p F Λ r s M 2) ≤ padicNorm p p * padicNorm p M := by
  refine padicNorm.sum_le' (fun x hx => ?_) (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _))
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [padicNorm.mul]
  have hc := norm_coeff_ZF_sq H s x.2
  have hg := norm_coeff_GF_pow H s M x.1
  have hg1 : padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) ≤ 1 := PI_GF_pow F s M x.1
  have hpp := padicNorm.nonneg (p := p) (p : ℚ)
  by_cases hj : padicNorm p (x.2 : ℚ) ≤ padicNorm p M
  · calc padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) *
          padicNorm p (coeff (p * x.2) (ZF p Λ s ^ 2))
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
    calc padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) *
          padicNorm p (coeff (p * x.2) (ZF p Λ s ^ 2))
        ≤ padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) *
            (padicNorm p p * padicNorm p x.2) :=
          mul_le_mul_of_nonneg_left hc (padicNorm.nonneg _)
      _ = padicNorm p p *
            (padicNorm p (coeff x.1 ((GF F s ^ M : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) * padicNorm p x.1) := by
          rw [hi]; ring
      _ ≤ padicNorm p p * padicNorm p M := mul_le_mul_of_nonneg_left hg hpp

/-- The terms $t \ge 3$: $|S_t|_p \le 1$. -/
theorem norm_Sx_le_one (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (M t : ℕ) :
    padicNorm p (Sx p F Λ r s M t) ≤ 1 := by
  refine padicNorm.sum_le' (fun x _ => ?_) zero_le_one
  rw [padicNorm.mul]
  exact mul_le_one_of_le (PI_GF_pow F s M x.1) (padicNorm.nonneg _) (((PI_ZF H s).pow t) _)

/-- For $p \ge 5$: $v_p((t+3)!) \le t$. -/
theorem padicValNat_factorial_add_three_le (h5 : 5 ≤ p) (t : ℕ) :
    padicValNat p (t + 3).factorial ≤ t := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := t + 3) (by omega)
  have h4 : 4 * padicValNat p (t + 3).factorial ≤ (p - 1) * padicValNat p (t + 3).factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- $|c^{t+3} / (t+3)!|_p \le |c|_p^3$ when $|c|_p \le |p|_p$. -/
theorem norm_pow_div_factorial_three (h5 : 5 ≤ p) {c : ℚ} (hc : padicNorm p c ≤ padicNorm p p)
    (t : ℕ) : padicNorm p (c ^ (t + 3) / (t + 3).factorial) ≤ padicNorm p c ^ 3 := by
  have hf : padicNorm p (p : ℚ) ^ t ≤ padicNorm p ((t + 3).factorial : ℚ) := by
    rw [padicNorm_nat_eq _ (Nat.factorial_ne_zero _)]
    exact pow_le_pow_of_le_one (padicNorm.nonneg _) padicNorm_p_le_one
      (padicValNat_factorial_add_three_le h5 t)
  have hfpos : 0 < padicNorm p ((t + 3).factorial : ℚ) := by
    have : ((t + 3).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero this).symm
  rw [padicNorm.div, padicNorm_pow, div_le_iff₀ hfpos, pow_add]
  have h1 : padicNorm p c ^ t ≤ padicNorm p p ^ t :=
    pow_le_pow_left₀ (padicNorm.nonneg _) hc t
  calc padicNorm p c ^ t * padicNorm p c ^ 3 ≤ padicNorm p p ^ t * padicNorm p c ^ 3 :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg (padicNorm.nonneg _) 3)
    _ ≤ padicNorm p ((t + 3).factorial : ℚ) * padicNorm p c ^ 3 :=
        mul_le_mul_of_nonneg_right hf (pow_nonneg (padicNorm.nonneg _) 3)
    _ = _ := by ring

theorem padicNorm_two (h5 : 5 ≤ p) : padicNorm p (2 : ℚ) = 1 := by
  have := (padicNorm.nat_eq_one_iff (p := p) 2).2 (fun h => by
    have := Nat.le_of_dvd (by norm_num) h; omega)
  simpa using this

/-- **The main estimate.** $|u_F(pM) - u_F(M)|_p \le |pM|_p^3$. -/
theorem main_estimate (h5 : 5 ≤ p) (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (M : ℕ) :
    padicNorm p (((uF F r s (p * M) - uF F r s M : ℤ)) : ℚ) ≤ padicNorm p ((p : ℚ) * M) ^ 3 := by
  push_cast
  rw [expansion H r s M, Finset.sum_range_succ', Sx_zero]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, add_sub_cancel_right]
  have hc : padicNorm p ((p : ℚ) * M) ≤ padicNorm p p := by
    rw [padicNorm.mul]
    calc padicNorm p (p : ℚ) * padicNorm p (M : ℚ) ≤ padicNorm p p * 1 :=
          mul_le_mul_of_nonneg_left (padicNorm.of_nat M) (padicNorm.nonneg _)
      _ = _ := mul_one _
  refine padicNorm.sum_le' (fun t _ => ?_) (pow_nonneg (padicNorm.nonneg _) 3)
  rcases t with _ | _ | t
  · rw [zero_add, Sx_one, mul_zero, padicNorm.zero]; exact pow_nonneg (padicNorm.nonneg _) 3
  · rw [show 0 + 1 + 1 = 2 by rfl, Nat.factorial_two, Nat.cast_ofNat, padicNorm.mul, padicNorm.div,
      padicNorm_two h5, div_one, padicNorm_pow]
    have h2 := norm_Sx_two H r s M
    rw [← padicNorm.mul] at h2
    calc padicNorm p ((p : ℚ) * M) ^ 2 * padicNorm p (Sx p F Λ r s M 2)
        ≤ padicNorm p ((p : ℚ) * M) ^ 2 * padicNorm p ((p : ℚ) * M) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg (padicNorm.nonneg _) 2)
      _ = _ := by ring
  · rw [padicNorm.mul, show t + 1 + 1 + 1 = t + 3 by ring]
    calc padicNorm p (((p : ℚ) * M) ^ (t + 3) / ((t + 3).factorial : ℚ)) *
          padicNorm p (Sx p F Λ r s M (t + 3))
        ≤ padicNorm p ((p : ℚ) * M) ^ 3 * 1 :=
          mul_le_mul (norm_pow_div_factorial_three h5 hc t) (norm_Sx_le_one H r s M _)
            (padicNorm.nonneg _) (pow_nonneg (padicNorm.nonneg _) 3)
      _ = _ := mul_one _

/-- **The cubic tower criterion.** Under `CubicHyp p F Λ` and $p \ge 5$:
$u_F(r,s;np^k) \equiv u_F(r,s;np^{k-1}) \pmod{p^{3k}}$ for all $r, n \ge 0$, $s \in \mathbb{Z}$
and $k \ge 1$. -/
theorem uF_tower (h5 : 5 ≤ p) (H : CubicHyp p F Λ) (r : ℕ) (s : ℤ) (n k : ℕ) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ uF F r s (n * p ^ k) - uF F r s (n * p ^ (k - 1)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set M := n * p ^ k'
  have hNk : n * p ^ (k' + 1) = p * M := by simp only [M]; ring
  rw [hNk, show k' + 1 - 1 = k' by omega]
  have h := main_estimate h5 H r s M
  have hM' : padicNorm p (M : ℚ) ≤ padicNorm p p ^ k' := by
    simp only [M]; push_cast
    rw [padicNorm.mul, padicNorm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (padicNorm.nonneg _) _) (padicNorm.of_nat n)
  have hle : padicNorm p ((uF F r s (p * M) - uF F r s M : ℤ) : ℚ) ≤
      (p : ℚ) ^ (-((3 * (k' + 1) : ℕ) : ℤ)) := by
    calc _ ≤ padicNorm p ((p : ℚ) * M) ^ 3 := h
      _ = (padicNorm p p * padicNorm p M) ^ 3 := by rw [padicNorm.mul]
      _ ≤ (padicNorm p p * padicNorm p p ^ k') ^ 3 := by
          have h0 : 0 ≤ padicNorm p (p : ℚ) * padicNorm p (M : ℚ) :=
            mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)
          exact pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left hM' (padicNorm.nonneg _)) 3
      _ = padicNorm p p ^ (3 * (k' + 1)) := by rw [← pow_succ', ← pow_mul]; ring_nf
      _ = (p : ℚ) ^ (-((3 * (k' + 1) : ℕ) : ℤ)) := by
          rw [padicNorm.padicNorm_p_of_prime, zpow_neg, zpow_natCast, inv_pow]
  have := (padicNorm.dvd_iff_norm_le (p := p) (n := 3 * (k' + 1))).mpr hle
  exact_mod_cast this

end

end

/-! ## The quadratic sums in `ZMod P` (Theorems 2 and 4) -/


section Core

variable {P : ℕ} [NeZero P]

/-- `ζ(x) = ∑_{t < x.val} t⁻²`, with `Ring.inverse` so that non-units contribute `0`. -/
noncomputable def zeta (x : ZMod P) : ZMod P :=
  ∑ t ∈ range x.val, Ring.inverse (t : ZMod P) ^ 2

theorem sum_range_natCast {M : Type*} [AddCommMonoid M] (H : ZMod P → M) :
    ∑ x ∈ range P, H (x : ZMod P) = ∑ z : ZMod P, H z := by
  refine Finset.sum_nbij' (fun x => (x : ZMod P)) (fun z => z.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact mem_univ _
  · intro a _; exact mem_range.2 (ZMod.val_lt a)
  · intro a ha; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 ha)]
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro a _; rfl

theorem inverse_neg_sq {M : Type*} [CommRing M] (x : M) :
    Ring.inverse (-x) ^ 2 = Ring.inverse x ^ 2 := by
  rw [Ring.inverse_pow, Ring.inverse_pow, neg_sq]

theorem sum_inverse_sq (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P)) :
    ∑ z : ZMod P, Ring.inverse z ^ 2 = 0 := by
  obtain ⟨t, ht⟩ := h2
  have key : ∀ z : ZMod P, Ring.inverse ((t : ZMod P) * z) ^ 2 =
      Ring.inverse (2 : ZMod P) ^ 2 * Ring.inverse z ^ 2 := by
    intro z; rw [ht, Ring.mul_inverse_rev]; ring
  have h4 : ∑ z : ZMod P, Ring.inverse z ^ 2 =
      Ring.inverse (2 : ZMod P) ^ 2 * ∑ z : ZMod P, Ring.inverse z ^ 2 := by
    calc ∑ z : ZMod P, Ring.inverse z ^ 2
        = ∑ z : ZMod P, Ring.inverse ((t : ZMod P) * z) ^ 2 :=
          (Equiv.sum_comp (Units.mulLeft t) (fun z => Ring.inverse z ^ 2)).symm
      _ = _ := by rw [mul_sum]; exact sum_congr rfl (fun z _ => key z)
  have h22 : (2 : ZMod P) * Ring.inverse 2 = 1 := Ring.mul_inverse_cancel _ (ht ▸ t.isUnit)
  have h3S : (3 : ZMod P) * ∑ z : ZMod P, Ring.inverse z ^ 2 = 0 := by
    linear_combination 4 * h4 +
      (∑ z : ZMod P, Ring.inverse z ^ 2) * (2 * Ring.inverse (2 : ZMod P) + 1) * h22
  exact h3.mul_right_eq_zero.1 h3S

variable (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P))
include h2 h3

theorem zeta_succ (x : ZMod P) : zeta (x + 1) = zeta x + Ring.inverse x ^ 2 := by
  obtain rfl | hP1 := eq_or_ne P 1
  · exact Subsingleton.elim _ _
  by_cases hx : x.val + 1 < P
  · have hv : (x + 1).val = x.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one'' hP1, Nat.mod_eq_of_lt hx]
    unfold zeta; rw [hv, sum_range_succ, ZMod.natCast_zmod_val]
  · have hx' : x.val + 1 = P := by have := ZMod.val_lt x; omega
    have hx1 : x + 1 = 0 := by
      have : ((x.val + 1 : ℕ) : ZMod P) = 0 := by rw [hx']; exact ZMod.natCast_self P
      rwa [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one] at this
    have : zeta x + Ring.inverse x ^ 2 = ∑ t ∈ range P, Ring.inverse (t : ZMod P) ^ 2 := by
      unfold zeta
      rw [show range P = range (x.val + 1) from congrArg range hx'.symm, sum_range_succ,
        ZMod.natCast_zmod_val]
    rw [this, sum_range_natCast (fun z => Ring.inverse z ^ 2), sum_inverse_sq h2 h3, hx1]
    simp [zeta]

omit [NeZero P] h2 h3 in
theorem zeta_zero : zeta (0 : ZMod P) = 0 := by simp [zeta]

theorem zeta_one : zeta (1 : ZMod P) = 0 := by
  have := zeta_succ h2 h3 0
  rw [zero_add] at this; rw [this, zeta_zero]; simp

/-- `ζ(1 - x) = -ζ(x)`: the oddness of `Z`. -/
theorem zeta_one_sub (x : ZMod P) : zeta (1 - x) = -zeta x := by
  suffices h : ∀ n : ℕ, zeta (1 - (n : ZMod P)) + zeta (n : ZMod P) = 0 by
    have := h x.val
    rw [ZMod.natCast_zmod_val] at this
    linear_combination this
  intro n
  induction n with
  | zero => simp [zeta_one h2 h3, zeta_zero]
  | succ n ih =>
    have e1 := zeta_succ h2 h3 (-(n : ZMod P))
    have e2 := zeta_succ h2 h3 (n : ZMod P)
    rw [inverse_neg_sq] at e1
    rw [show (1 : ZMod P) - (n : ZMod P) = -(n : ZMod P) + 1 by ring] at ih
    rw [show (1 : ZMod P) - ((n + 1 : ℕ) : ZMod P) = -(n : ZMod P) by push_cast; ring,
      show ((n + 1 : ℕ) : ZMod P) = (n : ZMod P) + 1 by push_cast; ring, e2]
    linear_combination ih - e1

/-- The class sum over an arithmetic progression. -/
theorem sum_class {d : ZMod P} (hd : IsUnit d) (β : ZMod P) (K : ℕ) :
    ∑ k ∈ range K, Ring.inverse (β + d * (k : ZMod P)) ^ 2 =
      Ring.inverse d ^ 2 *
        (zeta ((β + d * (K : ZMod P)) * Ring.inverse d) - zeta (β * Ring.inverse d)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    have hdd : d * Ring.inverse d = 1 := Ring.mul_inverse_cancel _ hd
    have e : (β + d * ((K + 1 : ℕ) : ZMod P)) * Ring.inverse d =
        (β + d * (K : ZMod P)) * Ring.inverse d + 1 := by
      push_cast; linear_combination hdd
    rw [e, zeta_succ h2 h3, Ring.mul_inverse_rev, Ring.inverse_inverse hd]
    linear_combination (-(Ring.inverse d * d + 1) * Ring.inverse (β + d * (K : ZMod P)) ^ 2) * hdd

end Core

section Reindex

variable {M : Type*} [AddCommMonoid M]

theorem not_mod_eq_of_lt {D β j E : ℕ} (hE : E % D = β) (hj : j < E) (hjE : E < j + D)
    (h : j % D = β) : False := by
  have h1 : j ≡ E [MOD D] := by unfold Nat.ModEq; rw [h, hE]
  have h2 : D ∣ E - j := (Nat.modEq_iff_dvd' hj.le).1 h1
  have h3 : E - j ≠ 0 := by omega
  have := Nat.le_of_dvd (by omega) h2
  omega

theorem sum_range_ite_mod (F : ℕ → M) {D β : ℕ} (hβ : β < D) (K : ℕ) :
    ∑ j ∈ range (β + D * K), (if j % D = β then F j else 0) =
      ∑ k ∈ range K, F (β + D * k) := by
  induction K with
  | zero =>
    simp only [mul_zero, add_zero, range_zero, sum_empty]
    refine sum_eq_zero fun j hj => ?_
    rw [mem_range] at hj
    rw [ite_eq_right (by rw [Nat.mod_eq_of_lt (by omega)]; omega)]
  | succ K ih =>
    rw [show β + D * (K + 1) = (β + D * K) + D by ring, sum_range_add, ih, sum_range_succ]
    congr 1
    rw [sum_eq_single 0]
    · rw [add_zero, ite_eq_left (by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hβ])]
    · intro x hx hx0
      rw [mem_range] at hx
      have hm : D * (K + 1) = D * K + D := by ring
      refine ite_eq_right fun h => ?_
      exact not_mod_eq_of_lt (D := D) (E := β + D * (K + 1)) (j := β + D * K + x)
        (by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hβ]) (by omega) (by omega) h
    · intro h; exact absurd (mem_range.2 (by omega)) h

theorem sum_range_ite_mod_ext (F : ℕ → M) {D β U E : ℕ} (hUE : U ≤ E) (hEU : E < U + D)
    (hE : E % D = β) :
    ∑ j ∈ range U, (if j % D = β then F j else 0) =
      ∑ j ∈ range E, (if j % D = β then F j else 0) := by
  obtain ⟨c, rfl⟩ : ∃ c, E = U + c := ⟨E - U, by omega⟩
  rw [sum_range_add]
  have : ∑ x ∈ range c, (if (U + x) % D = β then F (U + x) else 0) = 0 := by
    refine sum_eq_zero fun x hx => ?_
    rw [mem_range] at hx
    exact ite_eq_right fun h => not_mod_eq_of_lt hE (by omega) (by omega) h
  rw [this, add_zero]

end Reindex

section Class

variable {P : ℕ} [NeZero P] (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P))
include h2 h3

/-- The class sum in the form used for the pairs. -/
theorem sum_class_nat {D β U E : ℕ} (hD : IsUnit (D : ZMod P)) (hβ : β < D) (hUE : U ≤ E)
    (hEU : E < U + D) (hE : E % D = β) :
    ∑ j ∈ range U, (if j % D = β then Ring.inverse (j : ZMod P) ^ 2 else 0) =
      Ring.inverse (D : ZMod P) ^ 2 *
        (zeta ((E : ZMod P) * Ring.inverse (D : ZMod P)) -
          zeta ((β : ZMod P) * Ring.inverse (D : ZMod P))) := by
  rw [sum_range_ite_mod_ext _ hUE hEU hE]
  have hE' : E = β + D * (E / D) := by rw [← hE, Nat.mod_add_div]
  rw [hE', sum_range_ite_mod _ hβ]
  push_cast
  exact sum_class h2 h3 hD _ _

end Class


section Pair

theorem inverse_neg {M : Type*} [CommRing M] (x : M) : Ring.inverse (-x) = -Ring.inverse x := by
  by_cases hx : IsUnit x
  · have h1 : Ring.inverse (-x) * (-x) = 1 := Ring.inverse_mul_cancel _ hx.neg
    have h2 : x * Ring.inverse x = 1 := Ring.mul_inverse_cancel _ hx
    linear_combination (-Ring.inverse x) * h1 + (-Ring.inverse (-x)) * h2
  · rw [Ring.inverse_non_unit _ hx, Ring.inverse_non_unit _ (fun h => hx (by simpa using h.neg)),
      neg_zero]

variable {P : ℕ} [NeZero P] (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P))

/-- `Z(z/d)` for `z ∈ ZMod d`: `ζ` at the residue of `z.val / d` modulo `P`. -/
noncomputable def Zf (P d : ℕ) (z : ZMod d) : ZMod P :=
  zeta ((z.val : ZMod P) * Ring.inverse (d : ZMod P))

include h2 h3 in
theorem Zf_neg {d : ℕ} [NeZero d] (hd : IsUnit (d : ZMod P)) (z : ZMod d) :
    Zf P d (-z) = -Zf P d z := by
  unfold Zf
  rw [ZMod.neg_val]
  split_ifs with hz
  · subst hz; simp [zeta_zero]
  · rw [Nat.cast_sub (ZMod.val_lt z).le, sub_mul, Ring.mul_inverse_cancel _ hd,
      zeta_one_sub h2 h3]

/-- The point `T / e` in `ZMod d`. -/
noncomputable def pt (T e d : ℕ) : ZMod d := (T : ZMod d) * (e : ZMod d)⁻¹

theorem mul_pt {T e d : ℕ} (h : Nat.Coprime e d) : (e : ZMod d) * pt T e d = T := by
  unfold pt; rw [mul_left_comm, ZMod.coe_mul_inv_eq_one e h, mul_one]

/-- The pair sum `Y(e, e') = ∑_{i < T, e ∣ i, e' ∣ T - i} i⁻²`. -/
noncomputable def Ysum (P T e e' : ℕ) : ZMod P :=
  ∑ i ∈ range T, (if e ∣ i ∧ e' ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)

include h2 h3 in
/-- **The pair formula** for coprime `e, e'`. -/
theorem pair_sum {e e' T : ℕ} (he : 0 < e) (he' : 0 < e') (hcop : Nat.Coprime e e')
    (hue : IsUnit (e : ZMod P)) (hue' : IsUnit (e' : ZMod P)) (hT : (T : ZMod P) = 0) :
    (e : ZMod P) ^ 2 * (e' : ZMod P) ^ 2 * Ysum P T e e' =
      -(Zf P e (pt T e' e) + Zf P e' (pt T e e')) := by
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero e' := ⟨he'.ne'⟩
  set t := pt T e e' with ht
  set t' := pt T e' e with ht'
  have htt : (e : ZMod e') * t = T := mul_pt hcop
  have htt' : (e' : ZMod e) * t' = T := mul_pt hcop.symm
  set α := e * t.val with hα
  set s₀ := (-t').val with hs₀
  set E := T + e' * s₀ with hE
  have hαD : α < e * e' := by
    have := ZMod.val_lt t
    rw [hα]; exact Nat.mul_lt_mul_of_pos_left this he
  have hαe : (α : ZMod e) = 0 := by
    rw [hα]; push_cast; rw [ZMod.natCast_self, zero_mul]
  have hαe' : (α : ZMod e') = T := by
    rw [hα]; push_cast; rw [ZMod.natCast_zmod_val, htt]
  have hcond : ∀ i, i < T → ((e ∣ i ∧ e' ∣ T - i) ↔ i % (e * e') = α) := by
    intro i hi
    have h1 : i % (e * e') = α ↔ i ≡ α [MOD e * e'] := by
      unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hαD]
    rw [h1, ← Nat.modEq_and_modEq_iff_modEq_mul hcop, ← ZMod.natCast_eq_natCast_iff,
      ← ZMod.natCast_eq_natCast_iff, hαe, hαe', ← ZMod.natCast_eq_zero_iff i e,
      ← ZMod.natCast_eq_zero_iff (T - i) e', Nat.cast_sub hi.le, sub_eq_zero, eq_comm (a := (T : ZMod e'))]
  have hsum : Ysum P T e e' =
      ∑ i ∈ range T, (if i % (e * e') = α then Ring.inverse (i : ZMod P) ^ 2 else 0) := by
    refine sum_congr rfl fun i hi => ?_
    simp only [hcond i (mem_range.1 hi)]
  have hEe : (E : ZMod e) = (α : ZMod e) := by
    rw [hαe, hE]; push_cast; rw [hs₀, ZMod.natCast_zmod_val]; linear_combination -htt'
  have hEe' : (E : ZMod e') = (α : ZMod e') := by
    rw [hαe', hE]; push_cast; rw [ZMod.natCast_self]; ring
  have hEmod : E % (e * e') = α := by
    have : E ≡ α [MOD e * e'] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1
      ⟨(ZMod.natCast_eq_natCast_iff _ _ _).1 hEe, (ZMod.natCast_eq_natCast_iff _ _ _).1 hEe'⟩
    unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hαD]
  have hEU : E < T + e * e' := by
    have : s₀ < e := ZMod.val_lt _
    have : e' * s₀ < e' * e := Nat.mul_lt_mul_of_pos_left this he'
    rw [hE]; rw [mul_comm e e']; omega
  have hD : IsUnit ((e * e' : ℕ) : ZMod P) := by rw [Nat.cast_mul]; exact hue.mul hue'
  rw [hsum, sum_class_nat h2 h3 hD hαD (by omega) hEU hEmod]
  have hee : (e : ZMod P) * Ring.inverse (e : ZMod P) = 1 := Ring.mul_inverse_cancel _ hue
  have hee' : (e' : ZMod P) * Ring.inverse (e' : ZMod P) = 1 := Ring.mul_inverse_cancel _ hue'
  have hinv : Ring.inverse (((e * e' : ℕ) : ZMod P)) =
      Ring.inverse (e' : ZMod P) * Ring.inverse (e : ZMod P) := by
    rw [Nat.cast_mul, Ring.mul_inverse_rev]
  have hEv : (E : ZMod P) * Ring.inverse ((e * e' : ℕ) : ZMod P) =
      (s₀ : ZMod P) * Ring.inverse (e : ZMod P) := by
    rw [hinv, hE]; push_cast; rw [hT]
    linear_combination ((s₀ : ZMod P) * Ring.inverse (e : ZMod P)) * hee'
  have hαv : (α : ZMod P) * Ring.inverse ((e * e' : ℕ) : ZMod P) =
      (t.val : ZMod P) * Ring.inverse (e' : ZMod P) := by
    rw [hinv, hα]; push_cast
    linear_combination ((t.val : ZMod P) * Ring.inverse (e' : ZMod P)) * hee
  rw [hEv, hαv, hinv]
  have hZ1 : zeta ((s₀ : ZMod P) * Ring.inverse (e : ZMod P)) = -Zf P e t' := by
    rw [← Zf_neg h2 h3 hue t']; rfl
  have hZ2 : zeta ((t.val : ZMod P) * Ring.inverse (e' : ZMod P)) = Zf P e' t := rfl
  rw [hZ1, hZ2]
  linear_combination (-(Zf P e t' + Zf P e' t) * ((e : ZMod P) * Ring.inverse (e : ZMod P) + 1) *
      ((e' : ZMod P) * Ring.inverse (e' : ZMod P)) ^ 2) * hee +
    (-(Zf P e t' + Zf P e' t) * ((e' : ZMod P) * Ring.inverse (e' : ZMod P) + 1)) * hee'

include h2 h3 in
/-- The diagonal pairs vanish. -/
theorem diag_sum {e T : ℕ} (he : 0 < e) (hue : IsUnit (e : ZMod P)) (hT : (T : ZMod P) = 0) :
    Ysum P T e e = 0 := by
  unfold Ysum
  by_cases heT : e ∣ T
  · have hsum : ∑ i ∈ range T, (if e ∣ i ∧ e ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) =
        ∑ i ∈ range T, (if i % e = 0 then Ring.inverse (i : ZMod P) ^ 2 else 0) := by
      refine sum_congr rfl fun i hi => ?_
      have : (e ∣ i ∧ e ∣ T - i) ↔ i % e = 0 := by
        rw [← Nat.dvd_iff_mod_eq_zero]
        exact ⟨fun h => h.1, fun h => ⟨h, Nat.dvd_sub heT h⟩⟩
      simp only [this]
    rw [hsum, sum_class_nat h2 h3 hue he le_rfl (by omega) (Nat.mod_eq_zero_of_dvd heT), hT]
    simp [zeta_zero]
  · refine sum_eq_zero fun i hi => ?_
    refine ite_eq_right fun ⟨h1, h2'⟩ => ?_
    exact heT (by have := Nat.dvd_add h1 h2'; rwa [Nat.add_sub_cancel' (mem_range.1 hi).le] at this)

end Pair

section CoreSum

variable {P : ℕ} [NeZero P] (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P))

/-- `c(n) = a²[a ∣ n] + b²[b ∣ n] - m²[m ∣ n]` in `ZMod P`, with `m = a + b`. -/
noncomputable def cZ (P a b n : ℕ) : ZMod P :=
  (if a ∣ n then (a : ZMod P) ^ 2 else 0) + (if b ∣ n then (b : ZMod P) ^ 2 else 0) -
    (if a + b ∣ n then ((a + b : ℕ) : ZMod P) ^ 2 else 0)

theorem ite_mul_ite_mul {R : Type*} [CommRing R] (c c' : Prop) [Decidable c] [Decidable c']
    (x y z : R) :
    (if c then x else 0) * (if c' then y else 0) * z = x * y * (if c ∧ c' then z else 0) := by
  by_cases hc : c <;> by_cases hc' : c' <;> simp [hc, hc']

omit [NeZero P] in
theorem cZ_mul (a b T i : ℕ) :
    cZ P a b i * cZ P a b (T - i) * Ring.inverse (i : ZMod P) ^ 2 =
      (a : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if a ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) +
        (a : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if a ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) -
        (a : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if a ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) +
        (b : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if b ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) +
        (b : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if b ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) -
        (b : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if b ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) -
        ((a + b : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) -
        ((a + b : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) +
        ((a + b : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0) := by
  simp only [← ite_mul_ite_mul]
  unfold cZ
  ring

/-- The pair sums for `(a, b, m)` with `m = a + b`. -/
noncomputable def Ycomb (P a b T : ℕ) : ZMod P :=
  (a : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T a a +
    (a : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T a b -
    (a : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T a (a + b) +
    (b : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T b a +
    (b : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T b b -
    (b : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T b (a + b) -
    ((a + b : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T (a + b) a -
    ((a + b : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T (a + b) b +
    ((a + b : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T (a + b) (a + b)

omit [NeZero P] in
theorem sum_cZ_mul (a b T : ℕ) :
    ∑ i ∈ range T, cZ P a b i * cZ P a b (T - i) * Ring.inverse (i : ZMod P) ^ 2 =
      Ycomb P a b T := by
  simp only [cZ_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum, Ycomb, Ysum]

theorem pt_add_left (T a b : ℕ) : pt T (a + b) a = pt T b a := by
  unfold pt; push_cast; rw [ZMod.natCast_self, zero_add]

theorem pt_add_right (T a b : ℕ) : pt T (a + b) b = pt T a b := by
  unfold pt; push_cast; rw [ZMod.natCast_self, add_zero]

theorem pt_neg {T a b : ℕ} (h : Nat.Coprime a (a + b)) :
    pt T b (a + b) = -pt T a (a + b) := by
  have hb : (b : ZMod (a + b)) = -(a : ZMod (a + b)) := by
    have : ((a + b : ℕ) : ZMod (a + b)) = 0 := ZMod.natCast_self _
    push_cast at this; linear_combination this
  unfold pt
  rw [hb]
  have hinv : (-(a : ZMod (a + b)))⁻¹ = -(a : ZMod (a + b))⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [neg_mul_neg]; exact ZMod.coe_mul_inv_eq_one a h
  rw [hinv]; ring

include h2 h3 in
/-- **The cancellation** for coprime `a, b`: `∑_{e,e'} λ_e λ_{e'} e² e'² Y(e,e') = 0`. -/
theorem Ycomb_eq_zero {a b T : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hua : IsUnit (a : ZMod P)) (hub : IsUnit (b : ZMod P))
    (hum : IsUnit ((a + b : ℕ) : ZMod P)) (hT : (T : ZMod P) = 0) :
    Ycomb P a b T = 0 := by
  have hm : 0 < a + b := by omega
  have ham : Nat.Coprime a (a + b) := Nat.coprime_self_add_right.2 hab
  have hbm : Nat.Coprime b (a + b) := Nat.coprime_add_self_right.2 hab.symm
  have : NeZero (a + b) := ⟨hm.ne'⟩
  unfold Ycomb
  rw [diag_sum h2 h3 ha hua hT, diag_sum h2 h3 hb hub hT, diag_sum h2 h3 hm hum hT,
    pair_sum h2 h3 ha hb hab hua hub hT, pair_sum h2 h3 hb ha hab.symm hub hua hT,
    pair_sum h2 h3 ha hm ham hua hum hT, pair_sum h2 h3 hm ha ham.symm hum hua hT,
    pair_sum h2 h3 hb hm hbm hub hum hT, pair_sum h2 h3 hm hb hbm.symm hum hub hT,
    pt_add_left, pt_add_right, pt_neg ham, Zf_neg h2 h3 hum]
  ring

include h2 h3 in
/-- **Theorem 2 in `ZMod P`** for coprime `a, b`: the sum
`∑_{i + i' = T} c(i) i⁻¹ c(i') i'⁻¹` vanishes when `P ∣ T`. -/
theorem core_sum {a b T : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hua : IsUnit (a : ZMod P)) (hub : IsUnit (b : ZMod P))
    (hum : IsUnit ((a + b : ℕ) : ZMod P)) (hT : (T : ZMod P) = 0) :
    ∑ x ∈ antidiagonal T, (cZ P a b x.1 * Ring.inverse (x.1 : ZMod P)) *
      (cZ P a b x.2 * Ring.inverse (x.2 : ZMod P)) = 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
  simp only [hT, Ring.inverse_zero, mul_zero, zero_mul, add_zero]
  have e : ∀ i ∈ range T, cZ P a b i * Ring.inverse (i : ZMod P) *
      (cZ P a b (T - i) * Ring.inverse ((T - i : ℕ) : ZMod P)) =
      -(cZ P a b i * cZ P a b (T - i) * Ring.inverse (i : ZMod P) ^ 2) := by
    intro i hi
    rw [Nat.cast_sub (mem_range.1 hi).le, hT, zero_sub, inverse_neg]; ring
  rw [sum_congr rfl e, sum_neg_distrib, sum_cZ_mul, Ycomb_eq_zero h2 h3 ha hb hab hua hub hum hT,
    neg_zero]

end CoreSum


section VarCore

variable {P : ℕ} [NeZero P] (h2 : IsUnit (2 : ZMod P)) (h3 : IsUnit (3 : ZMod P))

/-- The weights of the variant in `ZMod P`:
`-a²[a ∣ n] + ½(2a)²[2a ∣ n] - b²[b ∣ n] + ½(2b)²[2b ∣ n] - m²[m ∣ n]`. -/
noncomputable def cmZ (P a b n : ℕ) : ZMod P :=
  -(if a ∣ n then (a : ZMod P) ^ 2 else 0) +
    Ring.inverse (2 : ZMod P) * (if 2 * a ∣ n then ((2 * a : ℕ) : ZMod P) ^ 2 else 0) -
    (if b ∣ n then (b : ZMod P) ^ 2 else 0) +
    Ring.inverse (2 : ZMod P) * (if 2 * b ∣ n then ((2 * b : ℕ) : ZMod P) ^ 2 else 0) -
    (if a + b ∣ n then ((a + b : ℕ) : ZMod P) ^ 2 else 0)

omit [NeZero P] in
theorem cmZ_mul (a b T i : ℕ) :
    cmZ P a b i * cmZ P a b (T - i) * Ring.inverse (i : ZMod P) ^ 2 =
      ((a : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if a ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0))
        - (Ring.inverse (2 : ZMod P) * ((a : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 *
          (if a ∣ i ∧ 2 * a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + ((a : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if a ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0))
        - (Ring.inverse (2 : ZMod P) * ((a : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 *
          (if a ∣ i ∧ 2 * b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + ((a : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if a ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0))
        - (Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if 2 * a ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + (Ring.inverse (2 : ZMod P) * Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 *
          (if 2 * a ∣ i ∧ 2 * a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        - (Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if 2 * a ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + (Ring.inverse (2 : ZMod P) * Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 *
          (if 2 * a ∣ i ∧ 2 * b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        - (Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if 2 * a ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + ((b : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if b ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0))
        - (Ring.inverse (2 : ZMod P) * ((b : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 *
          (if b ∣ i ∧ 2 * a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + ((b : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if b ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0))
        - (Ring.inverse (2 : ZMod P) * ((b : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 *
          (if b ∣ i ∧ 2 * b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + ((b : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if b ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0))
        - (Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if 2 * b ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + (Ring.inverse (2 : ZMod P) * Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 *
          (if 2 * b ∣ i ∧ 2 * a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        - (Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if 2 * b ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + (Ring.inverse (2 : ZMod P) * Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 *
          (if 2 * b ∣ i ∧ 2 * b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        - (Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if 2 * b ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + (((a + b : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0))
        - (Ring.inverse (2 : ZMod P) * (((a + b : ℕ) : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ 2 * a ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + (((a + b : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0))
        - (Ring.inverse (2 : ZMod P) * (((a + b : ℕ) : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ 2 * b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)))
        + (((a + b : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 *
          (if a + b ∣ i ∧ a + b ∣ T - i then Ring.inverse (i : ZMod P) ^ 2 else 0)) := by
  simp only [← ite_mul_ite_mul]
  unfold cmZ
  ring

/-- The 25 pair sums of the variant. -/
noncomputable def Ycm (P a b T : ℕ) : ZMod P :=
  ((a : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T (a) (a))
    - (Ring.inverse (2 : ZMod P) * ((a : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 * Ysum P T (a) (2 * a)))
    + ((a : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T (a) (b))
    - (Ring.inverse (2 : ZMod P) * ((a : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 * Ysum P T (a) (2 * b)))
    + ((a : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T (a) (a + b))
    - (Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T (2 * a) (a)))
    + (Ring.inverse (2 : ZMod P) * Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 * Ysum P T (2 * a) (2 * a)))
    - (Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T (2 * a) (b)))
    + (Ring.inverse (2 : ZMod P) * Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 * Ysum P T (2 * a) (2 * b)))
    - (Ring.inverse (2 : ZMod P) * (((2 * a : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T (2 * a) (a + b)))
    + ((b : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T (b) (a))
    - (Ring.inverse (2 : ZMod P) * ((b : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 * Ysum P T (b) (2 * a)))
    + ((b : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T (b) (b))
    - (Ring.inverse (2 : ZMod P) * ((b : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 * Ysum P T (b) (2 * b)))
    + ((b : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T (b) (a + b))
    - (Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T (2 * b) (a)))
    + (Ring.inverse (2 : ZMod P) * Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 * Ysum P T (2 * b) (2 * a)))
    - (Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T (2 * b) (b)))
    + (Ring.inverse (2 : ZMod P) * Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 * Ysum P T (2 * b) (2 * b)))
    - (Ring.inverse (2 : ZMod P) * (((2 * b : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T (2 * b) (a + b)))
    + (((a + b : ℕ) : ZMod P) ^ 2 * (a : ZMod P) ^ 2 * Ysum P T (a + b) (a))
    - (Ring.inverse (2 : ZMod P) * (((a + b : ℕ) : ZMod P) ^ 2 * ((2 * a : ℕ) : ZMod P) ^ 2 * Ysum P T (a + b) (2 * a)))
    + (((a + b : ℕ) : ZMod P) ^ 2 * (b : ZMod P) ^ 2 * Ysum P T (a + b) (b))
    - (Ring.inverse (2 : ZMod P) * (((a + b : ℕ) : ZMod P) ^ 2 * ((2 * b : ℕ) : ZMod P) ^ 2 * Ysum P T (a + b) (2 * b)))
    + (((a + b : ℕ) : ZMod P) ^ 2 * ((a + b : ℕ) : ZMod P) ^ 2 * Ysum P T (a + b) (a + b))

omit [NeZero P] in
theorem sum_cmZ_mul (a b T : ℕ) :
    ∑ i ∈ range T, cmZ P a b i * cmZ P a b (T - i) * Ring.inverse (i : ZMod P) ^ 2 =
      Ycm P a b T := by
  simp only [cmZ_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum, Ycm, Ysum]

omit [NeZero P] h2 h3 in
/-- A common factor of the pair. -/
theorem Ysum_gmul {g e e' T : ℕ} (hg : 0 < g) :
    Ysum P T (g * e) (g * e') =
      if g ∣ T then Ring.inverse (g : ZMod P) ^ 2 * Ysum P (T / g) e e' else 0 := by
  unfold Ysum
  split_ifs with hgT
  · obtain ⟨T', rfl⟩ := hgT
    rw [Nat.mul_div_cancel_left _ hg]
    have e1 : ∑ i ∈ range (g * T'), (if g * e ∣ i ∧ g * e' ∣ g * T' - i then
          Ring.inverse (i : ZMod P) ^ 2 else 0) =
        ∑ i ∈ range (0 + g * T'), (if i % g = 0 then (if g * e ∣ i ∧ g * e' ∣ g * T' - i then
          Ring.inverse (i : ZMod P) ^ 2 else 0) else 0) := by
      rw [zero_add]
      refine sum_congr rfl fun i _ => ?_
      by_cases hi : i % g = 0
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi]
        exact ite_eq_right fun h => hi (Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_mul_right g e) h.1))
    rw [e1, sum_range_ite_mod _ hg, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [zero_add, ← Nat.mul_sub, Nat.mul_dvd_mul_iff_left hg]
    rw [Nat.cast_mul, Ring.mul_inverse_rev]
    split_ifs <;> ring
  · refine sum_eq_zero fun i hi => ite_eq_right fun ⟨h1, h2'⟩ => hgT ?_
    have := Nat.dvd_add (dvd_trans (dvd_mul_right g e) h1) (dvd_trans (dvd_mul_right g e') h2')
    rwa [Nat.add_sub_cancel' (mem_range.1 hi).le] at this

omit [NeZero P] h2 h3 in
theorem natCast_div_eq_zero {g T : ℕ} (hug : IsUnit (g : ZMod P)) (hgT : g ∣ T)
    (hT : (T : ZMod P) = 0) : ((T / g : ℕ) : ZMod P) = 0 := by
  obtain ⟨T', rfl⟩ := hgT
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  rw [Nat.mul_div_cancel_left _ hg]
  rw [Nat.cast_mul] at hT
  exact hug.mul_right_eq_zero.1 hT

theorem pt_unique {T c d : ℕ} (h : Nat.Coprime c d) {x : ZMod d} (hx : (c : ZMod d) * x = T) :
    x = pt T c d := by
  unfold pt
  rw [← hx, mul_comm (c : ZMod d) x, mul_assoc, ZMod.coe_mul_inv_eq_one c h, mul_one]

theorem mul_val_pt {T c d : ℕ} [NeZero d] (h : Nat.Coprime c d) :
    c * (pt T c d).val ≡ T [MOD d] := by
  rw [← ZMod.natCast_eq_natCast_iff]; push_cast
  rw [ZMod.natCast_zmod_val, mul_pt h]

theorem mod_eq_val_pt {T c d x : ℕ} [NeZero d] (h : Nat.Coprime c d) (hx : c * x ≡ T [MOD d]) :
    x % d = (pt T c d).val := by
  have : (x : ZMod d) = pt T c d := pt_unique h (by
    rw [← Nat.cast_mul]; exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hx)
  rw [← this, ZMod.val_natCast]

omit [NeZero P] h2 h3 in
theorem Zf_one (z : ZMod 1) : Zf P 1 z = 0 := by
  unfold Zf; rw [Subsingleton.elim z 0, ZMod.val_zero]; simp [zeta_zero]

include h2 h3 in
theorem Zf_two (z : ZMod 2) : Zf P 2 z = 0 := by
  have hu2 : IsUnit ((2 : ℕ) : ZMod P) := by rwa [Nat.cast_ofNat]
  have h := Zf_neg h2 h3 hu2 z
  rw [ZMod.neg_eq_self_mod_two] at h
  have : (2 : ZMod P) * Zf P 2 z = 0 := by linear_combination h
  exact h2.mul_right_eq_zero.1 this

include h2 h3 in
theorem Ysum_one_two {T : ℕ} (hT : (T : ZMod P) = 0) : Ysum P T 1 2 = 0 := by
  have hu2 : IsUnit ((2 : ℕ) : ZMod P) := by rwa [Nat.cast_ofNat]
  have h := pair_sum h2 h3 one_pos two_pos (Nat.coprime_one_left 2) (by simp) hu2 hT
  rw [Zf_one, Zf_two h2 h3] at h
  have h4 : IsUnit ((2 : ZMod P) ^ 2) := h2.pow 2
  push_cast at h
  have : (2 : ZMod P) ^ 2 * Ysum P T 1 2 = 0 := by linear_combination h
  exact h4.mul_right_eq_zero.1 this

include h2 h3 in
theorem Ysum_two_one {T : ℕ} (hT : (T : ZMod P) = 0) : Ysum P T 2 1 = 0 := by
  have hu2 : IsUnit ((2 : ℕ) : ZMod P) := by rwa [Nat.cast_ofNat]
  have h := pair_sum h2 h3 two_pos one_pos (Nat.coprime_one_right 2) hu2 (by simp) hT
  rw [Zf_one, Zf_two h2 h3] at h
  have h4 : IsUnit ((2 : ZMod P) ^ 2) := h2.pow 2
  push_cast at h
  have : (2 : ZMod P) ^ 2 * Ysum P T 2 1 = 0 := by linear_combination h
  exact h4.mul_right_eq_zero.1 this

include h2 h3 in
theorem Ysum_e_two_e {e T : ℕ} (he : 0 < e) (hue : IsUnit (e : ZMod P))
    (hT : (T : ZMod P) = 0) : Ysum P T e (2 * e) = 0 := by
  have := Ysum_gmul (P := P) (g := e) (e := 1) (e' := 2) (T := T) he
  rw [mul_one, mul_comm e 2] at this
  rw [this]
  split_ifs with h
  · rw [Ysum_one_two h2 h3 (natCast_div_eq_zero hue h hT), mul_zero]
  · rfl

include h2 h3 in
theorem Ysum_two_e_e {e T : ℕ} (he : 0 < e) (hue : IsUnit (e : ZMod P))
    (hT : (T : ZMod P) = 0) : Ysum P T (2 * e) e = 0 := by
  have := Ysum_gmul (P := P) (g := e) (e := 2) (e' := 1) (T := T) he
  rw [mul_one, mul_comm e 2] at this
  rw [this]
  split_ifs with h
  · rw [Ysum_two_one h2 h3 (natCast_div_eq_zero hue h hT), mul_zero]
  · rfl

include h2 h3 in
/-- The pairs with common factor `2`. -/
theorem pair_two {e e' T : ℕ} (he : 0 < e) (he' : 0 < e') (hcop : Nat.Coprime e e')
    (hue : IsUnit (e : ZMod P)) (hue' : IsUnit (e' : ZMod P)) (hT : (T : ZMod P) = 0) :
    ((2 * e : ℕ) : ZMod P) ^ 2 * ((2 * e' : ℕ) : ZMod P) ^ 2 * Ysum P T (2 * e) (2 * e') =
      if 2 ∣ T then -(4 * (Zf P e (pt (T / 2) e' e) + Zf P e' (pt (T / 2) e e'))) else 0 := by
  rw [Ysum_gmul two_pos]
  split_ifs with h
  · have hu2 : IsUnit ((2 : ℕ) : ZMod P) := by rwa [Nat.cast_ofNat]
    have hp := pair_sum h2 h3 he he' hcop hue hue' (natCast_div_eq_zero hu2 h hT)
    have h22 : (2 : ZMod P) * Ring.inverse 2 = 1 := Ring.mul_inverse_cancel _ h2
    push_cast
    linear_combination (16 * Ring.inverse (2 : ZMod P) ^ 2) * hp -
      (4 * (Zf P e (pt (T / 2) e' e) + Zf P e' (pt (T / 2) e e')) *
        (2 * Ring.inverse (2 : ZMod P) + 1)) * h22
  · rw [mul_zero]

theorem pt_neg_two {T a b : ℕ} (h : Nat.Coprime (2 * a) (a + b)) :
    pt T (2 * b) (a + b) = -pt T (2 * a) (a + b) := by
  have hb : ((2 * b : ℕ) : ZMod (a + b)) = -((2 * a : ℕ) : ZMod (a + b)) := by
    have : ((a + b : ℕ) : ZMod (a + b)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢; linear_combination 2 * this
  unfold pt
  rw [hb]
  have hinv : (-((2 * a : ℕ) : ZMod (a + b)))⁻¹ = -((2 * a : ℕ) : ZMod (a + b))⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [neg_mul_neg]; exact ZMod.coe_mul_inv_eq_one _ h
  rw [hinv]; ring

theorem pt_half {T' e d : ℕ} (h2d : Nat.Coprime 2 d) (hed : Nat.Coprime e d) :
    pt (2 * T') (2 * e) d = pt T' e d := by
  symm
  apply pt_unique (Nat.Coprime.mul_right h2d.symm hed.symm).symm
  rw [Nat.cast_mul, mul_assoc, mul_pt hed]; push_cast; ring

omit [NeZero P] h3 in
include h2 in
/-- Doubling the denominator: $Z_{2d}(2T'/e) = Z_d(T'/e)$. -/
theorem Zf_scale {T' e d : ℕ} (hd : 0 < d) (hed : Nat.Coprime e (2 * d)) :
    Zf P (2 * d) (pt (2 * T') e (2 * d)) = Zf P d (pt T' e d) := by
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero (2 * d) := ⟨by omega⟩
  have hed' : Nat.Coprime e d := Nat.Coprime.coprime_mul_left_right hed
  set y := pt T' e d
  have hz : pt (2 * T') e (2 * d) = ((2 * y.val : ℕ) : ZMod (2 * d)) := by
    symm
    apply pt_unique hed
    rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff, show e * (2 * y.val) = 2 * (e * y.val) by ring]
    exact Nat.ModEq.mul_left' 2 (mul_val_pt hed')
  have hv : (pt (2 * T') e (2 * d)).val = 2 * y.val := by
    rw [hz, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt y; omega)]
  unfold Zf
  rw [hv]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, Ring.mul_inverse_rev]
  have h22 : (2 : ZMod P) * Ring.inverse 2 = 1 := Ring.mul_inverse_cancel _ h2
  push_cast
  linear_combination ((y.val : ZMod P) * Ring.inverse (d : ZMod P)) * h22

include h2 h3 in
/-- **Lemma 4**, the distribution relation: $\zeta(x/2) + \zeta((x+1)/2) = 4\zeta(x)$. -/
theorem zeta_half (x : ZMod P) :
    zeta (x * Ring.inverse 2) + zeta ((x + 1) * Ring.inverse 2) = 4 * zeta x := by
  have hi : (2 : ZMod P) * Ring.inverse 2 = 1 := Ring.mul_inverse_cancel _ h2
  have h0 : zeta (Ring.inverse (2 : ZMod P)) = 0 := by
    have h := zeta_one_sub h2 h3 (Ring.inverse 2)
    rw [show (1 : ZMod P) - Ring.inverse 2 = Ring.inverse 2 by linear_combination (-1 : ZMod P) * hi] at h
    have : (2 : ZMod P) * zeta (Ring.inverse 2) = 0 := by linear_combination h
    exact h2.mul_right_eq_zero.1 this
  suffices h : ∀ n : ℕ, zeta ((n : ZMod P) * Ring.inverse 2) +
      zeta (((n : ZMod P) + 1) * Ring.inverse 2) = 4 * zeta (n : ZMod P) by
    have := h x.val; rwa [ZMod.natCast_zmod_val] at this
  intro n
  induction n with
  | zero => simp [zeta_zero, h0]
  | succ n ih =>
    push_cast
    have e1 : ((n : ZMod P) + 1 + 1) * Ring.inverse 2 = (n : ZMod P) * Ring.inverse 2 + 1 := by
      linear_combination hi
    rw [e1, zeta_succ h2 h3, zeta_succ h2 h3 (n : ZMod P), Ring.mul_inverse_rev,
      Ring.inverse_inverse h2]
    linear_combination ih

include h2 h3 in
/-- Lemma 4 for the two halves $u/(2d)$, $v/(2d)$ of $y/d$. -/
theorem zeta_halves {d u v y : ℕ} (hd : 0 < d) (hud : IsUnit (d : ZMod P)) (hu : u < 2 * d)
    (hv : v < 2 * d) (hu' : u % d = y) (hv' : v % d = y) (huv : u ≠ v) :
    zeta ((u : ZMod P) * Ring.inverse ((2 * d : ℕ) : ZMod P)) +
      zeta ((v : ZMod P) * Ring.inverse ((2 * d : ℕ) : ZMod P)) =
      4 * zeta ((y : ZMod P) * Ring.inverse (d : ZMod P)) := by
  have hcase : ∀ w, w < 2 * d → w % d = y → w = y ∨ w = y + d := by
    intro w hw hw'
    have h1 := Nat.mod_add_div w d
    have hq : w / d < 2 := (Nat.div_lt_iff_lt_mul hd).2 (by linarith)
    rw [hw'] at h1
    obtain ⟨q, hq'⟩ : ∃ q, w / d = q := ⟨_, rfl⟩
    rw [hq'] at h1 hq
    interval_cases q
    · left; omega
    · right; omega
  have hdd : (d : ZMod P) * Ring.inverse (d : ZMod P) = 1 := Ring.mul_inverse_cancel _ hud
  have key : zeta ((y : ZMod P) * Ring.inverse ((2 * d : ℕ) : ZMod P)) +
      zeta (((y + d : ℕ) : ZMod P) * Ring.inverse ((2 * d : ℕ) : ZMod P)) =
      4 * zeta ((y : ZMod P) * Ring.inverse (d : ZMod P)) := by
    rw [Nat.cast_mul, Ring.mul_inverse_rev, Nat.cast_add]
    have e1 : (y : ZMod P) * (Ring.inverse (d : ZMod P) * Ring.inverse ((2 : ℕ) : ZMod P)) =
        ((y : ZMod P) * Ring.inverse (d : ZMod P)) * Ring.inverse 2 := by
      rw [Nat.cast_ofNat]; ring
    have e2 : ((y : ZMod P) + d) * (Ring.inverse (d : ZMod P) * Ring.inverse ((2 : ℕ) : ZMod P)) =
        ((y : ZMod P) * Ring.inverse (d : ZMod P) + 1) * Ring.inverse 2 := by
      rw [Nat.cast_ofNat]; linear_combination (Ring.inverse (2 : ZMod P)) * hdd
    rw [e1, e2]; exact zeta_half h2 h3 _
  rcases hcase u hu hu' with rfl | rfl <;> rcases hcase v hv hv' with h | h
  · exact absurd h.symm huv
  · rw [h]; exact key
  · rw [h, add_comm]; exact key
  · exact absurd h.symm huv


theorem modEq_of_add_mul_left {a b t T : ℕ} (h : (a + b) * t ≡ T [MOD a]) : b * t ≡ T [MOD a] := by
  rw [← ZMod.natCast_eq_natCast_iff] at h ⊢; push_cast at h ⊢
  rwa [ZMod.natCast_self, zero_add] at h

theorem modEq_of_add_mul_right {a b t T : ℕ} (h : (a + b) * t ≡ T [MOD b]) : a * t ≡ T [MOD b] := by
  rw [← ZMod.natCast_eq_natCast_iff] at h ⊢; push_cast at h ⊢
  rwa [ZMod.natCast_self, add_zero] at h

theorem mod_two_of_mul {c t T : ℕ} (hc : c % 2 = 1) (hT : T % 2 = 1) (h : c * t ≡ T [MOD 2]) :
    t % 2 = 1 := by
  unfold Nat.ModEq at h
  rw [hT, Nat.mul_mod, hc, one_mul, Nat.mod_mod] at h
  exact h

include h2 h3 in
/-- Lemma 4 for the group of $a$ ($T$ odd). -/
theorem halves_a {a b T : ℕ} (ha : 0 < a) (hao : a % 2 = 1) (hbe : b % 2 = 0)
    (hTo : T % 2 = 1) (hab : Nat.Coprime a b) (hua : IsUnit (a : ZMod P)) :
    Zf P a (pt T (2 * b) a) + Zf P (2 * a) (pt T (a + b) (2 * a)) = 4 * Zf P a (pt T b a) := by
  have : NeZero a := ⟨ha.ne'⟩
  have : NeZero (2 * a) := ⟨by omega⟩
  have h2a : Nat.Coprime 2 a := Nat.coprime_two_left.2 (Nat.odd_iff.2 hao)
  have h2ba : Nat.Coprime (2 * b) a := (Nat.Coprime.mul_right h2a.symm hab).symm
  have hm2 : Nat.Coprime (a + b) 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))
  have hm2a : Nat.Coprime (a + b) (2 * a) :=
    Nat.Coprime.mul_right hm2 (Nat.coprime_self_add_left.2 hab.symm)
  set t₀ := (pt T (2 * b) a).val with ht₀
  set t₁ := (pt T (a + b) (2 * a)).val with ht₁
  set ty := (pt T b a).val with hty
  have hi : (2 * t₀) % a = ty := by
    apply mod_eq_val_pt hab.symm
    have := mul_val_pt (T := T) h2ba
    rw [← ht₀] at this
    rwa [show b * (2 * t₀) = 2 * b * t₀ by ring]
  have hm := mul_val_pt (T := T) hm2a
  rw [← ht₁] at hm
  have hii : t₁ % a = ty := mod_eq_val_pt hab.symm (modEq_of_add_mul_left (hm.of_mul_left 2))
  have hiii : t₁ % 2 = 1 := mod_two_of_mul (by omega) hTo (hm.of_mul_right a)
  have h22 : (2 : ZMod P) * Ring.inverse 2 = 1 := Ring.mul_inverse_cancel _ h2
  unfold Zf
  rw [← ht₀, ← ht₁, ← hty]
  have e0 : (t₀ : ZMod P) * Ring.inverse (a : ZMod P) =
      ((2 * t₀ : ℕ) : ZMod P) * Ring.inverse ((2 * a : ℕ) : ZMod P) := by
    push_cast; rw [Ring.mul_inverse_rev]
    linear_combination (-((t₀ : ZMod P) * Ring.inverse (a : ZMod P))) * h22
  rw [e0]
  exact zeta_halves h2 h3 ha hua (by have := ZMod.val_lt (pt T (2 * b) a); omega)
    (ZMod.val_lt _) hi hii (by omega)

include h2 h3 in
/-- Lemma 4 for the group of $b$ ($T$ odd). -/
theorem halves_b {a b T : ℕ} (hb : 0 < b) (hao : a % 2 = 1) (hbe : b % 2 = 0)
    (hTo : T % 2 = 1) (hab : Nat.Coprime a b) (hub : IsUnit (b : ZMod P)) :
    Zf P (2 * b) (pt T a (2 * b)) + Zf P (2 * b) (pt T (a + b) (2 * b)) =
      4 * Zf P b (pt T a b) := by
  have : NeZero b := ⟨hb.ne'⟩
  have : NeZero (2 * b) := ⟨by omega⟩
  have ha2 : Nat.Coprime a 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 hao)
  have ha2b : Nat.Coprime a (2 * b) := Nat.Coprime.mul_right ha2 hab
  have hm2 : Nat.Coprime (a + b) 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))
  have hm2b : Nat.Coprime (a + b) (2 * b) :=
    Nat.Coprime.mul_right hm2 (Nat.coprime_add_self_left.2 hab)
  set s₁ := (pt T a (2 * b)).val with hs₁
  set s₂ := (pt T (a + b) (2 * b)).val with hs₂
  set sy := (pt T a b).val with hsy
  have h1 := mul_val_pt (T := T) ha2b
  have h2' := mul_val_pt (T := T) hm2b
  rw [← hs₁] at h1
  rw [← hs₂] at h2'
  have hi : s₁ % b = sy := mod_eq_val_pt hab (h1.of_mul_left 2)
  have hii : s₂ % b = sy := mod_eq_val_pt hab (modEq_of_add_mul_right (h2'.of_mul_left 2))
  have hiii : s₁ ≠ s₂ := by
    intro h
    rw [← h] at h2'
    have h3' : a * s₁ + b * s₁ ≡ a * s₁ + 0 [MOD 2 * b] := by
      rw [add_zero, ← add_mul]; exact h2'.trans h1.symm
    have h4 := (Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_left_cancel' _ h3'))
    rw [show 2 * b = b * 2 by ring, Nat.mul_dvd_mul_iff_left hb] at h4
    have h5 := mod_two_of_mul hao hTo (h1.of_mul_right b)
    omega
  unfold Zf
  rw [← hs₁, ← hs₂, ← hsy]
  exact zeta_halves h2 h3 hb hub (ZMod.val_lt _) (ZMod.val_lt _) hi hii hiii

include h2 h3 in
/-- **Theorem 2 for the variant in `ZMod P`**, for coprime $a$ odd and $b = 2\beta$ even. -/
theorem core_var {a b β T : ℕ} (ha : 0 < a) (hβ : 0 < β) (hbβ : b = 2 * β) (hao : a % 2 = 1)
    (hab : Nat.Coprime a b) (hua : IsUnit (a : ZMod P)) (hub : IsUnit (b : ZMod P))
    (hum : IsUnit ((a + b : ℕ) : ZMod P)) (hT : (T : ZMod P) = 0) :
    ∑ x ∈ antidiagonal T, (cmZ P a b x.1 * Ring.inverse (x.1 : ZMod P)) *
      (cmZ P a b x.2 * Ring.inverse (x.2 : ZMod P)) = 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
  simp only [hT, Ring.inverse_zero, mul_zero, zero_mul, add_zero]
  have e : ∀ i ∈ range T, cmZ P a b i * Ring.inverse (i : ZMod P) *
      (cmZ P a b (T - i) * Ring.inverse ((T - i : ℕ) : ZMod P)) =
      -(cmZ P a b i * cmZ P a b (T - i) * Ring.inverse (i : ZMod P) ^ 2) := by
    intro i hi
    rw [Nat.cast_sub (mem_range.1 hi).le, hT, zero_sub, inverse_neg]; ring
  rw [sum_congr rfl e, sum_neg_distrib, sum_cmZ_mul, neg_eq_zero]
  subst hbβ
  have hb : 0 < 2 * β := by omega
  have hb2 : 0 < 2 * (2 * β) := by omega
  have ha2 : 0 < 2 * a := by omega
  have hm : 0 < a + 2 * β := by omega
  have : NeZero (a + 2 * β) := ⟨hm.ne'⟩
  have hu2' : IsUnit ((2 : ℕ) : ZMod P) := by rwa [Nat.cast_ofNat]
  have hβu : IsUnit (β : ZMod P) := by
    rw [Nat.cast_mul] at hub; exact isUnit_of_mul_isUnit_right hub
  have hu2a : IsUnit ((2 * a : ℕ) : ZMod P) := by rw [Nat.cast_mul]; exact hu2'.mul hua
  have hu2b : IsUnit ((2 * (2 * β) : ℕ) : ZMod P) := by rw [Nat.cast_mul]; exact hu2'.mul hub
  have h2a : Nat.Coprime 2 a := Nat.coprime_two_left.2 (Nat.odd_iff.2 hao)
  have hβa : Nat.Coprime β a := Nat.Coprime.coprime_mul_left (hab.symm)
  have haβ : Nat.Coprime a β := hβa.symm
  have ha2b : Nat.Coprime a (2 * (2 * β)) := Nat.Coprime.mul_right h2a.symm hab
  have ham : Nat.Coprime a (a + 2 * β) := Nat.coprime_self_add_right.2 hab
  have hm2 : Nat.Coprime (a + 2 * β) 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))
  have h2am : Nat.Coprime (2 * a) (a + 2 * β) :=
    (Nat.Coprime.mul_right hm2 ham.symm).symm
  have hbm : Nat.Coprime (2 * β) (a + 2 * β) := Nat.coprime_add_self_right.2 hab.symm
  have h2bm : Nat.Coprime (2 * (2 * β)) (a + 2 * β) :=
    (Nat.Coprime.mul_right hm2 hbm.symm).symm
  have h22 : (2 : ZMod P) * Ring.inverse 2 = 1 := Ring.mul_inverse_cancel _ h2
  unfold Ycm
  rw [diag_sum h2 h3 ha hua hT, diag_sum h2 h3 ha2 hu2a hT, diag_sum h2 h3 hb hub hT,
    diag_sum h2 h3 hb2 hu2b hT, diag_sum h2 h3 hm hum hT,
    Ysum_e_two_e h2 h3 ha hua hT, Ysum_two_e_e h2 h3 ha hua hT,
    Ysum_e_two_e h2 h3 hb hub hT, Ysum_two_e_e h2 h3 hb hub hT,
    pair_sum h2 h3 ha hb hab hua hub hT, pair_sum h2 h3 hb ha hab.symm hub hua hT,
    pair_sum h2 h3 ha hb2 ha2b hua hu2b hT, pair_sum h2 h3 hb2 ha ha2b.symm hu2b hua hT,
    pair_sum h2 h3 ha hm ham hua hum hT, pair_sum h2 h3 hm ha ham.symm hum hua hT,
    pair_sum h2 h3 ha2 hm h2am hu2a hum hT, pair_sum h2 h3 hm ha2 h2am.symm hum hu2a hT,
    pair_sum h2 h3 hb hm hbm hub hum hT, pair_sum h2 h3 hm hb hbm.symm hum hub hT,
    pair_sum h2 h3 hb2 hm h2bm hu2b hum hT, pair_sum h2 h3 hm hb2 h2bm.symm hum hu2b hT,
    pair_two h2 h3 ha hβ haβ hua hβu hT, pair_two h2 h3 hβ ha hβa hβu hua hT,
    pair_two h2 h3 ha hb hab hua hub hT, pair_two h2 h3 hb ha hab.symm hub hua hT,
    pt_add_left T a (2 * β), pt_add_right T a (2 * β), pt_neg ham, pt_neg_two h2am]
  simp only [Zf_neg h2 h3 hum]
  by_cases hTe : 2 ∣ T
  · simp only [hTe, ↓reduceIte]
    obtain ⟨T', rfl⟩ := hTe
    rw [Nat.mul_div_cancel_left _ two_pos, pt_half h2a hβa, pt_half h2a hab.symm,
      Zf_scale h2 hβ hab, Zf_scale h2 ha (Nat.Coprime.mul_right hm2 ham.symm),
      Zf_scale h2 hb ha2b, Zf_scale h2 hb (Nat.Coprime.mul_right hm2 hbm.symm),
      pt_add_left T' a (2 * β), pt_add_right T' a (2 * β)]
    linear_combination (4 * (Zf P a (pt T' β a) + Zf P β (pt T' a β)) -
      4 * Ring.inverse (2 : ZMod P) * (Zf P a (pt T' (2 * β) a) +
        Zf P (2 * β) (pt T' a (2 * β)))) * h22
  · simp only [hTe, ↓reduceIte]
    have hTo : T % 2 = 1 := by omega
    have O1 := halves_a h2 h3 ha hao (by omega : (2 * β) % 2 = 0) hTo hab hua
    have O2 := halves_b h2 h3 hb hao (by omega : (2 * β) % 2 = 0) hTo hab hub
    linear_combination (2 * Ring.inverse (2 : ZMod P)) * O1 +
      (2 * Ring.inverse (2 : ZMod P)) * O2 +
      (4 * (Zf P a (pt T (2 * β) a) + Zf P (2 * β) (pt T a (2 * β)))) * h22

end VarCore



/-! ## Theorem 2: the quadratic estimate $v_p([x^T] M^2) \ge v_p(T)$ -/

section

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

theorem isUnit_natCast_padicInt_iff (i : ℕ) : IsUnit (i : ℤ_[p]) ↔ ¬ p ∣ i := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
    Nat.Prime.coprime_iff_not_dvd hp.out]

theorem isUnit_natCast_zmod_iff {e : ℕ} (he : 0 < e) (i : ℕ) :
    IsUnit (i : ZMod (p ^ e)) ↔ ¬ p ∣ i := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff he, Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd hp.out]

omit hp in
theorem inverse_eq_of_mul_eq_one {M : Type*} [CommMonoidWithZero M] {x y : M} (h : x * y = 1) :
    Ring.inverse x = y := by
  have hx : IsUnit x := IsUnit.of_mul_eq_one y h
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [h, mul_one]
    _ = Ring.inverse x * x * y := by rw [mul_assoc]
    _ = y := by rw [Ring.inverse_mul_cancel _ hx, one_mul]

/-- `toZModPow` commutes with `Ring.inverse` on natural numbers. -/
theorem toZModPow_inverse {e : ℕ} (he : 0 < e) (i : ℕ) :
    PadicInt.toZModPow e (Ring.inverse (i : ℤ_[p])) = Ring.inverse (i : ZMod (p ^ e)) := by
  by_cases h : p ∣ i
  · rw [Ring.inverse_non_unit _ (fun hu => (isUnit_natCast_padicInt_iff i).1 hu h),
      Ring.inverse_non_unit _ (fun hu => (isUnit_natCast_zmod_iff he i).1 hu h), map_zero]
  · have h1 : (i : ℤ_[p]) * Ring.inverse (i : ℤ_[p]) = 1 :=
      Ring.mul_inverse_cancel _ ((isUnit_natCast_padicInt_iff i).2 h)
    symm
    apply inverse_eq_of_mul_eq_one
    rw [← map_natCast (PadicInt.toZModPow e : ℤ_[p] →+* ZMod (p ^ e)) i, ← map_mul, h1, map_one]

/-- The coercion `ℤ_[p] → ℚ_[p]` sends `Ring.inverse` of a natural number to its inverse. -/
theorem coe_inverse {i : ℕ} (h : ¬ p ∣ i) :
    ((Ring.inverse (i : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) = (i : ℚ_[p])⁻¹ := by
  have h1 : (i : ℤ_[p]) * Ring.inverse (i : ℤ_[p]) = 1 :=
    Ring.mul_inverse_cancel _ ((isUnit_natCast_padicInt_iff i).2 h)
  apply eq_inv_of_mul_eq_one_right
  rw [← PadicInt.coe_natCast, ← PadicInt.coe_mul, h1, PadicInt.coe_one]

omit hp in
theorem coeff_Vof_mk (c : ℕ → ℤ) (n : ℕ) :
    coeff n (Vof p (mk fun n => (c n : ℚ))) = if p ∣ n then 0 else (c n : ℚ) / n := by
  rw [coeff_Vof]; simp

theorem PI_mk_int (c : ℕ → ℤ) : PI p (mk fun n => (c n : ℚ)) := fun n => by
  rw [coeff_mk]; exact padicNorm.of_int _

/-- The coefficients of $V = \sum_{p \nmid n} c(n) x^n / n$ as `p`-adic integers. -/
def μP (p : ℕ) [Fact p.Prime] (c : ℕ → ℤ) (i : ℕ) : ℤ_[p] :=
  (c i : ℤ_[p]) * Ring.inverse (i : ℤ_[p])

theorem coe_μP (c : ℕ → ℤ) (i : ℕ) :
    ((μP p c i : ℤ_[p]) : ℚ_[p]) = ((coeff i (Vof p (mk fun n => (c n : ℚ))) : ℚ) : ℚ_[p]) := by
  rw [coeff_Vof_mk, μP]
  by_cases h : p ∣ i
  · rw [Ring.inverse_non_unit _ (fun hu => (isUnit_natCast_padicInt_iff i).1 hu h)]
    simp [h]
  · rw [PadicInt.coe_mul, coe_inverse h]
    simp [h, div_eq_mul_inv]

theorem toZModPow_μP {e : ℕ} (he : 0 < e) (c : ℕ → ℤ) (i : ℕ) :
    PadicInt.toZModPow e (μP p c i) = (c i : ZMod (p ^ e)) * Ring.inverse (i : ZMod (p ^ e)) := by
  rw [μP, map_mul, toZModPow_inverse he, map_intCast]

/-- **The bridge from `ZMod` to `ℚ`.** If for $P = p^e \mid T$ ($e \ge 1$) the sum
$\sum_{i + i' = T} c(i) i^{-1}\, c(i') i'^{-1}$ vanishes in `ZMod P`, then
$|[x^T] V^2|_p \le |T|_p$ for $V = \sum_{p \nmid n} c(n) x^n / n$. -/
theorem norm_coeff_Vof_sq_of_core (h5 : 5 ≤ p) (c : ℕ → ℤ) {T : ℕ} (hT0 : T ≠ 0)
    (hcore : ∀ e : ℕ, 0 < e → IsUnit (2 : ZMod (p ^ e)) → IsUnit (3 : ZMod (p ^ e)) →
      (T : ZMod (p ^ e)) = 0 →
      ∑ x ∈ antidiagonal T, ((c x.1 : ZMod (p ^ e)) * Ring.inverse (x.1 : ZMod (p ^ e))) *
        ((c x.2 : ZMod (p ^ e)) * Ring.inverse (x.2 : ZMod (p ^ e))) = 0) :
    padicNorm p (coeff T (Vof p (mk fun n => (c n : ℚ)) ^ 2)) ≤ padicNorm p (T : ℚ) := by
  set e := padicValNat p T with he_def
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · have hT1 : ¬ p ∣ T := by
      intro h
      have := one_le_padicValNat_of_dvd hT0 h
      omega
    rw [(padicNorm.nat_eq_one_iff T).2 hT1]
    exact (((PI_mk_int c).Vof).pow 2) T
  have hu : ∀ x : ℕ, ¬ p ∣ x → IsUnit (x : ZMod (p ^ e)) := fun x hx =>
    (isUnit_natCast_zmod_iff hepos x).2 hx
  have h2 : IsUnit (2 : ZMod (p ^ e)) := by
    have := hu 2 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    rwa [Nat.cast_ofNat] at this
  have h3 : IsUnit (3 : ZMod (p ^ e)) := by
    have := hu 3 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    rwa [Nat.cast_ofNat] at this
  have hT : (T : ZMod (p ^ e)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact pow_padicValNat_dvd
  set S : ℤ_[p] := ∑ x ∈ antidiagonal T, μP p c x.1 * μP p c x.2 with hS
  have hS1 : PadicInt.toZModPow e S = 0 := by
    rw [hS, map_sum]
    simp only [map_mul, toZModPow_μP hepos]
    exact hcore e hepos h2 h3 hT
  have hS2 : (S : ℚ_[p]) = ((coeff T (Vof p (mk fun n => (c n : ℚ)) ^ 2) : ℚ) : ℚ_[p]) := by
    rw [hS, sq, coeff_mul, Rat.cast_sum]
    rw [show ((∑ x ∈ antidiagonal T, μP p c x.1 * μP p c x.2 : ℤ_[p]) : ℚ_[p]) =
      PadicInt.Coe.ringHom (∑ x ∈ antidiagonal T, μP p c x.1 * μP p c x.2) from rfl,
      map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, Rat.cast_mul]
    exact congrArg₂ _ (coe_μP c x.1) (coe_μP c x.2)
  have hmem : S ∈ Ideal.span {(p : ℤ_[p]) ^ e} := by
    rw [← PadicInt.ker_toZModPow]; exact hS1
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow S e).2 hmem
  rw [PadicInt.norm_def, hS2, Padic.eq_padicNorm] at hnorm
  have hTn : padicNorm p (T : ℚ) = (p : ℚ) ^ (-(e : ℤ)) := by
    rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hT0), padicValRat.of_nat]
  rw [hTn]
  have h' : ((padicNorm p (coeff T (Vof p (mk fun n => (c n : ℚ)) ^ 2)) : ℚ) : ℝ) ≤
      (((p : ℚ) ^ (-(e : ℤ)) : ℚ) : ℝ) := by
    rw [Rat.cast_zpow, Rat.cast_natCast]; exact hnorm
  exact_mod_cast h'

/-- A common factor $g$ of the support: if $c(gn) = g^2 c'(n)$ and $c(n) = 0$ for $g \nmid n$,
then $V_c(x) = g\, V_{c'}(x^g)$. -/
theorem Vof_gmul {g : ℕ} (hg : 0 < g) (hpg : ¬ p ∣ g) (c c' : ℕ → ℤ)
    (h1 : ∀ n, c (g * n) = (g : ℤ) ^ 2 * c' n) (h0 : ∀ n, ¬ g ∣ n → c n = 0) :
    Vof p (mk fun n => (c n : ℚ)) = C (g : ℚ) * expand g hg.ne' (Vof p (mk fun n => (c' n : ℚ))) := by
  ext n
  rw [coeff_C_mul, coeff_expand, coeff_Vof_mk]
  split_ifs with hn hgn hgn
  · obtain ⟨m, rfl⟩ := hgn
    rw [Nat.mul_div_cancel_left _ hg, coeff_Vof_mk]
    have : p ∣ m := ((Nat.Prime.dvd_mul hp.out).1 hn).resolve_left hpg
    simp [this]
  · simp
  · obtain ⟨m, rfl⟩ := hgn
    rw [Nat.mul_div_cancel_left _ hg, coeff_Vof_mk]
    have hm : ¬ p ∣ m := fun h => hn (dvd_mul_of_dvd_right h g)
    rw [ite_eq_right hm, h1]
    have hm0 : (m : ℚ) ≠ 0 := by
      have : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
      exact_mod_cast this
    have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    push_cast
    field_simp
  · rw [h0 n hgn]; simp

/-- The quadratic estimate passes from $c'$ to $c$ under `Vof_gmul`. -/
theorem norm_coeff_Vof_sq_gmul {g : ℕ} (hg : 0 < g) (hpg : ¬ p ∣ g) (c c' : ℕ → ℤ)
    (h1 : ∀ n, c (g * n) = (g : ℤ) ^ 2 * c' n) (h0 : ∀ n, ¬ g ∣ n → c n = 0)
    (h' : ∀ T, T ≠ 0 →
      padicNorm p (coeff T (Vof p (mk fun n => (c' n : ℚ)) ^ 2)) ≤ padicNorm p (T : ℚ))
    {T : ℕ} (hT0 : T ≠ 0) :
    padicNorm p (coeff T (Vof p (mk fun n => (c n : ℚ)) ^ 2)) ≤ padicNorm p (T : ℚ) := by
  rw [Vof_gmul hg hpg c c' h1 h0, mul_pow, ← map_pow, ← map_pow, coeff_C_mul, coeff_expand]
  split_ifs with hgT
  · obtain ⟨T', rfl⟩ := hgT
    rw [Nat.mul_div_cancel_left _ hg]
    have hT' : T' ≠ 0 := by rintro rfl; simp at hT0
    have hgn : padicNorm p (g : ℚ) = 1 := (padicNorm.nat_eq_one_iff g).2 hpg
    rw [padicNorm.mul, padicNorm_pow, hgn, one_pow, one_mul]
    push_cast
    rw [padicNorm.mul, hgn, one_mul]
    exact h' T' hT'
  · rw [mul_zero, padicNorm.zero]; exact padicNorm.nonneg _

/-- From $|[x^T] V^2|_p \le |T|_p$ to the form used in `CubicHyp`. -/
theorem quad_of_norm {V : ℚ⟦X⟧} (hV : X ∣ V)
    (h : ∀ T, T ≠ 0 → padicNorm p (coeff T (V ^ 2)) ≤ padicNorm p (T : ℚ)) (j : ℕ) :
    padicNorm p (coeff (p * j) (V ^ 2)) ≤ padicNorm p p * padicNorm p j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have : coeff (p * 0) (V ^ 2) = 0 := by
      rw [mul_zero]; obtain ⟨W, hW⟩ := hV; rw [hW]; simp
    rw [this]; simp
  · have := h (p * j) (Nat.mul_ne_zero hp0 hj.ne')
    rwa [Nat.cast_mul, padicNorm.mul] at this

omit hp in
theorem cf_cast {e : ℕ} (a b i : ℕ) :
    ((cf a b i : ℤ) : ZMod (p ^ e)) * Ring.inverse (i : ZMod (p ^ e)) =
      cZ (p ^ e) a b i * Ring.inverse (i : ZMod (p ^ e)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · congr 1
    simp only [cf, cZ, hi.ne', ite_false]
    split_ifs <;> push_cast <;> ring

/-- **Theorem 2 for coprime $a, b$.** $|[x^T] M^2|_p \le |T|_p$. -/
theorem norm_coeff_Mred_sq_coprime (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) {T : ℕ}
    (hT0 : T ≠ 0) :
    padicNorm p (coeff T (Mred p a b ^ 2)) ≤ padicNorm p (T : ℚ) := by
  refine norm_coeff_Vof_sq_of_core h5 (cf a b) hT0 fun e he h2 h3 hT => ?_
  have hu : ∀ x : ℕ, ¬ p ∣ x → IsUnit (x : ZMod (p ^ e)) := fun x hx =>
    (isUnit_natCast_zmod_iff he x).2 hx
  simp only [cf_cast]
  exact core_sum h2 h3 ha hb hab (hu a hpa) (hu b hpb) (hu (a + b) hpm) hT

theorem cf_gmul {g : ℕ} (hg : 0 < g) (a b n : ℕ) :
    cf (g * a) (g * b) (g * n) = (g : ℤ) ^ 2 * cf a b n := by
  unfold cf
  simp only [mul_eq_zero, hg.ne', false_or, Nat.mul_dvd_mul_iff_left hg,
    show g * a + g * b = g * (a + b) by ring]
  split_ifs <;> push_cast <;> ring

theorem cf_gmul_of_not_dvd {g a b n : ℕ} (h : ¬ g ∣ n) : cf (g * a) (g * b) n = 0 := by
  unfold cf
  have h1 : ¬ g * a ∣ n := fun h' => h (dvd_trans (dvd_mul_right g a) h')
  have h2 : ¬ g * b ∣ n := fun h' => h (dvd_trans (dvd_mul_right g b) h')
  have h3 : ¬ g * a + g * b ∣ n := fun h' => h (dvd_trans (by
    rw [show g * a + g * b = g * (a + b) by ring]; exact dvd_mul_right g _) h')
  simp [h1, h2, h3]

/-- **Theorem 2.** For $a, b \ge 1$ and $p \ge 5$ with $p \nmid ab(a+b)$:
$|[x^T] M^2|_p \le |T|_p$ for every $T \ge 1$. -/
theorem norm_coeff_Mred_sq (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hpa : ¬ p ∣ a)
    (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) {T : ℕ} (hT0 : T ≠ 0) :
    padicNorm p (coeff T (Mred p a b ^ 2)) ≤ padicNorm p (T : ℚ) := by
  set g := Nat.gcd a b with hg_def
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hga : a = g * (a / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hgb : b = g * (b / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  have hpg : ¬ p ∣ g := fun h => hpa (dvd_trans h (Nat.gcd_dvd_left a b))
  have ha0 : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hg
  have hb0 : 0 < b / g := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg
  have hcop : Nat.Coprime (a / g) (b / g) := Nat.coprime_div_gcd_div_gcd hg
  have hpa0 : ¬ p ∣ a / g := fun h => hpa (hga ▸ dvd_mul_of_dvd_right h g)
  have hpb0 : ¬ p ∣ b / g := fun h => hpb (hgb ▸ dvd_mul_of_dvd_right h g)
  have hpm0 : ¬ p ∣ a / g + b / g := fun h => hpm (by
    rw [hga, hgb, show g * (a / g) + g * (b / g) = g * (a / g + b / g) by ring]
    exact dvd_mul_of_dvd_right h g)
  rw [Mred, hga, hgb]
  exact norm_coeff_Vof_sq_gmul hg hpg _ _ (cf_gmul hg (a / g) (b / g))
    (fun n hn => cf_gmul_of_not_dvd hn)
    (fun T' hT' => norm_coeff_Mred_sq_coprime h5 ha0 hb0 hcop hpa0 hpb0 hpm0 hT') hT0

end

end

/-! ## The hypotheses of the criterion for `f` -/

section

variable {p : ℕ} [hp : Fact p.Prime]

theorem cubicHyp_f (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hpa : ¬ p ∣ a)
    (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) : CubicHyp p (fU a b) (Λq a b) where
  const := constantCoeff_f a b
  hasLD := hasLD_fU ha hb
  pint := PI_Λq a b
  per := coeff_Λq_mul hpa hpb hpm
  quad := quad_of_norm (X_dvd_Vof p _) (fun _ hT => norm_coeff_Mred_sq h5 ha hb hpa hpb hpm hT)

end

theorem u_eq_uF (a b r : ℕ) (s : ℤ) (N : ℕ) : u a b r s N = uF (fU a b) r s N := by
  rw [u, zpowSeries_f]; rfl


/-! ## Theorem 4: Bala's variant $f^-$ -/

section

noncomputable section

/-- `1 + X ^ e` as a unit, for `e ≥ 1`. -/
def onePlusU (e : ℕ) (he : 0 < e) : ℤ⟦X⟧ˣ :=
  ⟨1 + X ^ e, invOfUnit (1 + X ^ e) 1, mul_invOfUnit _ 1 (by simp [zero_pow he.ne']),
    invOfUnit_mul _ 1 (by simp [zero_pow he.ne'])⟩

theorem onePlusU_eq {e : ℕ} (he : 0 < e) :
    onePlusU e he = oneSubU (2 * e) (by omega) * (oneSubU e he)⁻¹ := by
  have h1 : (1 - X ^ e : ℤ⟦X⟧) * invOfUnit (1 - X ^ e) 1 = 1 :=
    mul_invOfUnit _ 1 (by simp [zero_pow he.ne'])
  apply Units.ext
  simp only [onePlusU, oneSubU, Units.val_mul, Units.inv_mk]
  linear_combination (-(1 + X ^ e : ℤ⟦X⟧)) * h1

theorem hasLD_onePlusU {e : ℕ} (he : 0 < e) :
    HasLD (ιU (onePlusU e he)) (Le (2 * e) - Le e) := by
  rw [onePlusU_eq he, map_mul, map_inv]
  exact ((hasLD_oneSubU _).mul (hasLD_oneSubU he).inv).congr (by ring)

theorem constantCoeff_fm (a b : ℕ) : constantCoeff (fm a b) = 1 := by
  unfold fm
  simp only [map_mul, map_pow, constantCoeff_invOfUnit, map_sub, map_one, constantCoeff_X,
    inv_one, Units.val_one, one_pow, mul_one]
  rcases Nat.eq_zero_or_pos (a + b) with h | h
  · rw [h]; simp
  · rw [zero_pow h.ne']; simp

/-- `f⁻` as a unit of `ℤ⟦X⟧`. -/
def fmU (a b : ℕ) : ℤ⟦X⟧ˣ :=
  ⟨fm a b, invOfUnit (fm a b) 1, mul_invOfUnit _ 1 (by simp [constantCoeff_fm]),
    invOfUnit_mul _ 1 (by simp [constantCoeff_fm])⟩

theorem fmU_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    fmU a b = oneSubU (a + b) (by omega) ^ (a + b) * (onePlusU a ha)⁻¹ ^ a *
      (onePlusU b hb)⁻¹ ^ b := by
  apply Units.ext
  simp [fmU, onePlusU, oneSubU, fm]

/-- The weights of the variant: for $n \ge 1$,
$c^-(n) = -a^2 [a \mid n] + 2a^2 [2a \mid n] - b^2 [b \mid n] + 2b^2 [2b \mid n] - m^2 [m \mid n]$,
since $(1 + y)^{-e} = (1 - y)^e (1 - y^2)^{-e}$. -/
def cm (a b n : ℕ) : ℤ :=
  if n = 0 then 0 else
    -(if a ∣ n then (a : ℤ) ^ 2 else 0) + (if 2 * a ∣ n then 2 * (a : ℤ) ^ 2 else 0) -
      (if b ∣ n then (b : ℤ) ^ 2 else 0) + (if 2 * b ∣ n then 2 * (b : ℤ) ^ 2 else 0) -
      (if a + b ∣ n then ((a + b : ℕ) : ℤ) ^ 2 else 0)

/-- $\Lambda^- = \theta f^- / f^-$ over `ℚ`. -/
def Λm (a b : ℕ) : ℚ⟦X⟧ := mk fun n => (cm a b n : ℚ)

theorem hasLD_fmU {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : HasLD (ιU (fmU a b)) (Λm a b) := by
  rw [fmU_eq ha hb, map_mul, map_mul, map_pow, map_pow, map_pow, map_inv, map_inv]
  refine ((((hasLD_oneSubU (by omega : 0 < a + b)).pow (a + b)).mul
    (((hasLD_onePlusU ha).inv).pow a)).mul (((hasLD_onePlusU hb).inv).pow b)).congr ?_
  ext n
  simp only [map_add, map_sub, coeff_natCast_mul, map_neg, Le, coeff_mk, Λm, cm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [hn.ne', ne_eq, not_false_eq_true, true_and, ite_false]
    split_ifs <;> push_cast <;> ring

theorem cm_comm (a b n : ℕ) : cm a b n = cm b a n := by
  unfold cm; rw [add_comm b a]; split_ifs <;> ring

theorem cm_gmul {g : ℕ} (hg : 0 < g) (a b n : ℕ) :
    cm (g * a) (g * b) (g * n) = (g : ℤ) ^ 2 * cm a b n := by
  unfold cm
  simp only [mul_eq_zero, hg.ne', false_or, Nat.mul_dvd_mul_iff_left hg,
    show g * a + g * b = g * (a + b) by ring, show 2 * (g * a) = g * (2 * a) by ring,
    show 2 * (g * b) = g * (2 * b) by ring]
  split_ifs <;> push_cast <;> ring

theorem cm_gmul_of_not_dvd {g a b n : ℕ} (h : ¬ g ∣ n) : cm (g * a) (g * b) n = 0 := by
  unfold cm
  have h1 : ¬ g * a ∣ n := fun h' => h (dvd_trans (dvd_mul_right g a) h')
  have h2 : ¬ g * b ∣ n := fun h' => h (dvd_trans (dvd_mul_right g b) h')
  have h3 : ¬ g * a + g * b ∣ n := fun h' => h (dvd_trans (by
    rw [show g * a + g * b = g * (a + b) by ring]; exact dvd_mul_right g _) h')
  have h4 : ¬ 2 * (g * a) ∣ n := fun h' => h (dvd_trans (by
    rw [show 2 * (g * a) = g * (2 * a) by ring]; exact dvd_mul_right g _) h')
  have h5 : ¬ 2 * (g * b) ∣ n := fun h' => h (dvd_trans (by
    rw [show 2 * (g * b) = g * (2 * b) by ring]; exact dvd_mul_right g _) h')
  simp [h1, h2, h3, h4, h5]

/-- For odd $a, b$: $c^-(n) = (-1)^n c(n)$, since $f^-(x) = f(-x)$. -/
theorem cm_odd {a b : ℕ} (hao : a % 2 = 1) (hbo : b % 2 = 1) (n : ℕ) :
    cm a b n = (-1) ^ n * cf a b n := by
  unfold cm cf
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  simp only [hn.ne', ite_false]
  have h2a : Nat.Coprime 2 a := Nat.coprime_two_left.2 (Nat.odd_iff.2 hao)
  have h2b : Nat.Coprime 2 b := Nat.coprime_two_left.2 (Nat.odd_iff.2 hbo)
  rcases Nat.even_or_odd n with he | ho
  · have ea : 2 * a ∣ n ↔ a ∣ n := ⟨fun h => dvd_trans (dvd_mul_left a 2) h,
      fun h => Nat.Coprime.mul_dvd_of_dvd_of_dvd h2a (even_iff_two_dvd.1 he) h⟩
    have eb : 2 * b ∣ n ↔ b ∣ n := ⟨fun h => dvd_trans (dvd_mul_left b 2) h,
      fun h => Nat.Coprime.mul_dvd_of_dvd_of_dvd h2b (even_iff_two_dvd.1 he) h⟩
    rw [he.neg_one_pow, one_mul]
    simp only [ea, eb]
    split_ifs <;> ring
  · have hno : ¬ 2 ∣ n := fun h => (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 h)
    have na : ¬ 2 * a ∣ n := fun h => hno (dvd_trans (dvd_mul_right 2 a) h)
    have nb : ¬ 2 * b ∣ n := fun h => hno (dvd_trans (dvd_mul_right 2 b) h)
    have nm : ¬ a + b ∣ n := fun h => hno (dvd_trans (show 2 ∣ a + b by omega) h)
    rw [ho.neg_one_pow]
    simp only [na, nb, nm, ite_false]
    split_ifs <;> ring

theorem cm_cast {P : ℕ} (h22 : (2 : ZMod P) * Ring.inverse 2 = 1) (a b i : ℕ) :
    ((cm a b i : ℤ) : ZMod P) * Ring.inverse (i : ZMod P) =
      cmZ P a b i * Ring.inverse (i : ZMod P) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · congr 1
    have key : ∀ x : ZMod P, Ring.inverse 2 * (2 * x) ^ 2 = 2 * x ^ 2 := fun x => by
      linear_combination (2 * x ^ 2) * h22
    simp only [cm, cmZ, hi.ne', ite_false, mul_ite, mul_zero, Nat.cast_mul, Nat.cast_ofNat, key]
    split_ifs <;> push_cast <;> ring

end

end

section

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

theorem cm_mul (h5 : 5 ≤ p) {a b : ℕ} (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b)
    (m : ℕ) : cm a b (p * m) = cm a b m := by
  have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h2a : ¬ p ∣ 2 * a := fun h => ((Nat.Prime.dvd_mul hp.out).1 h).elim hp2 hpa
  have h2b : ¬ p ∣ 2 * b := fun h => ((Nat.Prime.dvd_mul hp.out).1 h).elim hp2 hpb
  unfold cm
  simp only [mul_eq_zero, hp0, false_or, dvd_mul_iff_of_not_dvd hpa,
    dvd_mul_iff_of_not_dvd hpb, dvd_mul_iff_of_not_dvd hpm, dvd_mul_iff_of_not_dvd h2a,
    dvd_mul_iff_of_not_dvd h2b]

omit hp in
theorem coeff_sq_neg_one_pow {V W : ℚ⟦X⟧} (h : ∀ n, coeff n V = (-1) ^ n * coeff n W)
    (T : ℕ) : coeff T (V ^ 2) = (-1) ^ T * coeff T (W ^ 2) := by
  rw [sq, sq, coeff_mul, coeff_mul, mul_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [h, h, ← (mem_antidiagonal.1 hx), pow_add]; ring

/-- Theorem 2 for the variant, $a$ odd and $b$ even, coprime. -/
theorem norm_coeff_Mm_sq_mixed (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hao : a % 2 = 1) (hbe : b % 2 = 0) (hab : Nat.Coprime a b) (hpa : ¬ p ∣ a)
    (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) {T : ℕ} (hT0 : T ≠ 0) :
    padicNorm p (coeff T (Vof p (Λm a b) ^ 2)) ≤ padicNorm p (T : ℚ) := by
  refine norm_coeff_Vof_sq_of_core h5 (cm a b) hT0 fun e he h2 h3 hT => ?_
  have hu : ∀ x : ℕ, ¬ p ∣ x → IsUnit (x : ZMod (p ^ e)) := fun x hx =>
    (isUnit_natCast_zmod_iff he x).2 hx
  have h22 : (2 : ZMod (p ^ e)) * Ring.inverse 2 = 1 := Ring.mul_inverse_cancel _ h2
  simp only [cm_cast h22]
  exact core_var h2 h3 ha (β := b / 2) (by omega) (by omega) hao hab (hu a hpa) (hu b hpb)
    (hu (a + b) hpm) hT

/-- Theorem 2 for the variant, $a, b$ coprime. -/
theorem norm_coeff_Mm_sq_coprime (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) {T : ℕ}
    (hT0 : T ≠ 0) :
    padicNorm p (coeff T (Vof p (Λm a b) ^ 2)) ≤ padicNorm p (T : ℚ) := by
  rcases Nat.mod_two_eq_zero_or_one a with hae | hao <;>
    rcases Nat.mod_two_eq_zero_or_one b with hbe | hbo
  · exfalso
    have h2 : 2 ∣ Nat.gcd a b := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hae)
      (Nat.dvd_of_mod_eq_zero hbe)
    rw [hab] at h2; exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
  · have hsymm : Λm a b = Λm b a := by ext n; simp only [Λm, coeff_mk, cm_comm a b n]
    rw [hsymm]
    exact norm_coeff_Mm_sq_mixed h5 hb ha hbo hae hab.symm hpb hpa (by rwa [add_comm]) hT0
  · exact norm_coeff_Mm_sq_mixed h5 ha hb hao hbe hab hpa hpb hpm hT0
  · have h : ∀ n, coeff n (Vof p (Λm a b)) = (-1) ^ n * coeff n (Mred p a b) := by
      intro n
      rw [Mred, Λm, Λq, coeff_Vof_mk, coeff_Vof_mk, cm_odd hao hbo]
      split_ifs <;> push_cast <;> ring
    rw [coeff_sq_neg_one_pow h, padicNorm.mul, padicNorm_pow, padicNorm.neg, padicNorm.one,
      one_pow, one_mul]
    exact norm_coeff_Mred_sq_coprime h5 ha hb hab hpa hpb hpm hT0

/-- **Theorem 2 for the variant.** For $a, b \ge 1$ and $p \ge 5$ with $p \nmid ab(a+b)$:
$|[x^T] (M^-)^2|_p \le |T|_p$ for every $T \ge 1$. -/
theorem norm_coeff_Mm_sq (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hpa : ¬ p ∣ a)
    (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) {T : ℕ} (hT0 : T ≠ 0) :
    padicNorm p (coeff T (Vof p (Λm a b) ^ 2)) ≤ padicNorm p (T : ℚ) := by
  set g := Nat.gcd a b with hg_def
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hga : a = g * (a / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hgb : b = g * (b / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  have hpg : ¬ p ∣ g := fun h => hpa (dvd_trans h (Nat.gcd_dvd_left a b))
  have ha0 : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hg
  have hb0 : 0 < b / g := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg
  have hcop : Nat.Coprime (a / g) (b / g) := Nat.coprime_div_gcd_div_gcd hg
  have hpa0 : ¬ p ∣ a / g := fun h => hpa (hga ▸ dvd_mul_of_dvd_right h g)
  have hpb0 : ¬ p ∣ b / g := fun h => hpb (hgb ▸ dvd_mul_of_dvd_right h g)
  have hpm0 : ¬ p ∣ a / g + b / g := fun h => hpm (by
    rw [hga, hgb, show g * (a / g) + g * (b / g) = g * (a / g + b / g) by ring]
    exact dvd_mul_of_dvd_right h g)
  rw [Λm, hga, hgb]
  exact norm_coeff_Vof_sq_gmul hg hpg _ _ (cm_gmul hg (a / g) (b / g))
    (fun n hn => cm_gmul_of_not_dvd hn)
    (fun T' hT' => norm_coeff_Mm_sq_coprime h5 ha0 hb0 hcop hpa0 hpb0 hpm0 hT') hT0

theorem cubicHyp_fm (h5 : 5 ≤ p) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hpa : ¬ p ∣ a)
    (hpb : ¬ p ∣ b) (hpm : ¬ p ∣ a + b) : CubicHyp p (fmU a b) (Λm a b) where
  const := constantCoeff_fm a b
  hasLD := hasLD_fmU ha hb
  pint := PI_mk_int (cm a b)
  per := fun m => by simp only [Λm, coeff_mk, cm_mul h5 hpa hpb hpm]
  quad := quad_of_norm (X_dvd_Vof p _) (fun _ hT => norm_coeff_Mm_sq h5 ha hb hpa hpb hpm hT)

end

end

theorem um_eq_uF (a b r : ℕ) (s : ℤ) (N : ℕ) : um a b r s N = uF (fmU a b) r s N := by
  rw [um, show fm a b = ((fmU a b : ℤ⟦X⟧ˣ) : ℤ⟦X⟧) from rfl, zpowSeries_eq (fmU a b) rfl]; rfl


/-! ## The towers -/

/-- **The general family.** Let $a, b \ge 1$ and let $p \ge 5$ be a prime with $p \nmid ab(a+b)$.
Then for every $r \ge 1$, every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u_{r,s}(np^k) \equiv u_{r,s}(np^{k-1}) \pmod{p^{3k}}$. -/
theorem u_tower (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hpab : ¬ p ∣ a * b * (a + b)) (r : ℕ) (hr : 0 < r) (s : ℤ) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u a b r s (n * p ^ k) - u a b r s (n * p ^ (k - 1)) := by
  have := Fact.mk hp
  have _ := hr
  have _ := hn
  have hpa : ¬ p ∣ a := fun h => hpab (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) _)
  have hpb : ¬ p ∣ b := fun h => hpab (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) _)
  have hpm : ¬ p ∣ a + b := fun h => hpab (dvd_mul_of_dvd_right h _)
  rw [u_eq_uF, u_eq_uF]
  exact uF_tower h5 (cubicHyp_f h5 ha hb hpa hpb hpm) r s n k hk

/-! ## The named sequences -/

theorem not_dvd_of_pos_lt {p c : ℕ} (hc : 0 < c) (h : c < p) : ¬ p ∣ c :=
  Nat.not_dvd_of_pos_of_lt hc h

theorem f372211_eq : f372211 = f 2 3 := rfl

theorem f372212_eq : f372212 = f 2 5 := rfl

theorem f372213_eq : f372213 = f 3 4 := rfl

theorem A_eq (F : PowerSeries ℤ) (n : ℕ) :
    coeff n (F ^ n) = coeff (1 * n) (zpowSeries F (1 * (n : ℤ))) := by
  simp [zpowSeries]

theorem A372211_eq (n : ℕ) : A372211 n = u372211 1 1 n := by rw [u372211, ← A_eq]; rfl

theorem A372212_eq (n : ℕ) : A372212 n = u372212 1 1 n := by rw [u372212, ← A_eq]; rfl

theorem A372213_eq (n : ℕ) : A372213 n = u372213 1 1 n := by rw [u372213, ← A_eq]; rfl

theorem not_dvd_prod {p a b : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    (hm : ¬ p ∣ a + b) : ¬ p ∣ a * b * (a + b) := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact ha h
    · exact hb h
  · exact hm h

/-- **A372211**, the conjecture for $u(r,s;n)$: for every prime $p \ge 7$, every $r \ge 1$,
every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u(r,s;np^k) \equiv u(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
theorem u372211_tower (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u372211 r s (n * p ^ k) - u372211 r s (n * p ^ (k - 1)) :=
  u_tower 2 3 (by norm_num) (by norm_num) p hp (by omega)
    (not_dvd_prod hp (not_dvd_of_pos_lt (by norm_num) (by omega))
      (not_dvd_of_pos_lt (by norm_num) (by omega)) (not_dvd_of_pos_lt (by norm_num) (by omega)))
    r hr s n k hn hk

/-- **A372211**, the main conjecture for primes $p \ge 7$:
$a(np^k) \equiv a(np^{k-1}) \pmod{p^{3k}}$ for all $n, k \ge 1$. -/
theorem a372211_tower (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A372211 (n * p ^ k) - A372211 (n * p ^ (k - 1)) := by
  rw [A372211_eq, A372211_eq]
  exact u372211_tower p hp h7 1 one_pos 1 n k hn hk

/-- **A372212**, the conjecture for $u(r,s;n)$: for every prime $p \ge 11$, every $r \ge 1$,
every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u(r,s;np^k) \equiv u(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
theorem u372212_tower (p : ℕ) (hp : p.Prime) (h11 : 11 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u372212 r s (n * p ^ k) - u372212 r s (n * p ^ (k - 1)) :=
  u_tower 2 5 (by norm_num) (by norm_num) p hp (by omega)
    (not_dvd_prod hp (not_dvd_of_pos_lt (by norm_num) (by omega))
      (not_dvd_of_pos_lt (by norm_num) (by omega)) (not_dvd_of_pos_lt (by norm_num) (by omega)))
    r hr s n k hn hk

/-- **A372212**, the main conjecture: for every prime $p \ge 11$ and all $n, k \ge 1$:
$a(np^k) \equiv a(np^{k-1}) \pmod{p^{3k}}$. -/
theorem a372212_tower (p : ℕ) (hp : p.Prime) (h11 : 11 ≤ p) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A372212 (n * p ^ k) - A372212 (n * p ^ (k - 1)) := by
  rw [A372212_eq, A372212_eq]
  exact u372212_tower p hp h11 1 one_pos 1 n k hn hk

theorem not_dvd_seven {p : ℕ} (hp : p.Prime) (h7 : p ≠ 7) : ¬ p ∣ 3 + 4 := fun h =>
  h7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)

/-- **A372213**, the conjecture for $u(r,s;n)$: for every prime $p \ge 5$ with $p \ne 7$ (Bala
asks for $p \ge 11$), every $r \ge 1$, every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u(r,s;np^k) \equiv u(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
theorem u372213_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) (r : ℕ) (hr : 0 < r)
    (s : ℤ) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ u372213 r s (n * p ^ k) - u372213 r s (n * p ^ (k - 1)) :=
  u_tower 3 4 (by norm_num) (by norm_num) p hp h5
    (not_dvd_prod hp (not_dvd_of_pos_lt (by norm_num) (by omega))
      (not_dvd_of_pos_lt (by norm_num) (by omega)) (not_dvd_seven hp h7))
    r hr s n k hn hk

/-- **A372213**, the main conjecture: for every prime $p \ge 5$ with $p \ne 7$ (Bala asks for
$p \ge 11$) and all $n, k \ge 1$: $a(np^k) \equiv a(np^{k-1}) \pmod{p^{3k}}$. -/
theorem a372213_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A372213 (n * p ^ k) - A372213 (n * p ^ (k - 1)) := by
  rw [A372213_eq, A372213_eq]
  exact u372213_tower p hp h5 h7 1 one_pos 1 n k hn hk

/-- $G_3 = f_{1,3}$: $(1 + x + x^2 + x^3)^4/(1 + x + x^2)^3 = (1 - x^4)^4/((1 - x)(1 - x^3)^3)$. -/
theorem G3_eq : G3 = f 1 3 := by
  have h1 : (1 - X : ℤ⟦X⟧) * invOfUnit (1 - X) 1 = 1 := mul_invOfUnit _ 1 (by simp)
  have h3 : (1 - X ^ 3 : ℤ⟦X⟧) * invOfUnit (1 - X ^ 3) 1 = 1 := mul_invOfUnit _ 1 (by simp)
  have hJ : (1 + X + X ^ 2 : ℤ⟦X⟧) * invOfUnit (1 + X + X ^ 2) 1 = 1 :=
    mul_invOfUnit _ 1 (by simp)
  have hJ' : invOfUnit (1 + X + X ^ 2 : ℤ⟦X⟧) 1 = (1 - X) * invOfUnit (1 - X ^ 3) 1 := by
    linear_combination (-invOfUnit (1 + X + X ^ 2 : ℤ⟦X⟧) 1) * h3 +
      ((1 - X) * invOfUnit (1 - X ^ 3 : ℤ⟦X⟧) 1) * hJ
  unfold G3 f
  rw [hJ']
  simp only [show (1 : ℕ) + 3 = 4 from rfl, pow_one]
  linear_combination (-((1 + X + X ^ 2 + X ^ 3) ^ 4 * (1 - X) ^ 3 *
    invOfUnit (1 - X ^ 3 : ℤ⟦X⟧) 1 ^ 3)) * h1

theorem a351859_eq (r : ℕ) (s : ℤ) (n : ℕ) : a351859 r s n = u 1 3 r s n := by
  rw [a351859, u, G3_eq]

theorem A351859_eq (n : ℕ) : A351859 n = a351859 1 1 n := by
  rw [a351859, ← A_eq, G3, mul_pow, ← pow_mul, ← pow_mul]; rfl

/-- **A351859**, the conjecture for $a(r,s;n)$: for every prime $p \ge 5$, every $r \ge 1$,
every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$a(r,s;np^k) \equiv a(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
theorem a351859_rs_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ a351859 r s (n * p ^ k) - a351859 r s (n * p ^ (k - 1)) := by
  rw [a351859_eq, a351859_eq]
  exact u_tower 1 3 (by norm_num) (by norm_num) p hp h5
    (not_dvd_prod hp (not_dvd_of_pos_lt (by norm_num) (by omega))
      (not_dvd_of_pos_lt (by norm_num) (by omega)) (not_dvd_of_pos_lt (by norm_num) (by omega)))
    r hr s n k hn hk

/-- **A351859**, the main conjecture: for every prime $p \ge 5$ and all $n, k \ge 1$:
$a(np^k) \equiv a(np^{k-1}) \pmod{p^{3k}}$. -/
theorem a351859_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ A351859 (n * p ^ k) - A351859 (n * p ^ (k - 1)) := by
  rw [A351859_eq, A351859_eq]
  exact a351859_rs_tower p hp h5 1 one_pos 1 n k hn hk

/-- **A372211, the general clause** for $f_{a,b}$, read as $[x^n]\, f_{a,b}(x)^n$: for every
$m$ there is $P_0$ such that for all $a, b \ge 1$ with $a + b = m$, every prime $p \ge P_0$ and
all $n, k \ge 1$: $[x^{np^k}]\, f^{np^k} \equiv [x^{np^{k-1}}]\, f^{np^{k-1}} \pmod{p^{3k}}$. -/
theorem general_tower (m : ℕ) :
    ∃ P₀ : ℕ, ∀ a b : ℕ, 0 < a → 0 < b → a + b = m → ∀ p : ℕ, p.Prime → P₀ ≤ p →
      ∀ n k : ℕ, 0 < n → 0 < k →
        (p : ℤ) ^ (3 * k) ∣ coeff (n * p ^ k) (f a b ^ (n * p ^ k)) -
          coeff (n * p ^ (k - 1)) (f a b ^ (n * p ^ (k - 1))) := by
  refine ⟨m + 5, fun a b ha hb hm p hp hP n k hn hk => ?_⟩
  rw [A_eq, A_eq]
  exact u_tower a b ha hb p hp (by omega) (not_dvd_prod hp (not_dvd_of_pos_lt ha (by omega))
    (not_dvd_of_pos_lt hb (by omega)) (not_dvd_of_pos_lt (by omega) (by omega))) 1 one_pos 1 n k
    hn hk


/-- **The variant family.** Let $a, b \ge 1$ and let $p \ge 5$ be a prime with
$p \nmid ab(a+b)$. Then for every $r \ge 1$, every $s \in \mathbb{Z}$ and all $n, k \ge 1$:
$u^-_{r,s}(np^k) \equiv u^-_{r,s}(np^{k-1}) \pmod{p^{3k}}$. -/
theorem um_tower (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hpab : ¬ p ∣ a * b * (a + b)) (r : ℕ) (hr : 0 < r) (s : ℤ) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ um a b r s (n * p ^ k) - um a b r s (n * p ^ (k - 1)) := by
  have := Fact.mk hp
  have _ := hr
  have _ := hn
  have hpa : ¬ p ∣ a := fun h => hpab (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) _)
  have hpb : ¬ p ∣ b := fun h => hpab (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) _)
  have hpm : ¬ p ∣ a + b := fun h => hpab (dvd_mul_of_dvd_right h _)
  rw [um_eq_uF, um_eq_uF]
  exact uF_tower h5 (cubicHyp_fm h5 ha hb hpa hpb hpm) r s n k hk

/-- **A372211, the general clause** for $f^-_{a,b}$, read as $[x^n]\, f^-_{a,b}(x)^n$: for every
$m$ there is $P_0$ such that for all $a, b \ge 1$ with $a + b = m$, every prime $p \ge P_0$ and
all $n, k \ge 1$: $[x^{np^k}]\, (f^-)^{np^k} \equiv [x^{np^{k-1}}]\, (f^-)^{np^{k-1}}
\pmod{p^{3k}}$. -/
theorem general_variant_tower (m : ℕ) :
    ∃ P₀ : ℕ, ∀ a b : ℕ, 0 < a → 0 < b → a + b = m → ∀ p : ℕ, p.Prime → P₀ ≤ p →
      ∀ n k : ℕ, 0 < n → 0 < k →
        (p : ℤ) ^ (3 * k) ∣ coeff (n * p ^ k) (fm a b ^ (n * p ^ k)) -
          coeff (n * p ^ (k - 1)) (fm a b ^ (n * p ^ (k - 1))) := by
  refine ⟨m + 5, fun a b ha hb hm p hp hP n k hn hk => ?_⟩
  rw [A_eq, A_eq]
  exact um_tower a b ha hb p hp (by omega) (not_dvd_prod hp (not_dvd_of_pos_lt ha (by omega))
    (not_dvd_of_pos_lt hb (by omega)) (not_dvd_of_pos_lt (by omega) (by omega))) 1 one_pos 1 n k
    hn hk

/-! ## Sanity checks -/

/-- For $a = b = 1$, $f = (1 - x^2)^2/(1 - x)^2 = (1 + x)^2$. -/
theorem f_one_one : f 1 1 = (1 + X) ^ 2 := by
  have h1 : (1 - X : ℤ⟦X⟧) * invOfUnit (1 - X) 1 = 1 := mul_invOfUnit _ 1 (by simp)
  unfold f
  simp only [pow_one, show (1 : ℕ) + 1 = 2 from rfl]
  linear_combination ((1 + X) ^ 2 * ((1 - X) * invOfUnit (1 - X : ℤ⟦X⟧) 1 + 1)) * h1

/-- For $a = b = 1$, $u_{1,1}(n) = \binom{2n}{n}$, the central binomial coefficients (A000984),
as the entry A372211 notes. -/
theorem u_one_one (n : ℕ) : u 1 1 1 1 n = ((2 * n).choose n : ℤ) := by
  rw [u, f_one_one, one_mul, one_mul]
  simp only [zpowSeries, Nat.cast_nonneg, ite_true, Int.toNat_natCast]
  rw [← pow_mul]
  have : (1 + X : ℤ⟦X⟧) = ((1 + Polynomial.X : Polynomial ℤ) : ℤ⟦X⟧) := by simp
  rw [this, ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- For $a = b = 1$, $f^- = (1 - x^2)^2/(1 + x)^2 = (1 - x)^2$. -/
theorem fm_one_one : fm 1 1 = (1 - X) ^ 2 := by
  have h1 : (1 + X : ℤ⟦X⟧) * invOfUnit (1 + X) 1 = 1 := mul_invOfUnit _ 1 (by simp)
  unfold fm
  simp only [pow_one, show (1 : ℕ) + 1 = 2 from rfl]
  linear_combination ((1 - X) ^ 2 * ((1 + X) * invOfUnit (1 + X : ℤ⟦X⟧) 1 + 1)) * h1

end OeisA372211

end
