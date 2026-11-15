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
# OEIS A340882 and A340883: Bala's pre-period conjectures

For an integer $q$ put $x = 1 + q$ and $R(n) = R(n, q) = \sum_{k<n} x^{k^2}
\prod_{j=k+1}^{n-1} (x^{2j} - 1)$; A340883 is $a(n) = R(n, 1)$. The file proves:
- A340882 is false, and it holds for a given $q$ and every $N \ge 1$ exactly when
  $q \in \{-2, -1, 0\}$; for $q \ne -1$ and a prime $p \mid x$ it fails at
  $N = p^{5 v_p(x) + 1}$;
- the exact pre-period $P(q, N)$ of $R(\cdot, q)$ modulo $N$ (Corollary 5), and the criterion
  "A340882 holds for $(q, N)$ iff $x = 0$ or $v_p(N) \le 5 v_p(x)$ for all $p \mid (N, x)$";
- A340883 conjecture 1) is false at $m = 64$; its pre-period part holds iff $64 \nmid m$; and
  $a(n + \varphi(m)) \equiv a(n) \pmod m$ for $n > P(1, m)$, so the period part always holds;
- A340883 conjecture 2): for coprime $m_1, m_2$ the least eventual period modulo $m_1 m_2$ is the
  lcm of those modulo $m_1$ and $m_2$.

*Set-up.* `S x n` is the row polynomial at an element of a commutative ring, so
$R(n, q) = $ `S (1 + q) n` and $a(n) = $ `S 2 n` by definition. Splitting off $k = n$ gives
Lemma 1, $R(n+1) = (x^{2n} - 1) R(n) + x^{n^2}$ (`S_succ`), and closed forms of $R(2), R(3), R(4)$.

*Lemma 0.* A multiple of an eventual period is a period from the same start (`per_mul`). If $L$
is a period from $n_0$ and $L' \ge 1$ is a period from $n_0'$, then $L$ is a period from $n_0'$
(`start_indep`): for $n > n_0'$, $s(n+L) \equiv s(n+L+n_0L') \equiv s(n+n_0L') \equiv s(n)$.
A congruence modulo every $p^{v_p(N)}$ holds modulo $N$ (`modEq_of_forall_primeFactors`, via
`Nat.factorization_prime_le_iff_dvd`).

*Theorem 3 ($p \nmid x$).* In a commutative ring with $y^o = 1$ and $n \ge 1$, the terms
$k < o$ of $R(o + n)$ vanish, since the product over $j \in [k+1, o+n-1]$ contains
$y^{2o} - 1 = 0$; the term $k = o + k'$ equals the term $k'$ of $R(n)$, since
$y^{(o+k')^2} = y^{k'^2}$ and $j \mapsto j + o$ reindexes the product (`S_add_period`). For
$p \nmid x$, Euler's theorem in `ZMod (p ^ e)` gives $x^{\varphi(p^e)} = 1$, so $R$ is purely
periodic modulo $p^e$ with period $\varphi(p^e)$ (`local_of_not_dvd`).

*Theorem 4 ($p \mid x$, $x \ne 0$, $v = v_p(x)$).* By induction, $R(n+1) \equiv (-1)^n
\pmod x$ (`S_succ_sub_dvd`). Then $R(n+2) - R(n) = x^{c(n)} U$ with $c(1) = 1$, $c(2) = 5$,
$c(n) = 2n$ for $n \ge 3$: $R(3) - R(1) = x (x+1)(x^4-1)$,
$R(4) - R(2) = x^5 (x^7 + x^6 + x^4 - x^3 - x^2 - 1)$, and for $n \ge 3$, Lemma 1 twice gives
$U = (x^{2n+2} - x^2 - 1) R(n) + x^{n^2 - 2n} (x^{2n+2} + x^{2n+1} - 1)$. In each case
$U \equiv \pm 1 \pmod p$, so $p^e \mid R(n+2) - R(n)$ iff $e \le c(n) v$ (`dvd_D_iff`, with
`padicValInt`). Arithmetic on `localPrePeriod` shows that $e \le c(n) v$ for every
$n > f(e, v)$ and fails at $n = f(e, v)$ when $f(e, v) \ge 1$ (`cexp_ge`, `cexp_lt`). So $2$ is
a period from $f(e, v)$, and by Lemma 0 no period works from any $n_0 < f(e, v)$, as it would
make $2$ a period from $n_0$ (`local_iff_of_dvd`). For $x = 0$, $R(n) = (-1)^{n-1}$ has
period $2$ from the start (`local_iff`).

*Corollary 5* (`prePeriod_spec`). If $L$ works modulo $N$, it works modulo each $p^{v_p(N)}$, so
each local pre-period is at most $n_0$, and so is their maximum (`prePeriod_le_iff`). Conversely
the product of the local periods is a multiple of each, hence a period modulo each $p^{v_p(N)}$
from $n_0$, hence modulo $N$. The criteria follow from $f(e, v) \le 1 \iff e \le 5v$
(`localPrePeriod_le_one_iff`), from $v_p(p^{5v+1}) = 5v + 1$, and from the existence of a prime
factor of $x \notin \{-1, 0, 1\}$. The literal refutation of A340882 is the case $q = 1$.

*A340883.* For $n \ge 3$, $64 \mid 2^{2n}$ and $64 \mid 2^{n^2}$, so $a(n+1) \equiv -a(n)
\pmod{64}$; with $a(3) = 91$ and $a(4) = 6245$ this gives $27, 37, 27, \dots$ from $n = 3$,
while $a(2) = 5$. The corrected pre-period part is Corollary 5 at $x = 2$, $v_2(2) = 1$. For the
period part take $p^e \parallel m$: for odd $p$, $\varphi(p^e) \mid \varphi(m)$ is a period from
the start; for $p = 2$ and $e \ge 2$, $2 \mid \varphi(2^e) \mid \varphi(m)$ and $2$ is a period
from $f(e, 1) \le P(1, m)$; for $p = 2$ and $e = 1$, every $a(n)$ is odd. The Chinese remainder
step gives $a(n + \varphi(m)) \equiv a(n) \pmod m$ for $n > P(1, m)$.

*Conjecture 2).* For $m \ge 1$ the eventual periods modulo $m$ form a nonempty set, as
$\varphi(m)$ is one, so the least one exists. Every eventual period $L$ is a multiple of the
least one $P$: otherwise $L \bmod P$ would be a smaller eventual period, by `per_mul` with
$\lfloor L/P \rfloor$ copies of $P$ (`mem_EP_iff`). For coprime $m_1, m_2$, $L$ is an eventual
period modulo $m_1 m_2$ iff it is one modulo $m_1$ and modulo $m_2$
(`Int.modEq_and_modEq_iff_modEq_mul`). So the two sides divide each other. If $m_1 m_2 = 0$, the
other modulus is $1$, whose period is $1$.

The sanity checks at the end verify the rows $R(1), R(2), R(3)$ from the comment of A340882 and
the first six terms of A340883.
-/

@[expose] public section

namespace OeisA340882

open Finset

/-- OEIS A340882, row $n$: $R(n, q) = \sum_{k=0}^{n-1} x^{k^2} \prod_{j=k+1}^{n-1}
(x^{2j} - 1)$ with $x = 1 + q$ (the FORMULA line). -/
def R (n : ℕ) (q : ℤ) : ℤ :=
  ∑ k ∈ range n, (1 + q) ^ (k ^ 2) * ∏ j ∈ Ico (k + 1) n, ((1 + q) ^ (2 * j) - 1)

/-- OEIS A340883: $a(n) = \sum_{k=0}^{n-1} 2^{k^2} \prod_{j=k+1}^{n-1} (2^{2j} - 1)$, the row
sums $R(n, 1)$ of A340882. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ range n, 2 ^ (k ^ 2) * ∏ j ∈ Ico (k + 1) n, (2 ^ (2 * j) - 1)

/-- The pre-period of $R(\cdot, q)$ modulo $p^e$ for a prime $p$ with $v = v_p(1 + q) \ge 1$:
$0$ if $e \le v$, $1$ if $v < e \le 5v$, and $\lfloor (e-1)/(2v) \rfloor$ if $e > 5v$. -/
def localPrePeriod (e v : ℕ) : ℕ :=
  if e ≤ v then 0 else if e ≤ 5 * v then 1 else (e - 1) / (2 * v)

/-- The pre-period of $R(\cdot, q)$ modulo $N$: the maximum of `localPrePeriod` over the primes
$p \mid N$ with $p \mid 1 + q$, and $0$ when $1 + q = 0$. -/
def prePeriod (q : ℤ) (N : ℕ) : ℕ :=
  if 1 + q = 0 then 0 else
    (N.primeFactors.filter (fun p : ℕ => (p : ℤ) ∣ 1 + q)).sup
      (fun p => localPrePeriod (N.factorization p) (padicValInt p (1 + q)))

/-! ### The row polynomial over a commutative ring -/

section Ring

variable {A : Type*} [CommRing A]

/-- The row polynomial at an element `x` of a commutative ring. -/
def S (x : A) (n : ℕ) : A :=
  ∑ k ∈ range n, x ^ (k ^ 2) * ∏ j ∈ Ico (k + 1) n, (x ^ (2 * j) - 1)

lemma S_zero (x : A) : S x 0 = 0 := by simp [S]

/-- Lemma 1: $R(n+1) = (x^{2n} - 1) R(n) + x^{n^2}$. -/
lemma S_succ (x : A) (n : ℕ) : S x (n + 1) = (x ^ (2 * n) - 1) * S x n + x ^ (n ^ 2) := by
  rw [S, sum_range_succ, Ico_self, prod_empty, mul_one, S, mul_sum]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [prod_Ico_succ_top (by simp at hk; omega)]
  ring

lemma S_one (x : A) : S x 1 = 1 := by simp [S]

lemma S_two (x : A) : S x 2 = x ^ 2 + x - 1 := by
  rw [S_succ x 1, S_one]; ring

lemma S_three (x : A) : S x 3 = x ^ 6 + x ^ 5 - x ^ 2 - x + 1 := by
  rw [S_succ x 2, S_two]; ring

lemma S_four (x : A) :
    S x 4 = x ^ 12 + x ^ 11 + x ^ 9 - x ^ 8 - x ^ 7 - x ^ 5 + x ^ 2 + x - 1 := by
  rw [S_succ x 3, S_three]; ring

lemma map_S {B : Type*} [CommRing B] (f : A →+* B) (x : A) (n : ℕ) :
    f (S x n) = S (f x) n := by
  simp [S, map_sum, map_prod]

/-- Theorem 3 over a ring: if $y^o = 1$ then $R(o + n) = R(n)$ for $n \ge 1$. -/
lemma S_add_period (y : A) {o : ℕ} (hy : y ^ o = 1) {n : ℕ} (hn : 1 ≤ n) :
    S y (o + n) = S y n := by
  rw [S, sum_range_add]
  have h1 :
      ∑ k ∈ range o, y ^ (k ^ 2) * ∏ j ∈ Ico (k + 1) (o + n), (y ^ (2 * j) - 1) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    have hk' := mem_range.mp hk
    rw [prod_eq_zero (i := o) (by simp; omega) (by rw [pow_mul', hy, one_pow, sub_self]),
      mul_zero]
  rw [h1, zero_add, S]
  refine sum_congr rfl fun k _ => ?_
  have e1 : y ^ ((o + k) ^ 2) = y ^ (k ^ 2) := by
    rw [show (o + k) ^ 2 = o * (o + 2 * k) + k ^ 2 by ring, pow_add, pow_mul, hy, one_pow,
      one_mul]
  have e2 : ∏ j ∈ Ico (o + k + 1) (o + n), (y ^ (2 * j) - 1) =
      ∏ j ∈ Ico (k + 1) n, (y ^ (2 * j) - 1) := by
    rw [show o + k + 1 = k + 1 + o by ring, show o + n = n + o by ring, ← prod_Ico_add']
    refine prod_congr rfl fun j _ => ?_
    rw [show 2 * (j + o) = 2 * j + 2 * o by ring, pow_add, pow_mul' y 2 o, hy, one_pow, mul_one]
  rw [e1, e2]

end Ring

lemma R_eq (n : ℕ) (q : ℤ) : R n q = S (1 + q) n := rfl

lemma a_eq_S (n : ℕ) : a n = S 2 n := rfl

lemma a_eq_R (n : ℕ) : a n = R n 1 := by
  rw [a_eq_S, R_eq]; norm_num

/-! ### Periods: Lemma 0 and the Chinese remainder theorem -/

section Periods

variable {s : ℕ → ℤ} {M : ℤ}

/-- A multiple of an eventual period is an eventual period with the same start. -/
lemma per_mul {L n₀ : ℕ} (h : ∀ n > n₀, s (n + L) ≡ s n [ZMOD M]) (t : ℕ) :
    ∀ n > n₀, s (n + t * L) ≡ s n [ZMOD M] := by
  induction t with
  | zero => intro n _; simp
  | succ t ih =>
    intro n hn
    rw [show n + (t + 1) * L = n + t * L + L by ring]
    exact (h (n + t * L) (by omega)).trans (ih n hn)

/-- Lemma 0: the start of periodicity does not depend on the period. If `L` is a period from
`n₀` and `L' ≥ 1` is a period from `n₀'`, then `L` is a period from `n₀'`. -/
lemma start_indep {L L' n₀ n₀' : ℕ} (hL : ∀ n > n₀, s (n + L) ≡ s n [ZMOD M])
    (hL' : ∀ n > n₀', s (n + L') ≡ s n [ZMOD M]) (hL'1 : 1 ≤ L') :
    ∀ n > n₀', s (n + L) ≡ s n [ZMOD M] := by
  intro n hn
  have hle : n₀ ≤ n₀ * L' := Nat.le_mul_of_pos_right n₀ hL'1
  have e1 := per_mul hL' n₀ n hn
  have e2 := hL (n + n₀ * L') (by omega)
  have e3 := per_mul hL' n₀ (n + L) (by omega)
  rw [show n + L + n₀ * L' = n + n₀ * L' + L by ring] at e3
  exact e3.symm.trans (e2.trans e1)

end Periods

/-- The Chinese remainder theorem over the prime-power factors of `N`. -/
lemma modEq_of_forall_primeFactors {N : ℕ} (hN : N ≠ 0) {u w : ℤ}
    (h : ∀ p ∈ N.primeFactors, u ≡ w [ZMOD (p : ℤ) ^ N.factorization p]) :
    u ≡ w [ZMOD N] := by
  rw [Int.modEq_iff_dvd]
  rcases eq_or_ne (w - u) 0 with h0 | h0
  · rw [h0]; exact dvd_zero _
  rw [Int.natCast_dvd]
  have hd : (w - u).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr h0
  refine (Nat.factorization_prime_le_iff_dvd hN hd).mp fun p hp => ?_
  by_cases hpN : p ∣ N
  · have hpm : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, hN⟩
    have := Int.modEq_iff_dvd.mp (h p hpm)
    rw [← Nat.cast_pow, Int.natCast_dvd] at this
    exact (hp.pow_dvd_iff_le_factorization hd).mp this
  · rw [Nat.factorization_eq_zero_of_not_dvd hpN]
    exact Nat.zero_le _

/-! ### Primes not dividing `x` (Theorem 3) -/

lemma S_int_period {M : ℕ} {x : ℤ} {o : ℕ} (h : x ^ o ≡ 1 [ZMOD M]) {n : ℕ}
    (hn : 1 ≤ n) :
    S x (n + o) ≡ S x n [ZMOD M] := by
  rw [← ZMod.intCast_eq_intCast_iff] at h ⊢
  have h' : (x : ZMod M) ^ o = 1 := by push_cast at h; exact h
  have hS : ∀ k, ((S x k : ℤ) : ZMod M) = S (x : ZMod M) k := fun k => by
    simpa using map_S (Int.castRingHom (ZMod M)) x k
  rw [hS, hS, add_comm, S_add_period _ h' hn]

lemma pow_totient_modEq {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) (e : ℕ) :
    x ^ (p ^ e).totient ≡ 1 [ZMOD (p ^ e : ℕ)] := by
  have hcop : IsCoprime x ((p ^ e : ℕ) : ℤ) := by
    rw [Nat.cast_pow]
    exact (((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hx).symm.pow_right
  rw [← ZMod.intCast_eq_intCast_iff]
  have := congrArg Units.val (ZMod.pow_totient (ZMod.unitOfIsCoprime x hcop))
  push_cast at this ⊢
  simpa using this

/-- Theorem 3: for $p \nmid x$, $R$ is purely periodic modulo $p^e$ with period
$\varphi(p^e)$. -/
lemma local_of_not_dvd {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) (e : ℕ) :
    ∀ n > 0, S x (n + (p ^ e).totient) ≡ S x n [ZMOD (p : ℤ) ^ e] := by
  intro n hn
  have := S_int_period (pow_totient_modEq hp hx e) (n := n) hn
  rwa [Nat.cast_pow] at this

/-! ### Primes dividing `x` (Theorem 4) -/

/-- Theorem 4(i): $R(n+1) \equiv (-1)^n \pmod x$. -/
lemma S_succ_sub_dvd (x : ℤ) (n : ℕ) : x ∣ S x (n + 1) - (-1) ^ n := by
  induction n with
  | zero => simp [S_one]
  | succ n ih =>
    have key : S x (n + 1 + 1) - (-1) ^ (n + 1) =
        x * (x ^ (2 * n + 1) * S x (n + 1) + x ^ (n ^ 2 + 2 * n)) - (S x (n + 1) - (-1) ^ n) := by
      rw [S_succ x (n + 1)]; ring
    rw [key]
    exact dvd_sub (dvd_mul_right _ _) ih

lemma S_zero_succ (n : ℕ) : S (0 : ℤ) (n + 1) = (-1) ^ n := by
  induction n with
  | zero => simp [S_one]
  | succ n ih =>
    rw [S_succ, ih, zero_pow (by omega), zero_pow (by positivity)]
    ring

lemma not_dvd_of_dvd_sub {p : ℕ} (hp : p.Prime) {U : ℤ} {k : ℕ}
    (h : (p : ℤ) ∣ U - (-1) ^ k) : ¬ (p : ℤ) ∣ U := by
  intro hU
  have h1 : (p : ℤ) ∣ (-1) ^ k := by
    have := dvd_sub hU h
    rwa [sub_sub_cancel] at this
  have hp' := Nat.prime_iff_prime_int.mp hp
  exact hp'.not_dvd_one (dvd_neg.mp (hp'.dvd_of_dvd_pow h1))

lemma pow_dvd_pow_mul_iff {p : ℕ} (hp : p.Prime) {x U : ℤ} (hx : x ≠ 0)
    (hU : ¬ (p : ℤ) ∣ U) (k e : ℕ) :
    (p : ℤ) ^ e ∣ x ^ k * U ↔ e ≤ k * padicValInt p x := by
  have := Fact.mk hp
  have hU0 : U ≠ 0 := by rintro rfl; exact hU (dvd_zero _)
  have hxk : x ^ k ≠ 0 := pow_ne_zero _ hx
  rw [padicValInt_dvd_iff, padicValInt.mul hxk hU0, padicValInt.eq_zero_of_not_dvd hU, add_zero]
  simp only [mul_eq_zero, hxk, hU0, or_self, false_or]
  rw [padicValInt, Int.natAbs_pow, padicValNat.pow, padicValInt]

lemma one_le_padicValInt {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : x ≠ 0) (hpx : (p : ℤ) ∣ x) :
    1 ≤ padicValInt p x := by
  have := Fact.mk hp
  have := (padicValInt_dvd_iff 1 x).mp (by simpa using hpx)
  tauto

/-- The valuation multiplier: $v_p(R(n+2) - R(n)) = c(n)\, v_p(x)$. -/
def cexp (n : ℕ) : ℕ := if n = 1 then 1 else if n = 2 then 5 else 2 * n

lemma cexp_of_ge {n : ℕ} (hn : 3 ≤ n) : cexp n = 2 * n := by
  unfold cexp; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Theorem 4(ii): $p^e \mid R(n+2) - R(n)$ if and only if $e \le c(n)\, v_p(x)$, where
$c(1) = 1$, $c(2) = 5$ and $c(n) = 2n$ for $n \ge 3$. -/
lemma dvd_D_iff {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : x ≠ 0) (hpx : (p : ℤ) ∣ x) {n : ℕ}
    (hn : 1 ≤ n) (e : ℕ) :
    (p : ℤ) ^ e ∣ S x (n + 2) - S x n ↔ e ≤ cexp n * padicValInt p x := by
  match n, hn with
  | 1, _ =>
    have hD : S x 3 - S x 1 = x ^ 1 * ((x + 1) * (x ^ 4 - 1)) := by
      rw [S_three, S_one]; ring
    show (p : ℤ) ^ e ∣ S x 3 - S x 1 ↔ _
    rw [hD, pow_dvd_pow_mul_iff hp hx _ 1 e]
    · rfl
    apply not_dvd_of_dvd_sub hp (k := 1)
    have : (x + 1) * (x ^ 4 - 1) - (-1) ^ 1 = x * (x ^ 4 + x ^ 3 - 1) := by ring
    rw [this]; exact dvd_mul_of_dvd_left hpx _
  | 2, _ =>
    have hD : S x 4 - S x 2 = x ^ 5 * (x ^ 7 + x ^ 6 + x ^ 4 - x ^ 3 - x ^ 2 - 1) := by
      rw [S_four, S_two]; ring
    show (p : ℤ) ^ e ∣ S x 4 - S x 2 ↔ _
    rw [hD, pow_dvd_pow_mul_iff hp hx _ 5 e]
    · rfl
    apply not_dvd_of_dvd_sub hp (k := 1)
    have : x ^ 7 + x ^ 6 + x ^ 4 - x ^ 3 - x ^ 2 - 1 - (-1) ^ 1 =
        x * (x ^ 6 + x ^ 5 + x ^ 3 - x ^ 2 - x) := by ring
    rw [this]; exact dvd_mul_of_dvd_left hpx _
  | m + 3, _ =>
    have hS : x ∣ S x (m + 3) - (-1) ^ (m + 2) := S_succ_sub_dvd x (m + 2)
    have hD : S x (m + 3 + 2) - S x (m + 3) = x ^ (2 * (m + 3)) *
        ((x ^ (2 * m + 8) - x ^ 2 - 1) * S x (m + 3) +
          x ^ (m ^ 2 + 4 * m + 3) * (x ^ (2 * m + 8) + x ^ (2 * m + 7) - 1)) := by
      rw [show m + 3 + 2 = m + 3 + 1 + 1 from rfl, S_succ x (m + 3 + 1), S_succ x (m + 3)]
      ring
    rw [hD, pow_dvd_pow_mul_iff hp hx _ _ e, cexp_of_ge (by omega)]
    apply not_dvd_of_dvd_sub hp (k := m + 3)
    have : (x ^ (2 * m + 8) - x ^ 2 - 1) * S x (m + 3) +
        x ^ (m ^ 2 + 4 * m + 3) * (x ^ (2 * m + 8) + x ^ (2 * m + 7) - 1) - (-1) ^ (m + 3) =
        x * ((x ^ (2 * m + 7) - x) * S x (m + 3) +
          x ^ (m ^ 2 + 4 * m + 2) * (x ^ (2 * m + 8) + x ^ (2 * m + 7) - 1)) -
        (S x (m + 3) - (-1) ^ (m + 2)) := by ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_left hpx _) (hpx.trans hS)

lemma cexp_ge {e v n : ℕ} (hv : 1 ≤ v) (hn : localPrePeriod e v < n) : e ≤ cexp n * v := by
  unfold localPrePeriod at hn
  split_ifs at hn with h1 h2
  · have : 1 ≤ cexp n := by unfold cexp; split_ifs <;> omega
    calc e ≤ 1 * v := by omega
      _ ≤ cexp n * v := Nat.mul_le_mul_right v this
  · have : 5 ≤ cexp n := by unfold cexp; split_ifs <;> omega
    calc e ≤ 5 * v := h2
      _ ≤ cexp n * v := Nat.mul_le_mul_right v this
  · have h2v : 0 < 2 * v := by omega
    have hf : 2 ≤ (e - 1) / (2 * v) := (Nat.le_div_iff_mul_le h2v).mpr (by omega)
    rw [cexp_of_ge (by omega)]
    have := (Nat.div_lt_iff_lt_mul h2v).mp hn
    have hc : n * (2 * v) = 2 * n * v := by ring
    omega

lemma cexp_lt {e v : ℕ} (hv : 1 ≤ v) (hf : 1 ≤ localPrePeriod e v) :
    ¬ e ≤ cexp (localPrePeriod e v) * v := by
  unfold localPrePeriod at hf ⊢
  split_ifs at hf ⊢ with h1 h2
  · omega
  · simp [cexp]; omega
  · have h2v : 0 < 2 * v := by omega
    have hf2 : 2 ≤ (e - 1) / (2 * v) := (Nat.le_div_iff_mul_le h2v).mpr (by omega)
    rcases Nat.eq_or_lt_of_le hf2 with h | h
    · rw [← h]; simp [cexp]; omega
    · rw [cexp_of_ge (by omega)]
      have := Nat.div_mul_le_self (e - 1) (2 * v)
      have hc : (e - 1) / (2 * v) * (2 * v) = 2 * ((e - 1) / (2 * v)) * v := by ring
      omega

/-- Period 2 from the local pre-period, for $p \mid x$. -/
lemma period_two_of_dvd {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : x ≠ 0) (hpx : (p : ℤ) ∣ x)
    (e : ℕ) :
    ∀ n > localPrePeriod e (padicValInt p x), S x (n + 2) ≡ S x n [ZMOD (p : ℤ) ^ e] := by
  intro n hn
  have hv := one_le_padicValInt hp hx hpx
  exact (Int.modEq_iff_dvd.mpr ((dvd_D_iff hp hx hpx (by omega) e).mpr (cexp_ge hv hn))).symm

/-- Theorem 4(v): for $p \mid x$, the pre-period modulo $p^e$ is `localPrePeriod`. -/
lemma local_iff_of_dvd {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : x ≠ 0) (hpx : (p : ℤ) ∣ x)
    (e n₀ : ℕ) :
    (∃ L ≥ 1, ∀ n > n₀, S x (n + L) ≡ S x n [ZMOD (p : ℤ) ^ e]) ↔
      localPrePeriod e (padicValInt p x) ≤ n₀ := by
  constructor
  · rintro ⟨L, hL1, hL⟩
    by_contra hlt'
    have hlt := Nat.lt_of_not_le hlt'
    have hv := one_le_padicValInt hp hx hpx
    have h2 := start_indep (s := S x) (period_two_of_dvd hp hx hpx e) hL hL1 _ hlt
    exact cexp_lt hv (by omega)
      ((dvd_D_iff hp hx hpx (by omega) e).mp (Int.modEq_iff_dvd.mp h2.symm))
  · intro h
    exact ⟨2, by norm_num, fun n hn => period_two_of_dvd hp hx hpx e n (by omega)⟩

/-- The local pre-period at `p`: zero unless `x ≠ 0` and `p ∣ x`. -/
def fLoc (p e : ℕ) (x : ℤ) : ℕ :=
  if x ≠ 0 ∧ (p : ℤ) ∣ x then localPrePeriod e (padicValInt p x) else 0

lemma local_iff {p : ℕ} (hp : p.Prime) (x : ℤ) (e n₀ : ℕ) :
    (∃ L ≥ 1, ∀ n > n₀, S x (n + L) ≡ S x n [ZMOD (p : ℤ) ^ e]) ↔
      fLoc p e x ≤ n₀ := by
  unfold fLoc
  split_ifs with h
  · exact local_iff_of_dvd hp h.1 h.2 e n₀
  · simp only [zero_le, iff_true]
    by_cases hx : x = 0
    · subst hx
      refine ⟨2, by norm_num, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [show m + 1 + 2 = (m + 2) + 1 from rfl, S_zero_succ, S_zero_succ, pow_add]
      norm_num
    · have hpx : ¬ (p : ℤ) ∣ x := fun h' => h ⟨hx, h'⟩
      exact ⟨(p ^ e).totient, Nat.totient_pos.mpr (pow_pos hp.pos e),
        fun n hn => local_of_not_dvd hp hpx e n (by omega)⟩

lemma prePeriod_le_iff (q : ℤ) (N n₀ : ℕ) :
    prePeriod q N ≤ n₀ ↔
      ∀ p ∈ N.primeFactors, fLoc p (N.factorization p) (1 + q) ≤ n₀ := by
  unfold prePeriod
  split_ifs with hx
  · simp [fLoc, hx]
  · rw [Finset.sup_le_iff]
    simp only [Finset.mem_filter, and_imp, fLoc]
    constructor
    · intro h p hp
      split_ifs with h'
      · exact h p hp h'.2
      · exact Nat.zero_le _
    · intro h p hp hpx
      have := h p hp
      rwa [ite_eq_left ⟨hx, hpx⟩] at this

/-! ### Corollary 5 and A340882 -/

theorem prePeriod_spec (q : ℤ) (N : ℕ) (hN : 1 ≤ N) (n₀ : ℕ) :
    (∃ L ≥ 1, ∀ n > n₀, R (n + L) q ≡ R n q [ZMOD N]) ↔ prePeriod q N ≤ n₀ := by
  simp only [R_eq]
  rw [prePeriod_le_iff]
  constructor
  · rintro ⟨L, hL1, hL⟩ p hp
    refine (local_iff (Nat.prime_of_mem_primeFactors hp) _ _ _).mp ⟨L, hL1, fun n hn => ?_⟩
    exact (hL n hn).of_dvd (by exact_mod_cast Nat.ordProj_dvd N p)
  · intro h
    have h' : ∀ p ∈ N.primeFactors, ∃ L ≥ 1, ∀ n > n₀,
        S (1 + q) (n + L) ≡ S (1 + q) n [ZMOD (p : ℤ) ^ N.factorization p] :=
      fun p hp => (local_iff (Nat.prime_of_mem_primeFactors hp) _ _ _).mpr (h p hp)
    choose! L hL1 hL using h'
    have hpos : 0 < ∏ p ∈ N.primeFactors, L p := Finset.prod_pos fun p hp => hL1 p hp
    refine ⟨∏ p ∈ N.primeFactors, L p, hpos, fun n hn => ?_⟩
    refine modEq_of_forall_primeFactors (by omega) fun p hp => ?_
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem L hp
    rw [ht, mul_comm]
    exact per_mul (hL p hp) t n hn

lemma localPrePeriod_le_one_iff {e v : ℕ} (hv : 1 ≤ v) :
    localPrePeriod e v ≤ 1 ↔ e ≤ 5 * v := by
  unfold localPrePeriod
  split_ifs with h1 h2
  · omega
  · omega
  · have h2v : 0 < 2 * v := by omega
    have hf : 2 ≤ (e - 1) / (2 * v) := (Nat.le_div_iff_mul_le h2v).mpr (by omega)
    omega

theorem conjecture_A340882_iff_local (q : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    (∃ L ≥ 1, ∀ n ≥ 2, R (n + L) q ≡ R n q [ZMOD N]) ↔
      1 + q = 0 ∨ ∀ p ∈ N.primeFactors, (p : ℤ) ∣ 1 + q →
        N.factorization p ≤ 5 * padicValInt p (1 + q) := by
  have e : (∃ L ≥ 1, ∀ n ≥ 2, R (n + L) q ≡ R n q [ZMOD N]) ↔
      (∃ L ≥ 1, ∀ n > 1, R (n + L) q ≡ R n q [ZMOD N]) :=
    ⟨fun ⟨L, h1, h⟩ => ⟨L, h1, fun n hn => h n (by omega)⟩,
      fun ⟨L, h1, h⟩ => ⟨L, h1, fun n hn => h n (by omega)⟩⟩
  rw [e, prePeriod_spec q N hN 1, prePeriod_le_iff]
  by_cases hx : 1 + q = 0
  · simp [fLoc, hx]
  · simp only [hx, false_or, fLoc, ne_eq, not_false_eq_true, true_and]
    refine forall₂_congr fun p hp => ?_
    split_ifs with hpx
    · rw [localPrePeriod_le_one_iff (one_le_padicValInt (Nat.prime_of_mem_primeFactors hp) hx hpx)]
      exact ⟨fun h _ => h, fun h => h hpx⟩
    · exact ⟨fun _ h => absurd h hpx, fun _ => zero_le_one⟩

theorem conjecture_A340882_fails (q : ℤ) (hq : q ≠ -1) (p : ℕ) (hp : p.Prime)
    (hpq : (p : ℤ) ∣ 1 + q) :
    ¬ ∃ L ≥ 1, ∀ n ≥ 2,
      R (n + L) q ≡ R n q [ZMOD p ^ (5 * padicValInt p (1 + q) + 1)] := by
  intro h
  have hN : 1 ≤ p ^ (5 * padicValInt p (1 + q) + 1) := Nat.one_le_pow _ _ hp.pos
  have hx : 1 + q ≠ 0 := by omega
  rcases (conjecture_A340882_iff_local q _ hN).mp (by exact_mod_cast h) with h0 | h1
  · exact hx h0
  · have hmem : p ∈ (p ^ (5 * padicValInt p (1 + q) + 1)).primeFactors := by
      rw [Nat.primeFactors_prime_pow (by omega) hp]; simp
    have := h1 p hmem hpq
    rw [hp.factorization_pow, Finsupp.single_eq_same] at this
    omega

theorem conjecture_A340882_iff (q : ℤ) :
    (∀ N : ℕ, 1 ≤ N → ∃ L ≥ 1, ∀ n ≥ 2, R (n + L) q ≡ R n q [ZMOD N]) ↔
      q = -2 ∨ q = -1 ∨ q = 0 := by
  constructor
  · intro h
    by_contra hq
    have hx1 : (1 + q).natAbs ≠ 1 := by
      intro h1
      rcases Int.natAbs_eq_iff.mp h1 with h2 | h2 <;> omega
    obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd hx1
    exact conjecture_A340882_fails q (by omega) p hp (Int.natCast_dvd.mpr hpx)
      (by exact_mod_cast h _ (Nat.one_le_pow _ _ hp.pos))
  · intro hq N hN
    rw [conjecture_A340882_iff_local q N hN]
    have hp1 : ∀ p ∈ N.primeFactors, ¬ (p : ℤ) ∣ 1 := fun p hp h => by
      have := Int.natCast_dvd.mp h
      simp only [Int.natAbs_one, Nat.dvd_one] at this
      exact (Nat.prime_of_mem_primeFactors hp).ne_one this
    rcases hq with rfl | rfl | rfl
    · right; intro p hp hpx; exact absurd (by simpa using hpx) (hp1 p hp)
    · left; norm_num
    · right; intro p hp hpx; exact absurd (by simpa using hpx) (hp1 p hp)

theorem not_conjecture_A340882 :
    ¬ ∀ (q : ℤ) (N : ℕ), 1 ≤ N →
      ∃ L ≥ 1, ∀ n ≥ 2, R (n + L) q ≡ R n q [ZMOD N] := by
  intro h
  have := (conjecture_A340882_iff 1).mp (h 1)
  omega

/-! ### A340883 -/

lemma a_succ_add_dvd {n : ℕ} (hn : 3 ≤ n) : (64 : ℤ) ∣ a (n + 1) + a n := by
  rw [a_eq_S, a_eq_S, S_succ]
  have h1 : (64 : ℤ) ∣ 2 ^ (2 * n) := by
    rw [show (64 : ℤ) = 2 ^ 6 by norm_num]; exact pow_dvd_pow 2 (by omega)
  have h2 : (64 : ℤ) ∣ 2 ^ (n ^ 2) := by
    rw [show (64 : ℤ) = 2 ^ 6 by norm_num]; exact pow_dvd_pow 2 (by nlinarith)
  have : ((2 : ℤ) ^ (2 * n) - 1) * S 2 n + 2 ^ (n ^ 2) + S 2 n =
      2 ^ (2 * n) * S 2 n + 2 ^ (n ^ 2) := by
    ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left h1 _) h2

theorem a_mod_64 :
    a 2 = 5 ∧ ∀ n ≥ 1, a (2 * n + 1) ≡ 27 [ZMOD 64] ∧ a (2 * n + 2) ≡ 37 [ZMOD 64] := by
  refine ⟨by decide +kernel, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => exact ⟨by decide +kernel, by decide +kernel⟩
  | succ n hn ih =>
    obtain ⟨-, ih2⟩ := ih
    have h1 := a_succ_add_dvd (n := 2 * n + 2) (by omega)
    have h2 := a_succ_add_dvd (n := 2 * n + 2 + 1) (by omega)
    rw [show 2 * (n + 1) + 1 = 2 * n + 2 + 1 by ring,
      show 2 * (n + 1) + 2 = 2 * n + 2 + 1 + 1 by ring]
    unfold Int.ModEq at *
    omega

theorem not_conjecture1_A340883 :
    ¬ ∀ m : ℕ, 1 ≤ m →
      ∃ L ≥ 1, L ∣ m.totient ∧ ∀ n ≥ 2, a (n + L) ≡ a n [ZMOD m] := by
  intro h
  obtain ⟨L, hL1, -, hL⟩ := h 64 (by norm_num)
  have h2 := hL 2 le_rfl
  obtain ⟨ha2, hodd⟩ := a_mod_64
  push_cast at h2
  rcases Nat.even_or_odd L with ⟨k, hk⟩ | ⟨k, hk⟩
  · have := (hodd k (by omega)).2
    rw [show 2 + L = 2 * k + 2 by omega] at h2
    unfold Int.ModEq at *
    rw [ha2] at h2
    omega
  · have := (hodd (k + 1) (by omega)).1
    rw [show 2 + L = 2 * (k + 1) + 1 by omega] at h2
    unfold Int.ModEq at *
    rw [ha2] at h2
    omega

theorem conjecture1_A340883_prePeriod_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ L ≥ 1, ∀ n ≥ 2, a (n + L) ≡ a n [ZMOD m]) ↔ ¬ 64 ∣ m := by
  simp only [a_eq_R]
  rw [conjecture_A340882_iff_local 1 m hm]
  have h2 : padicValInt 2 (1 + 1) = 1 := by
    have := Fact.mk Nat.prime_two
    simpa using padicValInt_self (p := 2)
  have h64 : 64 ∣ m ↔ 6 ≤ m.factorization 2 := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact Nat.prime_two.pow_dvd_iff_le_factorization (by omega)
  rw [h64]
  constructor
  · rintro (h | h)
    · norm_num at h
    · intro h6
      have hmem : 2 ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr
          ⟨Nat.prime_two, Nat.dvd_of_factorization_pos (by omega), by omega⟩
      have := h 2 hmem (by norm_num)
      rw [h2] at this
      omega
  · intro h
    right
    intro p hp hp2
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp
      (by have := Int.natCast_dvd.mp hp2; simpa using this)
    subst this
    rw [h2]
    omega

theorem a_period_totient (m : ℕ) (hm : 1 ≤ m) :
    ∀ n > prePeriod 1 m, a (n + m.totient) ≡ a n [ZMOD m] := by
  intro n hn
  simp only [a_eq_S]
  refine modEq_of_forall_primeFactors (by omega) fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hfl : fLoc p (m.factorization p) (1 + 1) ≤ prePeriod 1 m :=
    (prePeriod_le_iff 1 m _).mp le_rfl p hp
  rw [show (1 : ℤ) + 1 = 2 by norm_num] at hfl
  have hdvd : (p ^ m.factorization p).totient ∣ m.totient :=
    Nat.totient_dvd_of_dvd (Nat.ordProj_dvd m p)
  have he : 1 ≤ m.factorization p :=
    hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
  by_cases hp2 : p = 2
  · subst hp2
    by_cases he1 : m.factorization 2 = 1
    · -- modulo 2 every term is odd
      have h1 : ∀ k > 0, S 2 (k + 1) ≡ S 2 k [ZMOD (2 : ℕ) ^ m.factorization 2] := by
        intro k hk
        rw [he1, pow_one]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hA := S_succ_sub_dvd 2 (j + 1)
        have hB := S_succ_sub_dvd 2 j
        refine (Int.modEq_iff_dvd.mpr ?_).symm
        have : S (2 : ℤ) (j + 1 + 1) - S 2 (j + 1) =
            (S 2 (j + 1 + 1) - (-1) ^ (j + 1)) - (S 2 (j + 1) - (-1) ^ j) + 2 * (-(-1) ^ j) := by
          ring
        rw [this]
        exact dvd_add (dvd_sub (by exact_mod_cast hA) (by exact_mod_cast hB)) (dvd_mul_right _ _)
      have := per_mul h1 m.totient n (by omega)
      rwa [mul_one] at this
    · have h2 : ∀ k > fLoc 2 (m.factorization 2) 2,
          S 2 (k + 2) ≡ S 2 k [ZMOD ((2 : ℕ) : ℤ) ^ m.factorization 2] := by
        unfold fLoc
        rw [ite_eq_left ⟨by norm_num, by norm_num⟩]
        exact period_two_of_dvd Nat.prime_two (by norm_num) (by norm_num) _
      have h2d : 2 ∣ m.totient := by
        refine dvd_trans ?_ hdvd
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
        exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
      obtain ⟨t, ht⟩ := h2d
      rw [ht, mul_comm]
      exact per_mul h2 t n (by omega)
  · have hnd : ¬ (p : ℤ) ∣ 2 := fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp
        (by have := Int.natCast_dvd.mp h; simpa using this))
    obtain ⟨t, ht⟩ := hdvd
    rw [ht, mul_comm]
    exact per_mul (local_of_not_dvd hpp hnd _) t n (by omega)

theorem conjecture1_A340883_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ L ≥ 1, L ∣ m.totient ∧ ∀ n ≥ 2, a (n + L) ≡ a n [ZMOD m]) ↔ ¬ 64 ∣ m := by
  rw [← conjecture1_A340883_prePeriod_iff m hm]
  constructor
  · rintro ⟨L, hL1, -, hL⟩
    exact ⟨L, hL1, hL⟩
  · intro h
    have hP : prePeriod 1 m ≤ 1 := by
      rw [← prePeriod_spec 1 m hm 1]
      obtain ⟨L, hL1, hL⟩ := h
      exact ⟨L, hL1, fun n hn => by rw [← a_eq_R, ← a_eq_R]; exact hL n hn⟩
    exact ⟨m.totient, Nat.totient_pos.mpr (by omega), dvd_rfl,
      fun n hn => a_period_totient m hm n (by omega)⟩

/-! ### A340883 conjecture 2) -/

/-- The period of A340883 modulo $m$: the least $L \ge 1$ with $a(n + L) \equiv a(n) \pmod m$
for all large $n$. -/
noncomputable def period (m : ℕ) : ℕ :=
  sInf {L : ℕ | 1 ≤ L ∧ ∃ n₀, ∀ n > n₀, a (n + L) ≡ a n [ZMOD m]}

/-- The eventual periods of A340883 modulo `m`. -/
def EP (m : ℕ) : Set ℕ :=
  {L : ℕ | 1 ≤ L ∧ ∃ n₀, ∀ n > n₀, a (n + L) ≡ a n [ZMOD m]}

lemma period_mem {m : ℕ} (hm : 1 ≤ m) : period m ∈ EP m :=
  Nat.sInf_mem ⟨m.totient, Nat.totient_pos.mpr (by omega), prePeriod 1 m, a_period_totient m hm⟩

/-- Lemma 0, first part: the eventual periods are the multiples of the least one. -/
lemma mem_EP_iff {m : ℕ} (hm : 1 ≤ m) {L : ℕ} (hL : 1 ≤ L) :
    L ∈ EP m ↔ period m ∣ L := by
  obtain ⟨hP1, n₁, hP⟩ := period_mem hm
  constructor
  · rintro ⟨-, n₂, hL'⟩
    by_contra hnd
    have hr : L % period m ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
    have hmem : L % period m ∈ EP m := by
      refine ⟨Nat.pos_of_ne_zero hr, n₁ + n₂, fun n hn => ?_⟩
      have e1 := per_mul hP (L / period m) (n + L % period m) (by omega)
      rw [add_assoc, Nat.mod_add_div'] at e1
      exact e1.symm.trans (hL' n (by omega))
    exact absurd (Nat.sInf_le hmem) (not_le.mpr (Nat.mod_lt L (by omega)))
  · rintro ⟨t, rfl⟩
    refine ⟨hL, n₁, ?_⟩
    rw [mul_comm]
    exact per_mul hP t

lemma mem_EP_mul_iff {m₁ m₂ : ℕ} (h : m₁.Coprime m₂) {L : ℕ} :
    L ∈ EP (m₁ * m₂) ↔ L ∈ EP m₁ ∧ L ∈ EP m₂ := by
  constructor
  · rintro ⟨hL, n₀, hn⟩
    refine ⟨⟨hL, n₀, fun n h' => (hn n h').of_dvd ?_⟩,
      ⟨hL, n₀, fun n h' => (hn n h').of_dvd ?_⟩⟩
    · push_cast; exact dvd_mul_right _ _
    · push_cast; exact dvd_mul_left _ _
  · rintro ⟨⟨hL, n₁, h₁⟩, ⟨-, n₂, h₂⟩⟩
    refine ⟨hL, n₁ + n₂, fun n hn => ?_⟩
    rw [Nat.cast_mul]
    exact (Int.modEq_and_modEq_iff_modEq_mul (by simpa using h)).mp
      ⟨h₁ n (by omega), h₂ n (by omega)⟩

lemma period_one : period 1 = 1 := by
  have h1 : 1 ∈ EP 1 := ⟨le_rfl, 0, fun n _ => by rw [Nat.cast_one]; exact Int.modEq_one⟩
  exact le_antisymm (Nat.sInf_le h1) (period_mem le_rfl).1

theorem conjecture2_A340883 (m₁ m₂ : ℕ) (h : m₁.Coprime m₂) :
    period (m₁ * m₂) = (period m₁).lcm (period m₂) := by
  rcases Nat.eq_zero_or_pos m₁ with rfl | h1
  · rw [(Nat.coprime_zero_left _).mp h, mul_one, period_one, Nat.lcm_one_right]
  rcases Nat.eq_zero_or_pos m₂ with rfl | h2
  · rw [(Nat.coprime_zero_right _).mp h, one_mul, period_one, Nat.lcm_one_left]
  have hm : 1 ≤ m₁ * m₂ := Nat.mul_pos h1 h2
  have hA := period_mem hm
  have hB : 1 ≤ (period m₁).lcm (period m₂) := Nat.lcm_pos (period_mem h1).1 (period_mem h2).1
  apply Nat.dvd_antisymm
  · rw [← mem_EP_iff hm hB, mem_EP_mul_iff h, mem_EP_iff h1 hB, mem_EP_iff h2 hB]
    exact ⟨Nat.dvd_lcm_left _ _, Nat.dvd_lcm_right _ _⟩
  · obtain ⟨hA1, hA2⟩ := (mem_EP_mul_iff h).mp hA
    exact Nat.lcm_dvd ((mem_EP_iff h1 hA.1).mp hA1) ((mem_EP_iff h2 hA.1).mp hA2)

/-! ### Sanity checks -/

/-- The first rows of A340882, as listed in its comment. -/
example (q : ℤ) : R 1 q = 1 ∧ R 2 q = 1 + 3 * q + q ^ 2 ∧
    R 3 q = 1 + 8 * q + 24 * q ^ 2 + 30 * q ^ 3 + 20 * q ^ 4 + 7 * q ^ 5 + q ^ 6 := by
  refine ⟨by rw [R_eq, S_one], by rw [R_eq, S_two]; ring, by rw [R_eq, S_three]; ring⟩

/-- The first terms of A340883. -/
example :
    a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 91 ∧ a 4 = 6245 ∧ a 5 = 1658011 ∧ a 6 = 1729699685 := by
  decide +kernel

end OeisA340882

end
