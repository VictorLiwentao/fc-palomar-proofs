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
# OEIS A363985 family: Bala's supercongruences for $u_m$, for every $m \in \mathbb{Z}$

This file proves `OeisA363985.u_tower`: for every integer $m$, every prime $p \ge 5$ and all
$n, r \ge 1$,
$$u_m(np^r) \equiv u_m(np^{r-1}) \pmod{p^{3r}}, \qquad
u_m(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{mn+k}{k} \binom{2k}{k},$$
with the polynomial binomial $\binom{mn+k}{k}$. The corollaries `a363985_tower`,
`a363987_tower` and `a363989_tower` are $m = 2, 3, 4$. For `a362676_tower`,
$A362676(n) = (-1)^n u_{-1}(n)$ (`a362676_eq`, from `Ring.choose_neg`) and
$(-1)^{np^r} = (-1)^{np^{r-1}}$ for odd $p$. Bala's companion conjecture for
$v_m(n) = \sum_k (-4)^{n-k} \binom{n}{k} \binom{mn+2k}{2k} \binom{2k}{k}$ (A363986, A363988,
A363990) is not covered.

Write $N = pN'$ with $p^{r-1} \mid N'$, $T(N, j) = \binom{2j}{j} \binom{2N-2j}{N-j}$,
$E(X, y) = (-1)^y \binom{X-1}{y} = \prod_{i \le y} (1 - X/i)$ for $X \in \mathbb{Z}$, and
$u_c(y) = \prod_{l \le y,\ p \nmid l} (l + c)$ (`uprod`). All congruences are equalities in
`ZMod (p ^ (3 r))`.

1. **Single sum** (`u_eq_sum_S`). $u_m(N) = \sum_j S_m(N, j)$ with
   $S_m(N, j) = (-1)^j \binom{mN}{N-j} T(N, j)$. Vandermonde (`Ring.add_choose_eq`) gives
   $\binom{mN+k}{k} = \sum_l \binom{mN}{l} \binom{k}{l}$. The inner sum
   $f(l, L) = \sum_t (-4)^{L-t} \binom{L}{t} \binom{2l+2t}{l+t}$ satisfies
   $f(l, L+1) = f(l+1, L) - 4 f(l, L)$, and induction on $L$ gives
   $\binom{l+L}{l} f(l, L) = (-1)^L \binom{2l}{l} \binom{2L}{L}$. So $(-1)^L f(l, L)$ is the
   super Catalan number $S(l, L)$ (`sc`), an integer by construction.
2. **Exact descents** (`E_descent`, `choose_ratio`). For every $X \in \mathbb{Z}$,
   $E(pX, y)\, u_0(y) = E(X, \lfloor y/p \rfloor)\, u_{-pX}(y)$ and
   $\binom{pX}{pk} u_0(pk) = \binom{X}{k} u_{-pX}(pk)$. Negative tops, and so $m < 0$, need no
   separate case.
3. **Jacobsthal-type bound** (`jacobsthal_prod`). If $p^{1+s} \mid Z$, $p^e \mid k$ and
   $e \le s$, then $\prod_{l \le pk,\ p \nmid l} (1 + Z/l) \equiv 1 \pmod{p^{3+s+2e}}$, by a
   second-order expansion of the product, the harmonic sum and the block sums of $l^{-2}$.
   This is Coster's product form of Jacobsthal's congruence (see Straub, Lemma 5.1).
4. **Divisible layer** (`div_layer`). From
   $T(N, j) \binom{2N}{2j} = \binom{2N}{N} \binom{N}{j}^2$ (`central_pair_ratio`) and step 2,
   $S_m(N, pj') = S_m(N', j')\, G$ exactly, where $G$ is a ratio of the products of step 3 for
   $\binom{mN'}{N'-j'}$, $\binom{2N'}{N'}$, $\binom{N'}{j'}^2$ and $\binom{2N'}{2j'}^{-1}$. So
   $G \equiv 1 \pmod{p^{r+2+2e}}$ with $e = \min(v_p(j'), r-1)$. If $e < r - 1$, then
   $p^{r-1-e}$ divides both $\binom{mN'}{N'-j'}$ and $\binom{N'}{j'}$
   (`int_pow_dvd_of_pow_dvd_mul`), so $p^{3r} \mid S_m(N', j') (G - 1)$.
5. **Unit layer** (`unit_layer`). For $p \nmid j$,
   $S_m(N, j)\, j (N - j) = (-1)^N m N^2 c(N; j)$ with the integer kernel
   $c(N; j) = (-1)^{N-j} \binom{mN-1}{N-j-1} \binom{N-1}{j-1} S(j, N-j)$ (`S_mul_cker`), and
   $c(N; j) E(2N, 2j-1) = \binom{2N}{N} E(mN, N-j-1) E(N, j-1)^2$ (`cker_mul_E`). The rational
   kernel $\mathrm{Ker}(M; a, b, e) = \binom{2M}{M} E(mM, a) E(M, b)^2 / E(2M, e)$ descends
   exactly to $\mathrm{Ker}(M; \lfloor a/p \rfloor, \lfloor b/p \rfloor, \lfloor e/p \rfloor)$
   times a ratio of unit products (`Ker_descent`). With
   $\Phi(M; A) = \mathrm{Ker}(M; M - 1 - \lfloor A/2 \rfloor, \lfloor A/2 \rfloor, A)$ this gives
   $c(pM; j) = \Phi(M; \lfloor 2j/p \rfloor) \cdot (\text{unit ratio})$ (`cker_eq_Phi`) and
   $\Phi(pM; A) = \Phi(M; \lfloor A/p \rfloor) \cdot (\text{unit ratio})$ (`Phi_descent`). In
   `ZMod` the kernel `Kf` is $\Phi$ evaluated through the even unit $2j = pA + 2 - (A \bmod 2)$
   (`rep`); the exact identities, with denominators cleared in $\mathbb{Z}$, give `cker_eq_Kf`
   and `Kf_descent`, with unit ratios $\equiv 1$ modulo $p^{v_p(pM)}$. Hence
   $S_m(N, j) \equiv -(-1)^N m N^2 j^{-2}\, \Phi(N'; \lfloor 2j/p \rfloor)$. Put $x = 2j$. The
   sums of $x^{-2}$ over the even units of a block of length $p^u$ vanish modulo $p^u$
   (`halfblock`: the reflection $x \mapsto (2D+1)p^u - x$ swaps even and odd units, and
   `block_invSq` handles the full block). The nested block lemma (`nested_block`, fibres
   $x \mapsto \lfloor x/p^u \rfloor$) then gives $p^r \mid \sum_x x^{-2} \Phi(N'; \lfloor x/p \rfloor)$,
   and $p^{2r} \mid N^2$ finishes the unit layer.
6. **Assembly** (`tower_zmod`). Split $\sum_j S_m(N, j)$ into the terms with $p \nmid j$
   (step 5) and $j = pj'$ (step 4).

The hypothesis $p \ge 5$ is used in the block sums (2 and 3 are units), in the choice of the even
unit representative and through $p$ odd. The layer decomposition and the nested block lemma follow
Beukers and Straub. The descent of the unit layer through $\lfloor 2k/p^s \rfloor$ with
half-block sums of $k^{-2}$ follows the proof of Theorem 1.2 of Osburn–Sahu–Straub. The super
Catalan factorization $\binom{2j}{j} \binom{2N-2j}{N-j} = \binom{N}{j} S(j, N-j)$ is used in
the same way by Osburn–Sahu and in the proof of Theorem 1.3 of Osburn–Sahu–Straub. The super
Catalan numbers go back to Catalan; Gessel named
them and proved the recurrence $4S(a, b) = S(a+1, b) + S(a, b+1)$, which is the recurrence of
step 1.

*References:*
- Peter Bala, [A363985](https://oeis.org/A363985), [A363987](https://oeis.org/A363987),
  [A363989](https://oeis.org/A363989) (July 2, 2023) and [A362676](https://oeis.org/A362676)
  (July 3, 2023).
- R. Osburn and B. Sahu, *A supercongruence for generalized Domb numbers*, Funct. Approx.
  Comment. Math. 48 (2013), 29–36, [arXiv:1201.6195](https://arxiv.org/abs/1201.6195).
- R. Osburn, B. Sahu and A. Straub, *Supercongruences for sporadic sequences*, Proc. Edinb.
  Math. Soc. 59 (2016), [arXiv:1312.2195](https://arxiv.org/abs/1312.2195).
- A. Straub, *Multivariate Apéry numbers and supercongruences of rational functions*,
  Algebra Number Theory 8 (2014), [arXiv:1401.0854](https://arxiv.org/abs/1401.0854).
- M. Coster, *Supercongruences*, PhD thesis, Universiteit Leiden, 1988.
- I. M. Gessel, *Super ballot numbers*, J. Symbolic Comput. 14 (1992), 179–194.
-/

@[expose] public section

open Finset

namespace OeisA363985

/-- Bala's sequence $u_m(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{mn+k}{k}
\binom{2k}{k}$, with the polynomial binomial $\binom{mn+k}{k}$ (`Ring.choose`). -/
def u (m : ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-4) ^ (n - k) * (n.choose k : ℤ) * Ring.choose (m * n + k) k * ((2 * k).choose k : ℤ)

/-- OEIS A363985: $a(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{2n+k}{k} \binom{2k}{k}$. -/
def a363985 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-4) ^ (n - k) * (n.choose k : ℤ) * ((2 * n + k).choose k : ℤ) * ((2 * k).choose k : ℤ)

/-- OEIS A363987: $a(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{3n+k}{k} \binom{2k}{k}$. -/
def a363987 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-4) ^ (n - k) * (n.choose k : ℤ) * ((3 * n + k).choose k : ℤ) * ((2 * k).choose k : ℤ)

/-- OEIS A363989: $a(n) = \sum_{k=0}^{n} (-4)^{n-k} \binom{n}{k} \binom{4n+k}{k} \binom{2k}{k}$. -/
def a363989 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-4) ^ (n - k) * (n.choose k : ℤ) * ((4 * n + k).choose k : ℤ) * ((2 * k).choose k : ℤ)

/-- OEIS A362676: $a(n) = \sum_{k=0}^{n} 4^{n-k} \binom{n}{k} \binom{n-1}{k} \binom{2k}{k}$.
At $n = 0$ the factor $\binom{-1}{0} = 1$ is `Nat.choose 0 0 = 1`, with the same value. -/
def a362676 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), 4 ^ (n - k) * n.choose k * (n - 1).choose k * (2 * k).choose k

/-! ### Sanity checks -/

example : a363985 0 = 1 ∧ a363985 1 = 2 ∧ a363985 2 = 26 ∧ a363985 3 = 272 ∧
    a363985 4 = 3418 := by decide +kernel

example : a362676 0 = 1 ∧ a362676 1 = 4 ∧ a362676 2 = 32 ∧ a362676 3 = 328 := by decide +kernel

example : a363985 5 % 125 = a363985 1 % 125 := by decide +kernel

/-! ### Shared infrastructure

Copied from the MosN8 package of this repository (Wentao Li, Apache-2.0): divisibility helpers,
the nested block lemma, block sums of inverse squares, the harmonic sum, the Jacobsthal-type
product bound and the unit products `uprod`. -/

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

theorem E_ne_zero {X y : ℕ} (h : y < X) : E X y ≠ 0 := by
  rw [E_natCast (by omega)]
  have : (X - 1).choose y ≠ 0 := (Nat.choose_pos (by omega)).ne'
  positivity

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

/-- `uprod p c y` is coprime to `p` when `p ∣ c`. -/
theorem isCoprime_uprod' {p : ℕ} (hp : p.Prime) {c : ℤ} (hc : (p : ℤ) ∣ c) (y : ℕ) :
    IsCoprime (p : ℤ) (uprod p c y) := by
  obtain ⟨d, hd⟩ := uprod_sub_dvd p hc y
  have := isCoprime_uprod hp y
  have e : uprod p c y = uprod p 0 y + (p : ℤ) * d := by linear_combination hd
  rw [e]
  exact this.add_mul_left_right d

theorem isUnit_uprod' {p : ℕ} [hp : Fact p.Prime] {K : ℕ} {c : ℤ} (hc : (p : ℤ) ∣ c) (y : ℕ) :
    IsUnit (uprod p c y : ZMod (p ^ K)) := by
  obtain ⟨u, v, huv⟩ := (isCoprime_uprod' hp.out hc y).pow_left (m := K)
  refine IsUnit.of_mul_eq_one (v : ZMod (p ^ K)) ?_
  have h := congrArg (Int.cast : ℤ → ZMod (p ^ K)) huv
  have h0 : (p : ZMod (p ^ K)) ^ K = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one, h0,
    mul_zero, zero_add] at h
  rw [mul_comm]
  exact h

/-! ### Super Catalan numbers -/

/-- `f(l, L) = ∑_{t ≤ L} (-4)^{L-t} C(L, t) C(2(l+t), l+t)`. -/
def fsum (l L : ℕ) : ℤ :=
  ∑ t ∈ range (L + 1), (-4) ^ (L - t) * (L.choose t : ℤ) * ((l + t).centralBinom : ℤ)

theorem fsum_succ (l L : ℕ) : fsum l (L + 1) = fsum (l + 1) L - 4 * fsum l L := by
  have h1 : fsum l (L + 1) = fsum (l + 1) L +
      (∑ t ∈ range (L + 1), (-4) ^ (L - t) * (L.choose (t + 1) : ℤ) *
        ((l + (t + 1)).centralBinom : ℤ) + (-4) ^ (L + 1) * (l.centralBinom : ℤ)) := by
    unfold fsum
    rw [sum_range_succ', Nat.choose_zero_right, Nat.sub_zero, add_zero, Nat.cast_one, mul_one,
      ← add_assoc, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl (fun t _ => ?_)
    rw [Nat.choose_succ_succ', show L + 1 - (t + 1) = L - t by omega,
      show l + 1 + t = l + (t + 1) by ring]
    push_cast
    ring
  have e : ∑ t ∈ range (L + 2), (-4 : ℤ) ^ (L + 1 - t) * (L.choose t : ℤ) *
      ((l + t).centralBinom : ℤ) = -4 * fsum l L := by
    rw [sum_range_succ, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self L), Nat.cast_zero, mul_zero,
      zero_mul, add_zero, fsum, mul_sum]
    refine sum_congr rfl (fun t ht => ?_)
    rw [show L + 1 - t = (L - t) + 1 by have := mem_range.1 ht; omega, pow_succ]
    ring
  rw [sum_range_succ'] at e
  simp only [Nat.choose_zero_right, Nat.sub_zero, add_zero, Nat.cast_one, mul_one,
    show ∀ t, L + 1 - (t + 1) = L - t from fun t => by omega] at e
  have h2 : 4 * fsum l L = -(∑ t ∈ range (L + 1), (-4) ^ (L - t) * (L.choose (t + 1) : ℤ) *
        ((l + (t + 1)).centralBinom : ℤ) + (-4) ^ (L + 1) * (l.centralBinom : ℤ)) := by
    linear_combination e
  linear_combination h1 + h2

theorem choose_mul_fsum : ∀ (L l : ℕ),
    ((l + L).choose l : ℤ) * fsum l L = (-1) ^ L * (l.centralBinom : ℤ) * (L.centralBinom : ℤ)
  | 0, l => by simp [fsum]
  | L + 1, l => by
    have ih1 := choose_mul_fsum L l
    have ih2 := choose_mul_fsum L (l + 1)
    have r1 : ((l + (L + 1)).choose l : ℤ) * ((L : ℤ) + 1) =
        ((l + L).choose l : ℤ) * ((l : ℤ) + L + 1) := by
      have := Nat.choose_mul_succ_eq (l + L) l
      rw [show l + L + 1 - l = L + 1 by omega, show l + L + 1 = l + (L + 1) by ring] at this
      exact_mod_cast this.symm
    have r2 : ((l + (L + 1)).choose l : ℤ) * ((L : ℤ) + 1) =
        ((l + 1 + L).choose (l + 1) : ℤ) * ((l : ℤ) + 1) := by
      have := Nat.choose_succ_right_eq (l + (L + 1)) l
      rw [show l + (L + 1) - l = L + 1 by omega, show l + (L + 1) = l + 1 + L by ring] at this
      rw [show l + (L + 1) = l + 1 + L by ring]
      exact_mod_cast this.symm
    have r3 : ((l + 1).centralBinom : ℤ) * ((l : ℤ) + 1) = 2 * (2 * l + 1) * (l.centralBinom : ℤ) := by
      have := Nat.succ_mul_centralBinom_succ l
      rw [mul_comm] at this
      exact_mod_cast this
    have r4 : ((L + 1).centralBinom : ℤ) * ((L : ℤ) + 1) = 2 * (2 * L + 1) * (L.centralBinom : ℤ) := by
      have := Nat.succ_mul_centralBinom_succ L
      rw [mul_comm] at this
      exact_mod_cast this
    rw [fsum_succ]
    apply mul_right_cancel₀ (show (L : ℤ) + 1 ≠ 0 by positivity)
    linear_combination fsum (l + 1) L * r2 + ((l : ℤ) + 1) * ih2
      + (-1) ^ L * (L.centralBinom : ℤ) * r3 - 4 * fsum l L * r1
      - 4 * ((l : ℤ) + L + 1) * ih1 + (-1) ^ L * (l.centralBinom : ℤ) * r4

/-- The super Catalan number `S(a, b) = (2a)! (2b)! / (a! b! (a+b)!)`, defined by a sum so
that it is visibly an integer. -/
def sc (a b : ℕ) : ℤ := (-1) ^ b * fsum a b

theorem choose_mul_sc (a b : ℕ) :
    ((a + b).choose a : ℤ) * sc a b = (a.centralBinom : ℤ) * (b.centralBinom : ℤ) := by
  unfold sc
  have h := choose_mul_fsum b a
  have hs : ((-1 : ℤ) ^ b) * (-1) ^ b = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (-1) ^ b * h + (a.centralBinom : ℤ) * (b.centralBinom : ℤ) * hs

/-! ### The single sum -/

theorem esum_eq {N l : ℕ} (hl : l ≤ N) :
    ∑ k ∈ range (N + 1), (-4 : ℤ) ^ (N - k) * (N.choose k : ℤ) * (k.choose l : ℤ) *
      (k.centralBinom : ℤ) = (-1) ^ (N - l) * (l.centralBinom : ℤ) * ((N - l).centralBinom : ℤ) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [show l + L + 1 = l + (L + 1) by ring, sum_range_add,
    sum_eq_zero (fun k hk => by rw [Nat.choose_eq_zero_of_lt (mem_range.1 hk)]; simp), zero_add,
    Nat.add_sub_cancel_left, ← choose_mul_fsum L l, fsum, mul_sum]
  refine sum_congr rfl (fun t ht => ?_)
  have ht' := mem_range.1 ht
  have hc := Nat.choose_mul (n := l + L) (k := l + t) (s := l) (by omega)
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at hc
  rw [show l + L - (l + t) = L - t by omega]
  have hc' : ((l + L).choose (l + t) : ℤ) * ((l + t).choose l : ℤ) =
      ((l + L).choose l : ℤ) * (L.choose t : ℤ) := by exact_mod_cast hc
  linear_combination (-4 : ℤ) ^ (L - t) * ((l + t).centralBinom : ℤ) * hc'

/-- The summand `(-1)^j C(m N, N - j) C(2j, j) C(2N - 2j, N - j)` of the single sum. -/
def S (m : ℤ) (N j : ℕ) : ℤ :=
  (-1) ^ j * Ring.choose (m * N) (N - j) * (j.centralBinom : ℤ) * ((N - j).centralBinom : ℤ)

/-- The single sum: `u_m(N) = ∑_j (-1)^j C(m N, N - j) C(2j, j) C(2N - 2j, N - j)`. -/
theorem u_eq_sum_S (m : ℤ) (N : ℕ) : u m N = ∑ j ∈ range (N + 1), S m N j := by
  set X : ℤ := m * N
  have hV : ∀ k, k ≤ N → Ring.choose (X + k) k =
      ∑ l ∈ range (N + 1), Ring.choose X l * (k.choose l : ℤ) := by
    intro k hk
    rw [Ring.add_choose_eq k (Commute.all _ _), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [sum_range_eq_of_vanish (fun l => Ring.choose X l * (k.choose l : ℤ))
      (show k + 1 ≤ N + 1 by omega) (fun l h1 _ => by
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
    refine sum_congr rfl (fun l hl => ?_)
    rw [Ring.choose_natCast, Nat.choose_symm (Nat.lt_succ_iff.1 (mem_range.1 hl))]
  have h1 : u m N = ∑ l ∈ range (N + 1), Ring.choose X l *
      ∑ k ∈ range (N + 1), (-4 : ℤ) ^ (N - k) * (N.choose k : ℤ) * (k.choose l : ℤ) *
        (k.centralBinom : ℤ) := by
    unfold u
    calc _ = ∑ k ∈ range (N + 1), ∑ l ∈ range (N + 1), Ring.choose X l *
          ((-4 : ℤ) ^ (N - k) * (N.choose k : ℤ) * (k.choose l : ℤ) * (k.centralBinom : ℤ)) := by
          refine sum_congr rfl (fun k hk => ?_)
          rw [hV k (Nat.lt_succ_iff.1 (mem_range.1 hk)), mul_sum, sum_mul]
          refine sum_congr rfl (fun l _ => ?_)
          rw [Nat.centralBinom_eq_two_mul_choose]
          ring
      _ = _ := by
          rw [sum_comm]
          exact sum_congr rfl (fun l _ => (mul_sum _ _ _).symm)
  rw [h1, ← sum_range_reflect]
  refine sum_congr rfl (fun j hj => ?_)
  have hj' := Nat.lt_succ_iff.1 (mem_range.1 hj)
  rw [Nat.add_sub_cancel, esum_eq (Nat.sub_le N j), show N - (N - j) = j by omega]
  unfold S
  ring

/-! ### Binomial identities -/

theorem cast_add_choose (i j : ℕ) :
    (((i + j).choose j : ℕ) : ℚ) = ((i + j).factorial : ℚ) / (i.factorial * j.factorial) := by
  rw [eq_div_iff (by positivity)]
  exact_mod_cast (by rw [← mul_assoc]; exact Nat.add_choose_mul_factorial_mul_factorial i j)

theorem cast_centralBinom (n : ℕ) :
    ((n.centralBinom : ℕ) : ℚ) = ((2 * n).factorial : ℚ) / (n.factorial * n.factorial) := by
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul, cast_add_choose]

/-- `C(2j, j) C(2L, L) C(2j + 2L, 2j) = C(2(j+L), j+L) C(j+L, j)^2`. -/
theorem central_mul_choose (j L : ℕ) :
    j.centralBinom * L.centralBinom * (2 * L + 2 * j).choose (2 * j) =
      (j + L).centralBinom * (L + j).choose j ^ 2 := by
  have h : ((j.centralBinom * L.centralBinom * (2 * L + 2 * j).choose (2 * j) : ℕ) : ℚ) =
      (((j + L).centralBinom * (L + j).choose j ^ 2 : ℕ) : ℚ) := by
    push_cast
    rw [cast_centralBinom, cast_centralBinom, cast_centralBinom, cast_add_choose,
      cast_add_choose, show 2 * (j + L) = 2 * L + 2 * j by ring, show L + j = j + L by ring]
    field_simp
  exact_mod_cast h

/-- `C(2a+2, a+1) C(2L, L) C(2a+2L+1, 2a+1) = C(2(a+1+L), a+1+L) C(a+L, a) C(a+1+L, a+1)`. -/
theorem central_mul_choose' (a L : ℕ) :
    (a + 1).centralBinom * L.centralBinom * (2 * L + (2 * a + 1)).choose (2 * a + 1) =
      (a + 1 + L).centralBinom * (L + a).choose a * (L + (a + 1)).choose (a + 1) := by
  have h : (((a + 1).centralBinom * L.centralBinom * (2 * L + (2 * a + 1)).choose (2 * a + 1) : ℕ) : ℚ) =
      (((a + 1 + L).centralBinom * (L + a).choose a * (L + (a + 1)).choose (a + 1) : ℕ) : ℚ) := by
    push_cast
    rw [cast_centralBinom, cast_centralBinom, cast_centralBinom, cast_add_choose,
      cast_add_choose, cast_add_choose]
    rw [show 2 * (a + 1) = (2 * a + 1) + 1 by ring, Nat.factorial_succ (2 * a + 1),
      show 2 * (a + 1 + L) = (2 * L + (2 * a + 1)) + 1 by ring,
      Nat.factorial_succ (2 * L + (2 * a + 1)), show L + (a + 1) = (L + a) + 1 by ring,
      Nat.factorial_succ (L + a), show a + 1 + L = (L + a) + 1 by ring, Nat.factorial_succ (L + a),
      Nat.factorial_succ a]
    push_cast
    field_simp
    ring
  exact_mod_cast h

/-! ### The unit-layer kernel -/

/-- The unit-layer kernel `c(N; j) = (-1)^{N-j} C(mN - 1, N - j - 1) C(N - 1, j - 1) S(j, N - j)`. -/
def cker (m : ℤ) (N j : ℕ) : ℤ :=
  (-1) ^ (N - j) * Ring.choose (m * N - 1) (N - j - 1) * ((N - 1).choose (j - 1) : ℤ) * sc j (N - j)

theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

theorem S_mul_cker (m : ℤ) {N j : ℕ} (h1 : 1 ≤ j) (h2 : j < N) :
    S m N j * j * ((N - j : ℕ) : ℤ) = (-1) ^ N * m * (N : ℤ) ^ 2 * cker m N j := by
  have hr := rchoose_succ_mul' (m * N) (N - j - 1)
  rw [show N - j - 1 + 1 = N - j by omega,
    show ((N - j - 1 : ℕ) : ℤ) + 1 = ((N - j : ℕ) : ℤ) by omega] at hr
  have hsc := choose_mul_sc j (N - j)
  rw [show j + (N - j) = N by omega] at hsc
  have hc : (N : ℤ) * ((N - 1).choose (j - 1) : ℤ) = (N.choose j : ℤ) * (j : ℤ) := by
    have := Nat.add_one_mul_choose_eq (N - 1) (j - 1)
    rw [show N - 1 + 1 = N by omega, show j - 1 + 1 = j by omega] at this
    exact_mod_cast this
  have hsign : (-1 : ℤ) ^ j = (-1) ^ N * (-1) ^ (N - j) := by
    rw [← pow_add, show N + (N - j) = j + 2 * (N - j) by omega, pow_add, pow_mul]; simp
  unfold S cker
  linear_combination (-1 : ℤ) ^ j * (j.centralBinom : ℤ) * ((N - j).centralBinom : ℤ) * (j : ℤ) * hr
    - (-1 : ℤ) ^ j * m * N * Ring.choose (m * N - 1) (N - j - 1) * (j : ℤ) * hsc
    - (-1 : ℤ) ^ j * m * N * Ring.choose (m * N - 1) (N - j - 1) * sc j (N - j) * hc
    + m * (N : ℤ) ^ 2 * Ring.choose (m * N - 1) (N - j - 1) * ((N - 1).choose (j - 1) : ℤ) *
      sc j (N - j) * hsign

theorem sc_mul_choose {N j : ℕ} (h1 : 1 ≤ j) (h2 : j < N) :
    sc j (N - j) * ((2 * N - 1).choose (2 * j - 1) : ℤ) =
      (N.centralBinom : ℤ) * ((N - 1).choose (j - 1) : ℤ) := by
  obtain ⟨L, rfl⟩ : ∃ L, N = j + L := ⟨N - j, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  have h3 := central_mul_choose' a L
  have h4 := choose_mul_sc (a + 1) L
  rw [Nat.add_sub_cancel_left, show 2 * (a + 1 + L) - 1 = 2 * L + (2 * a + 1) by omega,
    show 2 * (a + 1) - 1 = 2 * a + 1 by omega, show a + 1 + L - 1 = L + a by omega,
    show a + 1 - 1 = a by omega]
  rw [show L + (a + 1) = a + 1 + L by ring] at h3
  have h3' : ((a + 1).centralBinom : ℤ) * (L.centralBinom : ℤ) *
      ((2 * L + (2 * a + 1)).choose (2 * a + 1) : ℤ) = ((a + 1 + L).centralBinom : ℤ) *
      ((L + a).choose a : ℤ) * ((a + 1 + L).choose (a + 1) : ℤ) := by exact_mod_cast h3
  have hne : ((a + 1 + L).choose (a + 1) : ℤ) ≠ 0 := by
    have := Nat.choose_pos (show a + 1 ≤ a + 1 + L by omega); positivity
  apply mul_left_cancel₀ hne
  linear_combination ((2 * L + (2 * a + 1)).choose (2 * a + 1) : ℤ) * h4 + h3'

theorem cker_mul_E (m : ℤ) {N j : ℕ} (h1 : 1 ≤ j) (h2 : j < N) :
    cker m N j * E (2 * N) (2 * j - 1) =
      (N.centralBinom : ℤ) * E (m * N) (N - j - 1) * E N (j - 1) ^ 2 := by
  have h3 := sc_mul_choose h1 h2
  have hE1 : E N (j - 1) = (-1) ^ (j - 1) * ((N - 1).choose (j - 1) : ℤ) := E_natCast (by omega) _
  have hE2 : E (2 * N) (2 * j - 1) = (-1) ^ (2 * j - 1) * ((2 * N - 1).choose (2 * j - 1) : ℤ) := by
    have := E_natCast (X := 2 * N) (by omega) (2 * j - 1)
    push_cast at this
    exact this
  have hsign : (-1 : ℤ) ^ (N - j) * (-1) ^ (2 * j - 1) = (-1) ^ (N - j - 1) * ((-1) ^ (j - 1)) ^ 2 := by
    rw [← pow_mul, ← pow_add, ← pow_add, show N - j + (2 * j - 1) = (N - j - 1 + (j - 1) * 2) + 2 by
      omega, pow_add]
    simp
  rw [hE1, hE2]
  unfold cker E
  linear_combination (-1 : ℤ) ^ (N - j) * (-1) ^ (2 * j - 1) * Ring.choose (m * N - 1) (N - j - 1) *
      ((N - 1).choose (j - 1) : ℤ) * h3
    + (N.centralBinom : ℤ) * Ring.choose (m * N - 1) (N - j - 1) * ((N - 1).choose (j - 1) : ℤ) ^ 2 *
      hsign

/-! ### The kernel and its exact descent -/

/-- The rational kernel `C(2M, M) E(mM, a) E(M, b)^2 / E(2M, e)`. -/
def Ker (m : ℤ) (M a b e : ℕ) : ℚ :=
  (M.centralBinom : ℚ) * (E (m * M) a : ℚ) * (E M b : ℚ) ^ 2 / (E (2 * M) e : ℚ)

/-- Numerator of the unit ratio in the descent of `Ker`. -/
def Num (p : ℕ) (m : ℤ) (M a b e : ℕ) : ℤ :=
  uprod p (-((p : ℤ) * (2 * M))) (p * M) * uprod p (-((p : ℤ) * (m * M))) a *
    uprod p (-((p : ℤ) * M)) b ^ 2 * uprod p 0 e

/-- Denominator of the unit ratio in the descent of `Ker`. -/
def Den (p : ℕ) (M a b e : ℕ) : ℤ :=
  uprod p 0 (p * M) * uprod p 0 a * uprod p 0 b ^ 2 * uprod p (-((p : ℤ) * (2 * M))) e

theorem centralBinom_eq_rchoose (n : ℕ) : (n.centralBinom : ℤ) = Ring.choose (2 * (n : ℤ)) n := by
  rw [show 2 * (n : ℤ) = ((2 * n : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast,
    Nat.centralBinom_eq_two_mul_choose]

/-- The exact descent `Ker(pM; a, b, e) = Ker(M; ⌊a/p⌋, ⌊b/p⌋, ⌊e/p⌋) · Num / Den`. -/
theorem Ker_descent {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℤ) {M a b e : ℕ}
    (he : e < 2 * (p * M)) :
    Ker m (p * M) a b e * Den p M a b e = Ker m M (a / p) (b / p) (e / p) * Num p m M a b e := by
  have hp0 := hp.pos
  have r0 : ((p * M).centralBinom : ℤ) * uprod p 0 (p * M) =
      (M.centralBinom : ℤ) * uprod p (-((p : ℤ) * (2 * M))) (p * M) := by
    have h := choose_ratio hp hp2 (2 * M) M
    rwa [← centralBinom_eq_rchoose, show (p : ℤ) * (2 * M) = 2 * ((p * M : ℕ) : ℤ) by push_cast; ring,
      ← centralBinom_eq_rchoose, show 2 * ((p * M : ℕ) : ℤ) = (p : ℤ) * (2 * M) by push_cast; ring] at h
  have r1 : E (m * ((p * M : ℕ) : ℤ)) a * uprod p 0 a =
      E (m * M) (a / p) * uprod p (-((p : ℤ) * (m * M))) a := by
    rw [show m * ((p * M : ℕ) : ℤ) = (p : ℤ) * (m * M) by push_cast; ring]
    exact E_descent hp0 (m * M) a
  have r2 : E ((p * M : ℕ) : ℤ) b * uprod p 0 b = E M (b / p) * uprod p (-((p : ℤ) * M)) b := by
    rw [show ((p * M : ℕ) : ℤ) = (p : ℤ) * M by push_cast; ring]
    exact E_descent hp0 M b
  have r3 : E (2 * ((p * M : ℕ) : ℤ)) e * uprod p 0 e =
      E (2 * M) (e / p) * uprod p (-((p : ℤ) * (2 * M))) e := by
    rw [show 2 * ((p * M : ℕ) : ℤ) = (p : ℤ) * (2 * M) by push_cast; ring]
    exact E_descent hp0 (2 * M) e
  have n1 : (E (2 * ((p * M : ℕ) : ℤ)) e : ℚ) ≠ 0 := by
    have := E_ne_zero (X := 2 * (p * M)) he
    push_cast at this ⊢
    exact_mod_cast this
  have n2 : (E (2 * (M : ℤ)) (e / p) : ℚ) ≠ 0 := by
    have := E_ne_zero (X := 2 * M) (y := e / p)
      ((Nat.div_lt_iff_lt_mul hp0).2 (by rw [mul_comm]; linarith))
    push_cast at this
    exact_mod_cast this
  have r0' := congrArg (Int.cast : ℤ → ℚ) r0
  have r1' := congrArg (Int.cast : ℤ → ℚ) r1
  have r2' := congrArg (Int.cast : ℤ → ℚ) r2
  have r3' := congrArg (Int.cast : ℤ → ℚ) r3
  push_cast at r0' r1' r2' r3'
  unfold Ker Num Den
  push_cast at n1 ⊢
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff n1 n2]
  linear_combination
    (E (m * (p * M : ℤ)) a : ℚ) * (uprod p 0 a : ℚ) * (E ((p : ℤ) * M) b : ℚ) ^ 2 *
      (uprod p 0 b : ℚ) ^ 2 * (uprod p (-((p : ℤ) * (2 * M))) e : ℚ) * (E (2 * (M : ℤ)) (e / p) : ℚ) * r0'
    + (M.centralBinom : ℚ) * (uprod p (-((p : ℤ) * (2 * M))) (p * M) : ℚ) *
      (E ((p : ℤ) * M) b : ℚ) ^ 2 * (uprod p 0 b : ℚ) ^ 2 * (uprod p (-((p : ℤ) * (2 * M))) e : ℚ) *
      (E (2 * (M : ℤ)) (e / p) : ℚ) * r1'
    + (M.centralBinom : ℚ) * (uprod p (-((p : ℤ) * (2 * M))) (p * M) : ℚ) *
      (E (m * M) (a / p) : ℚ) * (uprod p (-((p : ℤ) * (m * M))) a : ℚ) *
      ((E ((p : ℤ) * M) b : ℚ) * (uprod p 0 b : ℚ) + (E M (b / p) : ℚ) * (uprod p (-((p : ℤ) * M)) b : ℚ)) *
      (uprod p (-((p : ℤ) * (2 * M))) e : ℚ) * (E (2 * (M : ℤ)) (e / p) : ℚ) * r2'
    - (M.centralBinom : ℚ) * (uprod p (-((p : ℤ) * (2 * M))) (p * M) : ℚ) *
      (E (m * M) (a / p) : ℚ) * (uprod p (-((p : ℤ) * (m * M))) a : ℚ) *
      (E M (b / p) : ℚ) ^ 2 * (uprod p (-((p : ℤ) * M)) b : ℚ) ^ 2 * r3'

/-- The level kernel `Φ(M; A) = Ker(M; M - 1 - ⌊A/2⌋, ⌊A/2⌋, A)`. -/
def Phi (m : ℤ) (M A : ℕ) : ℚ := Ker m M (M - 1 - A / 2) (A / 2) A

theorem not_dvd_two_mul {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hj : ¬ p ∣ j) : ¬ p ∣ 2 * j := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h2
  · have := Nat.le_of_dvd (by norm_num) h2; omega
  · exact hj h2

/-- For a unit `j`, `c(pM; j) = Φ(M; ⌊2j/p⌋) · Num / Den`. -/
theorem cker_eq_Phi {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℤ) {M j : ℕ} (hj : ¬ p ∣ j)
    (hj1 : 1 ≤ j) (hjN : j < p * M) :
    (cker m (p * M) j : ℚ) * Den p M (p * M - j - 1) (j - 1) (2 * j - 1) =
      Phi m M (2 * j / p) * Num p m M (p * M - j - 1) (j - 1) (2 * j - 1) := by
  have hp0 := hp.pos
  have hp2 : p ≠ 2 := by omega
  have hc := cker_mul_E m hj1 hjN
  have hne : (E (2 * ((p * M : ℕ) : ℤ)) (2 * j - 1) : ℚ) ≠ 0 := by
    have := E_ne_zero (X := 2 * (p * M)) (y := 2 * j - 1) (by omega)
    push_cast at this ⊢
    exact_mod_cast this
  have hcK : (cker m (p * M) j : ℚ) = Ker m (p * M) (p * M - j - 1) (j - 1) (2 * j - 1) := by
    unfold Ker
    rw [eq_div_iff hne]
    exact_mod_cast hc
  rw [hcK, Ker_descent hp hp2 m (by omega)]
  have hq : 2 * j / p / 2 = j / p := by
    rw [Nat.div_div_eq_div_mul, mul_comm p 2, Nat.mul_div_mul_left _ _ (by norm_num)]
  have h1 : (j - 1) / p = j / p := by
    have := Nat.succ_div_of_not_dvd (a := j - 1) (by rwa [show j - 1 + 1 = j by omega])
    rw [show j - 1 + 1 = j by omega] at this
    exact this.symm
  have h2 : (p * M - j - 1) / p = M - 1 - j / p := by
    rw [div_sub_sub_one hp0 (dvd_mul_right p M) hjN, Nat.mul_div_cancel_left _ hp0]
    omega
  have h3 : (2 * j - 1) / p = 2 * j / p := by
    have h := not_dvd_two_mul hp hp5 hj
    have := Nat.succ_div_of_not_dvd (a := 2 * j - 1) (by rwa [show 2 * j - 1 + 1 = 2 * j by omega])
    rw [show 2 * j - 1 + 1 = 2 * j by omega] at this
    exact this.symm
  unfold Phi
  rw [h1, h2, h3, hq]

/-- The descent `Φ(pM; A) = Φ(M; ⌊A/p⌋) · Num / Den`. -/
theorem Phi_descent {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℤ) {M A : ℕ}
    (hA : A < 2 * (p * M)) :
    Phi m (p * M) A * Den p M (p * M - 1 - A / 2) (A / 2) A =
      Phi m M (A / p) * Num p m M (p * M - 1 - A / 2) (A / 2) A := by
  have hp0 := hp.pos
  unfold Phi
  rw [Ker_descent hp hp2 m hA]
  have hq : A / 2 / p = A / p / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  have h2 : (p * M - 1 - A / 2) / p = M - 1 - A / p / 2 := by
    rw [show p * M - 1 - A / 2 = p * M - A / 2 - 1 by omega,
      div_sub_sub_one hp0 (dvd_mul_right p M) (by omega), Nat.mul_div_cancel_left _ hp0, hq]
    omega
  rw [h2, hq]

/-! ### A unit representative of each index -/

/-- An even unit `2j` with `⌊2j/p⌋ = A`: `2j = pA + 2` for even `A` and `pA + 1` for odd `A`. -/
def rep (p A : ℕ) : ℕ := (p * A + 2 - A % 2) / 2

theorem rep_spec {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {M A : ℕ} (hA : A < 2 * M) :
    ¬ p ∣ rep p A ∧ 1 ≤ rep p A ∧ rep p A < p * M ∧ 2 * rep p A / p = A := by
  have hp0 := hp.pos
  obtain ⟨t, ht⟩ : ∃ t, p = 2 * t + 1 := by
    have := hp.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with h | h
    · obtain ⟨t, ht⟩ := h
      have : 2 ∣ p := ⟨t, by omega⟩
      have := hp.eq_one_or_self_of_dvd 2 this
      omega
    · exact h
  have hpA : p * A = 2 * (t * A) + A := by rw [ht]; ring
  have h2 : 2 * rep p A = p * A + (2 - A % 2) := by
    unfold rep
    rw [hpA]
    omega
  have hd1 : 1 ≤ 2 - A % 2 := by omega
  have hd2 : 2 - A % 2 < p := by omega
  have hdiv : 2 * rep p A / p = A := by
    rw [h2, Nat.add_comm, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hd2, zero_add]
  refine ⟨fun h => ?_, by omega, ?_, hdiv⟩
  · have h' : p ∣ 2 * rep p A := dvd_mul_of_dvd_right h 2
    rw [h2] at h'
    have := (Nat.dvd_add_right (dvd_mul_right p A)).1 h'
    have := Nat.le_of_dvd (by omega) this
    omega
  · have hle : p * A ≤ p * (2 * M - 1) := Nat.mul_le_mul_left p (by omega)
    have : p * (2 * M - 1) + 3 ≤ 2 * (p * M) := by
      rw [Nat.mul_sub, mul_one]
      have : p * (2 * M) = 2 * (p * M) := by ring
      have : p ≤ p * (2 * M) := Nat.le_mul_of_pos_right p (by omega)
      omega
    omega

/-! ### The kernel in `ZMod (p ^ K)` -/

/-- Numerator and denominator for a unit index `j` of level `pM`. -/
def NumU (p : ℕ) (m : ℤ) (M j : ℕ) : ℤ := Num p m M (p * M - j - 1) (j - 1) (2 * j - 1)

def DenU (p M j : ℕ) : ℤ := Den p M (p * M - j - 1) (j - 1) (2 * j - 1)

/-- Numerator and denominator for the descent from `pM` to `M`. -/
def NumD (p : ℕ) (m : ℤ) (M A : ℕ) : ℤ := Num p m M (p * M - 1 - A / 2) (A / 2) A

def DenD (p M A : ℕ) : ℤ := Den p M (p * M - 1 - A / 2) (A / 2) A

/-- The level kernel in `ZMod (p ^ K)`: `Φ(M; A)` evaluated through the representative
`j = rep p A`, namely `c(pM; j) · Den / Num`. -/
noncomputable def Kf (p K : ℕ) (m : ℤ) (M A : ℕ) : ZMod (p ^ K) :=
  (cker m (p * M) (rep p A) : ZMod (p ^ K)) * (DenU p M (rep p A) : ZMod (p ^ K)) *
    (NumU p m M (rep p A) : ZMod (p ^ K))⁻¹

section ZModKernel

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

theorem isUnit_Num (m : ℤ) (M a b e : ℕ) : IsUnit (Num p m M a b e : ZMod (p ^ K)) := by
  unfold Num
  push_cast
  refine ((((isUnit_uprod' ?_ _).mul (isUnit_uprod' ?_ _)).mul ((isUnit_uprod' ?_ _).pow 2)).mul
    (isUnit_uprod' (dvd_zero _) _))
  · exact dvd_neg.2 (dvd_mul_right _ _)
  · exact dvd_neg.2 (dvd_mul_right _ _)
  · exact dvd_neg.2 (dvd_mul_right _ _)

theorem isUnit_Den (M a b e : ℕ) : IsUnit (Den p M a b e : ZMod (p ^ K)) := by
  unfold Den
  push_cast
  refine ((((isUnit_uprod' (dvd_zero _) _).mul (isUnit_uprod' (dvd_zero _) _)).mul
    ((isUnit_uprod' (dvd_zero _) _).pow 2)).mul (isUnit_uprod' ?_ _))
  exact dvd_neg.2 (dvd_mul_right _ _)

omit hp in
theorem Num_sub_Den (m : ℤ) {M f : ℕ} (a b e : ℕ) (h : (p : ℤ) ^ f ∣ (p : ℤ) * M) :
    (p : ℤ) ^ f ∣ Num p m M a b e - Den p M a b e := by
  have h1 : (p : ℤ) ^ f ∣ -((p : ℤ) * (2 * M)) :=
    dvd_neg.2 (h.trans ⟨2, by ring⟩)
  have h2 : (p : ℤ) ^ f ∣ -((p : ℤ) * (m * M)) := dvd_neg.2 (h.trans ⟨m, by ring⟩)
  have h3 : (p : ℤ) ^ f ∣ -((p : ℤ) * M) := dvd_neg.2 h
  have d1 := uprod_sub_dvd p h1 (p * M)
  have d2 := uprod_sub_dvd p h2 a
  have d3 := uprod_sub_dvd p h3 b
  have d4 := uprod_sub_dvd p h1 e
  unfold Num Den
  rw [sq, sq]
  refine mul_sub_mul_dvd (mul_sub_mul_dvd (mul_sub_mul_dvd d1 d2) (mul_sub_mul_dvd d3 d3)) ?_
  rw [← neg_sub]
  exact dvd_neg.2 d4

omit hp in
theorem ratio_sub_one_dvd {f : ℕ} {a d : ℤ} (hd : IsUnit (d : ZMod (p ^ K)))
    (h : (p : ℤ) ^ f ∣ a - d) :
    (p : ZMod (p ^ K)) ^ f ∣ (a : ZMod (p ^ K)) * (d : ZMod (p ^ K))⁻¹ - 1 := by
  have e : (a : ZMod (p ^ K)) * (d : ZMod (p ^ K))⁻¹ - 1 =
      ((a : ZMod (p ^ K)) - (d : ZMod (p ^ K))) * (d : ZMod (p ^ K))⁻¹ := by
    have := ZMod.mul_inv_of_unit _ hd
    linear_combination this
  rw [e]
  exact dvd_mul_of_dvd_left (intCast_dvd_sub h) _

/-- The level-one link: for a unit `j`, `c(pM; j) = K(M; ⌊2j/p⌋) · NumU / DenU`. -/
theorem cker_eq_Kf (hp5 : 5 ≤ p) (m : ℤ) {M j : ℕ} (hj : ¬ p ∣ j) (hj1 : 1 ≤ j)
    (hjN : j < p * M) :
    (cker m (p * M) j : ZMod (p ^ K)) =
      Kf p K m M (2 * j / p) * ((NumU p m M j : ZMod (p ^ K)) * (DenU p M j : ZMod (p ^ K))⁻¹) := by
  have hJ : 2 * j / p < 2 * M := (Nat.div_lt_iff_lt_mul hp.out.pos).2 (by nlinarith)
  obtain ⟨hr1, hr2, hr3, hr4⟩ := rep_spec hp.out hp5 hJ
  set j' := rep p (2 * j / p)
  have e1 : (cker m (p * M) j : ℚ) * DenU p M j = Phi m M (2 * j / p) * NumU p m M j :=
    cker_eq_Phi hp.out hp5 m hj hj1 hjN
  have e2 : (cker m (p * M) j' : ℚ) * DenU p M j' = Phi m M (2 * j / p) * NumU p m M j' := by
    have := cker_eq_Phi hp.out hp5 m hr1 hr2 hr3
    rw [hr4] at this
    exact this
  have hQ : ((cker m (p * M) j * DenU p M j * NumU p m M j' : ℤ) : ℚ) =
      ((cker m (p * M) j' * DenU p M j' * NumU p m M j : ℤ) : ℚ) := by
    push_cast
    linear_combination (NumU p m M j' : ℚ) * e1 - (NumU p m M j : ℚ) * e2
  have hZ := congrArg (Int.cast : ℤ → ZMod (p ^ K)) (Int.cast_injective hQ)
  push_cast at hZ
  have u1 : (DenU p M j : ZMod (p ^ K)) * (DenU p M j : ZMod (p ^ K))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (isUnit_Den (K := K) M (p * M - j - 1) (j - 1) (2 * j - 1))
  have u2 : (NumU p m M j' : ZMod (p ^ K)) * (NumU p m M j' : ZMod (p ^ K))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (isUnit_Num (K := K) m M (p * M - j' - 1) (j' - 1) (2 * j' - 1))
  unfold Kf
  linear_combination (DenU p M j : ZMod (p ^ K))⁻¹ * (NumU p m M j' : ZMod (p ^ K))⁻¹ * hZ
    - (cker m (p * M) j : ZMod (p ^ K)) * u1
    - (cker m (p * M) j : ZMod (p ^ K)) * (DenU p M j : ZMod (p ^ K)) *
      (DenU p M j : ZMod (p ^ K))⁻¹ * u2

/-- The descent of the level kernel: `K(pM; A) = K(M; ⌊A/p⌋) · NumD / DenD`. -/
theorem Kf_descent (hp5 : 5 ≤ p) (m : ℤ) {M A : ℕ} (hA : A < 2 * (p * M)) :
    Kf p K m (p * M) A =
      Kf p K m M (A / p) * ((NumD p m M A : ZMod (p ^ K)) * (DenD p M A : ZMod (p ^ K))⁻¹) := by
  have hp0 := hp.out.pos
  obtain ⟨h11, h12, h13, h14⟩ := rep_spec hp.out hp5 hA
  have hA' : A / p < 2 * M := (Nat.div_lt_iff_lt_mul hp0).2 (by linarith)
  obtain ⟨h31, h32, h33, h34⟩ := rep_spec hp.out hp5 hA'
  set j1 := rep p A
  set j3 := rep p (A / p)
  have e1 : (cker m (p * (p * M)) j1 : ℚ) * DenU p (p * M) j1 =
      Phi m (p * M) A * NumU p m (p * M) j1 := by
    have := cker_eq_Phi hp.out hp5 m h11 h12 h13
    rw [h14] at this
    exact this
  have e2 : Phi m (p * M) A * DenD p M A = Phi m M (A / p) * NumD p m M A :=
    Phi_descent hp.out (by omega) m hA
  have e3 : (cker m (p * M) j3 : ℚ) * DenU p M j3 = Phi m M (A / p) * NumU p m M j3 := by
    have := cker_eq_Phi hp.out hp5 m h31 h32 h33
    rw [h34] at this
    exact this
  have hQ : ((cker m (p * (p * M)) j1 * DenU p (p * M) j1 * DenD p M A * NumU p m M j3 : ℤ) : ℚ) =
      ((cker m (p * M) j3 * DenU p M j3 * NumU p m (p * M) j1 * NumD p m M A : ℤ) : ℚ) := by
    push_cast
    linear_combination (DenD p M A : ℚ) * (NumU p m M j3 : ℚ) * e1
      + (NumU p m (p * M) j1 : ℚ) * (NumU p m M j3 : ℚ) * e2
      - (NumU p m (p * M) j1 : ℚ) * (NumD p m M A : ℚ) * e3
  have hZ := congrArg (Int.cast : ℤ → ZMod (p ^ K)) (Int.cast_injective hQ)
  push_cast at hZ
  have uN1 : (NumU p m (p * M) j1 : ZMod (p ^ K)) * (NumU p m (p * M) j1 : ZMod (p ^ K))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (isUnit_Num (K := K) m _ _ _ _)
  have uD2 : (DenD p M A : ZMod (p ^ K)) * (DenD p M A : ZMod (p ^ K))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (isUnit_Den (K := K) _ _ _ _)
  have uN3 : (NumU p m M j3 : ZMod (p ^ K)) * (NumU p m M j3 : ZMod (p ^ K))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (isUnit_Num (K := K) m _ _ _ _)
  unfold Kf
  linear_combination (NumU p m (p * M) j1 : ZMod (p ^ K))⁻¹ * (DenD p M A : ZMod (p ^ K))⁻¹ *
      (NumU p m M j3 : ZMod (p ^ K))⁻¹ * hZ
    - (cker m (p * (p * M)) j1 : ZMod (p ^ K)) * (DenU p (p * M) j1 : ZMod (p ^ K)) *
      (NumU p m (p * M) j1 : ZMod (p ^ K))⁻¹ * uD2
    - (cker m (p * (p * M)) j1 : ZMod (p ^ K)) * (DenU p (p * M) j1 : ZMod (p ^ K)) *
      (NumU p m (p * M) j1 : ZMod (p ^ K))⁻¹ * (DenD p M A : ZMod (p ^ K)) *
      (DenD p M A : ZMod (p ^ K))⁻¹ * uN3
    + (cker m (p * M) j3 : ZMod (p ^ K)) * (DenU p M j3 : ZMod (p ^ K)) *
      (NumD p m M A : ZMod (p ^ K)) * (DenD p M A : ZMod (p ^ K))⁻¹ *
      (NumU p m M j3 : ZMod (p ^ K))⁻¹ * uN1

end ZModKernel

/-! ### Half-block sums and the unit layer -/

section HalfBlock

variable {p : ℕ} [hp : Fact p.Prime] {K : ℕ}

/-- The weight `x⁻²` on even units `x`, and `0` elsewhere. -/
noncomputable def hw (p K x : ℕ) : ZMod (p ^ K) := if 2 ∣ x then invSq p K x else 0

theorem invSq_reflect {u a x : ℕ} (ha : p ^ u ∣ a) (hx : x ≤ a) :
    (p : ZMod (p ^ K)) ^ u ∣ invSq p K (a - x) - invSq p K x := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · rw [pow_zero]; exact one_dvd _
  have hpa : p ∣ a := (dvd_pow_self p hu.ne').trans ha
  by_cases hpx : p ∣ x
  · have h' : p ∣ a - x := Nat.dvd_sub hpa hpx
    simp [invSq, hpx, h']
  · have hpy : ¬ p ∣ a - x := fun h => hpx (by
      have := Nat.dvd_sub hpa h; rwa [Nat.sub_sub_self hx] at this)
    have uX := natCast_mul_inv (K := K) hpx
    have uY := natCast_mul_inv (K := K) hpy
    have hXY : (x : ZMod (p ^ K)) + ((a - x : ℕ) : ZMod (p ^ K)) = (a : ZMod (p ^ K)) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hx]
    obtain ⟨c, hc⟩ := ha
    have haP : (a : ZMod (p ^ K)) = (p : ZMod (p ^ K)) ^ u * c := by rw [hc]; push_cast; ring
    set X := (x : ZMod (p ^ K))
    set Y := ((a - x : ℕ) : ZMod (p ^ K))
    have e : invSq p K (a - x) - invSq p K x = (X - Y) * (a : ZMod (p ^ K)) * X⁻¹ ^ 2 * Y⁻¹ ^ 2 := by
      simp only [invSq, ite_eq_right hpx, ite_eq_right hpy]
      linear_combination -(Y⁻¹ ^ 2) * (X * X⁻¹ + 1) * uX + X⁻¹ ^ 2 * (Y * Y⁻¹ + 1) * uY
        + (X - Y) * X⁻¹ ^ 2 * Y⁻¹ ^ 2 * hXY
    rw [e, haP]
    exact ⟨(X - Y) * c * X⁻¹ ^ 2 * Y⁻¹ ^ 2, by ring⟩

/-- Half-block sums (the even-index version of `block_invSq`): over the even units of a
block of length `p ^ u`, `∑ x⁻² ≡ 0 (mod p ^ u)` for `p ≥ 5`. -/
theorem halfblock (hp5 : 5 ≤ p) {u : ℕ} (hu : 1 ≤ u) (D : ℕ) :
    (p : ZMod (p ^ K)) ^ u ∣ ∑ i ∈ range (p ^ u), hw p K (D * p ^ u + i) := by
  set q := p ^ u with hq
  set B := D * q with hB
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.out.pos
  have hqodd : q % 2 = 1 := by
    have : Odd q := (hp.out.odd_of_ne_two (by omega)).pow
    exact Nat.odd_iff.1 this
  have hpB : p ∣ B := dvd_mul_of_dvd_right hpq D
  have hw0 : ∀ x, p ∣ x → hw p K x = 0 := fun x hx => by simp [hw, invSq, hx]
  have hB0 : hw p K (B + 0) = 0 := hw0 _ (by simpa using hpB)
  have hBq : hw p K (B + q) = 0 := hw0 _ (dvd_add hpB hpq)
  -- reflection `i ↦ q - i`, using that both endpoints vanish
  have r1 : ∑ i ∈ range q, hw p K (B + i) = ∑ i ∈ range q, hw p K (B + (i + 1)) := by
    have h1 := sum_range_succ (fun i => hw p K (B + i)) q
    have h2 := sum_range_succ' (fun i => hw p K (B + i)) q
    rw [hBq, add_zero] at h1
    rw [hB0, add_zero] at h2
    exact h1.symm.trans h2
  have r2 : ∑ i ∈ range q, hw p K (B + (i + 1)) = ∑ i ∈ range q, hw p K (B + q - i) := by
    rw [← sum_range_reflect (fun i => hw p K (B + (i + 1))) q]
    refine sum_congr rfl (fun i hi => ?_)
    have := mem_range.1 hi
    congr 1
    omega
  set a := 2 * B + q
  have hqa : q ∣ a := ⟨2 * D + 1, by simp only [a, hB]; ring⟩
  set O := ∑ i ∈ range q, (if 2 ∣ B + i then 0 else invSq p K (B + i))
  have hsum : ∑ i ∈ range q, hw p K (B + i) + O = ∑ i ∈ range q, invSq p K (B + i) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    simp only [hw]
    split_ifs <;> simp
  have hdiff : (p : ZMod (p ^ K)) ^ u ∣ ∑ i ∈ range q, hw p K (B + i) - O := by
    rw [r1, r2, ← sum_sub_distrib]
    refine dvd_sum (fun i hi => ?_)
    have hi' := mem_range.1 hi
    have hrefl : B + q - i = a - (B + i) := by simp only [a]; omega
    rw [hrefl]
    simp only [hw]
    by_cases h2 : 2 ∣ B + i
    · have : ¬ 2 ∣ a - (B + i) := by simp only [a]; omega
      rw [ite_eq_right this, ite_eq_left h2, sub_zero]
      exact dvd_zero _
    · have : 2 ∣ a - (B + i) := by simp only [a]; omega
      rw [ite_eq_left this, ite_eq_right h2]
      exact invSq_reflect hqa (by simp only [a]; omega)
  apply dvd_of_two_mul_dvd hp5
  have e : 2 * ∑ i ∈ range q, hw p K (B + i) =
      (∑ i ∈ range q, hw p K (B + i) + O) + (∑ i ∈ range q, hw p K (B + i) - O) := by ring
  rw [e, hsum]
  exact dvd_add (block_invSq hp5 hu D) hdiff

end HalfBlock

section UnitLayer

variable {p : ℕ} [hp : Fact p.Prime]

theorem inv_sq_eq_four_invSq {K j : ℕ} (hp5 : 5 ≤ p) (hj : ¬ p ∣ j) :
    ((j : ZMod (p ^ K))⁻¹) ^ 2 = 4 * invSq p K (2 * j) := by
  have hpj2 : ¬ p ∣ 2 * j := not_dvd_two_mul hp.out hp5 hj
  simp only [invSq, ite_eq_right hpj2]
  have h2 := two_mul_inv_two (K := K) hp5
  have hj' := natCast_mul_inv (K := K) hj
  have e : ((2 * j : ℕ) : ZMod (p ^ K))⁻¹ = (2 : ZMod (p ^ K))⁻¹ * (j : ZMod (p ^ K))⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    push_cast
    linear_combination (j : ZMod (p ^ K)) * (j : ZMod (p ^ K))⁻¹ * h2 + hj'
  rw [e]
  linear_combination -((j : ZMod (p ^ K))⁻¹ ^ 2) * (2 * (2 : ZMod (p ^ K))⁻¹ + 1) * h2

/-- The unit layer: `∑_{p ∤ j} S_m(n p^r, j) ≡ 0 (mod p^{3r})`. -/
theorem unit_layer (hp5 : 5 ≤ p) (m : ℤ) {n r : ℕ} (hr : 1 ≤ r) :
    ∑ j ∈ range (n * p ^ r + 1),
      (if p ∣ j then 0 else (S m (n * p ^ r) j : ZMod (p ^ (3 * r)))) = 0 := by
  have hp0 := hp.out.pos
  set N' := n * p ^ (r - 1) with hN'
  set N := n * p ^ r with hN
  have hNN : N = p * N' := by
    rw [hN, hN', show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]
    ring
  have hpN : p ∣ N := hNN ▸ dvd_mul_right p N'
  have hPN : (p : ZMod (p ^ (3 * r))) ^ r ∣ (N : ZMod (p ^ (3 * r))) :=
    ⟨n, by rw [hN]; push_cast; ring⟩
  have hpr : (p : ℤ) ^ r ∣ (p : ℤ) * N' := ⟨n, by rw [← Nat.cast_mul, ← hNN, hN]; push_cast; ring⟩
  set F : ℕ → ZMod (p ^ (3 * r)) := fun x => Kf p (3 * r) m N' (x / p) with hF
  set T0 : ZMod (p ^ (3 * r)) := (-1) ^ N * (m : ZMod (p ^ (3 * r))) * (N : ZMod (p ^ (3 * r))) ^ 2
    with hT0
  have hw0 : ∀ x, p ∣ x → hw p (3 * r) x = 0 := fun x hx => by simp [hw, invSq, hx]
  have h2r : (p : ZMod (p ^ (3 * r))) ^ (2 * r) = ((p : ZMod (p ^ (3 * r))) ^ r) ^ 2 := by
    rw [← pow_mul, mul_comm r 2]
  have step1 : ∀ j ∈ range (N + 1), (if p ∣ j then 0 else (S m N j : ZMod (p ^ (3 * r)))) =
      -T0 * 4 * (hw p (3 * r) (2 * j) * F (2 * j)) := by
    intro j hj
    by_cases hpj : p ∣ j
    · rw [ite_eq_left hpj, hw0 _ (dvd_mul_of_dvd_right hpj 2)]
      ring
    rw [ite_eq_right hpj]
    have hjle := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have hj1 : 1 ≤ j := Nat.pos_of_ne_zero (fun h => hpj (h ▸ dvd_zero p))
    have hjN : j < N := lt_of_le_of_ne hjle (fun h => hpj (h ▸ hpN))
    have hpy : ¬ p ∣ N - j := fun h => hpj (by
      have := Nat.dvd_sub hpN h; rwa [Nat.sub_sub_self hjle] at this)
    have hS := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * r))) (S_mul_cker m hj1 hjN)
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_one] at hS
    have hc := cker_eq_Kf (K := 3 * r) hp5 m hpj hj1 (hNN ▸ hjN)
    rw [← hNN] at hc
    have hG : (p : ZMod (p ^ (3 * r))) ^ r ∣
        (NumU p m N' j : ZMod (p ^ (3 * r))) * (DenU p N' j : ZMod (p ^ (3 * r)))⁻¹ - 1 :=
      ratio_sub_one_dvd (isUnit_Den N' (p * N' - j - 1) (j - 1) (2 * j - 1))
        (Num_sub_Den m (p * N' - j - 1) (j - 1) (2 * j - 1) hpr)
    set G := (NumU p m N' j : ZMod (p ^ (3 * r))) * (DenU p N' j : ZMod (p ^ (3 * r)))⁻¹
    set Kj := Kf p (3 * r) m N' (2 * j / p)
    set x := (j : ZMod (p ^ (3 * r)))
    set y := ((N - j : ℕ) : ZMod (p ^ (3 * r)))
    have ux : x * x⁻¹ = 1 := natCast_mul_inv hpj
    have uy : y * y⁻¹ = 1 := natCast_mul_inv hpy
    have hxy : x + y = (N : ZMod (p ^ (3 * r))) := by
      simp only [x, y]; rw [← Nat.cast_add, Nat.add_sub_cancel' hjle]
    have hmain : (S m N j : ZMod (p ^ (3 * r))) = -T0 * x⁻¹ ^ 2 * Kj := by
      apply eq_of_sub_eq_zero
      apply eq_zero_of_pow_dvd
      have key : (S m N j : ZMod (p ^ (3 * r))) - -T0 * x⁻¹ ^ 2 * Kj =
          T0 * Kj * (x⁻¹ * y⁻¹ * (G - 1) + x⁻¹ ^ 2 * y⁻¹ * (N : ZMod (p ^ (3 * r)))) := by
        simp only [hT0]
        linear_combination x⁻¹ * y⁻¹ * hS
          + x⁻¹ * y⁻¹ * (-1) ^ N * (m : ZMod (p ^ (3 * r))) * (N : ZMod (p ^ (3 * r))) ^ 2 * hc
          - (S m N j : ZMod (p ^ (3 * r))) * y * y⁻¹ * ux - (S m N j : ZMod (p ^ (3 * r))) * uy
          - (-1) ^ N * (m : ZMod (p ^ (3 * r))) * (N : ZMod (p ^ (3 * r))) ^ 2 * Kj * x⁻¹ ^ 2 * uy
          - (-1) ^ N * (m : ZMod (p ^ (3 * r))) * (N : ZMod (p ^ (3 * r))) ^ 2 * Kj * x⁻¹ * y⁻¹ * ux
          + (-1) ^ N * (m : ZMod (p ^ (3 * r))) * (N : ZMod (p ^ (3 * r))) ^ 2 * Kj * x⁻¹ ^ 2 * y⁻¹ *
            hxy
      rw [key]
      have hT : (p : ZMod (p ^ (3 * r))) ^ (2 * r) ∣ T0 := by
        simp only [hT0]
        rw [h2r]
        exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hPN 2) _
      have hB : (p : ZMod (p ^ (3 * r))) ^ r ∣
          x⁻¹ * y⁻¹ * (G - 1) + x⁻¹ ^ 2 * y⁻¹ * (N : ZMod (p ^ (3 * r))) :=
        dvd_add (dvd_mul_of_dvd_right hG _) (dvd_mul_of_dvd_right hPN _)
      have := mul_dvd_mul (dvd_mul_of_dvd_left hT Kj) hB
      rwa [← pow_add, show 2 * r + r = 3 * r by ring] at this
    rw [hmain, inv_sq_eq_four_invSq hp5 hpj, show hw p (3 * r) (2 * j) = invSq p (3 * r) (2 * j) from
      ite_eq_left (dvd_mul_right 2 j)]
    simp only [hF, Kj]
    ring
  rw [sum_congr rfl step1, ← mul_sum]
  have hsum : ∑ j ∈ range (N + 1), hw p (3 * r) (2 * j) * F (2 * j) =
      ∑ x ∈ range (2 * n * p ^ r), hw p (3 * r) x * F x := by
    rw [sum_range_succ, hw0 _ (dvd_mul_of_dvd_right hpN 2), zero_mul, add_zero,
      show 2 * n * p ^ r = 2 * N by rw [hN]; ring]
    exact (sum_range_mul_of_vanish (fun x => hw p (3 * r) x * F x) (by norm_num)
      (fun x hx => by simp [hw, hx]) N).symm
  have hnb := nested_block (p : ZMod (p ^ (3 * r))) (p := p) (s := r) (L := 2 * n) hp0 hr
    (hw p (3 * r)) (fun u A => Kf p (3 * r) m (n * p ^ (r - u)) A)
    (fun u hu _ D _ => halfblock hp5 hu D)
    (fun u hu hur A hA => by
      have hM : n * p ^ (r - u) = p * (n * p ^ (r - (u + 1))) := by
        rw [show r - u = (r - (u + 1)) + 1 by omega, pow_succ]; ring
      show (p : ZMod (p ^ (3 * r))) ^ (r - u) ∣ Kf p (3 * r) m (n * p ^ (r - u)) A -
        Kf p (3 * r) m (n * p ^ (r - (u + 1))) (A / p)
      rw [hM, Kf_descent hp5 m (by rw [← hM]; linarith)]
      have hG' := ratio_sub_one_dvd (K := 3 * r) (f := r - u)
        (isUnit_Den (n * p ^ (r - (u + 1))) (p * (n * p ^ (r - (u + 1))) - 1 - A / 2) (A / 2) A)
        (Num_sub_Den m (p * (n * p ^ (r - (u + 1))) - 1 - A / 2) (A / 2) A
          (by rw [← Nat.cast_mul, ← hM]; exact ⟨n, by push_cast; ring⟩))
      have e : Kf p (3 * r) m (n * p ^ (r - (u + 1))) (A / p) *
          ((NumD p m (n * p ^ (r - (u + 1))) A : ZMod (p ^ (3 * r))) *
            (DenD p (n * p ^ (r - (u + 1))) A : ZMod (p ^ (3 * r)))⁻¹) -
          Kf p (3 * r) m (n * p ^ (r - (u + 1))) (A / p) =
          Kf p (3 * r) m (n * p ^ (r - (u + 1))) (A / p) *
          ((NumD p m (n * p ^ (r - (u + 1))) A : ZMod (p ^ (3 * r))) *
            (DenD p (n * p ^ (r - (u + 1))) A : ZMod (p ^ (3 * r)))⁻¹ - 1) := by ring
      rw [e]
      exact dvd_mul_of_dvd_right hG' _)
  rw [← hsum] at hnb
  apply eq_zero_of_pow_dvd
  have hT : (p : ZMod (p ^ (3 * r))) ^ (2 * r) ∣ -T0 * 4 := by
    simp only [hT0]
    rw [h2r]
    exact dvd_mul_of_dvd_left (dvd_neg.2 (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hPN 2) _)) _
  have := mul_dvd_mul hT hnb
  rwa [← pow_add, show 2 * r + r = 3 * r by ring] at this

end UnitLayer

/-! ### The divisible layer and the tower -/

/-- If `p ^ n ∣ y z` in `ℤ` and `p ^ (j + 1) ∤ y`, then `p ^ (n - j) ∣ z`. -/
theorem int_pow_dvd_of_pow_dvd_mul {p : ℕ} [Fact p.Prime] {n j y : ℕ} {z : ℤ}
    (h : (p : ℤ) ^ n ∣ (y : ℤ) * z) (hy : ¬ p ^ (j + 1) ∣ y) : (p : ℤ) ^ (n - j) ∣ z := by
  have h1 : p ^ n ∣ y * z.natAbs := by
    have := Int.ofNat_dvd_left.1 (by exact_mod_cast h : ((p ^ n : ℕ) : ℤ) ∣ (y : ℤ) * z)
    rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
  have h2 := pow_dvd_of_pow_dvd_mul h1 hy
  exact_mod_cast Int.ofNat_dvd_left.2 h2

section Divisible

variable {p : ℕ} [hp : Fact p.Prime]

/-- The exact descent of `T(N, j) = C(2j, j) C(2(N-j), N-j)` from `(pN', pj)` to `(N', j)`. -/
theorem central_pair_ratio (hp2 : p ≠ 2) {j N' : ℕ} (hj : j ≤ N') :
    ((p * j).centralBinom : ℤ) * ((p * N' - p * j).centralBinom : ℤ) *
        uprod p (-((p : ℤ) * (2 * N'))) (p * (2 * j)) * uprod p 0 (p * N') * uprod p 0 (p * j) ^ 2 =
      (j.centralBinom : ℤ) * ((N' - j).centralBinom : ℤ) *
        uprod p (-((p : ℤ) * (2 * N'))) (p * N') * uprod p (-((p : ℤ) * N')) (p * j) ^ 2 *
        uprod p 0 (p * (2 * j)) := by
  have hpr := hp.out
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show p * (j + L) - p * j = p * L by rw [Nat.mul_add, Nat.add_sub_cancel_left],
    Nat.add_sub_cancel_left]
  have f1 := central_mul_choose (p * j) (p * L)
  rw [show 2 * (p * L) + 2 * (p * j) = p * (2 * (j + L)) by ring,
    show 2 * (p * j) = p * (2 * j) by ring, show p * j + p * L = p * (j + L) by ring,
    show p * L + p * j = p * (j + L) by ring] at f1
  have f2 := central_mul_choose j L
  rw [show 2 * L + 2 * j = 2 * (j + L) by ring, show L + j = j + L by ring] at f2
  have f1' : ((p * j).centralBinom : ℤ) * ((p * L).centralBinom : ℤ) *
      ((p * (2 * (j + L))).choose (p * (2 * j)) : ℤ) =
      ((p * (j + L)).centralBinom : ℤ) * ((p * (j + L)).choose (p * j) : ℤ) ^ 2 := by
    exact_mod_cast f1
  have f2' : (j.centralBinom : ℤ) * (L.centralBinom : ℤ) * ((2 * (j + L)).choose (2 * j) : ℤ) =
      ((j + L).centralBinom : ℤ) * ((j + L).choose j : ℤ) ^ 2 := by exact_mod_cast f2
  have r1 : ((p * (2 * (j + L))).choose (p * (2 * j)) : ℤ) * uprod p 0 (p * (2 * j)) =
      ((2 * (j + L)).choose (2 * j) : ℤ) *
        uprod p (-((p : ℤ) * (2 * ((j + L : ℕ) : ℤ)))) (p * (2 * j)) := by
    have h := choose_ratio hpr hp2 (2 * ((j + L : ℕ) : ℤ)) (2 * j)
    have e1 : Ring.choose ((p : ℤ) * (2 * ((j + L : ℕ) : ℤ))) (p * (2 * j)) =
        ((p * (2 * (j + L))).choose (p * (2 * j)) : ℤ) := by
      rw [show (p : ℤ) * (2 * ((j + L : ℕ) : ℤ)) = ((p * (2 * (j + L)) : ℕ) : ℤ) by push_cast; ring,
        Ring.choose_natCast]
    have e2 : Ring.choose (2 * ((j + L : ℕ) : ℤ)) (2 * j) = ((2 * (j + L)).choose (2 * j) : ℤ) := by
      rw [show 2 * ((j + L : ℕ) : ℤ) = ((2 * (j + L) : ℕ) : ℤ) by push_cast; ring,
        Ring.choose_natCast]
    rw [e1, e2] at h
    exact h
  have r2 : ((p * (j + L)).centralBinom : ℤ) * uprod p 0 (p * (j + L)) =
      ((j + L).centralBinom : ℤ) * uprod p (-((p : ℤ) * (2 * ((j + L : ℕ) : ℤ)))) (p * (j + L)) := by
    have h := choose_ratio hpr hp2 (2 * ((j + L : ℕ) : ℤ)) (j + L)
    have e1 : Ring.choose ((p : ℤ) * (2 * ((j + L : ℕ) : ℤ))) (p * (j + L)) =
        ((p * (j + L)).centralBinom : ℤ) := by
      rw [centralBinom_eq_rchoose]; congr 1; push_cast; ring
    rw [e1, ← centralBinom_eq_rchoose] at h
    exact h
  have r3 : ((p * (j + L)).choose (p * j) : ℤ) * uprod p 0 (p * j) =
      ((j + L).choose j : ℤ) * uprod p (-((p : ℤ) * ((j + L : ℕ) : ℤ))) (p * j) := by
    have h := choose_ratio hpr hp2 ((j + L : ℕ) : ℤ) j
    rw [show (p : ℤ) * ((j + L : ℕ) : ℤ) = ((p * (j + L) : ℕ) : ℤ) by push_cast; ring,
      Ring.choose_natCast, Ring.choose_natCast] at h
    rwa [show ((p * (j + L) : ℕ) : ℤ) = (p : ℤ) * ((j + L : ℕ) : ℤ) by push_cast; ring] at h
  have hne : (((2 * (j + L)).choose (2 * j) : ℕ) : ℤ) ≠ 0 := by
    have := Nat.choose_pos (show 2 * j ≤ 2 * (j + L) by omega); positivity
  apply mul_right_cancel₀ hne
  linear_combination
    -((p * j).centralBinom : ℤ) * ((p * L).centralBinom : ℤ) * uprod p 0 (p * (j + L)) *
      uprod p 0 (p * j) ^ 2 * r1
    + uprod p 0 (p * (j + L)) * uprod p 0 (p * j) ^ 2 * uprod p 0 (p * (2 * j)) * f1'
    + uprod p 0 (p * (2 * j)) * (((p * (j + L)).choose (p * j) : ℤ) * uprod p 0 (p * j)) ^ 2 * r2
    + uprod p 0 (p * (2 * j)) * ((j + L).centralBinom : ℤ) *
      uprod p (-((p : ℤ) * (2 * ((j + L : ℕ) : ℤ)))) (p * (j + L)) *
      (((p * (j + L)).choose (p * j) : ℤ) * uprod p 0 (p * j) +
        ((j + L).choose j : ℤ) * uprod p (-((p : ℤ) * ((j + L : ℕ) : ℤ))) (p * j)) * r3
    - uprod p 0 (p * (2 * j)) * uprod p (-((p : ℤ) * (2 * ((j + L : ℕ) : ℤ)))) (p * (j + L)) *
      uprod p (-((p : ℤ) * ((j + L : ℕ) : ℤ))) (p * j) ^ 2 * f2'

/-- The divisible layer: `S_m(pN', pj') ≡ S_m(N', j') (mod p^{3r})` when `p^{r-1} ∣ N'`. -/
theorem div_layer (hp5 : 5 ≤ p) (m : ℤ) {r N' j' : ℕ} (hr : 1 ≤ r) (hN' : p ^ (r - 1) ∣ N')
    (hj' : j' ≤ N') :
    (S m (p * N') (p * j') : ZMod (p ^ (3 * r))) = (S m N' j' : ZMod (p ^ (3 * r))) := by
  have hpr := hp.out
  have hp0 := hpr.pos
  have hp2 : p ≠ 2 := by omega
  -- the exact integer identity
  have rB := choose_ratio hpr hp2 (m * N') (N' - j')
  have rT := central_pair_ratio hp2 hj'
  have hodd : Odd p := hpr.odd_of_ne_two hp2
  have hsg : (-1 : ℤ) ^ (p * j') = (-1) ^ j' := by rw [pow_mul, hodd.neg_one_pow]
  have hsub : p * N' - p * j' = p * (N' - j') := (Nat.mul_sub p N' j').symm
  have hI : S m (p * N') (p * j') * (uprod p 0 (p * (N' - j')) *
        uprod p (-((p : ℤ) * (2 * N'))) (p * (2 * j')) * uprod p 0 (p * N') *
        uprod p 0 (p * j') ^ 2) =
      S m N' j' * (uprod p (-((p : ℤ) * (m * N'))) (p * (N' - j')) *
        uprod p (-((p : ℤ) * (2 * N'))) (p * N') * uprod p (-((p : ℤ) * N')) (p * j') ^ 2 *
        uprod p 0 (p * (2 * j'))) := by
    unfold S
    rw [hsg, show m * ((p * N' : ℕ) : ℤ) = (p : ℤ) * (m * N') by push_cast; ring, hsub]
    rw [hsub] at rT
    linear_combination (-1 : ℤ) ^ j' * ((p * j').centralBinom : ℤ) *
        ((p * (N' - j')).centralBinom : ℤ) * uprod p (-((p : ℤ) * (2 * N'))) (p * (2 * j')) *
        uprod p 0 (p * N') * uprod p 0 (p * j') ^ 2 * rB
      + (-1 : ℤ) ^ j' * Ring.choose (m * N') (N' - j') *
        uprod p (-((p : ℤ) * (m * N'))) (p * (N' - j')) * rT
  -- choose the valuation level `e`
  set e := Nat.findGreatest (fun e => p ^ e ∣ j') (r - 1) with he
  have he1 : e ≤ r - 1 := Nat.findGreatest_le _
  have he2 : p ^ e ∣ j' := Nat.findGreatest_spec (P := fun e => p ^ e ∣ j') (Nat.zero_le _) (by simp)
  have he3 : e < r - 1 → ¬ p ^ (e + 1) ∣ j' := fun h =>
    Nat.findGreatest_is_greatest (P := fun e => p ^ e ∣ j') (Nat.lt_succ_self _) (by omega)
  have heN : p ^ e ∣ N' := (pow_dvd_pow p he1).trans hN'
  have hpow : (p : ZMod (p ^ (3 * r))) ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hZ : ∀ c : ℤ, (p : ZMod (p ^ (3 * r))) ^ r ∣ (((-((p : ℤ) * (c * N'))) : ℤ) : ZMod (p ^ (3 * r))) := by
    intro c
    obtain ⟨t, ht⟩ := hN'
    exact ⟨-(c * t), by rw [ht, hpow]; push_cast; ring⟩
  have hZ1 : (p : ZMod (p ^ (3 * r))) ^ r ∣ (((-((p : ℤ) * N')) : ℤ) : ZMod (p ^ (3 * r))) := by
    have := hZ 1; rwa [one_mul] at this
  -- the Jacobsthal-type bounds
  have j1 := PR_sub_one (K := 3 * r) hp5 hr he1 (Nat.dvd_sub heN he2) (hZ m)
  have j2 := PR_sub_one (K := 3 * r) hp5 hr he1 heN (hZ 2)
  have j3 := PR_sub_one (K := 3 * r) hp5 hr he1 he2 hZ1
  have j4 := PR_sub_one (K := 3 * r) hp5 hr he1 (dvd_mul_of_dvd_right he2 2) (hZ 2)
  set U : ZMod (p ^ (3 * r)) := (uprod p 0 (p * (N' - j')) : ZMod (p ^ (3 * r))) *
    uprod p 0 (p * N') * uprod p 0 (p * j') ^ 2 * uprod p 0 (p * (2 * j'))
  set Den : ℤ := uprod p 0 (p * (N' - j')) * uprod p (-((p : ℤ) * (2 * N'))) (p * (2 * j')) *
    uprod p 0 (p * N') * uprod p 0 (p * j') ^ 2 with hDen
  set Num : ℤ := uprod p (-((p : ℤ) * (m * N'))) (p * (N' - j')) *
    uprod p (-((p : ℤ) * (2 * N'))) (p * N') * uprod p (-((p : ℤ) * N')) (p * j') ^ 2 *
    uprod p 0 (p * (2 * j')) with hNum
  have c1 : (uprod p (-((p : ℤ) * (m * N'))) (p * (N' - j')) : ZMod (p ^ (3 * r))) =
      PR p (3 * r) ((-((p : ℤ) * (m * N')) : ℤ) : ZMod (p ^ (3 * r))) (N' - j') *
        (uprod p 0 (p * (N' - j')) : ZMod (p ^ (3 * r))) := uprod_cast _ _
  have c2 : (uprod p (-((p : ℤ) * (2 * N'))) (p * N') : ZMod (p ^ (3 * r))) =
      PR p (3 * r) ((-((p : ℤ) * (2 * N')) : ℤ) : ZMod (p ^ (3 * r))) N' *
        (uprod p 0 (p * N') : ZMod (p ^ (3 * r))) := uprod_cast _ _
  have c3 : (uprod p (-((p : ℤ) * N')) (p * j') : ZMod (p ^ (3 * r))) =
      PR p (3 * r) ((-((p : ℤ) * N') : ℤ) : ZMod (p ^ (3 * r))) j' *
        (uprod p 0 (p * j') : ZMod (p ^ (3 * r))) := uprod_cast _ _
  have c4 : (uprod p (-((p : ℤ) * (2 * N'))) (p * (2 * j')) : ZMod (p ^ (3 * r))) =
      PR p (3 * r) ((-((p : ℤ) * (2 * N')) : ℤ) : ZMod (p ^ (3 * r))) (2 * j') *
        (uprod p 0 (p * (2 * j')) : ZMod (p ^ (3 * r))) := uprod_cast _ _
  have hND : (Num : ZMod (p ^ (3 * r))) - (Den : ZMod (p ^ (3 * r))) = U *
      ((PR p (3 * r) ((-((p : ℤ) * (m * N')) : ℤ) : ZMod (p ^ (3 * r))) (N' - j') *
        PR p (3 * r) ((-((p : ℤ) * (2 * N')) : ℤ) : ZMod (p ^ (3 * r))) N' *
        PR p (3 * r) ((-((p : ℤ) * N') : ℤ) : ZMod (p ^ (3 * r))) j' ^ 2 - 1) -
      (PR p (3 * r) ((-((p : ℤ) * (2 * N')) : ℤ) : ZMod (p ^ (3 * r))) (2 * j') - 1)) := by
    rw [hNum, hDen]
    simp only [Int.cast_mul, Int.cast_pow]
    rw [c1, c2, c3, c4]
    ring
  have hk : (p : ZMod (p ^ (3 * r))) ^ (r + 2 + 2 * e) ∣ (Num : ZMod (p ^ (3 * r))) - Den := by
    rw [hND]
    exact dvd_mul_of_dvd_right (dvd_sub (mul_sub_one_dvd (mul_sub_one_dvd j1 j2)
      (by rw [sq]; exact mul_sub_one_dvd j3 j3)) j4) _
  have hDu : IsUnit (Den : ZMod (p ^ (3 * r))) := by
    simp only [Den]
    push_cast
    refine (((isUnit_uprod' (dvd_zero _) _).mul (isUnit_uprod' ?_ _)).mul
      (isUnit_uprod' (dvd_zero _) _)).mul ((isUnit_uprod' (dvd_zero _) _).pow 2)
    exact dvd_neg.2 (dvd_mul_right _ _)
  have hI' : (S m (p * N') (p * j') : ZMod (p ^ (3 * r))) * (Den : ZMod (p ^ (3 * r))) =
      (S m N' j' : ZMod (p ^ (3 * r))) * (Num : ZMod (p ^ (3 * r))) := by
    rw [← Int.cast_mul, ← Int.cast_mul, hI]
  have uD := ZMod.mul_inv_of_unit _ hDu
  have hdiff : (S m (p * N') (p * j') : ZMod (p ^ (3 * r))) - (S m N' j' : ZMod (p ^ (3 * r))) =
      (S m N' j' : ZMod (p ^ (3 * r))) * ((Num : ZMod (p ^ (3 * r))) - Den) *
        (Den : ZMod (p ^ (3 * r)))⁻¹ := by
    linear_combination (Den : ZMod (p ^ (3 * r)))⁻¹ * hI'
      - (S m (p * N') (p * j') : ZMod (p ^ (3 * r))) * uD + (S m N' j' : ZMod (p ^ (3 * r))) * uD
  apply eq_of_sub_eq_zero
  apply eq_zero_of_pow_dvd
  rw [hdiff]
  by_cases hlt : e < r - 1
  · -- the summand itself carries `p ^ (2 (r - 1 - e))`
    have hnd := he3 hlt
    have hj1 : 1 ≤ j' := Nat.pos_of_ne_zero (fun h => hnd (h ▸ dvd_zero _))
    have hL : ¬ p ^ (e + 1) ∣ N' - j' := fun h => hnd (by
      have h1 : p ^ (e + 1) ∣ N' := (pow_dvd_pow p (by omega)).trans hN'
      have := Nat.dvd_sub h1 h
      rwa [Nat.sub_sub_self hj'] at this)
    have hL1 : 1 ≤ N' - j' := Nat.pos_of_ne_zero (fun h => hL (h ▸ dvd_zero _))
    have hA : (p : ℤ) ^ (r - 1 - e) ∣ Ring.choose (m * N') (N' - j') := by
      have h := rchoose_succ_mul' (m * N') (N' - j' - 1)
      rw [show N' - j' - 1 + 1 = N' - j' by omega,
        show ((N' - j' - 1 : ℕ) : ℤ) + 1 = ((N' - j' : ℕ) : ℤ) by omega] at h
      refine int_pow_dvd_of_pow_dvd_mul (y := N' - j') ?_ hL
      rw [mul_comm, h]
      obtain ⟨t, ht⟩ := hN'
      exact ⟨m * t * Ring.choose (m * N' - 1) (N' - j' - 1), by rw [ht]; push_cast; ring⟩
    have hC : (p : ℤ) ^ (r - 1 - e) ∣ (N'.choose j' : ℤ) := by
      have h := Nat.add_one_mul_choose_eq (N' - 1) (j' - 1)
      rw [show N' - 1 + 1 = N' by omega, show j' - 1 + 1 = j' by omega] at h
      refine int_pow_dvd_of_pow_dvd_mul (y := j') ?_ hnd
      obtain ⟨t, ht⟩ := hN'
      exact ⟨t * ((N' - 1).choose (j' - 1) : ℤ), by
        rw [show (j' : ℤ) * (N'.choose j' : ℤ) = ((N'.choose j' * j' : ℕ) : ℤ) by push_cast; ring,
          ← h, ht]; push_cast; ring⟩
    have hT := choose_mul_sc j' (N' - j')
    rw [show j' + (N' - j') = N' by omega] at hT
    have hS : (p : ℤ) ^ (2 * (r - 1 - e)) ∣ S m N' j' := by
      unfold S
      rw [two_mul, pow_add, mul_assoc, ← hT]
      obtain ⟨a, ha⟩ := hA
      obtain ⟨c, hc⟩ := hC
      exact ⟨(-1) ^ j' * a * c * sc j' (N' - j'), by rw [ha, hc]; ring⟩
    have hS' : (p : ZMod (p ^ (3 * r))) ^ (2 * (r - 1 - e)) ∣ (S m N' j' : ZMod (p ^ (3 * r))) := by
      obtain ⟨t, ht⟩ := hS
      exact ⟨(t : ZMod (p ^ (3 * r))), by rw [ht]; push_cast; ring⟩
    have := mul_dvd_mul hS' hk
    rw [← pow_add, show 2 * (r - 1 - e) + (r + 2 + 2 * e) = 3 * r by omega] at this
    exact dvd_mul_of_dvd_left this _
  · have he' : e = r - 1 := by omega
    rw [he', show r + 2 + 2 * (r - 1) = 3 * r by omega] at hk
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hk _) _

/-- The tower in `ZMod (p ^ (3 r))`. -/
theorem tower_zmod (hp5 : 5 ≤ p) (m : ℤ) {n r : ℕ} (hr : 1 ≤ r) :
    (u m (n * p ^ r) : ZMod (p ^ (3 * r))) = (u m (n * p ^ (r - 1)) : ZMod (p ^ (3 * r))) := by
  have hp0 := hp.out.pos
  have hNN : n * p ^ r = p * (n * p ^ (r - 1)) := by
    rw [show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]; ring
  rw [u_eq_sum_S, u_eq_sum_S, Int.cast_sum, Int.cast_sum]
  have hsplit : ∑ j ∈ range (n * p ^ r + 1), (S m (n * p ^ r) j : ZMod (p ^ (3 * r))) =
      ∑ j ∈ range (n * p ^ r + 1),
        (if p ∣ j then 0 else (S m (n * p ^ r) j : ZMod (p ^ (3 * r)))) +
      ∑ j ∈ range (n * p ^ r + 1),
        (if p ∣ j then (S m (n * p ^ r) j : ZMod (p ^ (3 * r))) else 0) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun j _ => by split_ifs <;> simp)
  rw [hsplit, unit_layer hp5 m hr, zero_add, hNN]
  have hN' : p ^ (r - 1) ∣ n * p ^ (r - 1) := dvd_mul_left _ _
  generalize n * p ^ (r - 1) = N' at hN' ⊢
  set G : ℕ → ZMod (p ^ (3 * r)) := fun j =>
    if p ∣ j ∧ j ≤ p * N' then (S m (p * N') j : ZMod (p ^ (3 * r))) else 0 with hG
  have h1 : ∑ j ∈ range (p * N' + 1),
      (if p ∣ j then (S m (p * N') j : ZMod (p ^ (3 * r))) else 0) =
      ∑ j ∈ range (p * (N' + 1)), G j := by
    rw [sum_range_eq_of_vanish G (show p * N' + 1 ≤ p * (N' + 1) by rw [Nat.mul_succ]; omega)
      (fun x hx _ => by simp only [G]; rw [ite_eq_right (fun h => by have := h.2; omega)])]
    refine sum_congr rfl (fun j hj => ?_)
    have := Nat.lt_succ_iff.1 (mem_range.1 hj)
    simp only [G, this, and_true]
  rw [h1, sum_range_mul_of_vanish G hp0 (fun s hs => by
    simp only [G]; rw [ite_eq_right (fun h => hs h.1)])]
  refine sum_congr rfl (fun j hj => ?_)
  have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
  simp only [G]
  rw [ite_eq_left ⟨dvd_mul_right p j, Nat.mul_le_mul_left p hj⟩]
  exact div_layer hp5 m hr hN' hj

end Divisible

/-! ### The four OEIS entries -/

theorem u_natCast (c n : ℕ) :
    u c n = ∑ k ∈ Finset.range (n + 1),
      (-4) ^ (n - k) * (n.choose k : ℤ) * ((c * n + k).choose k : ℤ) * ((2 * k).choose k : ℤ) := by
  unfold u
  refine sum_congr rfl (fun k _ => ?_)
  rw [show (c : ℤ) * n + k = ((c * n + k : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast]

theorem a363985_eq (n : ℕ) : a363985 n = u 2 n := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, u_natCast]; rfl

theorem a363987_eq (n : ℕ) : a363987 n = u 3 n := by
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, u_natCast]; rfl

theorem a363989_eq (n : ℕ) : a363989 n = u 4 n := by
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, u_natCast]; rfl

/-- `A362676(n) = (-1)^n u_{-1}(n)`. -/
theorem a362676_eq (n : ℕ) : (a362676 n : ℤ) = (-1) ^ n * u (-1) n := by
  unfold a362676 u
  push_cast
  rw [mul_sum]
  refine sum_congr rfl (fun k hk => ?_)
  have hk' := Nat.lt_succ_iff.1 (mem_range.1 hk)
  have hc : Ring.choose ((-1 : ℤ) * n + k) k = (-1) ^ k * ((n - 1).choose k : ℤ) := by
    have e1 : (-1 : ℤ) * n + k = -((n - k : ℕ) : ℤ) := by push_cast [Nat.cast_sub hk']; ring
    rw [e1, Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain rfl : k = 0 := by omega
      simp
    · have e2 : ((n - k : ℕ) : ℤ) + k - 1 = ((n - 1 : ℕ) : ℤ) := by
        have : 1 ≤ n := hn
        push_cast [Nat.cast_sub hk', Nat.cast_sub this]
        ring
      rw [e2, Ring.choose_natCast]
  rw [hc, show (-4 : ℤ) ^ (n - k) = (-1) ^ (n - k) * 4 ^ (n - k) by rw [← mul_pow]; norm_num]
  have hs : (-1 : ℤ) ^ n * ((-1) ^ (n - k) * (-1) ^ k) = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk', ← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (-(4 : ℤ) ^ (n - k) * (n.choose k : ℤ) * ((n - 1).choose k : ℤ) *
    ((2 * k).choose k : ℤ)) * hs

/--
For every integer $m$, every prime $p \ge 5$ and all $n, r \ge 1$:
$u_m(np^r) \equiv u_m(np^{r-1}) \pmod{p^{3r}}$.
- Peter Bala, OEIS A363985, Jul 02 2023 (the conjecture for $u_m$, for all $m \in \mathbb{Z}$).
-/
theorem u_tower (m : ℤ) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) : u m (n * p ^ r) ≡ u m (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  have _ := hn
  have := Fact.mk hp
  have h := tower_zmod hp5 m (n := n) hr
  rw [ZMod.intCast_eq_intCast_iff] at h
  exact_mod_cast h

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$ for OEIS A363985.
- Peter Bala, OEIS A363985, Jul 02 2023.
-/
theorem a363985_tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) :
    a363985 (n * p ^ r) ≡ a363985 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  rw [a363985_eq, a363985_eq]
  exact u_tower 2 hp hp5 hn hr

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$ for OEIS A363987.
- Peter Bala, OEIS A363987, Jul 02 2023.
-/
theorem a363987_tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) :
    a363987 (n * p ^ r) ≡ a363987 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  rw [a363987_eq, a363987_eq]
  exact u_tower 3 hp hp5 hn hr

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$ for OEIS A363989.
- Peter Bala, OEIS A363989, Jul 02 2023.
-/
theorem a363989_tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) :
    a363989 (n * p ^ r) ≡ a363989 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  rw [a363989_eq, a363989_eq]
  exact u_tower 4 hp hp5 hn hr

/--
For every prime $p \ge 5$ and all $n, r \ge 1$:
$a(np^r) \equiv a(np^{r-1}) \pmod{p^{3r}}$ for OEIS A362676.
- Peter Bala, OEIS A362676, Jul 03 2023.
-/
theorem a362676_tower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) : a362676 (n * p ^ r) ≡ a362676 (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have h := u_tower (-1) hp hp5 hn hr
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hs : (-1 : ℤ) ^ (n * p ^ r) = (-1) ^ (n * p ^ (r - 1)) := by
    rw [show n * p ^ r = p * (n * p ^ (r - 1)) by
      rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel hr], pow_mul, hodd.neg_one_pow]
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [show (p : ℤ) ^ (3 * r) = ((p ^ (3 * r) : ℕ) : ℤ) by push_cast; ring,
    ← ZMod.intCast_eq_intCast_iff] at h
  have e1 := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * r))) (a362676_eq (n * p ^ r))
  have e2 := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * r))) (a362676_eq (n * p ^ (r - 1)))
  have hs' := congrArg (Int.cast : ℤ → ZMod (p ^ (3 * r))) hs
  push_cast at e1 e2 h hs'
  rw [e1, e2, h, hs']

end OeisA363985

end
