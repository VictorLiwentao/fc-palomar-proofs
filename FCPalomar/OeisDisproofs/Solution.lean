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
# Counterexamples to five OEIS conjectures

This file refutes five conjectures from OEIS entries. The statements and the readings chosen are
explained in `Challenge.lean`. Each refutation is one or a few kernel computations by
`decide +kernel`.

*A333564.* At $(r, s, p, n, k) = (2, 1, 3, 1, 1)$ the clause asks
$a(2,1;3) \equiv a(2,1;1) \pmod{27}$. Here $a(2,1;1) = 4$ and
$a(2,1;3) = 2^6(1 - 16 + 100) = 5440$, and $5436 \equiv 9 \pmod{27}$.

*A034171.* Take $p = 7$ and $n = 50 = 7^2 + 1$. Bala's exceptions for $p = 7$ are
$mp + k$ with $m, k \le 2$, so they are at most $16$, and $50$ is not one of them. The kernel
evaluates the numerator $3^m\prod_{k \le m}(3k+1)$ and the denominator $(m+1)!$ exactly, with
tail-recursive products, for $m = 349$ and $m = 49$. It checks that each denominator divides its
numerator, so both values are natural numbers, and that their residues modulo $49$ are $31$ and
$17$. Their difference is $14 \not\equiv 0 \pmod{49}$.

*A298799.* First the generating function. If $A(0) = 1$ and $A^9(1 - 27x) = 1$, then
differentiating gives $A^8\bigl(9(1 - 27x)A' - 27A\bigr) = 0$. Power series over $\mathbb{Q}$
have no zero divisors and $A \ne 0$, so $(1 - 27x)A' = 3A$. In coefficients this is
$(n+1)a(n+1) = (27n + 3)a(n)$, so $a(n) = 3^n\prod_{k<n}(9k+1)/n!$ by induction. This gives
uniqueness. For existence, let $B$ be the series with these coefficients. The recurrence gives
$(1 - 27x)B' = 3B$, so $B^9(1 - 27x)$ has derivative $9B^8 \cdot 3B - 27B^9 = 0$ and constant
term $1$; hence it is $1$. Then take $p = 19$ and $n = 362 = 19^2 + 1$, which is not an
exception (those are at most $40$). As for A034171, the kernel computes $a(6878)$, a number with
$9841$ digits, and $a(362)$ exactly. Their residues modulo $361$ are $218$ and $294$, and the
difference is $285 \not\equiv 0 \pmod{361}$.

*A382407.* The kernel computes $a(10) = 0$, with a bounded search for the square root in place
of `Nat.sqrt`. Since $10 \notin \{2, 4, 8, 13\}$, $10 \ne 3^j$ and $10 \ne 5 \cdot 3^j$, the
conjecture fails at $k = 10$. For the "if" direction:
- If $9 \mid x + y + z$ and $xy + yz + zx = m^2$, then $3$ divides $x$, $y$ and $z$. This is a
  check of all residues modulo $9$. Then $3 \mid m$, and $(x/3, y/3, z/3)$ is a partition of
  $n/3$ of the same kind. So $a(n/3) = 0$ implies $a(n) = 0$ when $9 \mid n$.
- The kernel computes $a(k) = 0$ for $k = 1, 2, 3, 4, 5, 8, 10, 13, 15$. Induction on $j$ with
  the descent gives $a(3^j) = 0$ and $a(5 \cdot 3^j) = 0$ for all $j$.
The descent adapts the mod $3$ descent of Huang and Sun for the analogous problem with
$x^2 + y^2 + z^2$.

*A399793.* A sign function on $S$ is the same as the subset $T \subseteq S$ where it is $1$, and
then $\sum_{x \in S} x f(x) = 2\sum_{x \in T} x - \sum_{x \in S} x$. So $S$ is good if and only
if $\lvert 2\sum_T x - \sum_S x\rvert \le 1$ for some $T \subseteq S$, which the kernel decides.
The sets $\{1, 2\} \cup [9, 13]$, $\{1, 2\} \cup [10, 14]$, $\{1, 2, 3, 4\} \cup [13, 15]$,
$\{1, 2, 3\} \cup [12, 16]$ and $\{1, 2, 3\} \cup [13, 17]$ are bad. They have sizes
$7, 7, 7, 8, 8$, while $\ell(n) = 6, 6, 6, 7, 7$ for $n = 13, \dots, 17$.

*Sanity checks.* The file also checks the first terms of each sequence against the entries:
$a(1,1;n)$ for $n \le 5$, the first six terms of A034171 and A298799, $a(1), \dots, a(20)$ of
A382407, and $a(2), \dots, a(8)$ of A399793.

*References:*
- Peter Bala, [A333564](https://oeis.org/A333564), April 7, 2020.
- Peter Bala, comments in [A034171](https://oeis.org/A034171) and
  [A298799](https://oeis.org/A298799), December 23, 2019.
- Felix Huber, [A382407](https://oeis.org/A382407), April 4, 2025.
- Yifan Xie, [A399793](https://oeis.org/A399793), September 12, 2026.
- C. Huang and Z.-W. Sun, *On partitions of integers with restrictions involving squares*,
  arXiv:2105.03416 (2021).
-/

@[expose] public section

namespace OeisDisproofs

section A333564

/-- Bala's family in OEIS A333564:
$a(r,s;n) = 2^{rn}\sum_{k=0}^{sn-1}(-1)^{sn-1+k}\binom{n+k}{k}^r$.
The entry is the case $r = s = 1$. -/
def a333564 (r s n : ℕ) : ℤ :=
  2 ^ (r * n) * ∑ k ∈ Finset.range (s * n), (-1) ^ (s * n - 1 + k) * ((n + k).choose k : ℤ) ^ r

/-- Bala's general clause in OEIS A333564, read with the modulus $p^{3k}$ and for $r \ge 1$:
for all $r, s \ge 1$, every prime $p \ge 3$ and all $n, k \ge 1$,
$a(r,s;np^k) \equiv a(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
def Conj333564 : Prop :=
  ∀ r s : ℕ, 1 ≤ r → 1 ≤ s → ∀ p : ℕ, p.Prime → 3 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    a333564 r s (n * p ^ k) ≡ a333564 r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)]

/-- The entry's first terms: $a(1,1;n) = 2, 8, 56, 384, 2752$ for $n = 1, \dots, 5$. -/
example : (List.range 5).map (fun n => a333564 1 1 (n + 1)) = [2, 8, 56, 384, 2752] := by
  decide +kernel

/-- Bala's general clause in OEIS A333564 is false. -/
theorem not_conj333564 : ¬ Conj333564 := by
  intro h
  have := h 2 1 (by norm_num) le_rfl 3 Nat.prime_three le_rfl 1 1 le_rfl le_rfl
  revert this
  decide +kernel

end A333564

section KernelArithmetic

/-- `prodAux c n acc = acc * ∏_{k < n} (c k + 1)`, computed tail-recursively. -/
def prodAux (c : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => prodAux c n (acc * (c * n + 1))

theorem prodAux_eq (c n acc : ℕ) :
    prodAux c n acc = acc * ∏ k ∈ Finset.range n, (c * k + 1) := by
  induction n generalizing acc with
  | zero => simp [prodAux]
  | succ n ih => rw [prodAux, ih, Finset.prod_range_succ]; ring

/-- `factAux n acc = acc * n!`, computed tail-recursively. -/
def factAux : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => factAux n (acc * (n + 1))

theorem factAux_eq (n acc : ℕ) : factAux n acc = acc * n.factorial := by
  induction n generalizing acc with
  | zero => simp [factAux]
  | succ n ih => rw [factAux, ih, Nat.factorial_succ]; ring

/-- If `D ∣ N`, the rational number `N / D` is the natural number `N / D`. -/
theorem cast_div_of_mod_eq_zero {N D : ℕ} (hD : D ≠ 0) (h : N % D = 0) :
    (N : ℚ) / D = ((N / D : ℕ) : ℚ) :=
  (Nat.cast_div (Nat.dvd_of_mod_eq_zero h) (by exact_mod_cast hD)).symm

/-- $3^m\prod_{k<n}(ck+1)/n!$ as a quotient of natural numbers that the kernel evaluates. -/
theorem prod_div_factorial_eq (c m n : ℕ) :
    (3 : ℚ) ^ m * (∏ k ∈ Finset.range n, ((c : ℚ) * k + 1)) / n.factorial =
      ((3 ^ m * prodAux c n 1 : ℕ) : ℚ) / (factAux n 1 : ℕ) := by
  rw [prodAux_eq, factAux_eq]
  push_cast
  simp

end KernelArithmetic

section BalaException

/-- Bala's exceptional set in A034171 ($d = 3$) and A298799 ($d = 9$): the numbers
$n = mp + k$ with $0 \le m \le (p-1)/d$ and $1 \le k \le (p-1)/d$. -/
def balaException (d p n : ℕ) : Prop :=
  ∃ m k : ℕ, n = m * p + k ∧ m ≤ (p - 1) / d ∧ 1 ≤ k ∧ k ≤ (p - 1) / d

end BalaException

section A034171

/-- OEIS A034171, offset $0$: $a(n) = 3^n\,\mathrm{A007559}(n+1)/(n+1)!$, where
$\mathrm{A007559}(n+1) = \prod_{k=0}^{n}(3k+1) = (3n+1)!!!$ is a triple factorial. -/
def a034171 (n : ℕ) : ℚ :=
  3 ^ n * (∏ k ∈ Finset.range (n + 1), (3 * k + 1 : ℚ)) / (n + 1).factorial

/-- Bala's conjecture in OEIS A034171, with his offset $1$, so that his $a(n)$ is
`a034171 (n - 1)`: for every prime $p \equiv 1 \pmod 3$ and every $n \ge 1$ outside his
exceptional set, $a(pn) \equiv a(n) \pmod{p^2}$. -/
def Conj034171 : Prop :=
  ∀ p : ℕ, p.Prime → p % 3 = 1 → ∀ n : ℕ, 1 ≤ n → ¬ balaException 3 p n →
    ∃ t : ℤ, a034171 (p * n - 1) - a034171 (n - 1) = (p : ℚ) ^ 2 * t

theorem a034171_eq (n : ℕ) :
    a034171 n = ((3 ^ n * prodAux 3 (n + 1) 1 : ℕ) : ℚ) / (factAux (n + 1) 1 : ℕ) := by
  rw [a034171, ← prod_div_factorial_eq]
  push_cast
  rfl

/-- The entry's first terms $1, 6, 42, 315, 2457, 19656$. -/
example : (List.range 6).map a034171 = [1, 6, 42, 315, 2457, 19656] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, a034171_eq]
  norm_num [prodAux, factAux]

/-- Bala's conjecture in OEIS A034171 is false. -/
theorem not_conj034171 : ¬ Conj034171 := by
  intro h
  have hex : ¬ balaException 3 7 50 := by
    rintro ⟨m, k, h1, h2, h3, h4⟩
    norm_num at h2 h4
    omega
  obtain ⟨t, ht⟩ := h 7 (by norm_num) (by norm_num) 50 (by norm_num) hex
  norm_num only at ht
  rw [a034171_eq, a034171_eq, cast_div_of_mod_eq_zero (by decide +kernel) (by decide +kernel),
    cast_div_of_mod_eq_zero (by decide +kernel) (by decide +kernel)] at ht
  have h1 : (3 ^ 349 * prodAux 3 (349 + 1) 1 / factAux (349 + 1) 1) % 49 = 31 := by
    decide +kernel
  have h2 : (3 ^ 49 * prodAux 3 (49 + 1) 1 / factAux (49 + 1) 1) % 49 = 17 := by
    decide +kernel
  generalize 3 ^ 349 * prodAux 3 (349 + 1) 1 / factAux (349 + 1) 1 = x at ht h1
  generalize 3 ^ 49 * prodAux 3 (49 + 1) 1 / factAux (49 + 1) 1 = y at ht h2
  have : (x : ℤ) - y = 49 * t := by exact_mod_cast ht
  omega

end A034171

section A298799

open PowerSeries

/-- $A(x) = (1 - 27x)^{-1/9}$, the generating function of OEIS A298799: the power series with
constant term $1$ and $A(x)^9 (1 - 27x) = 1$. -/
def IsGF298799 (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ A ^ 9 * (1 - 27 * X) = 1

/-- Bala's conjecture in OEIS A298799 for a sequence $a$: for every prime $p \equiv 1 \pmod 9$
and every $n \ge 1$ outside his exceptional set, $a(pn) \equiv a(n) \pmod{p^2}$. -/
def Conj298799 (a : ℕ → ℚ) : Prop :=
  ∀ p : ℕ, p.Prime → p % 9 = 1 → ∀ n : ℕ, 1 ≤ n → ¬ balaException 9 p n →
    ∃ t : ℤ, a (p * n) - a n = (p : ℚ) ^ 2 * t

/-- The product formula $a(n) = 3^n\prod_{k<n}(9k+1)/n!$ of OEIS A298799. -/
noncomputable def f298799 (n : ℕ) : ℚ :=
  3 ^ n * (∏ k ∈ Finset.range n, (9 * k + 1 : ℚ)) / n.factorial

theorem f298799_zero : f298799 0 = 1 := by simp [f298799]

theorem f298799_succ (n : ℕ) : f298799 (n + 1) * (n + 1) = (27 * n + 3) * f298799 n := by
  simp only [f298799, Finset.prod_range_succ, Nat.factorial_succ, pow_succ, Nat.cast_mul]
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem f298799_eq (n : ℕ) :
    f298799 n = ((3 ^ n * prodAux 9 n 1 : ℕ) : ℚ) / (factAux n 1 : ℕ) := by
  rw [f298799, ← prod_div_factorial_eq]
  push_cast
  rfl

theorem ofNat_eq_C (m : ℕ) [m.AtLeastTwo] : (OfNat.ofNat m : ℚ⟦X⟧) = C (OfNat.ofNat m : ℚ) :=
  (map_ofNat C m).symm

/-- $(1 - 27x)A' = 3A$ holds if and only if $(n+1)a(n+1) = (27n+3)a(n)$ for every $n$. -/
theorem derivative_eq_iff_coeff (A : ℚ⟦X⟧) :
    d⁄dX A * (1 - 27 * X) = 3 * A ↔
      ∀ n : ℕ, coeff (n + 1) A * (n + 1) = (27 * n + 3) * coeff n A := by
  have key : ∀ n : ℕ, coeff n (d⁄dX A * (1 - 27 * X)) - coeff n (3 * A) =
      coeff (n + 1) A * (n + 1) - (27 * n + 3) * coeff n A := by
    intro n
    have e : d⁄dX A * (1 - 27 * X) = d⁄dX A - C (27 : ℚ) * (d⁄dX A * X) := by
      rw [ofNat_eq_C 27]; ring
    rw [e, map_sub, coeff_derivative, ofNat_eq_C 3, coeff_C_mul, coeff_C_mul]
    rcases n with _ | m
    · simp
    · rw [coeff_succ_mul_X, coeff_derivative]
      push_cast
      ring
  constructor
  · intro h n
    have := key n
    rw [h, sub_self] at this
    linarith
  · intro h
    ext n
    have := key n
    rw [h n, sub_self] at this
    linarith

theorem derivative_one_sub_27X : d⁄dX (1 - 27 * X : ℚ⟦X⟧) = -27 := by
  rw [map_sub, derivative_one, ofNat_eq_C 27, Derivation.leibniz, derivative_C, derivative_X]
  simp

theorem derivative_eq_of_isGF298799 {A : ℚ⟦X⟧} (hA : IsGF298799 A) :
    d⁄dX A * (1 - 27 * X) = 3 * A := by
  obtain ⟨h0, h⟩ := hA
  have hd := congrArg (d⁄dX) h
  rw [Derivation.leibniz, derivative_one, derivative_pow, derivative_one_sub_27X] at hd
  simp only [smul_eq_mul, Nat.cast_ofNat] at hd
  norm_num at hd
  have hA0 : A ≠ 0 := by
    intro h'
    rw [h', map_zero] at h0
    exact zero_ne_one h0
  have : A ^ 8 * (9 * (d⁄dX A * (1 - 27 * X) - 3 * A)) = 0 := by
    linear_combination hd
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (pow_ne_zero _ hA0)
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (by rw [ofNat_eq_C 9]; exact (map_ne_zero C).mpr (by norm_num))
    · exact sub_eq_zero.mp h2

/-- Every solution has the coefficients $3^n\prod_{k<n}(9k+1)/n!$. -/
theorem coeff_eq_of_isGF298799 {A : ℚ⟦X⟧} (hA : IsGF298799 A) (n : ℕ) :
    coeff n A = f298799 n := by
  have hrec := (derivative_eq_iff_coeff A).mp (derivative_eq_of_isGF298799 hA)
  induction n with
  | zero => simpa [f298799_zero] using hA.1
  | succ n ih =>
    have h1 := hrec n
    rw [ih] at h1
    have : (n + 1 : ℚ) ≠ 0 := by positivity
    calc coeff (n + 1) A = coeff (n + 1) A * (n + 1) / (n + 1) := by field_simp
      _ = f298799 (n + 1) * (n + 1) / (n + 1) := by rw [h1, f298799_succ]
      _ = f298799 (n + 1) := by field_simp

theorem isGF298799_mk : IsGF298799 (mk f298799) := by
  have hB : d⁄dX (mk f298799) * (1 - 27 * X) = 3 * mk f298799 := by
    rw [derivative_eq_iff_coeff]
    intro n
    simp only [coeff_mk]
    exact f298799_succ n
  refine ⟨by simp [f298799_zero], ?_⟩
  apply derivative.ext
  · rw [Derivation.leibniz, derivative_one, derivative_pow, derivative_one_sub_27X]
    simp only [smul_eq_mul, Nat.cast_ofNat]
    norm_num
    linear_combination (9 * mk f298799 ^ 8) * hB
  · simp [f298799_zero]

/-- Exactly one power series is $(1 - 27x)^{-1/9}$. -/
theorem existsUnique_isGF298799 : ∃! A : ℚ⟦X⟧, IsGF298799 A := by
  refine ⟨mk f298799, isGF298799_mk, fun A hA => ?_⟩
  ext n
  rw [coeff_eq_of_isGF298799 hA, coeff_mk]

/-- The entry's first terms $1, 3, 45, 855, 17955, 398601$. -/
example (A : ℚ⟦X⟧) (hA : IsGF298799 A) :
    (List.range 6).map (fun n => coeff n A) = [1, 3, 45, 855, 17955, 398601] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, coeff_eq_of_isGF298799 hA, f298799_eq]
  norm_num [prodAux, factAux]

/-- Bala's conjecture in OEIS A298799 is false. -/
theorem not_conj298799 (A : ℚ⟦X⟧) (hA : IsGF298799 A) : ¬ Conj298799 (fun n => coeff n A) := by
  intro h
  have hex : ¬ balaException 9 19 362 := by
    rintro ⟨m, k, h1, h2, h3, h4⟩
    norm_num at h2 h4
    omega
  obtain ⟨t, ht⟩ := h 19 (by norm_num) (by norm_num) 362 (by norm_num) hex
  simp only [coeff_eq_of_isGF298799 hA] at ht
  norm_num only at ht
  rw [f298799_eq, f298799_eq, cast_div_of_mod_eq_zero (by decide +kernel) (by decide +kernel),
    cast_div_of_mod_eq_zero (by decide +kernel) (by decide +kernel)] at ht
  have h1 : (3 ^ 6878 * prodAux 9 6878 1 / factAux 6878 1) % 361 = 218 := by
    decide +kernel
  have h2 : (3 ^ 362 * prodAux 9 362 1 / factAux 362 1) % 361 = 294 := by
    decide +kernel
  generalize 3 ^ 6878 * prodAux 9 6878 1 / factAux 6878 1 = x at ht h1
  generalize 3 ^ 362 * prodAux 9 362 1 / factAux 362 1 = y at ht h2
  have : (x : ℤ) - y = 361 * t := by exact_mod_cast ht
  omega

end A298799

section A382407

/-- The partitions $n = x + y + z$ into positive integers with $xy + yz + zx$ a perfect square,
as the triples $(x, y, z)$ with $1 \le x \le y \le z$. -/
def partitions382407 (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun t =>
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧
      IsSquare (t.1 * t.2.1 + t.2.1 * t.2.2 + t.1 * t.2.2)

/-- OEIS A382407: the number of partitions $n = x + y + z$ into positive integers with
$xy + yz + zx$ a perfect square. -/
def a382407 (n : ℕ) : ℕ := (partitions382407 n).card

/-- Huber's set $\{2, 4, 8, 13\} \cup \mathrm{A000244} \cup \mathrm{A005030}$, where
$\mathrm{A000244} = \{3^j : j \ge 0\}$ and $\mathrm{A005030} = \{5 \cdot 3^j : j \ge 0\}$. -/
def huberSet : Set ℕ := {2, 4, 8, 13} ∪ Set.range (3 ^ ·) ∪ Set.range (5 * 3 ^ ·)

/-- Huber's conjecture in OEIS A382407 (offset $1$): for $k \ge 1$, $a(k) = 0$ if and only if
$k$ lies in his set. -/
def Conj382407 : Prop := ∀ k : ℕ, 1 ≤ k → (a382407 k = 0 ↔ k ∈ huberSet)

/-- A bounded search for a square root, which the kernel evaluates quickly. -/
def SqCheck (P : ℕ) : Prop := ∃ m ∈ Finset.range (P + 1), m * m = P

instance : DecidablePred SqCheck :=
  fun P => inferInstanceAs (Decidable (∃ m ∈ Finset.range (P + 1), m * m = P))

theorem isSquare_iff_sqCheck (P : ℕ) : IsSquare P ↔ SqCheck P := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, Finset.mem_range.mpr ?_, hm.symm⟩
    rcases m with _ | m
    · omega
    · have : m + 1 ≤ (m + 1) * (m + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  · rintro ⟨m, -, hm⟩
    exact ⟨m, hm.symm⟩

/-- `partitions382407` with the bounded square test. -/
def partitionsCheck (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun t =>
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧
      SqCheck (t.1 * t.2.1 + t.2.1 * t.2.2 + t.1 * t.2.2)

theorem a382407_eq (n : ℕ) : a382407 n = (partitionsCheck n).card := by
  rw [a382407, partitions382407, partitionsCheck]
  congr 1
  refine Finset.filter_congr fun t _ => ?_
  rw [isSquare_iff_sqCheck]

/-- The entry's first terms $a(1), \dots, a(20)$. -/
example : (List.range 20).map (fun n => a382407 (n + 1)) =
    [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 3, 0, 1, 1, 1, 2, 2] := by
  simp only [a382407_eq]
  decide +kernel

/-- If $9 \mid x + y + z$ and $xy + yz + zx = m^2$, then $3$ divides $x$, $y$ and $z$. -/
theorem three_dvd_of_nine_dvd {x y z m : ℕ} (hn : 9 ∣ x + y + z)
    (hP : x * y + y * z + x * z = m * m) : 3 ∣ x ∧ 3 ∣ y ∧ 3 ∣ z := by
  have key : ∀ a ∈ Finset.range 9, ∀ b ∈ Finset.range 9, ∀ c ∈ Finset.range 9,
      ∀ d ∈ Finset.range 9, (a + b + c) % 9 = 0 →
      (a * b + b * c + a * c) % 9 = (d * d) % 9 → a % 3 = 0 ∧ b % 3 = 0 ∧ c % 3 = 0 := by
    decide +kernel
  have hx := Nat.mod_modEq x 9
  have hy := Nat.mod_modEq y 9
  have hz := Nat.mod_modEq z 9
  have hm := Nat.mod_modEq m 9
  have e1 : (x % 9 + y % 9 + z % 9) % 9 = 0 := by
    have := (hx.add hy).add hz
    unfold Nat.ModEq at this
    omega
  have e2 : (x % 9 * (y % 9) + y % 9 * (z % 9) + x % 9 * (z % 9)) % 9 =
      (m % 9 * (m % 9)) % 9 := by
    have h1 := ((hx.mul hy).add (hy.mul hz)).add (hx.mul hz)
    have h2 := hm.mul hm
    unfold Nat.ModEq at h1 h2
    rw [h1, hP, ← h2]
  have h9 : ∀ u : ℕ, u % 9 ∈ Finset.range 9 :=
    fun u => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num))
  obtain ⟨r1, r2, r3⟩ := key _ (h9 x) _ (h9 y) _ (h9 z) _ (h9 m) e1 e2
  omega

/-- The descent: if $9 \mid n$ and $a(n/3) = 0$, then $a(n) = 0$. -/
theorem a382407_eq_zero_of_nine_dvd {n : ℕ} (hn : 9 ∣ n) (h : a382407 (n / 3) = 0) :
    a382407 n = 0 := by
  rw [a382407, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h ⊢
  rintro ⟨x, y, z⟩ ht
  simp only [partitions382407, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht
  obtain ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩⟩, hxy, hyz, hs, ⟨m, hm⟩⟩ := ht
  obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩, ⟨z', rfl⟩⟩ := three_dvd_of_nine_dvd (hs ▸ hn) hm
  have h3m : 3 ∣ m := by
    have : 3 ∣ m * m := ⟨3 * (x' * y' + y' * z' + x' * z'), by rw [← hm]; ring⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp this with h | h <;> exact h
  obtain ⟨m', rfl⟩ := h3m
  apply h (x', y', z')
  simp only [partitions382407, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega, by omega,
    by omega, ⟨m', ?_⟩⟩
  have : 9 * (x' * y' + y' * z' + x' * z') = 9 * (m' * m') := by linarith [hm]
  omega

theorem a382407_three_pow (j : ℕ) : a382407 (3 ^ j) = 0 ∧ a382407 (3 ^ (j + 1)) = 0 := by
  induction j with
  | zero => exact ⟨by rw [a382407_eq]; decide +kernel, by rw [a382407_eq]; decide +kernel⟩
  | succ j ih =>
    refine ⟨ih.2, a382407_eq_zero_of_nine_dvd ⟨3 ^ j, by ring⟩ ?_⟩
    rw [show 3 ^ (j + 1 + 1) / 3 = 3 ^ (j + 1) by rw [pow_succ]; simp]
    exact ih.2

theorem a382407_five_mul_three_pow (j : ℕ) :
    a382407 (5 * 3 ^ j) = 0 ∧ a382407 (5 * 3 ^ (j + 1)) = 0 := by
  induction j with
  | zero => exact ⟨by rw [a382407_eq]; decide +kernel, by rw [a382407_eq]; decide +kernel⟩
  | succ j ih =>
    refine ⟨ih.2, a382407_eq_zero_of_nine_dvd ⟨5 * 3 ^ j, by ring⟩ ?_⟩
    rw [show 5 * 3 ^ (j + 1 + 1) / 3 = 5 * 3 ^ (j + 1) by rw [pow_succ]; omega]
    exact ih.2

/-- Huber's conjecture in OEIS A382407 is false. -/
theorem not_conj382407 : ¬ Conj382407 := by
  intro h
  have h10 : (10 : ℕ) ∈ huberSet :=
    (h 10 (by norm_num)).mp (by rw [a382407_eq]; decide +kernel)
  rcases h10 with (h10 | ⟨j, hj⟩) | ⟨j, hj⟩
  · simp at h10
  · rcases j with _ | j
    · simp at hj
    · simp only [pow_succ] at hj
      omega
  · rcases j with _ | j
    · simp at hj
    · simp only [pow_succ] at hj
      omega

/-- The "if" direction with $10$ added: if
$k \in \{2, 4, 8, 10, 13\} \cup \{3^j\} \cup \{5 \cdot 3^j\}$, then $a(k) = 0$. -/
theorem a382407_eq_zero_of_mem (k : ℕ)
    (hk : k ∈ ({2, 4, 8, 10, 13} : Set ℕ) ∪ Set.range (3 ^ ·) ∪ Set.range (5 * 3 ^ ·)) :
    a382407 k = 0 := by
  rcases hk with (hk | ⟨j, rfl⟩) | ⟨j, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> (rw [a382407_eq]; decide +kernel)
  · exact (a382407_three_pow j).1
  · exact (a382407_five_mul_three_pow j).1

end A382407

section A399793

/-- A finite set $S$ of positive integers is good if some $f : S \to \{-1, 1\}$ has
$\lvert\sum_{x \in S} x f(x)\rvert \le 1$. Here $f$ is a function on $\mathbb{N}$ whose values
on $S$ are $\pm 1$. -/
def IsGood399793 (S : Finset ℕ) : Prop :=
  ∃ f : ℕ → ℤ, (∀ x ∈ S, f x = 1 ∨ f x = -1) ∧ |∑ x ∈ S, (x : ℤ) * f x| ≤ 1

/-- OEIS A399793: the largest size of a bad subset of $\{1, \dots, n\}$. -/
noncomputable def a399793 (n : ℕ) : ℕ :=
  sSup {k | ∃ S ⊆ Finset.Icc 1 n, S.card = k ∧ ¬ IsGood399793 S}

/-- The lower bound in OEIS A399793: $\lfloor n/2 \rfloor$ if $n \equiv 2, 3, 4, 5 \pmod 8$,
and $\lfloor n/2 \rfloor - 1$ otherwise. -/
def ell399793 (n : ℕ) : ℕ :=
  if n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 then n / 2 else n / 2 - 1

/-- The conjecture in OEIS A399793: $a(n) = \ell(n)$ for every $n \ge 13$. -/
def Conj399793 : Prop := ∀ n : ℕ, 13 ≤ n → a399793 n = ell399793 n

/-- A sign function on `S` is the choice of the subset `T` where it is `1`. -/
theorem isGood399793_iff (S : Finset ℕ) :
    IsGood399793 S ↔ ∃ T ∈ S.powerset, |2 * ∑ x ∈ T, (x : ℤ) - ∑ x ∈ S, (x : ℤ)| ≤ 1 := by
  constructor
  · rintro ⟨f, hf, hs⟩
    refine ⟨S.filter (fun x => f x = 1), Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    have e : ∑ x ∈ S, (x : ℤ) * f x =
        2 * ∑ x ∈ S.filter (fun x => f x = 1), (x : ℤ) - ∑ x ∈ S, (x : ℤ) := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun x => f x = 1) (fun x => (x : ℤ) * f x),
        ← Finset.sum_filter_add_sum_filter_not S (fun x => f x = 1) (fun x => (x : ℤ))]
      have e1 : ∑ x ∈ S.filter (fun x => f x = 1), (x : ℤ) * f x =
          ∑ x ∈ S.filter (fun x => f x = 1), (x : ℤ) :=
        Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2, mul_one]
      have e2 : ∑ x ∈ S.filter (fun x => ¬ f x = 1), (x : ℤ) * f x =
          -∑ x ∈ S.filter (fun x => ¬ f x = 1), (x : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x hx => ?_
        obtain ⟨hxS, hx1⟩ := Finset.mem_filter.mp hx
        rcases hf x hxS with h | h
        · exact absurd h hx1
        · rw [h, mul_neg_one]
      rw [e1, e2]
      ring
    rwa [← e]
  · rintro ⟨T, hT, hs⟩
    rw [Finset.mem_powerset] at hT
    refine ⟨fun x => if x ∈ T then 1 else -1, fun x _ => by dsimp only; split_ifs <;> simp, ?_⟩
    have e : ∑ x ∈ S, (x : ℤ) * (if x ∈ T then 1 else -1) =
        2 * ∑ x ∈ T, (x : ℤ) - ∑ x ∈ S, (x : ℤ) := by
      have hT' : S.filter (fun x => x ∈ T) = T := by
        ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hT h, h⟩⟩
      rw [← Finset.sum_filter_add_sum_filter_not S (fun x => x ∈ T),
        ← Finset.sum_filter_add_sum_filter_not S (fun x => x ∈ T) (fun x => (x : ℤ)), hT']
      have e1 : ∑ x ∈ T, (x : ℤ) * (if x ∈ T then 1 else -1) = ∑ x ∈ T, (x : ℤ) :=
        Finset.sum_congr rfl fun x hx => by simp [hx]
      have e2 : ∑ x ∈ S.filter (fun x => x ∉ T), (x : ℤ) * (if x ∈ T then 1 else -1) =
          -∑ x ∈ S.filter (fun x => x ∉ T), (x : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun x hx => by simp [(Finset.mem_filter.mp hx).2]
      rw [e1, e2]
      ring
    rwa [e]

theorem bddAbove_a399793 (n : ℕ) :
    BddAbove {k | ∃ S ⊆ Finset.Icc 1 n, S.card = k ∧ ¬ IsGood399793 S} := by
  refine ⟨n, fun k ⟨S, hS, hk, _⟩ => ?_⟩
  have := Finset.card_le_card hS
  simp only [Nat.card_Icc, add_tsub_cancel_right] at this
  omega

/-- A bad subset of $\{1, \dots, n\}$ bounds $a(n)$ from below. -/
theorem card_le_a399793 {n : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 n)
    (hbad : ∀ T ∈ S.powerset, ¬ |2 * ∑ x ∈ T, (x : ℤ) - ∑ x ∈ S, (x : ℤ)| ≤ 1) :
    S.card ≤ a399793 n := by
  refine le_csSup (bddAbove_a399793 n) ⟨S, hS, rfl, ?_⟩
  rw [isGood399793_iff]
  rintro ⟨T, hT, h⟩
  exact hbad T hT h

/-- A bad set of size $k$ and goodness of every larger subset give $a(n) = k$. -/
theorem a399793_eq_of {n k : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 n)
    (hbad : ∀ T ∈ S.powerset, ¬ |2 * ∑ x ∈ T, (x : ℤ) - ∑ x ∈ S, (x : ℤ)| ≤ 1) (hk : S.card = k)
    (hup : ∀ U ∈ (Finset.Icc 1 n).powerset,
      (∀ T ∈ U.powerset, ¬ |2 * ∑ x ∈ T, (x : ℤ) - ∑ x ∈ U, (x : ℤ)| ≤ 1) → U.card ≤ k) :
    a399793 n = k := by
  refine le_antisymm (csSup_le ⟨k, S, hS, hk, ?_⟩ ?_) (hk ▸ card_le_a399793 S hS hbad)
  · rw [isGood399793_iff]
    rintro ⟨T, hT, h⟩
    exact hbad T hT h
  · rintro j ⟨U, hU, rfl, hbadU⟩
    exact hup U (Finset.mem_powerset.mpr hU) fun T hT h =>
      hbadU ((isGood399793_iff U).mpr ⟨T, hT, h⟩)

/-- The entry's first terms $a(2), \dots, a(8) = 1, 2, 2, 3, 4, 4, 5$; $a(6) = 4$ is its
example. -/
example : a399793 2 = 1 ∧ a399793 3 = 2 ∧ a399793 4 = 2 ∧ a399793 5 = 3 ∧ a399793 6 = 4 ∧
    a399793 7 = 4 ∧ a399793 8 = 5 :=
  ⟨a399793_eq_of {2} (by decide) (by decide +kernel) rfl (by decide +kernel),
    a399793_eq_of {1, 3} (by decide) (by decide +kernel) rfl (by decide +kernel),
    a399793_eq_of {1, 3} (by decide) (by decide +kernel) rfl (by decide +kernel),
    a399793_eq_of {1, 2, 5} (by decide) (by decide +kernel) rfl (by decide +kernel),
    a399793_eq_of {1, 4, 5, 6} (by decide) (by decide +kernel) rfl (by decide +kernel),
    a399793_eq_of {1, 4, 5, 6} (by decide) (by decide +kernel) rfl (by decide +kernel),
    a399793_eq_of {1, 2, 6, 7, 8} (by decide) (by decide +kernel) rfl (by decide +kernel)⟩

/-- For $13 \le n \le 17$, $a(n) > \ell(n)$. -/
theorem ell399793_lt_a399793 (n : ℕ) (h₁ : 13 ≤ n) (h₂ : n ≤ 17) :
    ell399793 n < a399793 n := by
  interval_cases n
  · exact lt_of_lt_of_le (by decide)
      (card_le_a399793 {1, 2, 9, 10, 11, 12, 13} (by decide) (by decide +kernel))
  · exact lt_of_lt_of_le (by decide)
      (card_le_a399793 {1, 2, 10, 11, 12, 13, 14} (by decide) (by decide +kernel))
  · exact lt_of_lt_of_le (by decide)
      (card_le_a399793 {1, 2, 3, 4, 13, 14, 15} (by decide) (by decide +kernel))
  · exact lt_of_lt_of_le (by decide)
      (card_le_a399793 {1, 2, 3, 12, 13, 14, 15, 16} (by decide) (by decide +kernel))
  · exact lt_of_lt_of_le (by decide)
      (card_le_a399793 {1, 2, 3, 13, 14, 15, 16, 17} (by decide) (by decide +kernel))

/-- The conjecture in OEIS A399793 is false. -/
theorem not_conj399793 : ¬ Conj399793 :=
  fun h => (ell399793_lt_a399793 13 le_rfl (by norm_num)).ne (h 13 le_rfl).symm

end A399793

end OeisDisproofs

end
