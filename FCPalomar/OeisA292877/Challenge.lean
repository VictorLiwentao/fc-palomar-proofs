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
# Challenge: Hanna's power-coefficient parity conjectures (OEIS A292877 and seven relatives)

Written for this package; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

Paul D. Hanna defined eight sequences by conditions on one coefficient of a power of their
generating function $A(x) = \sum_n a(n) x^n$, and conjectured where their odd terms are.

- A292877: $[x^{n-1}]\, 1/A(x)^{n^2} = 0$ for $n > 2$. Conjectures: (1) $a(2^n)$ is odd;
  (2) $a(n)$ is odd iff $n$ is Fibbinary; (3) there are $F(n+1)$ odd terms among
  $a(2^n), \dots, a(2^{n+1}-1)$.
- A303562: $[x^{n-1}]\, 1/A(x)^{n^2+n-1} = 0$ for $n > 2$. Conjecture: $a(n)$ is odd iff
  $n = (4^k-1)/3$.
- A303563: $[x^{n-1}]\, 1/A(x)^{n^2-n+1} = 0$ for $n > 2$. Conjecture: $a(n)$ is odd iff
  $n = 2^k - 1$.
- A171791: $[x^n]\, A(x)^{(n+1)^2} = 0$ for $n > 1$. Conjecture: for $n > 0$, $a(n)$ is odd iff
  $n = 2f + 1$ with $f$ Fibbinary.
- A230218: $[x^n]\, A(x)^{n^2+n+1} = 0$ for $n > 1$. Conjecture: for $n > 0$, $a(n)$ is odd iff
  $n$ is a power of $2$.
- A263075: $[x^{n-1}]\, A(x)^{n^2} = n^n (n-1)!$ for $n \ge 1$. Conjecture as for A171791.
- A263190: $[x^{n-1}]\, A(x)^{n^2} = (n!)^2$ for $n \ge 1$. Conjecture (3) as for A171791.
- A371673: $[x^{n-1}]\, A(x)^{n^2} = C_{n-1}\, n^n$ for $n \ge 1$. Conjecture as for A171791.

Here $C_n$ = `catalan n` and "Fibbinary" (OEIS A003714) means no two adjacent `1`s in binary,
stated as `n &&& (n >>> 1) = 0`. $F$ = `Nat.fib`.

*Readings.*
- $1/A(x)^k$ is `(A ^ k)⁻¹`, the inverse in `ℚ⟦X⟧`. Every condition below includes or forces
  $A(0) = 1$, so this is the true inverse.
- For the first five entries the conditions do not involve $a(0)$ and $a(1)$. The data and the
  PARI programs of these entries start with $a(0) = a(1) = 1$, and the name of A171791 states
  it. So the definitions include $a(0) = a(1) = 1$.
- For the last three entries the conditions at $n = 1, 2$ force $a(0) = a(1) = 1$, and nothing
  else is assumed.
- Each entry has exactly one solution in `ℚ⟦X⟧` (`*_existsUnique`), and its coefficients are
  integers (`*_integral`). The parity statements are about the integer sequence $a$ with
  $[x^n] A = a(n)$.
- For A263190 only conjecture (3) is stated. Conjectures (1), $a(n)/(n!)^2 \to 1/e$, and (2),
  no negative terms, are not treated.

*General form.* For $m \in \mathbb{Z}$ let $T_m \in \mathbb{Z}[[x]]$ be the Fuss–Catalan
series, the solution of $T = 1 + x T^m$ with $T(0) = 1$ (`IsFussCatalan`). Integer powers of
series with constant term $1$ are `zpowQ` and `zpowZ`. The package also states two families
that contain the eight entries.
- Family (I): $a(0) = a(1) = 1$ and $[x^N] A^{-(N^2 + (m-1)N + 1)} = 0$ for $N \ge 2$.
- Family (II): $a(0) = a(1) = 1$ and $[x^N] A^{N^2 - mN + 1} = R_N$ for $N \ge 2$, with
  $R_N \in \mathbb{Z}$.

Both families have exactly one solution (`familyI_existsUnique`, `familyII_existsUnique`). Its
coefficients are integers congruent modulo $2$ to those of $T_m$ (`familyI_integral_mod_two`,
`familyII_integral_mod_two`). In family (II) this assumes that $2E_N$ divides $R_N$ for
$N \ge 2$, where $E_N = N^2 - mN + 1$. This is equivalent to $v_p(R_N) \ge v_p(E_N)$ for every
prime $p$ together with $v_2(R_N) \ge v_2(E_N) + 1$.

With $N = n - 1$ where Hanna writes $[x^{n-1}]$, A303563, A292877 and A303562 are family (I)
with $m = 2, 3, 4$, A230218 is family (II) with $m = -1$, and the other four are family (II)
with $m = -2$.

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

/-! ### The general form -/

/-- For every $m \in \mathbb{Z}$ there is exactly one Fuss–Catalan series $T_m$. -/
theorem fussCatalan_existsUnique (m : ℤ) : ∃! T : ℤ⟦X⟧, IsFussCatalan m T := by
  sorry

/-- Family (I) has exactly one solution in `ℚ⟦X⟧`. -/
theorem familyI_existsUnique (m : ℤ) : ∃! A : ℚ⟦X⟧, IsFamilyI m A := by
  sorry

/-- Family (II) has exactly one solution in `ℚ⟦X⟧`. -/
theorem familyII_existsUnique (m : ℤ) (R : ℕ → ℤ) : ∃! A : ℚ⟦X⟧, IsFamilyII m R A := by
  sorry

/-- Family (I): every coefficient of $A$ is an integer, congruent modulo $2$ to the coefficient
of $T_m$. -/
theorem familyI_integral_mod_two (m : ℤ) (A : ℚ⟦X⟧) (hA : IsFamilyI m A) (T : ℤ⟦X⟧)
    (hT : IsFussCatalan m T) (n : ℕ) : ∃ a : ℤ, coeff n A = a ∧ 2 ∣ a - coeff n T := by
  sorry

/-- Family (II), when $2(N^2 - mN + 1)$ divides $R_N$ for $N \ge 2$: every coefficient of $A$
is an integer, congruent modulo $2$ to the coefficient of $T_m$. -/
theorem familyII_integral_mod_two (m : ℤ) (R : ℕ → ℤ)
    (hR : ∀ N : ℕ, 2 ≤ N → 2 * ((N : ℤ) ^ 2 - m * N + 1) ∣ R N) (A : ℚ⟦X⟧)
    (hA : IsFamilyII m R A) (T : ℤ⟦X⟧) (hT : IsFussCatalan m T) (n : ℕ) :
    ∃ a : ℤ, coeff n A = a ∧ 2 ∣ a - coeff n T := by
  sorry

/-! ### A292877 -/

/-- The g.f. of A292877 exists and is unique. -/
theorem a292877_existsUnique : ∃! A : ℚ⟦X⟧, IsA292877 A := by
  sorry

/-- A292877 has integer terms. -/
theorem a292877_integral (A : ℚ⟦X⟧) (hA : IsA292877 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n := by
  sorry

/-- A292877, conjecture (1): $a(2^n)$ is odd for $n \ge 0$. -/
theorem a292877_conj1 (A : ℚ⟦X⟧) (hA : IsA292877 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) : Odd (a (2 ^ n)) := by
  sorry

/-- A292877, conjecture (2): $a(n)$ is odd if and only if $n$ is a Fibbinary number. -/
theorem a292877_conj2 (A : ℚ⟦X⟧) (hA : IsA292877 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) : Odd (a n) ↔ Fibbinary n := by
  sorry

/-- A292877, conjecture (3): the number of odd terms among $a(2^n), \dots, a(2^{n+1}-1)$ is
$F(n+1)$, for $n \ge 0$. -/
theorem a292877_conj3 (A : ℚ⟦X⟧) (hA : IsA292877 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) :
    ((Finset.Icc (2 ^ n) (2 ^ (n + 1) - 1)).filter fun k => Odd (a k)).card = Nat.fib (n + 1) := by
  sorry

/-! ### A303562 and A303563 -/

/-- The g.f. of A303562 exists and is unique. -/
theorem a303562_existsUnique : ∃! A : ℚ⟦X⟧, IsA303562 A := by
  sorry

/-- A303562 has integer terms. -/
theorem a303562_integral (A : ℚ⟦X⟧) (hA : IsA303562 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n := by
  sorry

/-- A303562: $a(n)$ is odd if and only if $n = (4^k - 1)/3$ for some $k \ge 0$. -/
theorem a303562_parity (A : ℚ⟦X⟧) (hA : IsA303562 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) : Odd (a n) ↔ ∃ k, n = (4 ^ k - 1) / 3 := by
  sorry

/-- The g.f. of A303563 exists and is unique. -/
theorem a303563_existsUnique : ∃! A : ℚ⟦X⟧, IsA303563 A := by
  sorry

/-- A303563 has integer terms. -/
theorem a303563_integral (A : ℚ⟦X⟧) (hA : IsA303563 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n := by
  sorry

/-- A303563: $a(n)$ is odd if and only if $n = 2^k - 1$ for some $k \ge 0$. -/
theorem a303563_parity (A : ℚ⟦X⟧) (hA : IsA303563 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) : Odd (a n) ↔ ∃ k, n = 2 ^ k - 1 := by
  sorry

/-! ### A230218 -/

/-- The g.f. of A230218 exists and is unique. -/
theorem a230218_existsUnique : ∃! A : ℚ⟦X⟧, IsA230218 A := by
  sorry

/-- A230218 has integer terms. -/
theorem a230218_integral (A : ℚ⟦X⟧) (hA : IsA230218 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n := by
  sorry

/-- A230218: for $n > 0$, $a(n)$ is odd if and only if $n$ is a power of $2$. -/
theorem a230218_parity (A : ℚ⟦X⟧) (hA : IsA230218 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ k, n = 2 ^ k := by
  sorry

/-! ### A171791, A263075, A263190 and A371673 -/

/-- The g.f. of A171791 exists and is unique. -/
theorem a171791_existsUnique : ∃! A : ℚ⟦X⟧, IsA171791 A := by
  sorry

/-- A171791 has integer terms. -/
theorem a171791_integral (A : ℚ⟦X⟧) (hA : IsA171791 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n := by
  sorry

/-- A171791: for $n > 0$, $a(n)$ is odd if and only if $n = 2f + 1$ with $f$ Fibbinary. -/
theorem a171791_parity (A : ℚ⟦X⟧) (hA : IsA171791 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 := by
  sorry

/-- The g.f. of A263075 exists and is unique. -/
theorem a263075_existsUnique : ∃! A : ℚ⟦X⟧, IsA263075 A := by
  sorry

/-- A263075 has integer terms. -/
theorem a263075_integral (A : ℚ⟦X⟧) (hA : IsA263075 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n := by
  sorry

/-- A263075: for $n > 0$, $a(n)$ is odd if and only if $n = 2f + 1$ with $f$ Fibbinary. -/
theorem a263075_parity (A : ℚ⟦X⟧) (hA : IsA263075 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 := by
  sorry

/-- The g.f. of A263190 exists and is unique. -/
theorem a263190_existsUnique : ∃! A : ℚ⟦X⟧, IsA263190 A := by
  sorry

/-- A263190 has integer terms. -/
theorem a263190_integral (A : ℚ⟦X⟧) (hA : IsA263190 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n := by
  sorry

/-- A263190, conjecture (3): for $n > 0$, $a(n)$ is odd if and only if $n = 2f + 1$ with $f$
Fibbinary. -/
theorem a263190_conj3 (A : ℚ⟦X⟧) (hA : IsA263190 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 := by
  sorry

/-- The g.f. of A371673 exists and is unique. -/
theorem a371673_existsUnique : ∃! A : ℚ⟦X⟧, IsA371673 A := by
  sorry

/-- A371673 has integer terms. -/
theorem a371673_integral (A : ℚ⟦X⟧) (hA : IsA371673 A) : ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n := by
  sorry

/-- A371673: for $n > 0$, $a(n)$ is odd if and only if $n = 2f + 1$ with $f$ Fibbinary. -/
theorem a371673_parity (A : ℚ⟦X⟧) (hA : IsA371673 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n)
    (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ f, Fibbinary f ∧ n = 2 * f + 1 := by
  sorry

end OeisA292877

end
