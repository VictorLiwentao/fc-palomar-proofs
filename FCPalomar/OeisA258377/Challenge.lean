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
# Challenge: OEIS A258377–A258381, Bala's 2-adic statements for Hanna's type-B series

Written for this package from the OEIS entries; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

For an integer $N$, Peter Bala (after Paul D. Hanna) considers the o.g.f. $A(z)$ with
$$A^{N+1}(z) = \frac{1}{1-z} \mathrm{BINOMIAL}(\mathrm{BINOMIAL}(A(z)))^N, \qquad
\mathrm{BINOMIAL}(F)(z) = \frac{1}{1-z} F\Big(\frac{z}{1-z}\Big).$$
Equivalently, $A^{N+1}(z) = \frac{1}{1-z} \frac{1}{(1-2z)^N} A^N\big(\frac{z}{1-2z}\big)$.
OEIS A258377, A258378, A258379, A258380 and A258381 are the cases $N = 1, 2, 3, 4, 5$.

The statements take $N \in \mathbb{N}$ and $A \in \mathbb{Q}[[z]]$ with $A(0) = 1$ (offset $0$).
This makes the inverses and the substitutions well defined. The equation then determines $A$
(`existsUnique`). It forces $a(1) = 2N + 1$, as in the data. (The comment in A258377 writes the
form $1 + Nz + \dots$, copied from the type-A case; it is not assumed.) Statements about
$a(n) = [z^n] A(z)$ take an integer sequence `a` with these values; one exists
(`exists_int_coeff`).

Bala's comments of Dec 06 2017 (in the FORMULA field for A258379) state, for
$k = 1, 2, 3, \dots$:
- A258377 and A258381: $a(n)$ is odd and $a(n) \bmod 2^k$ is purely periodic with period
  $2^{k-1}$;
- A258378: $a(n) \equiv 1 \pmod 4$; A258379: $a(n)$ is odd; A258380: $a(n) \equiv 1 \pmod 8$;
  and $a(n) \bmod 2^k$ is purely periodic with period length a divisor of $2^{k-1}$;
- example patterns modulo $4$, $8$, $16$ and $32$ with their periods.

A period is the least period, `leastPeriodMod`, defined with `Function.minimalPeriod`. "Period
$2^{k-1}$" is read as least period exactly $2^{k-1}$. Bala's remarks on residues modulo $3$ and
$5$ are not formalized. The general statements hold for every $N$: integrality, period $2^{k-1}$
modulo $2^k$, and, for $k \ge 3$, least period exactly $2^{k-1}$ if and only if
$N \equiv 1, 2 \pmod 4$.

*References:*
- Peter Bala, [A258377](https://oeis.org/A258377), [A258378](https://oeis.org/A258378),
  [A258379](https://oeis.org/A258379), [A258380](https://oeis.org/A258380) and
  [A258381](https://oeis.org/A258381), May 28 2015; 2-adic comments Dec 06 2017.
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

/-- The two forms of the equation in the entries agree:
$\mathrm{BINOMIAL}(\mathrm{BINOMIAL}(A))^N = \frac{1}{(1-2z)^N} A^N(\frac{z}{1-2z})$. -/
theorem isSolution_iff (N : ℕ) (A : ℚ⟦X⟧) : IsSolution N A ↔ constantCoeff A = 1 ∧
    A ^ (N + 1) = (1 - X)⁻¹ * (1 - 2 * X)⁻¹ ^ N * (A ^ N).subst (X * (1 - 2 * X)⁻¹ : ℚ⟦X⟧) := by
  sorry

/-- For every $N$, exactly one $A \in \mathbb{Q}[[z]]$ with $A(0) = 1$ satisfies the type-B
equation. -/
theorem existsUnique (N : ℕ) : ∃! A : ℚ⟦X⟧, IsSolution N A := by
  sorry

/-- The coefficients $a(n)$ are integers. -/
theorem exists_int_coeff (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) :
    ∃ a : ℕ → ℤ, ∀ n, coeff n A = a n := by
  sorry

/-- Every $a(n)$ is odd. -/
theorem odd (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (n : ℕ) : Odd (a n) := by
  sorry

/-- For $k \ge 1$ and all $n \ge 0$: $a(n + 2^{k-1}) \equiv a(n) \pmod{2^k}$. -/
theorem periodic (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    a (n + 2 ^ (k - 1)) ≡ a n [ZMOD 2 ^ k] := by
  sorry

/-- For $k \ge 1$, $a(n) \bmod 2^k$ is purely periodic with least period dividing $2^{k-1}$. -/
theorem leastPeriodMod_dvd (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (k : ℕ) (hk : 1 ≤ k) :
    leastPeriodMod a (2 ^ k) ∣ 2 ^ (k - 1) := by
  sorry

/-- For $k \ge 3$ and all $n \ge 0$:
$a(n + 2^{k-2}) - a(n) \equiv 2^{k-2} \cdot 3N(N+1) \pmod{2^k}$. -/
theorem shift_sub (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (k : ℕ) (hk : 3 ≤ k) (n : ℕ) :
    a (n + 2 ^ (k - 2)) - a n ≡ 2 ^ (k - 2) * (3 * N * (N + 1)) [ZMOD 2 ^ k] := by
  sorry

/-- For $k \ge 3$, the least period of $a(n) \bmod 2^k$ is exactly $2^{k-1}$ if and only if
$N \equiv 1, 2 \pmod 4$. (For $k = 2$ it is $2$ for every odd $N$.) -/
theorem leastPeriodMod_eq_iff (N : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution N A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) (k : ℕ) (hk : 3 ≤ k) :
    leastPeriodMod a (2 ^ k) = 2 ^ (k - 1) ↔ N % 4 = 1 ∨ N % 4 = 2 := by
  sorry

/-- OEIS A258377 ($N = 1$), Peter Bala: $a(n)$ is odd, and for $k = 1, 2, 3, \dots$ the
sequence $a(n) \bmod 2^k$ is purely periodic with (least) period $2^{k-1}$. -/
theorem a258377 (A : ℚ⟦X⟧) (hA : IsSolution 1 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, Odd (a n)) ∧ ∀ k ≥ 1, leastPeriodMod a (2 ^ k) = 2 ^ (k - 1) := by
  sorry

/-- Bala's examples for A258377: $a(n) \bmod 4 = (1, 3, 1, 3, \dots)$ with period $2$, and
$a(n) \bmod 8 = (1, 3, 5, 7, 1, 3, 5, 7, \dots)$ with period $4$. -/
theorem a258377_examples (A : ℚ⟦X⟧) (hA : IsSolution 1 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 4) = ![1, 3] (Fin.ofNat 2 n)) ∧ leastPeriodMod a 4 = 2) ∧
    ((∀ n, (a n : ZMod 8) = ![1, 3, 5, 7] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 8 = 4) := by
  sorry

/-- OEIS A258378 ($N = 2$), Peter Bala: $a(n) \equiv 1 \pmod 4$, and for $k = 1, 2, 3, \dots$
the sequence $a(n) \bmod 2^k$ is purely periodic with period length a divisor of $2^{k-1}$.
Sharper: for $k \ge 3$ the least period is exactly $2^{k-1}$. -/
theorem a258378 (A : ℚ⟦X⟧) (hA : IsSolution 2 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, a n ≡ 1 [ZMOD 4]) ∧ (∀ k ≥ 1, leastPeriodMod a (2 ^ k) ∣ 2 ^ (k - 1)) ∧
      ∀ k ≥ 3, leastPeriodMod a (2 ^ k) = 2 ^ (k - 1) := by
  sorry

/-- Bala's examples for A258378: $a(n) \bmod 8 = (1, 5, 5, 1, \dots)$ with period $4$, and
$a(n) \bmod 16 = (1, 5, 5, 1, 9, 13, 13, 9, \dots)$ with period $8$. -/
theorem a258378_examples (A : ℚ⟦X⟧) (hA : IsSolution 2 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 8) = ![1, 5, 5, 1] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 8 = 4) ∧
    ((∀ n, (a n : ZMod 16) = ![1, 5, 5, 1, 9, 13, 13, 9] (Fin.ofNat 8 n)) ∧
      leastPeriodMod a 16 = 8) := by
  sorry

/-- OEIS A258379 ($N = 3$), Peter Bala: $a(n)$ is odd, and for $k = 1, 2, 3, \dots$ the
sequence $a(n) \bmod 2^k$ is purely periodic with period length a divisor of $2^{k-1}$. -/
theorem a258379 (A : ℚ⟦X⟧) (hA : IsSolution 3 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, Odd (a n)) ∧ ∀ k ≥ 1, leastPeriodMod a (2 ^ k) ∣ 2 ^ (k - 1) := by
  sorry

/-- Bala's examples for A258379: $a(n) \bmod 4 = (1, 3, \dots)$ with period $2$,
$a(n) \bmod 8 = (1, 7, \dots)$ with period $2$, and $a(n) \bmod 16 = (1, 7, 9, 15, \dots)$ with
period $4$. -/
theorem a258379_examples (A : ℚ⟦X⟧) (hA : IsSolution 3 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 4) = ![1, 3] (Fin.ofNat 2 n)) ∧ leastPeriodMod a 4 = 2) ∧
    ((∀ n, (a n : ZMod 8) = ![1, 7] (Fin.ofNat 2 n)) ∧ leastPeriodMod a 8 = 2) ∧
    ((∀ n, (a n : ZMod 16) = ![1, 7, 9, 15] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 16 = 4) := by
  sorry

/-- OEIS A258380 ($N = 4$), Peter Bala: $a(n) \equiv 1 \pmod 8$, and for $k = 1, 2, 3, \dots$
the sequence $a(n) \bmod 2^k$ is purely periodic with period length a divisor of $2^{k-1}$. -/
theorem a258380 (A : ℚ⟦X⟧) (hA : IsSolution 4 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, a n ≡ 1 [ZMOD 8]) ∧ ∀ k ≥ 1, leastPeriodMod a (2 ^ k) ∣ 2 ^ (k - 1) := by
  sorry

/-- Bala's examples for A258380: $a(n) \bmod 16 = (1, 9, 9, 1, \dots)$ with period $4$, and
$a(n) \bmod 32 = (1, 9, 25, 17, \dots)$ with period $4$. -/
theorem a258380_examples (A : ℚ⟦X⟧) (hA : IsSolution 4 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 16) = ![1, 9, 9, 1] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 16 = 4) ∧
    ((∀ n, (a n : ZMod 32) = ![1, 9, 25, 17] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 32 = 4) := by
  sorry

/-- OEIS A258381 ($N = 5$), Peter Bala: $a(n)$ is odd, and for $k = 1, 2, 3, \dots$ the
sequence $a(n) \bmod 2^k$ is purely periodic with (least) period $2^{k-1}$. -/
theorem a258381 (A : ℚ⟦X⟧) (hA : IsSolution 5 A) (a : ℕ → ℤ) (ha : ∀ n, coeff n A = a n) :
    (∀ n, Odd (a n)) ∧ ∀ k ≥ 1, leastPeriodMod a (2 ^ k) = 2 ^ (k - 1) := by
  sorry

/-- Bala's examples for A258381: $a(n) \bmod 4 = (1, 3, 1, 3, \dots)$ with period $2$, and
$a(n) \bmod 8 = (1, 3, 5, 7, 1, 3, 5, 7, \dots)$ with period $4$. -/
theorem a258381_examples (A : ℚ⟦X⟧) (hA : IsSolution 5 A) (a : ℕ → ℤ)
    (ha : ∀ n, coeff n A = a n) :
    ((∀ n, (a n : ZMod 4) = ![1, 3] (Fin.ofNat 2 n)) ∧ leastPeriodMod a 4 = 2) ∧
    ((∀ n, (a n : ZMod 8) = ![1, 3, 5, 7] (Fin.ofNat 4 n)) ∧ leastPeriodMod a 8 = 4) := by
  sorry

end OeisA258377

end
