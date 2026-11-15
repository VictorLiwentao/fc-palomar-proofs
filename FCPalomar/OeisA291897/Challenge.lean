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
# Challenge: Shevelev's conjectures on OEIS A291897 and A292911 (Euler polynomials at $n$)

Written for this package from the OEIS entries; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

The Euler polynomials $E_m(x)$ have the e.g.f. $\sum_m E_m(x)\, t^m/m! = 2e^{xt}/(e^t + 1)$. The
Euler numbers $E_k$ have the e.g.f. $\operatorname{sech} t = \sum_k E_k\, t^k/k!$.

- A291897 (Vladimir Shevelev): $a(n)$ is the numerator of $E_{2n-1}(n)$, for $n \ge 1$.
  Conjecture: $a(n)$ is divisible by $(2n-1)^2$. The entry also notes that $(2n-1)^3$ sometimes
  divides $a(n)$, for example for $n = 1, 3, 7, 9, \dots$
- A292911 (Vladimir Shevelev): the numbers $n$ such that A291897$(n)$ is divisible by
  $(2n-1)^3$. Conjecture: every prime of the form $4k+1$ (A002144) is contained in the sequence
  $\{2a(n) - 1\}$.

*Definitions.*
- `eulerPoly m` is $E_m(x) \in \mathbb{Q}[x]$, defined by the recurrence
  $E_m(x) = x^m - \frac12 \sum_{k<m} \binom mk E_k(x)$. The theorem `eulerPoly_egf` states the
  e.g.f.: $\bigl(\sum_m E_m(x)\, t^m/m!\bigr)(e^t + 1) = 2e^{xt}$ for every $x \in \mathbb{Q}$.
- `eulerNum m` is $E_m \in \mathbb{Z}$, defined by
  $E_m = [m = 0] - \sum_{k<m,\ m-k \text{ even}} \binom mk E_k$. This is the coefficient form of
  $\cosh t \cdot \operatorname{sech} t = 1$. The theorem `eulerNum_egf` states
  $\bigl(\sum_k E_k\, t^k/k!\bigr)(e^t + e^{-t}) = 2$.
- `a291897 n` is `Rat.num` of $E_{2n-1}(n)$; the statements take $n \ge 1$, the offset of the
  entry. `a292911` is the set of terms of A292911, $\{n \ge 1 : (2n-1)^3 \mid a(n)\}$.

*Readings.* "Prime of the form $4k+1$" is `p % 4 = 1`. "$p$ is contained in $\{2a(n) - 1\}$"
means that $p = 2a - 1$ for some term $a$ of A292911.

*Further statements.*
- `a291897_cube_dvd_iff`: for $n \ge 1$, $(2n-1)^3 \mid a(n)$ if and only if $2n - 1$ divides
  the Euler number $E_{2n-2}$. This describes the note in A291897.
- `prime_cube_dvd_num_iff` and `prime_mem_a292911_iff`: for an odd prime $p$, $p^3$ divides the
  numerator of $E_p((p+1)/2)$, that is, $(p+1)/2$ is a term of A292911, if and only if
  $p \equiv 1 \pmod 4$. The "if" half is Shevelev's A292911 conjecture. The "only if" half says
  that no prime $p \equiv 3 \pmod 4$ is of the form $2a(n) - 1$.

*References:*
- Vladimir Shevelev, [A291897](https://oeis.org/A291897), September 22, 2017.
- Vladimir Shevelev, [A292911](https://oeis.org/A292911), September 26, 2017.
- NIST Digital Library of Mathematical Functions, [§24.2](https://dlmf.nist.gov/24.2), Euler
  numbers and polynomials.
-/

@[expose] public section

namespace OeisA291897

open PowerSeries

/-- The Euler polynomials, by the recurrence
$E_m(x) = x^m - \frac12 \sum_{k<m} \binom mk E_k(x)$. -/
noncomputable def eulerPoly (m : ℕ) : Polynomial ℚ :=
  Polynomial.X ^ m -
    Polynomial.C (1 / 2) * ∑ k : Fin m, (m.choose k : Polynomial ℚ) * eulerPoly k

/-- The Euler numbers, by the recurrence
$E_m = [m = 0] - \sum_{k<m,\ m-k \text{ even}} \binom mk E_k$. -/
def eulerNum (m : ℕ) : ℤ :=
  (if m = 0 then 1 else 0) -
    ∑ k : Fin m, if Even (m - k) then (m.choose k : ℤ) * eulerNum k else 0

/-- OEIS A291897: the numerator of $E_{2n-1}(n)$ (offset $1$). -/
noncomputable def a291897 (n : ℕ) : ℤ := ((eulerPoly (2 * n - 1)).eval (n : ℚ)).num

/-- OEIS A292911: the numbers $n \ge 1$ such that A291897$(n)$ is divisible by $(2n-1)^3$. -/
def a292911 : Set ℕ := {n | 1 ≤ n ∧ (2 * (n : ℤ) - 1) ^ 3 ∣ a291897 n}

/-- `eulerPoly` has the e.g.f. $\sum_m E_m(x)\, t^m/m! = 2e^{xt}/(e^t + 1)$. -/
theorem eulerPoly_egf (x : ℚ) :
    (mk fun m => (eulerPoly m).eval x / m.factorial) * (exp ℚ + 1) = 2 * rescale x (exp ℚ) := by
  sorry

/-- `eulerNum` has the e.g.f. $\sum_k E_k\, t^k/k! = \operatorname{sech} t = 2/(e^t + e^{-t})$. -/
theorem eulerNum_egf :
    (mk fun k => (eulerNum k : ℚ) / k.factorial) * (exp ℚ + rescale (-1) (exp ℚ)) = 2 := by
  sorry

/-- OEIS A291897, Shevelev's conjecture: $(2n-1)^2$ divides $a(n)$ for $n \ge 1$. -/
theorem a291897_conjecture (n : ℕ) (hn : 1 ≤ n) : (2 * (n : ℤ) - 1) ^ 2 ∣ a291897 n := by
  sorry

/-- For $n \ge 1$: $(2n-1)^3$ divides $a(n)$ if and only if $2n - 1$ divides the Euler number
$E_{2n-2}$. -/
theorem a291897_cube_dvd_iff (n : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℤ) - 1) ^ 3 ∣ a291897 n ↔ 2 * (n : ℤ) - 1 ∣ eulerNum (2 * n - 2) := by
  sorry

/-- OEIS A292911, Shevelev's conjecture: every prime $p \equiv 1 \pmod 4$ is $2a - 1$ for a term
$a$ of A292911. -/
theorem a292911_conjecture (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ a ∈ a292911, 2 * a - 1 = p := by
  sorry

/-- For an odd prime $p$: $p^3$ divides the numerator of $E_p((p+1)/2)$ if and only if
$p \equiv 1 \pmod 4$. -/
theorem prime_cube_dvd_num_iff (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : ℤ) ^ 3 ∣ ((eulerPoly p).eval (((p : ℚ) + 1) / 2)).num ↔ p % 4 = 1 := by
  sorry

/-- For an odd prime $p$: $(p+1)/2$ is a term of A292911 if and only if $p \equiv 1 \pmod 4$. -/
theorem prime_mem_a292911_iff (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (p + 1) / 2 ∈ a292911 ↔ p % 4 = 1 := by
  sorry

end OeisA291897

end
