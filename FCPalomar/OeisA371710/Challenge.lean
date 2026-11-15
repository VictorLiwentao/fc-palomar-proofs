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
# Challenge: OEIS A371710, Hanna's mod-3 pattern

Written for this package; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

OEIS A371710 is the e.g.f. $A(x) = \sum_{n \ge 1} a(n) x^n / n!$ with
$\sum_{n \ge 0} (A(x)^n - x)^n / n! = 1$. Paul D. Hanna conjectured (April 10, 2024):
"for n > 0, a(6*n + k) == [2,0,2,1,2,2] (mod 3) at k = [0,1,2,3,4,5], respectively."

The infinite sum is taken coefficientwise: for every $m$, the coefficient of $x^m$ in the
partial sums $\sum_{n < N}$ equals that of $1$ for all large $N$. This is convergence in the
$x$-adic topology. The term $n = 0$ is $1$. The equation forces $A(0) = 0$, since otherwise the
constant terms of the partial sums never stabilize.

The statements below give existence and uniqueness of $A$, integrality of every $a(m)$,
Hanna's pattern, and a stronger form: modulo $3$, $a(m) \equiv 2$ for even $m \ge 2$ and
$a(m) \equiv 1 - m$ for odd $m \ge 3$.

*References:*
- Paul D. Hanna, [A371710](https://oeis.org/A371710), April 10, 2024.
-/

@[expose] public section

namespace OeisA371710

open PowerSeries

/-- Hanna's equation $\sum_{n \ge 0} (A(x)^n - x)^n / n! = 1$. The infinite sum is taken
coefficientwise: for every $m$, the coefficient of $x^m$ in the partial sums $\sum_{n < N}$ equals
that of $1$ for all large $N$. -/
def IsSolution (A : ℚ⟦X⟧) : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, ∀ N' ≥ N,
    coeff m (∑ n ∈ Finset.range N', (n.factorial : ℚ)⁻¹ • (A ^ n - X) ^ n) = coeff m (1 : ℚ⟦X⟧)

/-- OEIS A371710: exactly one $A(x) \in \mathbb{Q}[[x]]$ satisfies
$\sum_{n \ge 0} (A(x)^n - x)^n / n! = 1$. -/
theorem a371710_existsUnique : ∃! A : ℚ⟦X⟧, IsSolution A := by
  sorry

/-- A solution has $A(0) = 0$, so $A(x) = \sum_{n \ge 1} a(n) x^n / n!$ as in the OEIS entry. -/
theorem a371710_constantCoeff (A : ℚ⟦X⟧) (hA : IsSolution A) : constantCoeff A = 0 := by
  sorry

/-- Every $a(m) = m!\,[x^m] A(x)$ is an integer. -/
theorem a371710_integral (A : ℚ⟦X⟧) (hA : IsSolution A) (m : ℕ) :
    ∃ a : ℤ, (m.factorial : ℚ) * coeff m A = a := by
  sorry

/-- Hanna's conjecture for OEIS A371710: for $n > 0$ and $k \in \{0, \dots, 5\}$,
$a(6n + k) \equiv [2, 0, 2, 1, 2, 2]_k \pmod 3$. -/
theorem a371710_mod_three (A : ℚ⟦X⟧) (hA : IsSolution A) (n : ℕ) (hn : 0 < n) (k : Fin 6) :
    ∃ a : ℤ, ((6 * n + (k : ℕ)).factorial : ℚ) * coeff (6 * n + (k : ℕ)) A = a ∧
      a ≡ ![2, 0, 2, 1, 2, 2] k [ZMOD 3] := by
  sorry

/-- The stronger form: $a(m) \equiv 2 \pmod 3$ for even $m \ge 2$, and
$a(m) \equiv 1 - m \pmod 3$ for odd $m \ge 3$. -/
theorem a371710_mod_three_strong (A : ℚ⟦X⟧) (hA : IsSolution A) (m : ℕ) (hm : 2 ≤ m) :
    ∃ a : ℤ, (m.factorial : ℚ) * coeff m A = a ∧
      (Even m → a ≡ 2 [ZMOD 3]) ∧ (Odd m → a ≡ 1 - m [ZMOD 3]) := by
  sorry

end OeisA371710

end
