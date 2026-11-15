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
# Challenge: OEIS A326097 and A385907, Hanna's parity pattern

Written for this package; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

OEIS A326097 is the e.g.f. $A(x) = \sum_k a(k) x^k / k!$ with
$1 = \sum_{n \ge 0} ((1+x)^n - A(x))^n / n!$. Paul D. Hanna conjectured (June 6, 2019) that
"a(4*n+2) = 1 (mod 2), otherwise the terms a(k) are even for k > 3". The statements below
prove the stronger form: $a(k)$ is odd if and only if $k \in \{0, 1, 3\}$ or $k \equiv 2 \pmod 4$.
OEIS A385907 replaces $(1+x)^n$ by $1/(1-x)^n$; it has the same parity pattern.

The infinite sum is taken coefficientwise: for every $m$, the coefficient of $x^m$ in the
partial sums $\sum_{n < N}$ equals that of $1$ for all large $N$. This is convergence in the
$x$-adic topology. It forces $A(0) = 1$, since otherwise the constant terms of the partial sums
never stabilize.

*References:*
- Paul D. Hanna, [A326097](https://oeis.org/A326097), June 6, 2019.
- Paul D. Hanna, [A385907](https://oeis.org/A385907), July 24, 2025.
-/

@[expose] public section

namespace OeisA326097

open PowerSeries

/-- Hanna's equation $1 = \sum_{n \ge 0} (q(x)^n - A(x))^n / n!$ for a base series $q$.
The infinite sum is taken coefficientwise: for every $m$, the coefficient of $x^m$ in the partial
sums $\sum_{n < N}$ equals that of $1$ for all large $N$. -/
def IsSolution (q A : ℚ⟦X⟧) : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, ∀ N' ≥ N,
    coeff m (∑ n ∈ Finset.range N', (n.factorial : ℚ)⁻¹ • (q ^ n - A) ^ n) = coeff m (1 : ℚ⟦X⟧)

/-- OEIS A326097: exactly one $A(x) \in \mathbb{Q}[[x]]$ satisfies
$1 = \sum_{n \ge 0} ((1+x)^n - A(x))^n / n!$. -/
theorem a326097_existsUnique : ∃! A : ℚ⟦X⟧, IsSolution (1 + X) A := by
  sorry

/-- Hanna's parity conjecture for OEIS A326097, in the stronger form: every
$a(k) = k!\,[x^k] A(x)$ is an integer, and $a(k)$ is odd if and only if $k \in \{0, 1, 3\}$ or
$k \equiv 2 \pmod 4$. -/
theorem a326097_parity (A : ℚ⟦X⟧) (hA : IsSolution (1 + X) A) (k : ℕ) :
    ∃ a : ℤ, (k.factorial : ℚ) * coeff k A = a ∧ (Odd a ↔ k = 0 ∨ k = 1 ∨ k = 3 ∨ k % 4 = 2) := by
  sorry

/-- OEIS A385907: exactly one $A(x) \in \mathbb{Q}[[x]]$ satisfies
$1 = \sum_{n \ge 0} (1/(1-x)^n - A(x))^n / n!$. -/
theorem a385907_existsUnique : ∃! A : ℚ⟦X⟧, IsSolution (1 - X)⁻¹ A := by
  sorry

/-- The parity pattern of OEIS A385907: every $a(k) = k!\,[x^k] A(x)$ is an integer, and $a(k)$
is odd if and only if $k \in \{0, 1, 3\}$ or $k \equiv 2 \pmod 4$. -/
theorem a385907_parity (A : ℚ⟦X⟧) (hA : IsSolution (1 - X)⁻¹ A) (k : ℕ) :
    ∃ a : ℤ, (k.factorial : ℚ) * coeff k A = a ∧ (Odd a ↔ k = 0 ∨ k = 1 ∨ k = 3 ∨ k % 4 = 2) := by
  sorry

end OeisA326097

end
