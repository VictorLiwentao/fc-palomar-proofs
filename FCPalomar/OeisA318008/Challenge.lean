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
# Challenge: OEIS A318008, Hanna's parity conjecture

Written for this package; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

OEIS A318008 is the o.g.f. $A(x) = \sum_{n \ge 1} a(n) x^n$ with $A(A(x - x^2)) = x + x^2$.
Paul D. Hanna conjectured (September 6, 2018) that "a(2^k-1) = 1 (mod 2) and
a(2^(k+1)-2) = 1 (mod 2) for k >= 1, and a(n) is even elsewhere".

The statements take $A \in \mathbb{Q}[[x]]$ with $A(0) = 0$, as the offset $1$ of the entry
requires. This condition makes both substitutions well defined. The normalization $a(1) = 1$ of
the data is not assumed: the equation forces it.

The entry also states $a(2n - 1) = \mathrm{A277292}(n)$. OEIS A277292 is the series
$G(x) = \sum_{n \ge 1} b(n) x^{2n-1}$ with $\mathrm{Rev}(G + G^2) = G - G^2$, where
$\mathrm{Rev}$ is the compositional inverse. The last statements take $G \in \mathbb{Q}[[x]]$
with $G(0) = 0$ and read the equation as $(G + G^2) \circ (G - G^2) = x$. They show that $G$ is
unique and odd, that $a(2n - 1) = b(n)$, and that $b(n)$ is an integer that is odd if and only if
$n$ is a power of $2$. The last fact is not an OEIS claim.

*References:*
- Paul D. Hanna, [A318008](https://oeis.org/A318008), September 6, 2018.
- Paul D. Hanna, [A277292](https://oeis.org/A277292), October 12, 2016.
-/

@[expose] public section

namespace OeisA318008

open PowerSeries

/-- The defining equation $A(A(x - x^2)) = x + x^2$ of OEIS A318008, for $A$ with $A(0) = 0$. -/
def IsSolution (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ A.subst (A.subst (X - X ^ 2 : ℚ⟦X⟧)) = X + X ^ 2

/-- OEIS A318008: exactly one $A(x) \in \mathbb{Q}[[x]]$ with $A(0) = 0$ satisfies
$A(A(x - x^2)) = x + x^2$. -/
theorem exists_unique_solution : ∃! A : ℚ⟦X⟧, IsSolution A := by
  sorry

/-- Hanna's parity conjecture for OEIS A318008: every $a(n) = [x^n] A(x)$ is an integer, and
$a(n)$ is odd if and only if $n = 2^k - 1$ or $n = 2^{k+1} - 2$ for some $k \ge 1$. -/
theorem parity_conjecture (A : ℚ⟦X⟧) (hA : IsSolution A) (n : ℕ) :
    ∃ a : ℤ, coeff n A = a ∧ (Odd a ↔ ∃ k ≥ 1, n = 2 ^ k - 1 ∨ n = 2 ^ (k + 1) - 2) := by
  sorry

/-- The defining equation $\mathrm{Rev}(G + G^2) = G - G^2$ of OEIS A277292, for $G$ with
$G(0) = 0$: the series $G - G^2$ is the compositional inverse of $G + G^2$. -/
def IsSolution277292 (G : ℚ⟦X⟧) : Prop :=
  constantCoeff G = 0 ∧ (G + G ^ 2).subst (G - G ^ 2) = X

/-- OEIS A277292: exactly one $G(x) \in \mathbb{Q}[[x]]$ with $G(0) = 0$ satisfies
$\mathrm{Rev}(G + G^2) = G - G^2$. -/
theorem a277292_existsUnique : ∃! G : ℚ⟦X⟧, IsSolution277292 G := by
  sorry

/-- The series $G$ of OEIS A277292 is odd, as the formula $G(x) = \sum_{n \ge 1} b(n) x^{2n-1}$
of the entry states. -/
theorem a277292_odd (G : ℚ⟦X⟧) (hG : IsSolution277292 G) (n : ℕ) : coeff (2 * n) G = 0 := by
  sorry

/-- The comment $a(2n - 1) = \mathrm{A277292}(n)$ of OEIS A318008: the odd coefficients of $A$
are those of $G$. -/
theorem a318008_odd_bisection (A G : ℚ⟦X⟧) (hA : IsSolution A) (hG : IsSolution277292 G)
    (n : ℕ) (hn : 1 ≤ n) : coeff (2 * n - 1) A = coeff (2 * n - 1) G := by
  sorry

/-- OEIS A277292 is integral, and $\mathrm{A277292}(n) = [x^{2n-1}] G(x)$ is odd if and only if
$n$ is a power of $2$. -/
theorem a277292_parity (G : ℚ⟦X⟧) (hG : IsSolution277292 G) (n : ℕ) (hn : 1 ≤ n) :
    ∃ b : ℤ, coeff (2 * n - 1) G = b ∧ (Odd b ↔ ∃ j, n = 2 ^ j) := by
  sorry

end OeisA318008

end
