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
# Challenge: OEIS A317345 and A317343, Hanna's residues modulo 10

Written for this package; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

OEIS A317345 is the e.g.f. $A(x) = \sum_n a(n) x^n / n!$ with
$[x^n]\, \exp(n^3 x) / A(x)^{n^2} = 0$ for $n \ge 1$. Paul D. Hanna conjectured (July 26, 2018)
"a(5*n+k) = [1,1,5,5,5](k) (mod 10), for n>=0 and k = 0..4". OEIS A317343 is the e.g.f. with
$[x^n]\, \exp(n^2 x) / A(x)^n = 0$ for $n \ge 1$. Its residues modulo $10$ are
$[1, 1, 3, 3, 5]$; OEIS does not state them.

Both entries belong to the family $F(a, b)$: $A(0) = 1$ and
$[x^n]\, \exp(n^a x)\, A(x)^{-n^b} = 0$ for every $n \ge 1$. A317345 is $F(3, 2)$ and A317343 is
$F(2, 1)$. The condition is invariant under $A \mapsto cA$. So $A(0) = 1$ is a normalization taken
from the data, where $a(0) = 1$; the OEIS name does not state it. In Lean, $\exp(n^a x)$ is
`rescale (n ^ a) (exp ℚ)` and $A^{-n^b}$ is `A⁻¹ ^ (n ^ b)`, where `A⁻¹` is the inverse in
`ℚ⟦X⟧`. Since $A(0) = 1$, this is the true inverse.

The general statement `padic_congruence`: if $1 \le b$ and `p` is a prime with $b < pa$, then
every $a(n)$ lies in $\mathbb{Z}_{(p)}$ and $a(n) \equiv a(n \bmod p) \pmod p$. Here
`padicNorm p q ≤ 1` means $q \in \mathbb{Z}_{(p)}$, and `padicNorm p (q - q') < 1` means
$q \equiv q' \pmod p$ in $\mathbb{Z}_{(p)}$. If $b < 2a$, this holds for every prime, so every
$a(n)$ is an integer (`integer_coefficients`).

*References:*
- Paul D. Hanna, [A317345](https://oeis.org/A317345), July 26, 2018.
- Paul D. Hanna, [A317343](https://oeis.org/A317343), July 26, 2018.
-/

@[expose] public section

namespace OeisA317345

open PowerSeries

/-- The family $F(a, b)$: $A(0) = 1$ and $[x^n]\,\exp(n^a x)\,A(x)^{-n^b} = 0$ for every
$n \ge 1$. -/
def IsSolution (a b : ℕ) (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧
    ∀ n : ℕ, 1 ≤ n → coeff n (rescale ((n : ℚ) ^ a) (exp ℚ) * A⁻¹ ^ (n ^ b)) = 0

/-- For all $a$ and $b$, exactly one power series has the property of $F(a, b)$. -/
theorem exists_unique_solution (a b : ℕ) : ∃! A : ℚ⟦X⟧, IsSolution a b A := by
  sorry

/-- Let $1 \le b$ and let `p` be a prime with $b < pa$. Then every $a(n) = n!\,[x^n] A(x)$ lies in
$\mathbb{Z}_{(p)}$, and $a(n) \equiv a(n \bmod p) \pmod p$. -/
theorem padic_congruence (a b p : ℕ) (hp : p.Prime) (hb : 1 ≤ b) (hbp : b < p * a) (A : ℚ⟦X⟧)
    (hA : IsSolution a b A) (n : ℕ) :
    padicNorm p ((n.factorial : ℚ) * coeff n A) ≤ 1 ∧
      padicNorm p ((n.factorial : ℚ) * coeff n A -
        ((n % p).factorial : ℚ) * coeff (n % p) A) < 1 := by
  sorry

/-- If $1 \le b < 2a$, then every $a(n) = n!\,[x^n] A(x)$ is an integer. -/
theorem integer_coefficients (a b : ℕ) (hb : 1 ≤ b) (hab : b < 2 * a) (A : ℚ⟦X⟧)
    (hA : IsSolution a b A) (n : ℕ) : ∃ z : ℤ, (n.factorial : ℚ) * coeff n A = z := by
  sorry

/-- Hanna's conjecture for OEIS A317345: every $a(n)$ is an integer and
$a(5n + k) \equiv [1, 1, 5, 5, 5](k) \pmod{10}$ for $n \ge 0$ and $0 \le k \le 4$. -/
theorem a317345_mod_ten (A : ℚ⟦X⟧) (hA : IsSolution 3 2 A) (n k : ℕ) (hk : k < 5) :
    ∃ z : ℤ, ((5 * n + k).factorial : ℚ) * coeff (5 * n + k) A = z ∧
      z ≡ [1, 1, 5, 5, 5].getD k 0 [ZMOD 10] := by
  sorry

/-- The analogue for OEIS A317343: every $a(n)$ is an integer and
$a(5n + k) \equiv [1, 1, 3, 3, 5](k) \pmod{10}$ for $n \ge 0$ and $0 \le k \le 4$. -/
theorem a317343_mod_ten (A : ℚ⟦X⟧) (hA : IsSolution 2 1 A) (n k : ℕ) (hk : k < 5) :
    ∃ z : ℤ, ((5 * n + k).factorial : ℚ) * coeff (5 * n + k) A = z ∧
      z ≡ [1, 1, 3, 3, 5].getD k 0 [ZMOD 10] := by
  sorry

end OeisA317345

end
