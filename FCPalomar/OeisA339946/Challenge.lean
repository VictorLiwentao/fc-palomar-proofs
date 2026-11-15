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
# Challenge: OEIS A339946 and A361717, Bala's prime-level supercongruences

**A339946.** Peter Bala defines $a(n) = [x^n]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$, where $P_n$ is
the Legendre polynomial. He conjectures $a(p) \equiv a(1) \pmod{p^5}$ for every prime $p \ge 7$
(Dec 2020). In Mar 2022 he extends this: for every positive integer $m$, put
$a_m(n) = [x^{mn}]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$; then $a_m(p) \equiv a_m(1) \pmod{p^5}$ for
all primes $p \ge 7$.

The Legendre polynomial is $P_n(t) = \tilde P_n\bigl(\frac{1-t}{2}\bigr)$, where
$\tilde P_n(x) = \sum_k (-1)^k \binom{n}{k} \binom{n+k}{n} x^k$ is Mathlib's
`Polynomial.shiftedLegendre n` (its Rodrigues formula is
$n!\,\tilde P_n = \frac{d^n}{dx^n}\bigl(x^n (1-x)^n\bigr)$). We evaluate $P_n$ at the power series
$\frac{1-x}{1+x} \in \mathbb{Q}[[x]]$ and invert in $\mathbb{Q}[[x]]$; the constant term is
$P_n(1) = 1$. The values are rational by definition. A congruence $u \equiv v \pmod{p^5}$ is
stated as $u - v = p^5 z$ for an integer $z$.

We also state that the range $p \ge 7$ is optimal: $a_m(5) \equiv 2 + 625 m^2 \pmod{5^5}$, so the
congruence at $p = 5$ holds exactly when $5 \mid m$. This is not a claim of Bala; it records the
sharpness noted with the proof.

**A361717.** Bala defines $a(n) = \sum_{k=0}^{n-1} \binom{n-1}{k}^2 \binom{n+k}{k}$ (offset 0,
$a(0) = 0$). Conjecture 2 (Mar 2023): $a(p-1) \equiv 1 - 2p - p^2 \pmod{p^3}$ for every prime
$p \ne 3$.

Written for this package from the OEIS entries; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

*References:*
- Peter Bala, [A339946](https://oeis.org/A339946), Dec 23, 2020, and comment of Mar 10, 2022.
- Peter Bala, [A361717](https://oeis.org/A361717), Mar 26, 2023.
-/

@[expose] public section

namespace OeisA339946

open PowerSeries

/-- The Legendre polynomial $P_n(t) = \tilde P_n\bigl(\frac{1-t}{2}\bigr)$ over $\mathbb{Q}$, with
$\tilde P_n$ = `Polynomial.shiftedLegendre n`. -/
noncomputable def legendreP (n : ℕ) : Polynomial ℚ :=
  (Polynomial.map (Int.castRingHom ℚ) (Polynomial.shiftedLegendre n)).comp
    (Polynomial.C (1 / 2) * (1 - Polynomial.X))

/-- The power series $\frac{1-x}{1+x}$. -/
noncomputable def mobius : ℚ⟦X⟧ := (1 - X) * (1 + X)⁻¹

/-- Bala's $a_m(n) = [x^{mn}]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$. -/
noncomputable def am (m n : ℕ) : ℚ := coeff (m * n) (Polynomial.aeval mobius (legendreP n))⁻¹

/-- OEIS A339946: $a(n) = [x^n]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$. -/
noncomputable def a339946 (n : ℕ) : ℚ := coeff n (Polynomial.aeval mobius (legendreP n))⁻¹

/-- OEIS A361717: $a(n) = \sum_{k=0}^{n-1} \binom{n-1}{k}^2 \binom{n+k}{k}$. -/
def a361717 (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (n - 1).choose k ^ 2 * (n + k).choose k

/-- Bala (A339946, Mar 2022): for every $m \ge 1$ and every prime $p \ge 7$,
$a_m(p) \equiv a_m(1) \pmod{p^5}$. -/
theorem am_congr (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ z : ℤ, am m p - am m 1 = (p : ℚ) ^ 5 * z := by
  sorry

/-- Bala (A339946, Dec 2020): for every prime $p \ge 7$, $a(p) \equiv a(1) \pmod{p^5}$. -/
theorem a339946_congr (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ z : ℤ, a339946 p - a339946 1 = (p : ℚ) ^ 5 * z := by
  sorry

/-- Bala (A361717, Conjecture 2): for every prime $p \ne 3$,
$a(p-1) \equiv 1 - 2p - p^2 \pmod{p^3}$. -/
theorem a361717_conj2 (p : ℕ) (hp : p.Prime) (h3 : p ≠ 3) :
    (a361717 (p - 1) : ℤ) ≡ 1 - 2 * p - p ^ 2 [ZMOD p ^ 3] := by
  sorry

/-- Sharpness at $p = 5$: $a_m(5) \equiv 2 + 625 m^2 \pmod{5^5}$ for every $m \ge 1$. -/
theorem am_five (m : ℕ) (hm : 1 ≤ m) : ∃ z : ℤ, am m 5 = 2 + 625 * (m : ℚ) ^ 2 + 5 ^ 5 * z := by
  sorry

/-- At $p = 5$, $a_m(5) \equiv a_m(1) \pmod{5^5}$ holds exactly when $5 \mid m$. So $p \ge 7$ is
the optimal uniform range. -/
theorem am_five_congr_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ z : ℤ, am m 5 - am m 1 = (5 : ℚ) ^ 5 * z) ↔ 5 ∣ m := by
  sorry

end OeisA339946
