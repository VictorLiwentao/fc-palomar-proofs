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
# Challenge: OEIS A333472, Bala's quadratic supercongruences for $[x^{rn}]\, c(x/(1+x))^{sn}$

Let $c(x) = (1 - \sqrt{1 - 4x})/(2x) = \sum_{n \ge 0} C_n x^n$ be the generating function of the
Catalan numbers (OEIS A000108), and let $F(x) = c(x/(1+x))$. OEIS A333472 is
$a(n) = [x^n]\, F(x)^n$. Peter Bala conjectures that
$a(np^k) \equiv a(np^{k-1}) \pmod{p^{2k}}$ for every prime $p \ge 5$ and all positive integers
$n$ and $k$. More generally, he conjectures the same congruences for
$a(r,s;n) = [x^{rn}]\, F(x)^{sn}$, for every positive integer $r$ and every integer $s$.

Here $c$ is the power series whose coefficients are the Catalan numbers `catalan n`, and
$x/(1+x)$ is $x$ times the inverse of $1 + x$. For $sn < 0$ the power $F^{sn}$ is a power of
the inverse of $F$, which is a unit because $F(0) = 1$.

Written for this package from the OEIS entry; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

*References:*
- Peter Bala, [A333472](https://oeis.org/A333472), March 23, 2020.
-/

@[expose] public section

namespace OeisA333472

open PowerSeries

/-- The Catalan generating function $c(x) = \sum_{n \ge 0} C_n x^n$ over $\mathbb{Z}$, where
$C_n$ = `catalan n` are the Catalan numbers (OEIS A000108). -/
noncomputable def c : PowerSeries ℤ := PowerSeries.mk fun n => (catalan n : ℤ)

/-- $F(x) = c(x/(1+x))$, where $x/(1+x)$ is $x$ times the inverse `invOfUnit (1 + X) 1` of
$1 + x$. -/
noncomputable def F : PowerSeries ℤ := c.subst (X * invOfUnit (1 + X) 1 : PowerSeries ℤ)

/-- The integer power $F(x)^m$ for $m \in \mathbb{Z}$. For $m < 0$ it is $(F^{-1})^{-m}$, where
$F^{-1}$ = `invOfUnit F 1` is the inverse of $F$, as $F(0) = 1$. -/
noncomputable def Fzpow (m : ℤ) : PowerSeries ℤ :=
  if 0 ≤ m then F ^ m.toNat else invOfUnit F 1 ^ m.natAbs

/-- Bala's $a(r,s;n) = [x^{rn}]\, F(x)^{sn}$. -/
noncomputable def a (r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (Fzpow (s * n))

/-- OEIS A333472: $a(n) = [x^n]\, c(x/(1+x))^n$. -/
noncomputable def A333472 (n : ℕ) : ℤ := coeff n (F ^ n)

/-- **Bala's general clause.** For every prime $p \ge 5$, every positive integer $r$, every
integer $s$ and all positive integers $n$ and $k$:
$a(r,s;np^k) \equiv a(r,s;np^{k-1}) \pmod{p^{2k}}$. -/
theorem a_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (2 * k) ∣ a r s (n * p ^ k) - a r s (n * p ^ (k - 1)) := by
  sorry

/-- **Bala's conjecture on A333472.** For every prime $p \ge 5$ and all positive integers $n$
and $k$: $a(np^k) \equiv a(np^{k-1}) \pmod{p^{2k}}$. -/
theorem a333472_tower (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (2 * k) ∣ A333472 (n * p ^ k) - A333472 (n * p ^ (k - 1)) := by
  sorry

end OeisA333472

end
