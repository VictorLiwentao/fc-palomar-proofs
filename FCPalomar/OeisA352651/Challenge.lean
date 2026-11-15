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
# Challenge: integrality of Bala's $u_N$ for $N \le -1$ (OEIS A352651)

In OEIS A352651 Peter Bala considers, for an integer $N \ne 0, 1$,
$$u_N(n) = \frac{\binom{Nn}{2n}\binom{Nn/2}{2n}\binom{2n}{n}^2}{\binom{Nn/2}{n}^2},$$
and conjectures that $u_N(n)$ is an integer for every $n \ge 0$. A352651 itself is the case
$N = 5$. This file states the conjecture for every $N \le -1$ (`u_integral`). R. Blanco Gómez
lists these cases as open (Remark 5.1). Bala's $p^{3k}$ supercongruences for $u_N$ are not
stated here.

*Reading of the binomials.* The entry defines
$\binom{x}{y} = \Gamma(x+1)/(\Gamma(y+1)\,\Gamma(x-y+1))$. In each binomial of $u_N(n)$ the
lower index is an integer $k \ge 0$, namely $2n$ or $n$. For $N < 0$ the top is a negative
integer or half-integer, where $\Gamma(x+1)$ can have a pole. We take the limit in the top with
$k$ fixed:
$$\binom{x}{k} = \frac{x(x-1)\cdots(x-k+1)}{k!} \qquad (x \in \mathbb{Q}).$$
This is `gbinom`. It agrees with Mathlib's `Ring.choose` on `ℚ`. It is Bala's own reading: his
formulas $\mathrm{A275652}(n) = \frac53\, u_{-1}(n)$ and $\mathrm{A275654}(n) = \frac75\, u_{-3}(n)$
for $n \ge 1$ hold under it. For example $u_{-1}(1) = 6$ and $\mathrm{A275652}(1) = 10$, and
$u_{-3}(1) = 20$ and $\mathrm{A275654}(1) = 28$. Continuing the whole Gamma quotient in $n$
instead gives $u_{-3}(1) = 100/3$, so under that reading the conjecture fails.

Division by zero in `ℚ` gives zero. For $N \le -1$ the denominator $\binom{Nn/2}{n}^2$ is
nonzero (`denominator_ne_zero`), so `u_integral` is not vacuous.

Written for this package from the OEIS entries; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

*References:*
- Peter Bala, [A352651](https://oeis.org/A352651), COMMENTS, March 25, 2022.
- Peter Bala, [A275652](https://oeis.org/A275652) and [A275654](https://oeis.org/A275654),
  FORMULA, March 2022.
- R. Blanco Gómez, Zenodo, [doi:10.5281/zenodo.23426707](https://doi.org/10.5281/zenodo.23426707),
  2026, Remark 5.1.
-/

@[expose] public section

namespace OeisA352651

open Finset

/-- The generalized binomial coefficient $\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$ for rational
$x$ and an integer $k \ge 0$. -/
def gbinom (x : ℚ) (k : ℕ) : ℚ := (∏ i ∈ range k, (x - i)) / k.factorial

/-- Bala's $u_N(n) = \binom{Nn}{2n}\binom{Nn/2}{2n}\binom{2n}{n}^2 / \binom{Nn/2}{n}^2$, with the
binomials read as `gbinom`. -/
def u (N : ℤ) (n : ℕ) : ℚ :=
  gbinom (N * n) (2 * n) * gbinom (N * n / 2) (2 * n) * gbinom (2 * n) n ^ 2 /
    gbinom (N * n / 2) n ^ 2

/-- For $N \le -1$ and $n \ge 0$, the binomial $\binom{Nn/2}{n}$ in the denominator of $u_N(n)$
is nonzero. -/
theorem denominator_ne_zero (N : ℤ) (hN : N ≤ -1) (n : ℕ) : gbinom (N * n / 2) n ≠ 0 := by
  sorry

/-- **Bala's conjecture for $N \le -1$, integrality.** For every integer $N \le -1$ and every
$n \ge 0$, $u_N(n)$ is an integer. -/
theorem u_integral (N : ℤ) (hN : N ≤ -1) (n : ℕ) : ∃ m : ℤ, u N n = m := by
  sorry

end OeisA352651

end
