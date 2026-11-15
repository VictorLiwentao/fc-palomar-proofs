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
# Challenge: OEIS A183128 and A183129, Hanna's binomial-power exponentials

For $f : \mathbb{N} \times \mathbb{N} \to \mathbb{Z}$, Paul D. Hanna's series have the form
$$\exp\Bigl(\sum_{n \ge 1} \Bigl[\sum_{k \ge 0} f(n,k)\,x^k\Bigr] \frac{x^n}{n}\Bigr).$$
The coefficient of $x^m$ in the logarithm is $\sum_{n=1}^{m} f(n, m-n)/n$. `hannaLog f` is the
power series over $\mathbb{Q}$ with these coefficients, and `hannaExp f` is its exponential.

Hanna (2010) conjectured that the following series have integer coefficients ("Conjecture: this
sequence consists entirely of integers"). Each entry defines its sequence (offset 0) as the
coefficients of the series.

| Entry | $f(n,k)$ | inner sum |
| --- | --- | --- |
| A183128 | $\binom{n+k-1}{k}^{k^2+1}$ | $k \ge 0$ |
| A183129 | $\binom{n+k-1}{k}^{k^2+k}$ | $k \ge 0$ |
| A181076 | $\binom{n+k-1}{k}^{n}$ | $k \ge 0$ |
| A181078 | $\binom{n+k-1}{k}^{n+k-1}$ | $k \ge 0$ |
| A181082 | $\binom{n}{k}^{n+k}$ | $0 \le k \le n$ |
| A181084 | $\binom{n}{k}^{n+k+1}$ | $0 \le k \le n$ |

He also notes that three related series do NOT have integer coefficients: the exponent $k^2$
(in A183128), the exponent $k^2+k-1$ (in A183129), and $\binom{n}{k}^{k}$ for $0 \le k \le n$
(in A181070). In Lean, `k ^ 2 + k - 1` is $0$ at $k = 0$, where the source has $-1$; both give
the term $1$, because $\binom{n-1}{0} = 1$.

The file also states the general results behind these claims for the univariate series
$A_e(x,x) = \exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} B(n,k)^{e(n,k)} x^k] x^n/n\bigr)$ with
$B(n,k) = [z^k]\,U(z)^n$ and $U \in 1 + z\mathbb{Z}[[z]]$: the integrality criterion (Theorem 1),
its Corollary 2, and the obstruction at $k = 1$ (Theorem 4). The source states Theorem 1 for the
bivariate series $A_e(x,y)$; here only its diagonal $y = x$ is stated. $U = 1/(1-z)$ (written
`mk 1`) gives $B(n,k) = \binom{n+k-1}{k}$, and $U = 1 + z$ gives $B(n,k) = \binom{n}{k}$.

Integer coefficients are stated as `∃ z : ℤ, coeff m F = z`, and $\exp$ of a series $L$ with zero
constant term as `subst L (exp ℚ)`.

Written for this package; not copied from an existing formalization.
The `sorry` marks the statements to be proved; it is not a proof.

*References:*
- Paul D. Hanna, [A183128](https://oeis.org/A183128) and [A183129](https://oeis.org/A183129),
  2010.
- Paul D. Hanna, [A181076](https://oeis.org/A181076), [A181078](https://oeis.org/A181078),
  [A181082](https://oeis.org/A181082), [A181084](https://oeis.org/A181084) and
  [A181070](https://oeis.org/A181070), 2010.
-/

@[expose] public section

namespace OeisA181076

open PowerSeries

/-- Hanna's logarithm $\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr] \frac{x^n}{n}$ over
$\mathbb{Q}$: its coefficient of $x^m$ is $\sum_{n=1}^{m} f(n, m-n)/n$. -/
noncomputable def hannaLog (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ :=
  mk fun m => ∑ n ∈ Finset.Icc 1 m, (f n (m - n) : ℚ) / n

/-- Hanna's series $\exp\Bigl(\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr]
\frac{x^n}{n}\Bigr)$ over $\mathbb{Q}$. -/
noncomputable def hannaExp (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ := subst (hannaLog f) (exp ℚ)

/-- OEIS A183128: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+1} x^k] x^n/n\bigr)$. -/
noncomputable def a183128 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + 1))

/-- OEIS A183129: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+k} x^k] x^n/n\bigr)$. -/
noncomputable def a183129 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k))

/-- OEIS A181076: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{n} x^k] x^n/n\bigr)$. -/
noncomputable def a181076 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ n)

/-- OEIS A181078: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{n+k-1} x^k] x^n/n\bigr)$. -/
noncomputable def a181078 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1))

/-- OEIS A181082: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k=0}^{n} \binom{n}{k}^{n+k} x^k] x^n/n\bigr)$. -/
noncomputable def a181082 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k) else 0)

/-- OEIS A181084: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k=0}^{n} \binom{n}{k}^{n+k+1} x^k] x^n/n\bigr)$. -/
noncomputable def a181084 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k + 1) else 0)

/-- **Hanna's conjecture in A183128.** Every term of A183128 is an integer. -/
theorem a183128_integral (m : ℕ) : ∃ z : ℤ, a183128 m = z := by
  sorry

/-- **Hanna's conjecture in A183129.** Every term of A183129 is an integer. -/
theorem a183129_integral (m : ℕ) : ∃ z : ℤ, a183129 m = z := by
  sorry

/-- **Hanna's note in A183128.** The series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2} x^k] x^n/n\bigr)$ does not have
integer coefficients. -/
theorem a183128_note :
    ¬∀ m, ∃ z : ℤ, coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2)) = z := by
  sorry

/-- **Hanna's note in A183129.** The series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+k-1} x^k] x^n/n\bigr)$ does not
have integer coefficients. -/
theorem a183129_note :
    ¬∀ m, ∃ z : ℤ,
      coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k - 1)) = z := by
  sorry

/-- **Hanna's note in A181070.** The series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k=0}^{n} \binom{n}{k}^{k} x^k] x^n/n\bigr)$ does not have
integer coefficients. -/
theorem a181070_note :
    ¬∀ m, ∃ z : ℤ,
      coeff m (hannaExp fun n k => if k ≤ n then (n.choose k : ℤ) ^ k else 0) = z := by
  sorry

/-- **Hanna's conjecture in A181076.** Every term of A181076 is an integer. -/
theorem a181076_integral (m : ℕ) : ∃ z : ℤ, a181076 m = z := by
  sorry

/-- **Hanna's conjecture in A181078.** Every term of A181078 is an integer. -/
theorem a181078_integral (m : ℕ) : ∃ z : ℤ, a181078 m = z := by
  sorry

/-- **Hanna's conjecture in A181082.** Every term of A181082 is an integer. -/
theorem a181082_integral (m : ℕ) : ∃ z : ℤ, a181082 m = z := by
  sorry

/-- **Hanna's conjecture in A181084.** Every term of A181084 is an integer. -/
theorem a181084_integral (m : ℕ) : ∃ z : ℤ, a181084 m = z := by
  sorry

/-- **The criterion (Theorem 1), diagonal form.** Let $U \in 1 + z\mathbb{Z}[[z]]$,
$B(n,k) = [z^k]\,U^n$, and let $e(n,k) \ge 1$ for $n, k \ge 1$. Suppose that for every prime $p$
and all $n, k \ge 1$, with $b = B(n,k)$, $b' = B(pn,pk)$, $e = e(n,k)$, $e' = e(pn,pk)$ and
$r = 1 + v_p(n)$:
- (E1) if $p \nmid b$, then $e' \equiv e \pmod{(p-1)p^{v_p(n)}}$;
- (E2) if $p \mid b$, then $e' = e$, or both $p^r \mid b^e$ and $p^r \mid b'^{e'}$.

Then $\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} B(n,k)^{e(n,k)} x^k] x^n/n\bigr)$ has integer
coefficients. -/
theorem integral_of_criterion (U : ℤ⟦X⟧) (hU : constantCoeff U = 1) (e : ℕ → ℕ → ℕ)
    (he : ∀ n k : ℕ, 0 < n → 0 < k → 0 < e n k)
    (hE1 : ∀ p n k : ℕ, p.Prime → 0 < n → 0 < k → ¬(p : ℤ) ∣ coeff k (U ^ n) →
      e (p * n) (p * k) ≡ e n k [MOD (p - 1) * p ^ padicValNat p n])
    (hE2 : ∀ p n k : ℕ, p.Prime → 0 < n → 0 < k → (p : ℤ) ∣ coeff k (U ^ n) →
      e (p * n) (p * k) = e n k ∨
        ((p : ℤ) ^ (padicValNat p n + 1) ∣ coeff k (U ^ n) ^ e n k ∧
          (p : ℤ) ^ (padicValNat p n + 1) ∣ coeff (p * k) (U ^ (p * n)) ^ e (p * n) (p * k)))
    (m : ℕ) : ∃ z : ℤ, coeff m (hannaExp fun n k => coeff k (U ^ n) ^ e n k) = z := by
  sorry

/-- **Corollary 2(a), diagonal form.** For $U \in 1 + z\mathbb{Z}[[z]]$ and a constant exponent
$c \ge 1$, $\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} B(n,k)^{c} x^k] x^n/n\bigr)$ has integer
coefficients. -/
theorem integral_of_const_exponent (U : ℤ⟦X⟧) (hU : constantCoeff U = 1) {c : ℕ} (hc : 0 < c)
    (m : ℕ) : ∃ z : ℤ, coeff m (hannaExp fun n k => coeff k (U ^ n) ^ c) = z := by
  sorry

/-- **Corollary 2(b), diagonal form.** Let $U \in 1 + z\mathbb{Z}[[z]]$ and
$B(n,k) = [z^k]\,U^n$. Let $e(n,k)$ agree for $n \ge 1$ with a polynomial $P \in \mathbb{Z}[n,k]$,
with $e(n,k) \ge 1$ for $n, k \ge 1$. Assume (M): for all $n, k \ge 1$ with $|B(n,k)| \ge 2$
there is $j \ge 1$ with $n \mid j\,B(n,k)$ and $e(n,k) \ge \min(n, j+1)$. Then
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} B(n,k)^{e(n,k)} x^k] x^n/n\bigr)$ has integer
coefficients. -/
theorem integral_of_polynomial_exponent (U : ℤ⟦X⟧) (hU : constantCoeff U = 1)
    (e : ℕ → ℕ → ℕ) (P : MvPolynomial (Fin 2) ℤ)
    (hP : ∀ n k : ℕ, 0 < n → (e n k : ℤ) = MvPolynomial.eval ![(n : ℤ), k] P)
    (he : ∀ n k : ℕ, 0 < n → 0 < k → 0 < e n k)
    (hM : ∀ n k : ℕ, 0 < n → 0 < k → 2 ≤ |coeff k (U ^ n)| →
      ∃ j : ℕ, 0 < j ∧ (n : ℤ) ∣ j * coeff k (U ^ n) ∧ min n (j + 1) ≤ e n k)
    (m : ℕ) : ∃ z : ℤ, coeff m (hannaExp fun n k => coeff k (U ^ n) ^ e n k) = z := by
  sorry

/-- **The obstruction at $k = 1$ (Theorem 4), diagonal form.** Let $U \in 1 + z\mathbb{Z}[[z]]$
and $B(n,k) = [z^k]\,U^n$. Let $e(n,k)$ agree for $n \ge 1$ with a polynomial
$P \in \mathbb{Z}[n,k]$, with $e(n,k) \ge 1$ for $n, k \ge 1$. If a prime $p \nmid [z]\,U$ has
$e(p,1) = 1$ and $e(p^2,p) \ne 1$, then
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} B(n,k)^{e(n,k)} x^k] x^n/n\bigr)$ does not have integer
coefficients. -/
theorem not_integral_of_exponent (U : ℤ⟦X⟧) (hU : constantCoeff U = 1) (e : ℕ → ℕ → ℕ)
    (P : MvPolynomial (Fin 2) ℤ)
    (hP : ∀ n k : ℕ, 0 < n → (e n k : ℤ) = MvPolynomial.eval ![(n : ℤ), k] P)
    (he : ∀ n k : ℕ, 0 < n → 0 < k → 0 < e n k) {p : ℕ} (hp : p.Prime)
    (hu : ¬(p : ℤ) ∣ coeff 1 U) (h1 : e p 1 = 1) (h2 : e (p ^ 2) p ≠ 1) :
    ¬∀ m, ∃ z : ℤ, coeff m (hannaExp fun n k => coeff k (U ^ n) ^ e n k) = z := by
  sorry

end OeisA181076

end
