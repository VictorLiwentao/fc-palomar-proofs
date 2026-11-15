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
# Challenge: OEIS A181316 and A180606, Hanna's $q$-integer powers

Write $[n]_q = 1 + q + \dots + q^{n-1}$, so that $[n]_q = (q^n - 1)/(q - 1)$ for $q \ne 1$.
Paul D. Hanna (OEIS A181316, 2010) conjectures that
$$\exp\Bigl(\sum_{n \ge 1} (q - 1) \Bigl(\frac{q^n - 1}{q - 1}\Bigr)^{n-1} \frac{x^n}{n}\Bigr)$$
has integer coefficients for every integer $q > 1$. A181316 is the case $q = 3$, and A180606
(Hanna, 2010) is $\exp\left(\sum_{n \ge 1} (2^n - 1)^{n-1} x^n / n\right)$, the case $q = 2$.

The file also states three extensions:
- the conjecture for every integer $q \ne 1$ (at $q = 1$ Hanna's expression is $0/0$);
- the sharp form: for integers $q$ and $c$, $\exp\left(\sum_{n \ge 1} c\,[n]_q^{n-1} x^n/n\right)$
  has integer coefficients if and only if every prime dividing $q - 1$ divides $c$;
- the same criterion for $c\,[n]_q^{e(n)}$ with a general exponent $e$, which also gives
  Hanna's claim on A155206 and A155210 (exponent $n$).

Integer coefficients are stated as `∀ n, ∃ z : ℤ, coeff n F = z`, and $\exp$ of a series $L$
with zero constant term as `subst L (exp ℚ)`.

Written for this package; not copied from an existing formalization.
The `sorry` marks the statements to be proved; it is not a proof.

*References:*
- Paul D. Hanna, [A181316](https://oeis.org/A181316), 2010 (the conjecture).
- Paul D. Hanna, [A180606](https://oeis.org/A180606), 2010.
- Paul D. Hanna, [A155206](https://oeis.org/A155206) and [A155210](https://oeis.org/A155210),
  2009 (exponent $n$).
-/

@[expose] public section

namespace OeisA181316

open PowerSeries

/-- The $q$-integer $[n]_q = \sum_{i < n} q^i$. For $q \ne 1$ it equals $(q^n - 1)/(q - 1)$;
for $q = 1$ it is $n$. -/
def qInt (q : ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, q ^ i

/-- Hanna's series $\sum_{n \ge 1} (q-1)\left(\frac{q^n-1}{q-1}\right)^{n-1} \frac{x^n}{n}$
over $\mathbb{Q}$, written as in A181316. -/
noncomputable def hannaSeries (q : ℤ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else
    ((q : ℚ) - 1) * (((q : ℚ) ^ n - 1) / ((q : ℚ) - 1)) ^ (n - 1) / n

/-- The series $\sum_{n \ge 1} c\,[n]_q^{e(n)} x^n / n$ over $\mathbb{Q}$. -/
noncomputable def logSeries (q c : ℤ) (e : ℕ → ℕ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (c : ℚ) * (qInt q n : ℚ) ^ e n / n

/-- **Hanna's conjecture (A181316).** For every integer $q > 1$,
$\exp\left(\sum_{n \ge 1} (q-1)\left(\frac{q^n-1}{q-1}\right)^{n-1} \frac{x^n}{n}\right)$ has
integer coefficients. -/
theorem conjecture (q : ℤ) (hq : 1 < q) (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (hannaSeries q) (exp ℚ)) = z := by
  sorry

/-- Hanna's conjecture holds for every integer $q \ne 1$. -/
theorem hannaSeries_integral (q : ℤ) (hq : q ≠ 1) (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (hannaSeries q) (exp ℚ)) = z := by
  sorry

/-- **OEIS A181316** ($q = 3$): $\exp\left(\sum_{n \ge 1} 2\left(\frac{3^n-1}{2}\right)^{n-1}
\frac{x^n}{n}\right)$ has integer coefficients. -/
theorem a181316_integral (n : ℕ) : ∃ z : ℤ, coeff n (subst (hannaSeries 3) (exp ℚ)) = z := by
  sorry

/-- **OEIS A180606** ($q = 2$): $\exp\left(\sum_{n \ge 1} (2^n - 1)^{n-1} x^n / n\right)$ has
integer coefficients. -/
theorem a180606_integral (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (mk fun n : ℕ => if n = 0 then (0 : ℚ) else
      ((2 : ℚ) ^ n - 1) ^ (n - 1) / n) (exp ℚ)) = z := by
  sorry

/-- **Sharp form.** For integers $q$ and $c$,
$\exp\left(\sum_{n \ge 1} c\,[n]_q^{n-1} x^n / n\right)$ has integer coefficients if and only
if every prime dividing $q - 1$ divides $c$. For $q = 1$ the condition means $c = 0$. -/
theorem integral_iff (q c : ℤ) :
    (∀ n, ∃ z : ℤ, coeff n (subst (logSeries q c (fun n => n - 1)) (exp ℚ)) = z) ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ q - 1 → (p : ℤ) ∣ c := by
  sorry

/-- **General exponent.** Let $e(pM) \equiv e(M) \pmod{\varphi(p^k)}$ whenever $p$ is prime and
$p^k \mid pM$ (equivalently, $e(N) \equiv e(N/p) \pmod{\varphi(p^{v_p(N)})}$ for every prime
$p \mid N$), and let $e(n) \ge 1$ for $n \ge 2$. Then for integers $q$ and $c$,
$\exp\left(\sum_{n \ge 1} c\,[n]_q^{e(n)} x^n / n\right)$ has integer coefficients if and only
if every prime dividing $q - 1$ divides $c$. -/
theorem integral_iff_of_exponent (q c : ℤ) (e : ℕ → ℕ)
    (he1 : ∀ p k M : ℕ, p.Prime → p ^ k ∣ p * M → e (p * M) ≡ e M [MOD Nat.totient (p ^ k)])
    (he2 : ∀ n, 2 ≤ n → 1 ≤ e n) :
    (∀ n, ∃ z : ℤ, coeff n (subst (logSeries q c e) (exp ℚ)) = z) ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ q - 1 → (p : ℤ) ∣ c := by
  sorry

/-- **Hanna's claim in A155206 and A155210.** For every integer $m \ne 1$,
$\exp\left(\sum_{n \ge 1} \frac{(m^n - 1)^n}{(m - 1)^{n-1}} \frac{x^n}{n}\right)$ has integer
coefficients. A155206 is $m = 3$ and A155210 is $m = 4$. At $m = 1$ the expression is $0/0$. -/
theorem a155206_integral (m : ℤ) (hm : m ≠ 1) (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (mk fun n : ℕ => if n = 0 then (0 : ℚ) else
      ((m : ℚ) ^ n - 1) ^ n / ((m : ℚ) - 1) ^ (n - 1) / n) (exp ℚ)) = z := by
  sorry

end OeisA181316

end
