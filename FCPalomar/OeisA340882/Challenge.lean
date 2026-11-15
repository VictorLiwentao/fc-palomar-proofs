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
# Challenge: OEIS A340882 and A340883, Bala's pre-period conjectures

Written for this package; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

For an integer $q$ put $x = 1 + q$. The FORMULA line of OEIS A340882 defines the row polynomial
"R(n,q) = Sum_{k = 0..n-1} x^(k^2) * ( Product_{j = k+1..n-1} x^(2*j) - 1 ), where x = 1 + q."
The parentheses mean the product of $x^{2j} - 1$:
$R(n, q) = \sum_{k=0}^{n-1} x^{k^2} \prod_{j=k+1}^{n-1} (x^{2j} - 1)$ for $n \ge 1$, so
$R(1, q) = 1$, $R(2, q) = 1 + 3q + q^2$. The name and a comment of A340882 give $R$ through a
power series with the exponent $nk + n^2$; the data and the FORMULA line need $2nk + n^2$
there. We define $R$ by the FORMULA line. A340883 lists the row sums $a(n) = R(n, 1)$, with
FORMULA "a(n) = Sum_{k = 0..n-1} 2^(k^2) * ( Product_{j = k+1..n-1} 2^(2*j) - 1 )."
So $a = 1, 5, 91, 6245, 1658011, \dots$ (offset 1).

Peter Bala (OEIS, February 2021) conjectured:
- A340882: "Conjecture: For fixed integers q and N, the sequence mod(R(n,q),N)n>=1 is either
  purely periodic or periodic with a pre-period 1."
- A340883: "1) The sequence taken modulo n becomes periodic with a pre-period of length either
  0 or 1, and with the minimum period dividing phi(n)."
  Here Bala's $n$ is the modulus; we call it $m$.

*Conventions.* Both sequences start at $n = 1$; the value at $n = 0$ is the empty sum $0$ and
no statement uses it. A sequence $s$ has pre-period at most $n_0$ modulo $N$ when there is
$L \ge 1$ with $s(n + L) \equiv s(n) \pmod N$ for every $n > n_0$. "Purely periodic" is the
case $n_0 = 0$ and "pre-period 1" is the case $n_0 = 1$. A purely periodic sequence is also
periodic from $n = 2$ with the same $L$, so Bala's disjunction says exactly: there is $L \ge 1$
with $s(n + L) \equiv s(n)$ for every $n \ge 2$. For A340883 we state the clause as: there is
$L \ge 1$ with $L \mid \varphi(m)$ and $a(n + L) \equiv a(n) \pmod m$ for every $n \ge 2$. This
is exact: every eventual period is a multiple of the least one, and the start of periodicity
does not depend on the chosen period.

*The pre-period.* For a prime $p \mid x$ with $x \ne 0$, put $v = v_p(x)$ and $e = v_p(N)$.
The pre-period of $R(\cdot, q)$ modulo $p^e$ is $f(e, v)$: $0$ if $e \le v$, $1$ if
$v < e \le 5v$, and $\lceil e/(2v) \rceil - 1 = \lfloor (e-1)/(2v) \rfloor$ if $e > 5v$
(`localPrePeriod`). The pre-period modulo $N$ is the maximum of $f(v_p(N), v_p(x))$ over the
primes $p \mid N$ with $p \mid x$, and $0$ if there is no such prime (`prePeriod`). For $x = 0$
it is $0$, since $R(n, -1) = (-1)^{n-1}$; the definition treats this case separately, as
`padicValInt p 0 = 0` in Mathlib. For $x = \pm 1$ no prime divides $x$.

The file states:
- A340882 is false (`not_conjecture_A340882`). It holds for a given $q$ and every $N \ge 1$ if and
  only if $q \in \{-2, -1, 0\}$ (`conjecture_A340882_iff`). For $q \ne -1$ and every prime
  $p \mid x$ it fails at $N = p^{5 v_p(x) + 1}$ (`conjecture_A340882_fails`).
- The exact pre-period: for every $q$, $N \ge 1$ and $n_0$, the pre-period is at most $n_0$ if
  and only if `prePeriod q N ≤ n₀` (`prePeriod_spec`). Hence A340882 holds for $(q, N)$ if and
  only if $x = 0$ or $v_p(N) \le 5 v_p(x)$ for every prime $p \mid N$ with $p \mid x$
  (`conjecture_A340882_iff_local`).
- A340883 conjecture 1) is false (`not_conjecture1_A340883`): modulo $64$, $a(2) = 5$, and
  $a(n) \equiv 27$ for odd $n \ge 3$ and $a(n) \equiv 37$ for even $n \ge 4$ (`a_mod_64`).
- The corrected conjecture 1): the pre-period of A340883 modulo $m \ge 1$ is at most $1$ if and
  only if $64 \nmid m$ (`conjecture1_A340883_prePeriod_iff`); $a(n + \varphi(m)) \equiv a(n)
  \pmod m$ for every $n > P(1, m)$ (`a_period_totient`), so the period part holds for every
  $m$; and the full clause holds for $m$ if and only if $64 \nmid m$ (`conjecture1_A340883_iff`).
- A340883 conjecture 2) holds (`conjecture2_A340883`): Bala states that for coprime moduli the
  period modulo their product is the lcm of the two periods. Here the period modulo $m$ is the
  least eventual period (`period`). For coprime $m_1, m_2$ with $m_1 m_2 = 0$ the other modulus
  is $1$, and the identity holds trivially.

*References:*
- P. Bala, [A340882](https://oeis.org/A340882) and [A340883](https://oeis.org/A340883),
  OEIS, February 2021.
-/

@[expose] public section

namespace OeisA340882

open Finset

/-- OEIS A340882, row $n$: $R(n, q) = \sum_{k=0}^{n-1} x^{k^2} \prod_{j=k+1}^{n-1}
(x^{2j} - 1)$ with $x = 1 + q$ (the FORMULA line). -/
def R (n : ℕ) (q : ℤ) : ℤ :=
  ∑ k ∈ range n, (1 + q) ^ (k ^ 2) * ∏ j ∈ Ico (k + 1) n, ((1 + q) ^ (2 * j) - 1)

/-- OEIS A340883: $a(n) = \sum_{k=0}^{n-1} 2^{k^2} \prod_{j=k+1}^{n-1} (2^{2j} - 1)$, the row
sums $R(n, 1)$ of A340882. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ range n, 2 ^ (k ^ 2) * ∏ j ∈ Ico (k + 1) n, (2 ^ (2 * j) - 1)

/-- The pre-period of $R(\cdot, q)$ modulo $p^e$ for a prime $p$ with $v = v_p(1 + q) \ge 1$:
$0$ if $e \le v$, $1$ if $v < e \le 5v$, and $\lfloor (e-1)/(2v) \rfloor$ if $e > 5v$. -/
def localPrePeriod (e v : ℕ) : ℕ :=
  if e ≤ v then 0 else if e ≤ 5 * v then 1 else (e - 1) / (2 * v)

/-- The pre-period of $R(\cdot, q)$ modulo $N$: the maximum of `localPrePeriod` over the primes
$p \mid N$ with $p \mid 1 + q$, and $0$ when $1 + q = 0$. -/
def prePeriod (q : ℤ) (N : ℕ) : ℕ :=
  if 1 + q = 0 then 0 else
    (N.primeFactors.filter (fun p : ℕ => (p : ℤ) ∣ 1 + q)).sup
      (fun p => localPrePeriod (N.factorization p) (padicValInt p (1 + q)))

/-- Bala's A340882 conjecture is false: it is not true that for all integers $q$ and $N \ge 1$
there is $L \ge 1$ with $R(n + L, q) \equiv R(n, q) \pmod N$ for every $n \ge 2$. -/
theorem not_conjecture_A340882 :
    ¬ ∀ (q : ℤ) (N : ℕ), 1 ≤ N →
      ∃ L ≥ 1, ∀ n ≥ 2, R (n + L) q ≡ R n q [ZMOD N] := by
  sorry

/-- A340882 holds for a given $q$ and every $N \ge 1$ if and only if $q \in \{-2, -1, 0\}$,
that is $1 + q \in \{-1, 0, 1\}$. -/
theorem conjecture_A340882_iff (q : ℤ) :
    (∀ N : ℕ, 1 ≤ N → ∃ L ≥ 1, ∀ n ≥ 2, R (n + L) q ≡ R n q [ZMOD N]) ↔
      q = -2 ∨ q = -1 ∨ q = 0 := by
  sorry

/-- For $q \ne -1$ and every prime $p \mid 1 + q$, A340882 fails at $N = p^{5 v_p(1+q) + 1}$.
($p \mid 1 + q$ already excludes $1 + q = \pm 1$.) -/
theorem conjecture_A340882_fails (q : ℤ) (hq : q ≠ -1) (p : ℕ) (hp : p.Prime)
    (hpq : (p : ℤ) ∣ 1 + q) :
    ¬ ∃ L ≥ 1, ∀ n ≥ 2,
      R (n + L) q ≡ R n q [ZMOD p ^ (5 * padicValInt p (1 + q) + 1)] := by
  sorry

/-- The exact pre-period of $R(\cdot, q)$ modulo $N$: for every $n_0$ there is $L \ge 1$ with
$R(n + L, q) \equiv R(n, q) \pmod N$ for every $n > n_0$ if and only if
$P(q, N) \le n_0$. -/
theorem prePeriod_spec (q : ℤ) (N : ℕ) (hN : 1 ≤ N) (n₀ : ℕ) :
    (∃ L ≥ 1, ∀ n > n₀, R (n + L) q ≡ R n q [ZMOD N]) ↔ prePeriod q N ≤ n₀ := by
  sorry

/-- A340882 holds for $(q, N)$ if and only if $1 + q = 0$ or $v_p(N) \le 5 v_p(1 + q)$ for every
prime $p \mid N$ with $p \mid 1 + q$. -/
theorem conjecture_A340882_iff_local (q : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    (∃ L ≥ 1, ∀ n ≥ 2, R (n + L) q ≡ R n q [ZMOD N]) ↔
      1 + q = 0 ∨ ∀ p ∈ N.primeFactors, (p : ℤ) ∣ 1 + q →
        N.factorization p ≤ 5 * padicValInt p (1 + q) := by
  sorry

/-- Bala's A340883 conjecture 1) is false: it is not true that for every $m \ge 1$ there is
$L \ge 1$ with $L \mid \varphi(m)$ and $a(n + L) \equiv a(n) \pmod m$ for every $n \ge 2$. -/
theorem not_conjecture1_A340883 :
    ¬ ∀ m : ℕ, 1 ≤ m →
      ∃ L ≥ 1, L ∣ m.totient ∧ ∀ n ≥ 2, a (n + L) ≡ a n [ZMOD m] := by
  sorry

/-- A340883 modulo $64$: $a(2) = 5$, and for $n \ge 1$, $a(2n + 1) \equiv 27$ and
$a(2n + 2) \equiv 37 \pmod{64}$. So $a(2)$ never recurs and the pre-period is $2$. -/
theorem a_mod_64 :
    a 2 = 5 ∧ ∀ n ≥ 1, a (2 * n + 1) ≡ 27 [ZMOD 64] ∧ a (2 * n + 2) ≡ 37 [ZMOD 64] := by
  sorry

/-- The pre-period part of A340883 conjecture 1), corrected: for $m \ge 1$ there is $L \ge 1$
with $a(n + L) \equiv a(n) \pmod m$ for every $n \ge 2$ if and only if $64 \nmid m$. -/
theorem conjecture1_A340883_prePeriod_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ L ≥ 1, ∀ n ≥ 2, a (n + L) ≡ a n [ZMOD m]) ↔ ¬ 64 ∣ m := by
  sorry

/-- The period part of A340883 conjecture 1) holds for every $m \ge 1$:
$a(n + \varphi(m)) \equiv a(n) \pmod m$ for every $n > P(1, m)$. -/
theorem a_period_totient (m : ℕ) (hm : 1 ≤ m) :
    ∀ n > prePeriod 1 m, a (n + m.totient) ≡ a n [ZMOD m] := by
  sorry

/-- A340883 conjecture 1) holds for $m \ge 1$ if and only if $64 \nmid m$. -/
theorem conjecture1_A340883_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ L ≥ 1, L ∣ m.totient ∧ ∀ n ≥ 2, a (n + L) ≡ a n [ZMOD m]) ↔ ¬ 64 ∣ m := by
  sorry

/-- The period of A340883 modulo $m$: the least $L \ge 1$ with $a(n + L) \equiv a(n) \pmod m$
for all large $n$. -/
noncomputable def period (m : ℕ) : ℕ :=
  sInf {L : ℕ | 1 ≤ L ∧ ∃ n₀, ∀ n > n₀, a (n + L) ≡ a n [ZMOD m]}

/-- A340883 conjecture 2) holds: if $m_1$ and $m_2$ are coprime, the period of A340883 modulo
$m_1 m_2$ is the lcm of its periods modulo $m_1$ and modulo $m_2$. -/
theorem conjecture2_A340883 (m₁ m₂ : ℕ) (h : m₁.Coprime m₂) :
    period (m₁ * m₂) = (period m₁).lcm (period m₂) := by
  sorry

end OeisA340882

end
