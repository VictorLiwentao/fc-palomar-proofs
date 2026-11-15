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
# Challenge: counterexamples to five OEIS conjectures

Each section states one conjecture from an OEIS entry, with the entry's definitions, and asks
for its negation. Each refutation is a finite computation.

* **A333564** (P. Bala). The entry conjectures $a(np^k) \equiv a(np^{k-1}) \pmod{p^{3k}}$
  for primes $p \ge 3$ and $n, k \ge 1$. Bala adds that, for integer $r$ and positive integer
  $s$, the sequence $a(r,s;n) = 2^{rn}\sum_{k=0}^{sn-1}(-1)^{sn-1+k}\binom{n+k}{k}^r$
  "satisfies the same congruences". We read this as the modulus $p^{3k}$ for all primes
  $p \ge 3$. The revision history fixes this reading: revision 2 (Bala, Apr 7 2020) wrote "the
  same supercongruences", with the main conjecture for $p \ge 5$; revision 3 (Bala, Apr 9 2020)
  changed the main conjecture to $p \ge 3$; revision 24 (Oct 6 2021) replaced "supercongruences"
  by "congruences" in a global edit. Under the weaker reading modulo $p^k$ the counterexample
  does not apply.
  We state the clause for $r \ge 1$ only, where the values are integers. This is a special
  case of Bala's clause, so its failure refutes his clause.
* **A034171** (P. Bala). With offset $1$, $c(n) = \mathrm{A034171}(n-1)$, Bala conjectures
  $c(pn) \equiv c(n) \pmod{p^2}$ for every prime $p \equiv 1 \pmod 3$ and every $n \ge 1$
  that is not of the form $mp + k$ with $0 \le m \le (p-1)/3$ and $1 \le k \le (p-1)/3$.
* **A298799** (P. Bala). For the expansion $a(n)$ of $(1-27x)^{-1/9}$, the same statement
  for primes $p \equiv 1 \pmod 9$, with $(p-1)/9$ in place of $(p-1)/3$.
* **A382407** (F. Huber). For the number $a(n)$ of partitions $n = x + y + z$ into positive
  integers with $xy + yz + zx$ a perfect square, Huber conjectures that $a(k) = 0$ if and only
  if $k \in \{2, 4, 8, 13\} \cup \mathrm{A000244} \cup \mathrm{A005030}$, that is,
  $k = 2, 4, 8, 13$, $k = 3^j$ or $k = 5 \cdot 3^j$ with $j \ge 0$. A second statement asks
  for the "if" direction with $10$ added to the set.
* **A399793** (Y. Xie). A finite set $S$ of positive integers is good if some
  $f : S \to \{-1, 1\}$ has $\lvert\sum_{x \in S} x f(x)\rvert \le 1$, and bad otherwise. Let
  $a(n)$ be the largest size of a bad subset of $\{1, \dots, n\}$, and let
  $\ell(n) = \lfloor n/2 \rfloor$ if $n \equiv 2, 3, 4, 5 \pmod 8$ and
  $\ell(n) = \lfloor n/2 \rfloor - 1$ otherwise. The entry has $a(n) \ge \ell(n)$ and
  conjectures equality for $n \ge 13$.

The sequences A034171 and A298799 are defined over $\mathbb{Q}$. Their values are integers, so
a congruence modulo $p^2$ says that the difference is $p^2$ times an integer.

Written for this package from the OEIS entries; not copied from an existing formalization.
The `sorry`s mark the statements to be proved; they are not proofs.

*References:*
- Peter Bala, [A333564](https://oeis.org/A333564), April 7, 2020 (revision history:
  revisions 2, 3 and 24).
- Peter Bala, comments in [A034171](https://oeis.org/A034171) and
  [A298799](https://oeis.org/A298799), December 23, 2019.
- Felix Huber, [A382407](https://oeis.org/A382407), April 4, 2025.
- Yifan Xie, [A399793](https://oeis.org/A399793), September 12, 2026.
-/

@[expose] public section

namespace OeisDisproofs

section A333564

/-- Bala's family in OEIS A333564:
$a(r,s;n) = 2^{rn}\sum_{k=0}^{sn-1}(-1)^{sn-1+k}\binom{n+k}{k}^r$.
The entry is the case $r = s = 1$. -/
def a333564 (r s n : ℕ) : ℤ :=
  2 ^ (r * n) * ∑ k ∈ Finset.range (s * n), (-1) ^ (s * n - 1 + k) * ((n + k).choose k : ℤ) ^ r

/-- Bala's general clause in OEIS A333564, read with the modulus $p^{3k}$ and for $r \ge 1$:
for all $r, s \ge 1$, every prime $p \ge 3$ and all $n, k \ge 1$,
$a(r,s;np^k) \equiv a(r,s;np^{k-1}) \pmod{p^{3k}}$. -/
def Conj333564 : Prop :=
  ∀ r s : ℕ, 1 ≤ r → 1 ≤ s → ∀ p : ℕ, p.Prime → 3 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    a333564 r s (n * p ^ k) ≡ a333564 r s (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)]

/-- Bala's general clause in OEIS A333564 is false. -/
theorem not_conj333564 : ¬ Conj333564 := by
  sorry

end A333564

section BalaException

/-- Bala's exceptional set in A034171 ($d = 3$) and A298799 ($d = 9$): the numbers
$n = mp + k$ with $0 \le m \le (p-1)/d$ and $1 \le k \le (p-1)/d$. -/
def balaException (d p n : ℕ) : Prop :=
  ∃ m k : ℕ, n = m * p + k ∧ m ≤ (p - 1) / d ∧ 1 ≤ k ∧ k ≤ (p - 1) / d

end BalaException

section A034171

/-- OEIS A034171, offset $0$: $a(n) = 3^n\,\mathrm{A007559}(n+1)/(n+1)!$, where
$\mathrm{A007559}(n+1) = \prod_{k=0}^{n}(3k+1) = (3n+1)!!!$ is a triple factorial. -/
def a034171 (n : ℕ) : ℚ :=
  3 ^ n * (∏ k ∈ Finset.range (n + 1), (3 * k + 1 : ℚ)) / (n + 1).factorial

/-- Bala's conjecture in OEIS A034171, with his offset $1$, so that his $a(n)$ is
`a034171 (n - 1)`: for every prime $p \equiv 1 \pmod 3$ and every $n \ge 1$ outside his
exceptional set, $a(pn) \equiv a(n) \pmod{p^2}$. -/
def Conj034171 : Prop :=
  ∀ p : ℕ, p.Prime → p % 3 = 1 → ∀ n : ℕ, 1 ≤ n → ¬ balaException 3 p n →
    ∃ t : ℤ, a034171 (p * n - 1) - a034171 (n - 1) = (p : ℚ) ^ 2 * t

/-- Bala's conjecture in OEIS A034171 is false. -/
theorem not_conj034171 : ¬ Conj034171 := by
  sorry

end A034171

section A298799

open PowerSeries

/-- $A(x) = (1 - 27x)^{-1/9}$, the generating function of OEIS A298799: the power series with
constant term $1$ and $A(x)^9 (1 - 27x) = 1$. -/
def IsGF298799 (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ A ^ 9 * (1 - 27 * X) = 1

/-- Bala's conjecture in OEIS A298799 for a sequence $a$: for every prime $p \equiv 1 \pmod 9$
and every $n \ge 1$ outside his exceptional set, $a(pn) \equiv a(n) \pmod{p^2}$. -/
def Conj298799 (a : ℕ → ℚ) : Prop :=
  ∀ p : ℕ, p.Prime → p % 9 = 1 → ∀ n : ℕ, 1 ≤ n → ¬ balaException 9 p n →
    ∃ t : ℤ, a (p * n) - a n = (p : ℚ) ^ 2 * t

/-- Exactly one power series is $(1 - 27x)^{-1/9}$. -/
theorem existsUnique_isGF298799 : ∃! A : ℚ⟦X⟧, IsGF298799 A := by
  sorry

/-- Bala's conjecture in OEIS A298799 is false. -/
theorem not_conj298799 (A : ℚ⟦X⟧) (hA : IsGF298799 A) : ¬ Conj298799 (fun n => coeff n A) := by
  sorry

end A298799

section A382407

/-- The partitions $n = x + y + z$ into positive integers with $xy + yz + zx$ a perfect square,
as the triples $(x, y, z)$ with $1 \le x \le y \le z$. -/
def partitions382407 (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun t =>
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧
      IsSquare (t.1 * t.2.1 + t.2.1 * t.2.2 + t.1 * t.2.2)

/-- OEIS A382407: the number of partitions $n = x + y + z$ into positive integers with
$xy + yz + zx$ a perfect square. -/
def a382407 (n : ℕ) : ℕ := (partitions382407 n).card

/-- Huber's set $\{2, 4, 8, 13\} \cup \mathrm{A000244} \cup \mathrm{A005030}$, where
$\mathrm{A000244} = \{3^j : j \ge 0\}$ and $\mathrm{A005030} = \{5 \cdot 3^j : j \ge 0\}$. -/
def huberSet : Set ℕ := {2, 4, 8, 13} ∪ Set.range (3 ^ ·) ∪ Set.range (5 * 3 ^ ·)

/-- Huber's conjecture in OEIS A382407 (offset $1$): for $k \ge 1$, $a(k) = 0$ if and only if
$k$ lies in his set. -/
def Conj382407 : Prop := ∀ k : ℕ, 1 ≤ k → (a382407 k = 0 ↔ k ∈ huberSet)

/-- Huber's conjecture in OEIS A382407 is false. -/
theorem not_conj382407 : ¬ Conj382407 := by
  sorry

/-- The "if" direction with $10$ added: if
$k \in \{2, 4, 8, 10, 13\} \cup \{3^j\} \cup \{5 \cdot 3^j\}$, then $a(k) = 0$. -/
theorem a382407_eq_zero_of_mem (k : ℕ)
    (hk : k ∈ ({2, 4, 8, 10, 13} : Set ℕ) ∪ Set.range (3 ^ ·) ∪ Set.range (5 * 3 ^ ·)) :
    a382407 k = 0 := by
  sorry

end A382407

section A399793

/-- A finite set $S$ of positive integers is good if some $f : S \to \{-1, 1\}$ has
$\lvert\sum_{x \in S} x f(x)\rvert \le 1$. Here $f$ is a function on $\mathbb{N}$ whose values
on $S$ are $\pm 1$. -/
def IsGood399793 (S : Finset ℕ) : Prop :=
  ∃ f : ℕ → ℤ, (∀ x ∈ S, f x = 1 ∨ f x = -1) ∧ |∑ x ∈ S, (x : ℤ) * f x| ≤ 1

/-- OEIS A399793: the largest size of a bad subset of $\{1, \dots, n\}$. -/
noncomputable def a399793 (n : ℕ) : ℕ :=
  sSup {k | ∃ S ⊆ Finset.Icc 1 n, S.card = k ∧ ¬ IsGood399793 S}

/-- The lower bound in OEIS A399793: $\lfloor n/2 \rfloor$ if $n \equiv 2, 3, 4, 5 \pmod 8$,
and $\lfloor n/2 \rfloor - 1$ otherwise. -/
def ell399793 (n : ℕ) : ℕ :=
  if n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 then n / 2 else n / 2 - 1

/-- The conjecture in OEIS A399793: $a(n) = \ell(n)$ for every $n \ge 13$. -/
def Conj399793 : Prop := ∀ n : ℕ, 13 ≤ n → a399793 n = ell399793 n

/-- For $13 \le n \le 17$, $a(n) > \ell(n)$. -/
theorem ell399793_lt_a399793 (n : ℕ) (h₁ : 13 ≤ n) (h₂ : n ≤ 17) :
    ell399793 n < a399793 n := by
  sorry

/-- The conjecture in OEIS A399793 is false. -/
theorem not_conj399793 : ¬ Conj399793 := by
  sorry

end A399793

end OeisDisproofs

end
