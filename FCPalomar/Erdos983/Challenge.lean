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
# Challenge: Erdős Problem 983, the Erdős–Straus upper bound

Copied verbatim from `FormalConjectures/ErdosProblems/983.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos983

/-- `numSmooth A S` is the number of elements of `A` all of whose prime factors lie in `S`.
The element `1` has no prime factors, so it is counted for every `S`. -/
def numSmooth (A S : Finset ℕ) : ℕ :=
  (A.filter fun a => ∀ p ∈ a.primeFactors, p ∈ S).card

/-- $f(k,n)$ is the least $r$ such that every $A\subseteq\{1,\ldots,n\}$ with $|A|=k$ has a set
$S$ of $r$ primes with more than $r$ elements of $A$ divisible only by primes from $S$.

For $\pi(n)<k\leq n$ the value $r=\pi(n)$ is admissible (take all primes $\leq n$), so `sInf` is
a minimum. Outside this range `f k n = 0` is a junk value: for $k\leq\pi(n)$ no $r$ is
admissible, and for $k>n$ every $r$ is. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
    ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < numSmooth A S}

/--
Erdős and Straus [Er70b, p. 139, (14)] proved
$$f(\pi(n)+1,n)\leq 2\pi(n^{1/2})+1.$$
-/
theorem erdos_983.variants.upper_bound (n : ℕ) :
    f (Nat.primeCounting n + 1) n ≤ 2 * Nat.primeCounting (Nat.sqrt n) + 1 := by
  sorry

end Erdos983

end
