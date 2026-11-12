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
# Challenge: Erdős Problem 1186, the van der Waerden and probabilistic bounds

Copied verbatim from `FormalConjectures/ErdosProblems/1186.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos1186

/--
`monoCount k n c` is the number of monochromatic $k$-term arithmetic progressions in
$\{1,\ldots,n\}$ under the $2$-colouring `c`. The progression $a, a+d, \ldots, a+(k-1)d$ with first
term $a$ and common difference $d \geq 1$ is the pair `(a, d)`, with $a \geq 1$ and
$a + (k-1)d \leq n$. Each progression is counted once.

This is the count of [Er80, p. 93]: there are $\sim n^2/(2(k-1))$ progressions, and the upper bound
in (7) there is their number times the probability $2^{1-k}$ that a random colouring makes one of
them monochromatic. The definition is meant for $k \geq 2$.
-/
def monoCount (k n : ℕ) (c : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ =>
    p.1 + (k - 1) * p.2 ≤ n ∧ ∀ i < k, c (p.1 + i * p.2) = c p.1).card

/--
`minMonoCount k n` is the least number of monochromatic $k$-term arithmetic progressions in a
$2$-colouring of $\{1,\ldots,n\}$. This is $A(n;k)$ in [Er80, p. 93]. The set of values contains
`monoCount k n (fun _ => true)`, so `sInf` is a true minimum.
-/
noncomputable def minMonoCount (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ c : ℕ → Bool, monoCount k n c = m}

/--
`δ k` is the largest constant $\delta_k$ such that every $2$-colouring of $\{1,\ldots,n\}$ has at
least $(\delta_k - o(1))n^2$ monochromatic $k$-term arithmetic progressions, that is,
$\liminf_{n\to\infty} A(n;k)/n^2$.

The quotient `minMonoCount k n / n ^ 2` lies in $[0,1]$, so this `liminf` is not a junk value.
Convergence of the quotient is not assumed. If it converges, `δ k` is its limit.
-/
noncomputable def δ (k : ℕ) : ℝ :=
  atTop.liminf (fun n : ℕ ↦ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2)

/--
Van der Waerden's theorem implies $\delta_k\gg_k 1$.

For fixed $k$ this says $\delta_k > 0$.
-/
theorem erdos_1186.variants.van_der_waerden (k : ℕ) (hk : 2 ≤ k) : 0 < δ k := by
  sorry

/--
The probabilistic method implies
$$\delta_k \leq \frac{1}{(k-1)2^{k}}.$$
-/
theorem erdos_1186.variants.probabilistic (k : ℕ) (hk : 2 ≤ k) :
    δ k ≤ 1 / (((k : ℝ) - 1) * 2 ^ k) := by
  sorry

end Erdos1186

end
