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
# Challenge: Erdős Problem 626, Erdős's upper bound for g_k(n)

Copied verbatim from `FormalConjectures/ErdosProblems/626.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos626

/--
`g k n` is $g_k(n)$: the largest $m$ such that some graph on $n$ vertices has chromatic number
exactly $k$ and girth $> m$, that is, no cycle of length $\leq m$.

The girth is `SimpleGraph.egirth`, which is `⊤` for an acyclic graph. The value `sSup ∅ = 0`
for $n < k$ affects only finitely many $n$. For $k \leq 2$ the set is unbounded whenever an
acyclic graph on $n$ vertices with chromatic number $k$ exists, and then `sSup` is also $0$; this
case is not used below, where $k \geq 4$.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.chromaticNumber = k ∧ (m : ℕ∞) < G.egirth}

/--
Erdős [Er59b] proved that for $k \geq 4$
$$g_k(n) \leq \frac{2}{\log(k-2)}\log n + 1.$$
We state it for all sufficiently large $n$.
-/
theorem erdos_626.variants.erdos_upper :
    ∀ k : ℕ, 4 ≤ k → ∀ᶠ n : ℕ in atTop,
      (g k n : ℝ) ≤ 2 * Real.log n / Real.log ((k : ℝ) - 2) + 1 := by
  sorry

end Erdos626

end
