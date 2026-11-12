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
# Challenge: Dirac's 6-critical graphs, Erdős Problems 917 and 1032

Copied verbatim from `FormalConjectures/ErdosProblems/917.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f`, and `SimpleGraph.IsCriticalEdges`, `IsCriticalEdge`, `Subgraph.IsCriticalVerts`, `Subgraph.IsCriticalVertex` and `IsCritical` from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, and `IsKCritical` and the statement of `erdos_1032.variants.dirac_six` from `FormalConjectures/ErdosProblems/1032.lean` (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

section

variable {V : Type*} {G : SimpleGraph V}

namespace SimpleGraph

variable (G) in
/-- A set of edges is critical if deleting them reduces the chromatic number. -/
def IsCriticalEdges (edges : Set (Sym2 V)) : Prop :=
  (G.deleteEdges edges).chromaticNumber < G.chromaticNumber

variable (G) in
/-- An edge is critical if deleting it reduces the chromatic number. -/
def IsCriticalEdge (e : Sym2 V) : Prop := G.IsCriticalEdges ({e} : Set (Sym2 V))

/--
A set of vertices is critical if deleting them reduces the chromatic number.
-/
def Subgraph.IsCriticalVerts (verts : Set V) (G' : G.Subgraph) : Prop :=
  (G'.deleteVerts verts).coe.chromaticNumber < G'.coe.chromaticNumber

/--
A vertex is critical if deleting it reduces the chromatic number.
-/
def Subgraph.IsCriticalVertex (v : V) (G' : G.Subgraph) : Prop := G'.IsCriticalVerts {v}

variable (G)

/--
A graph `G` is `k`-critical (or vertex-critical) if its chromatic number is `k`,
and deleting any single vertex reduces the chromatic number.
-/
def IsCritical (k : ℕ) : Prop := G.chromaticNumber = k ∧ ∀ v, (⊤ : G.Subgraph).IsCriticalVertex v

end SimpleGraph

end

section

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

namespace SimpleGraph

/-- Copied from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`. -/
lemma lt_chromaticNumber_iff_not_colorable : n < G.chromaticNumber ↔ ¬ G.Colorable n := by
  rw [← chromaticNumber_le_iff_colorable, not_le]

/-- Copied from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`. -/
lemma le_chromaticNumber_iff_not_colorable (hn : n ≠ 0) :
    n ≤ G.chromaticNumber ↔ ¬ G.Colorable (n - 1) := by
  let n + 1 := n; simp [ENat.add_one_le_iff, lt_chromaticNumber_iff_not_colorable]

end SimpleGraph

end

open Filter Asymptotics

namespace Erdos917

/-- A graph `G` is `k`-critical if it has chromatic number `k` and every proper subgraph has
chromatic number less than `k`. For a finite graph a proper subgraph misses a vertex or an edge, so
this holds iff `G.IsCritical k` (deleting any vertex lowers the chromatic number) and deleting any
edge lowers the chromatic number.

The definition of Dirac quoted in [Er69b] uses only the edge condition. That would allow isolated
vertices, and then $f_k(n)$ below would be a running maximum. We use the standard notion, which is
also the one in [LMY23]. -/
def IsKCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.IsCritical k ∧ ∀ e ∈ G.edgeSet, G.IsCriticalEdge e

/-- $f_k(n)$ is the largest number of edges of a `k`-critical graph on `n` vertices. A graph on `n`
vertices has at most $\binom{n}{2}$ edges, so the `sSup` is a maximum whenever such a graph exists.
If there is none (for example if $n < k$), the value is `0`. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), IsKCritical G k ∧ G.edgeSet.ncard = m}

/-- The conjectured value $\frac{1}{2}\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2$ of $f_k(n)$
for $k \geq 6$. It is also used for $k = 3$ in `erdos_917.variants.erdos_three_dvd`, where it is
$0$. -/
noncomputable def conjecturedValue (k n : ℕ) : ℝ :=
  1 / 2 * (1 - 1 / ((k / 3 : ℕ) : ℝ)) * (n : ℝ) ^ 2

/--
In fact Dirac [Di52] proved
$$f_6(4n+2) \geq 4n^2+8n+3,$$
as witnessed by taking two disjoint copies of $C_{2n+1}$ and adding all edges between them.

We take $n \geq 1$, so that $C_{2n+1}$ is a cycle.
-/
theorem erdos_917.variants.dirac (n : ℕ) (hn : 1 ≤ n) :
    4 * n ^ 2 + 8 * n + 3 ≤ f 6 (4 * n + 2) := by
  sorry

/--
Erdős [Er69b] observed that Dirac's construction generalises to show that, if $3\mid k$, there are
infinitely many values of $n$ (those of the shape $mk/3$ where $m$ is odd) such that
$$f_k(n) \geq \frac{1}{2}\left(1-\frac{1}{k/3}\right)n^2 + n.$$

We take $m \geq 3$, so that the cycle $C_m$ exists.
-/
theorem erdos_917.variants.erdos_three_dvd (k : ℕ) (hk : 3 ≤ k) (h3 : 3 ∣ k) (m : ℕ)
    (hm : Odd m) (hm3 : 3 ≤ m) :
    conjecturedValue k (m * (k / 3)) + ((m * (k / 3) : ℕ) : ℝ) ≤ (f k (m * (k / 3)) : ℝ) := by
  sorry

end Erdos917

open Filter

namespace Erdos1032

def IsKCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.IsCritical k ∧ ∀ e ∈ G.edgeSet, G.IsCriticalEdge e

open scoped Classical in
theorem erdos_1032.variants.dirac_six :
    ∃ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n), IsKCritical G 6 ∧ (n : ℝ) / 2 < (G.minDegree : ℝ) := by
  sorry

end Erdos1032

end
