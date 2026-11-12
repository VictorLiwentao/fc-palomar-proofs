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
# Challenge: WOWII Conjecture 291 is false (12-vertex counterexample)

Copied verbatim from `FormalConjectures/WrittenOnTheWallII/GraphConjecture291.lean` in google-deepmind/formal-conjectures at commit `691719db2653905d5fa0775408370fb058e4c59f`, and the definitions `numTrianglesAtVertex`, `IsTotalDominating`, `IsTotalNDominatingSet`, `totalDominationNumber` and `havelHakimiStep` copied verbatim from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/{Degrees,Domination,Residue}.lean` at the same commit (The Formal Conjectures Authors, Apache-2.0). Only imports, attributes, test lemmas and unrelated declarations are left out.
The `sorry` marks the statement to be proved; it is not a proof.
-/

@[expose] public section

namespace SimpleGraph

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of triangles (3-cliques) of `G` incident to vertex `v`:
the number of 3-element cliques containing `v`. -/
noncomputable def numTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card

end

section

variable {α : Type*} {G : SimpleGraph α} [Fintype α] [DecidableEq α]

/-- A set `D` is a total dominating set if every vertex is adjacent to a vertex
in `D`. -/
def IsTotalDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

/-- An `n`-total dominating set is a total dominating set with `n` vertices. -/
@[mk_iff]
structure IsTotalNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isTotalDominating : G.IsTotalDominating D
  card_eq : D.card = n

/-- The total domination number of `G`. -/
noncomputable def totalDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsTotalNDominatingSet n D}

end

/--
Helper function: Performs one step of the Havel-Hakimi reduction on a degree sequence.
Assumes the input list `s` is sorted descending.
Removes the first element `d`, decrements the next `d` elements by 1, and re-sorts the list descending.

Note: when `s` is the list of vertices arising from a simple graph, if the first index is `s` then
the degree list always has length at least `s+1` so this makes sense.
-/
def havelHakimiStep (s : List ℕ) : List ℕ :=
  match s with
  | [] => []
  | d :: rest =>
    -- Split the rest into the part to decrement (first d elements) and the remaining part.
    let (to_decrement, remaining) := rest.splitAt d
    -- Decrement the elements
    let decremented := to_decrement.map (· - 1)
    -- Combine and re-sort descending.
    (decremented ++ remaining).mergeSort (· ≥ ·)

end SimpleGraph

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture291

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The minimum number of triangles incident to any vertex, over all vertices of $G$. -/
noncomputable def minTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (numTrianglesAtVertex G)

/-- The number of vertices achieving the minimum triangle count. -/
noncomputable def freqMinTriangles (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun v => numTrianglesAtVertex G v = minTrianglesAtVertex G)).card

/-- The descending degree sequence of $G$, used as the starting point of the
Havel-Hakimi reduction.

Uses `Finset.univ.val.map` (multiset, duplicate-preserving) rather than
`Finset.univ.image` (set, deduplicating), so that e.g. $C_4$ produces
$[2, 2, 2, 2]$ rather than $[2]$. -/
noncomputable def descDegreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map (fun v : α => G.degree v)).sort (· ≥ ·)

/-- The Havel-Hakimi sequence of iterates: `s i` is the result of applying
`havelHakimiStep` $i$ times to the descending degree sequence of $G$. -/
noncomputable def havelHakimiIterate (G : SimpleGraph α) [DecidableRel G.Adj] (i : ℕ) :
    List ℕ :=
  (havelHakimiStep)^[i] (descDegreeSequence G)

/-- The first step $i$ (counting from $0$) at which a zero appears in the
Havel-Hakimi reduction of the descending degree sequence of $G$, or in which
the sequence has been emptied. We use `sInf` over the set of such $i$ so the
definition is well-defined for every graph: in particular, when $G$ is a
connected graph with $n \ge 2$ the minimum degree at iteration $0$ is at least
$1$, so the first zero only appears at some $i \ge 1$; and since each step
strictly shortens the list (or empties it), at the latest by $i = n$ the
sequence is empty and the predicate holds vacuously.

This is the WOWII $k$ of Conjecture 291, which is the **first** step at which a
zero appears — typically strictly less than $n - \mathrm{residue}(G)$ (which is
the *total* number of reduction steps to reach the all-zero state). -/
noncomputable def havelHakimiZeroStep (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sInf {i | 0 ∈ havelHakimiIterate G i ∨ havelHakimiIterate G i = []}

/--
WOWII [Conjecture 291](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$ with $n > 2$,
$\gamma_t(G) \le k + \mathrm{frequency}(t_{\min}(v))$
where:

- $\gamma_t(G)$ is the total domination number,
- $k$ is the first step in which a zero appears in the Havel-Hakimi process,
- $\mathrm{frequency}(t_{\min}(v))$ is the number of vertices achieving the
  minimum triangle count.

This is false: the source records a 12-vertex counterexample by Zyad Tamimi (July 23, 2026)
with $\gamma_t(G) = 4 > 2 + 1 = k + \mathrm{frequency}(t_{\min}(v))$.

The hypothesis $n > 2$ is stated in the source's full list of conjectures (as for the
neighbouring Conjectures 290, 292 and 293) but omitted on its list of open conjectures;
the counterexample has $12$ vertices, so it refutes both readings.
-/
theorem conjecture291 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected) (_hn : 2 < Fintype.card α),
      G.totalDominationNumber ≤ havelHakimiZeroStep G + freqMinTriangles G := by
  sorry

end WrittenOnTheWallII.GraphConjecture291

end
