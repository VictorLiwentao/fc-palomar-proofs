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
import all Init.Data.List.Basic
import all Mathlib.Data.List.Sort

/-!
# Solution: a counterexample to WOWII Conjecture 291

Conjecture 291 of DeLaViña's *Written on the Wall II* says that every connected graph on more than
two vertices satisfies $\gamma_t(G) \le k + \mathrm{frequency}(t_{\min}(v))$. It is false: Zyad
Tamimi sent a 12-vertex counterexample (July 23, 2026), and the source lists the conjecture as
refuted. This file certifies the twelve-vertex member ($m = 6$) of the family that `vulnix0x4`
posted in google-deepmind/formal-conjectures issue 4562: it is connected, has
$\gamma_t(G) = 4$, $k = 2$ and $\mathrm{frequency}(t_{\min}(v)) = 1$.

The first three sections are verbatim copies of `FormalConjecturesForMathlib` files
`Combinatorics/SimpleGraph/{Degrees,Domination,Residue}.lean` (The Formal Conjectures Authors,
Apache-2.0), which define the invariants used by the statement.
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

end WrittenOnTheWallII.GraphConjecture291

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The average degree of `G`. -/
noncomputable def averageDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ  :=
  (∑ v, (G.degree v : ℚ)) / (Fintype.card α : ℚ)

/-- The multiset of degrees of a graph. -/
def degreeMultiset (G : SimpleGraph α) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map fun v => G.degree v

/-- The degree sequence of a graph, sorted in nondecreasing order. -/
noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

/--
The maximum number of occurrences of any term of the degree sequence of `G`.
-/
noncomputable def degreeSequenceMultiplicity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI degs := degreeSequence G
  (List.max? (degs.map (fun d => degs.count d))).getD 0

/-- Infinite graphs: definitions for max degree and clique number so that the maximum
degree of a graph with unbounded degree is
`∞` rather than 0.
-/
noncomputable
def edegree {V : Type*} (G : SimpleGraph V) (v : V) : ℕ∞ := (G.neighborSet v).encard

noncomputable
def emaxDegree {V : Type*} (G : SimpleGraph V) : ℕ∞ := ⨆ v, G.edegree v

/-- Cardinality of the union of the neighbourhoods of the ends of the non-edge `e`. -/
def non_edge_neighborhood_card (G : SimpleGraph α) [DecidableRel G.Adj] (e : Sym2 α) : ℕ :=
  Sym2.lift ⟨fun u v => (G.neighborFinset u ∪ G.neighborFinset v).card,
    fun u v => by simp [Finset.union_comm]⟩ e

/-- Minimum size of the neighbourhood of a non-edge of `G`. -/
noncomputable def NG (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let non_edges := (compl G).edgeFinset
  if h : non_edges.Nonempty then
    let neighbor_sizes := non_edges.image (non_edge_neighborhood_card G)
    (neighbor_sizes.min' (Finset.Nonempty.image h _))
  else
    (Fintype.card α : ℝ)

noncomputable def S (G : SimpleGraph α) : ℝ :=
  open scoped Classical in
  let card := Fintype.card α
  if card < 2 then 0 else
    let degrees := Multiset.ofList (List.map (fun v => G.degree v) Finset.univ.toList)
    let sorted_degrees := degrees.sort (· ≤ ·)
    ↑((sorted_degrees[card - 2]?).getD 0)

/-- The **second-smallest degree** of `G`'s degree sequence — DeLaVina's `σ(G)`
per the WOWII definitions popup (defEntry 65): "order the degree sequence in
nondecreasing order `d₁ ≤ d₂ ≤ … ≤ dₙ`, the second smallest degree of the
sequence is the 2nd entry". For graphs with `n ≤ 1` we conventionally
return `0`. -/
noncomputable def secondSmallestDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (degreeSequence G).getD 1 0

omit [DecidableEq α] in
/-- In a nontrivial preconnected finite graph, second-smallest degree one forces two leaves. -/
lemma exists_distinct_degree_one_of_secondSmallestDegree_eq_one [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Preconnected)
    (hσ : secondSmallestDegree G = 1) :
    ∃ x y : α, x ≠ y ∧ G.degree x = 1 ∧ G.degree y = 1 := by
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := α))
  obtain ⟨a, b, tail, hds⟩ : ∃ a b tail, ds = a :: b :: tail := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a rest =>
        cases hrest : rest with
        | nil => simp [h, hrest] at hlen
        | cons b tail => exact ⟨a, b, tail, rfl⟩
  have hb : b = 1 := by
    simpa [secondSmallestDegree, ds, hds] using hσ
  have hsorted : ds.Pairwise (· ≤ ·) := by
    simp [ds, degreeSequence]
  have hab : a ≤ b := by
    simpa [hds] using hsorted.rel_get_of_lt (a := ⟨0, by simp [hds]⟩)
      (b := ⟨1, by simp [hds]⟩) (by simp)
  have ha_mem : a ∈ ds := by
    simp [hds]
  have ha_pos : 0 < a := by
    have ha_map : a ∈ Finset.univ.val.map (fun v : α => G.degree v) := by
      simpa [ds, degreeSequence] using ha_mem
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha_map
    exact hG.degree_pos_of_nontrivial v
  have ha : a = 1 := by
    omega
  have hcount : 2 ≤ ds.count 1 := by
    simp [hds, ha, hb]
  have hcoeds : (↑ds : Multiset ℕ) =
      Finset.univ.val.map (fun v : α => G.degree v) := by
    simp [ds, degreeSequence]
  have hcountm :
      2 ≤ (Finset.univ.val.map (fun v : α => G.degree v)).count 1 := by
    rw [← hcoeds, Multiset.coe_count]
    exact hcount
  have hleaves : 2 ≤ (Finset.univ.filter fun v : α => G.degree v = 1).card := by
    rw [Multiset.count_map] at hcountm
    simpa only [← Finset.filter_val, Finset.card_val, eq_comm] using hcountm
  have htwo : 1 < (Finset.univ.filter fun v : α => G.degree v = 1).card := by
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp htwo
  exact ⟨x, y, hxy, (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩
/-- The length of a graph: the square root of the sum of the squares of degrees. -/
noncomputable def degreeL2Norm (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)

/-- The number of vertices of degree k in `G`. -/
def countDegreeK (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = k)).card

end SimpleGraph

/-!
Dominating sets and domination numbers

This file introduces dominating sets and related invariants.

Main definitions

* `SimpleGraph.IsDominating`   : A set of vertices that dominates all vertices.
* `SimpleGraph.IsNDominatingSet` : A dominating set with `n` vertices.
* `SimpleGraph.dominationNumber` : The domination number of a graph.
* `SimpleGraph.IsTotalDominating` : A total dominating set.
* `SimpleGraph.IsTotalNDominatingSet` : A total dominating set with `n` vertices.
* `SimpleGraph.totalDominationNumber` : The total domination number.

Future work should extend this file with connected, independent, and power
variants as well as domination-related lemmas.
-/

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α} [Fintype α] [DecidableEq α]

/-! ### Dominating sets -/

/-- A set `D` is a dominating set for `G` if every vertex of `G` is either in
`D` or adjacent to a vertex of `D`. -/
def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

/-- An `n`-dominating set is a dominating set with `n` vertices. -/
@[mk_iff]
structure IsNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isDominating : G.IsDominating D
  card_eq : D.card = n

/-! ### Domination number -/

/-- The domination number of a graph `G` is the minimum size of a dominating
set. It is `0` if there are no vertices. -/
noncomputable def dominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNDominatingSet n D}

/-- Computable domination number via powerset enumeration. -/
def computable_dom_num (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.powerset.filter (fun D : Finset α =>
    ∀ v : α, v ∈ D ∨ ∃ w ∈ D, G.Adj v w)).inf'
    ⟨Finset.univ, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
       fun v => Or.inl (Finset.mem_univ v)⟩⟩
    Finset.card

/-! ### Total domination -/

/-! ### Connected domination -/

/-- A set is a connected dominating set if it is dominating and induces a
connected subgraph. -/
def IsConnectedDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  G.IsDominating D ∧ (G.induce D).Connected

/-- The connected domination number of `G`. -/
noncomputable def connectedDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsConnectedDominating (D : Set α) ∧ D.card = n}

/-! ### Independent domination -/

def IsIndepDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  G.IsIndepSet D ∧ G.IsDominating D

@[mk_iff]
structure IsNIndepDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isIndep : G.IsIndepSet D
  isDominating : G.IsDominating D
  card_eq : D.card = n

noncomputable def indepDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNIndepDominatingSet n D}

/-! ### Vertex and edge covers -/

/-- A set of edges is an edge cover if every vertex is incident to some edge in it. -/
def IsEdgeCover (G : SimpleGraph α) (M : Set (Sym2 α)) : Prop :=
  M ⊆ G.edgeSet ∧ ∀ v, ∃ e ∈ M, v ∈ e

/-- The minimum edge cover number of `G`. -/
noncomputable def edgeCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ M : Finset (Sym2 α), G.IsEdgeCover (M : Set (Sym2 α)) ∧ M.card = n}

/-! ### Edge domination -/

def edgesAdjacent (e e' : Sym2 α) : Prop := ∃ v, v ∈ e ∧ v ∈ e'

def IsEdgeDominating (G : SimpleGraph α) (M : Set (Sym2 α)) : Prop :=
  ∀ ⦃e⦄, e ∈ G.edgeSet → e ∈ M ∨ ∃ e' ∈ M, edgesAdjacent e e'

@[mk_iff]
structure IsNEdgeDominatingSet (n : ℕ) (M : Finset (Sym2 α)) : Prop where
  isDominating : G.IsEdgeDominating (M : Set (Sym2 α))
  card_eq : M.card = n

noncomputable def edgeDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ M : Finset (Sym2 α), G.IsNEdgeDominatingSet n M}

/-! ### Domination equivalence -/

theorem dom_num_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    dominationNumber G = computable_dom_num G := by
  unfold SimpleGraph.dominationNumber SimpleGraph.computable_dom_num
  apply le_antisymm
  · apply csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩
    simp only [Set.mem_ofPred_eq]
    obtain ⟨D, hD_mem, hD_card⟩ := Finset.exists_mem_eq_inf' _ Finset.card
    exact ⟨D, hD_card ▸ ⟨(Finset.mem_filter.mp hD_mem).2, rfl⟩⟩
  · apply le_csInf
    · exact ⟨Fintype.card α, Finset.univ,
        ⟨fun v => Or.inl (Finset.mem_univ v), Finset.card_univ⟩⟩
    · intro b hb
      obtain ⟨D, hD⟩ := hb
      rw [← hD.card_eq]
      exact Finset.inf'_le _
        (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
          hD.isDominating⟩)

/-! ### Domination number of Cartesian products -/

omit [DecidableEq α] in
/-- The set `Finset.univ` is a dominating set of any graph, so the set of sizes of dominating
sets is nonempty and `dominationNumber` is attained by some dominating set. -/
lemma exists_isNDominatingSet_dominationNumber
    (G : SimpleGraph α) :
    ∃ D : Finset α, G.IsNDominatingSet G.dominationNumber D := by
  have hne : {n | ∃ D : Finset α, G.IsNDominatingSet n D}.Nonempty :=
    ⟨_, Finset.univ, ⟨fun v => Or.inl (Finset.mem_univ v), rfl⟩⟩
  exact Nat.sInf_mem hne

omit [Fintype α] [DecidableEq α] in
/-- If `D` is a dominating set of `G` with `n` elements then `γ(G) ≤ n`. -/
lemma dominationNumber_le_of_isDominating
    (G : SimpleGraph α) (D : Finset α) (hD : G.IsDominating D) :
    G.dominationNumber ≤ D.card :=
  Nat.sInf_le ⟨D, hD, rfl⟩

/--
**Projection bound: `γ(G) ≤ γ(G □ H)` whenever `H` has a vertex.**

Projecting a dominating set of `G □ H` onto the first coordinate yields a dominating set of
`G` of no larger size: a vertex `(v, b)` is dominated by some `(w, c)` with either `v = w`
(so `v` lies in the projection) or `G.Adj v w` (so `v` is dominated by `w` in the projection).
-/
theorem dominationNumber_le_dominationNumber_boxProd
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    G.dominationNumber ≤ (G □ H).dominationNumber := by
  obtain ⟨D, hD, hcard⟩ := exists_isNDominatingSet_dominationNumber (G □ H)
  refine le_trans (dominationNumber_le_of_isDominating G (D.image Prod.fst) ?_) ?_
  · intro v
    obtain ⟨b⟩ := ‹Nonempty β›
    rcases hD (v, b) with h | ⟨⟨w, c⟩, hw, hadj⟩
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst (Finset.mem_coe.mp h)))
    · rw [boxProd_adj] at hadj
      rcases hadj with ⟨hvw, -⟩ | ⟨-, hvw⟩
      · exact Or.inr ⟨w, Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst (Finset.mem_coe.mp hw)),
          hvw⟩
      · obtain rfl : v = w := hvw
        exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst (Finset.mem_coe.mp hw)))
  · exact hcard ▸ Finset.card_image_le

end SimpleGraph

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-!
## Residue
The residue of a graph is the number of zeros remaining after iteratively applying the Havel-Hakimi
algorithm to the degree sequence until all remaining degrees are zero.
-/

/--
`havelHakimiStep` drops the list length by exactly one on a nonempty list:
`(havelHakimiStep (d :: rest)).length = rest.length`. `splitAt` partitions `rest`,
and `map`, `++`, and `mergeSort` all preserve the total length while the head `d`
is dropped. This is the termination measure for the well-founded `residueAux` below.
-/
theorem havelHakimiStep_length_cons (d : ℕ) (rest : List ℕ) :
    (havelHakimiStep (d :: rest)).length = rest.length := by
  grind [havelHakimiStep, List.length_mergeSort]

/--
Auxiliary function to calculate the residue recursively.
Applies Havel-Hakimi steps until the sequence consists only of zeros or is empty.
Defined by well-founded recursion on the list length (via `havelHakimiStep_length_cons`),
so that it admits equational and inductive reasoning.
-/
def residueAux : List ℕ → ℕ
  | [] => 0        -- Empty sequence, residue is 0.
  | 0 :: s => 1 + s.length -- If the largest degree is 0 (and the list is sorted), all are 0.
  | d :: rest => residueAux (havelHakimiStep (d :: rest)) -- Apply one reduction step and recurse.
termination_by l => l.length
decreasing_by
  simp_wf
  rw [havelHakimiStep_length_cons]

/--
Computes the residue of a graph `G`, i.e. the number of zeros remaining after iteratively
applying the Havel-Hakimi algorithm to the degree sequence until all remaining degrees are zero.
Starts with the descending degree sequence and applies the Havel-Hakimi process.
-/
noncomputable def residue (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- Get the degree sequence sorted in descending order and apply `residueAux`.
  residueAux ((Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·))

end SimpleGraph

/-!
# Counterexample certificate for WOWII 291

Human author: Wentao Li. OpenAI Codex assisted with proof development.
The finite construction is the `m = 6` member documented by `vulnix0x4` in
https://github.com/google-deepmind/formal-conjectures/issues/4562 (July 23, 2026).
The upstream source credits the known disproof to Zyad Tamimi.
-/

/- Frozen target definitions, copied verbatim in value from the Apache 2.0 source. -/

namespace ResearchWOWII291

open SimpleGraph WrittenOnTheWallII.GraphConjecture291

/-- Vertex labels: `a, b, x₁, …, x₆, p, q, r, ℓ` correspond to `0, …, 11`. -/
def edges : Finset (Fin 12 × Fin 12) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 9),
   (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8),
   (2, 8), (2, 9), (3, 4), (3, 10), (4, 10), (9, 11)}

/-- Bit rows for the documented edge list, avoiding repeated set construction. -/
def row : Fin 12 → ℕ :=
  ![766, 509, 771, 1043, 1035, 3, 3, 3, 6, 2053, 24, 512]

/-- The explicitly documented twelve-vertex witness. -/
def witness : SimpleGraph (Fin 12) where
  Adj i j := (row i).testBit j.val = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel witness.Adj := fun i j =>
  inferInstanceAs (Decidable ((row i).testBit j.val = true))

/-- The bit representation has exactly the source's undirected edges. -/
theorem edge_certificate : ∀ i j : Fin 12,
    witness.Adj i j ↔ (i, j) ∈ edges ∨ (j, i) ∈ edges := by
  decide

set_option maxRecDepth 8192
set_option maxHeartbeats 200000

/-- Every vertex is joined to vertex zero by at most two edges. -/
theorem witness_connected : witness.Connected := by
  have paths : ∀ v : Fin 12, v = 0 ∨ witness.Adj 0 v ∨
      ∃ w : Fin 12, witness.Adj 0 w ∧ witness.Adj w v := by decide
  apply (connected_iff_exists_forall_reachable witness).mpr
  refine ⟨0, fun v => ?_⟩
  rcases paths v with h | h | ⟨w, h, h'⟩
  · subst v
    exact Reachable.refl _
  · exact h.reachable
  · exact h.reachable.trans h'.reachable

/-- The degree sequence retains all degree multiplicities. -/
theorem degree_certificate : descDegreeSequence witness =
    [8, 8, 4, 4, 4, 3, 2, 2, 2, 2, 2, 1] := by
  unfold descDegreeSequence
  simp only [SimpleGraph.degree, neighborFinset_eq_filter]
  unfold Multiset.sort
  simp_rw [List.mergeSort_eq_insertionSort]
  decide

/-- Exact enumeration of the eleven triangles. -/
theorem clique_certificate : witness.cliqueFinset 3 =
    {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 1, 6}, {0, 1, 7},
     {1, 2, 8}, {0, 2, 9}, {0, 3, 4}, {1, 3, 4}, {3, 4, 10}} := by
  have restrict : witness.cliqueFinset 3 =
      (Finset.univ.powersetCard 3).filter
        (fun s : Finset (Fin 12) => witness.IsClique (s : Set (Fin 12))) := by
    ext s
    simp only [mem_cliqueFinset_iff, isNClique_iff, Finset.mem_filter,
      Finset.mem_powersetCard_univ]
    exact and_comm
  rw [restrict]
  decide

/-- The exact incident-triangle table for all twelve vertices. -/
def triangleCounts : Fin 12 → ℕ := ![8, 8, 3, 4, 4, 1, 1, 1, 1, 1, 1, 0]

theorem triangle_count_certificate (v : Fin 12) :
    numTrianglesAtVertex witness v = triangleCounts v := by
  unfold numTrianglesAtVertex
  rw [clique_certificate]
  fin_cases v <;> decide

/-- A triangle-free leaf certifies that the minimum incident count is zero. -/
theorem minimum_triangle_certificate : minTrianglesAtVertex witness = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold minTrianglesAtVertex
  calc
    Finset.univ.inf' Finset.univ_nonempty (numTrianglesAtVertex witness) ≤
        numTrianglesAtVertex witness 11 :=
      Finset.inf'_le _ (Finset.mem_univ (11 : Fin 12))
    _ = 0 := by rw [triangle_count_certificate]; rfl

/-- The leaf is the unique vertex attaining the minimum triangle count. -/
theorem frequency_certificate : freqMinTriangles witness = 1 := by
  simp only [freqMinTriangles, minimum_triangle_certificate, triangle_count_certificate]
  decide

/-- The first two reductions, with no zero before the second. -/
theorem hh_certificate :
    havelHakimiIterate witness 0 = [8, 8, 4, 4, 4, 3, 2, 2, 2, 2, 2, 1] ∧
    havelHakimiIterate witness 1 = [7, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1] ∧
    havelHakimiIterate witness 2 = [2, 2, 2, 1, 1, 1, 1, 1, 1, 0] := by
  have first : havelHakimiStep [8, 8, 4, 4, 4, 3, 2, 2, 2, 2, 2, 1] =
      [7, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1] := by
    simp only [havelHakimiStep, List.mergeSort_eq_insertionSort]
    decide
  have second : havelHakimiStep [7, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1] =
      [2, 2, 2, 1, 1, 1, 1, 1, 1, 0] := by
    simp only [havelHakimiStep, List.mergeSort_eq_insertionSort]
    decide
  simp only [havelHakimiIterate, degree_certificate, Nat.iterate, first, second,
    and_self]

/-- The first zero step is two, counting the initial sequence as step zero. -/
theorem zero_step_certificate : havelHakimiZeroStep witness = 2 := by
  have at_two : 0 ∈ havelHakimiIterate witness 2 ∨
      havelHakimiIterate witness 2 = [] := by
    rw [hh_certificate.2.2]
    decide
  unfold havelHakimiZeroStep
  apply (csInf_eq_iff ⟨2, at_two⟩ 2).mpr
  refine ⟨at_two, fun i hi => ?_⟩
  change 0 ∈ havelHakimiIterate witness i ∨ havelHakimiIterate witness i = [] at hi
  by_contra h
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · rw [hh_certificate.1] at hi
    exact (by decide : ¬(0 ∈ [8, 8, 4, 4, 4, 3, 2, 2, 2, 2, 2, 1] ∨
      ([8, 8, 4, 4, 4, 3, 2, 2, 2, 2, 2, 1] : List ℕ) = [])) hi
  · rw [hh_certificate.2.1] at hi
    exact (by decide : ¬(0 ∈ [7, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1] ∨
      ([7, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1] : List ℕ) = [])) hi

/-- The four specified vertices totally dominate the witness. -/
theorem total_domination_upper : witness.IsTotalDominating
    ({0, 2, 3, 9} : Finset (Fin 12)) := by
  unfold IsTotalDominating
  decide

/-- Four neighborhood requirements force at least four selected vertices. -/
theorem total_domination_lower (D : Finset (Fin 12))
    (hD : witness.IsTotalDominating (D : Set (Fin 12))) : 4 ≤ D.card := by
  have neighborhoods :
      (∀ v : Fin 12, witness.Adj 11 v ↔ v = 9) ∧
      (∀ v : Fin 12, witness.Adj 5 v ↔ v = 0 ∨ v = 1) ∧
      (∀ v : Fin 12, witness.Adj 8 v ↔ v = 1 ∨ v = 2) ∧
      (∀ v : Fin 12, witness.Adj 9 v ↔ v = 0 ∨ v = 2 ∨ v = 11) ∧
      (∀ v : Fin 12, witness.Adj 10 v ↔ v = 3 ∨ v = 4) := by decide
  obtain ⟨q, hq, hqadj⟩ := hD 11
  have hq9 := (neighborhoods.1 q).mp hqadj
  subst q
  obtain ⟨r, hr, hradj⟩ := hD 10
  have hr34 := (neighborhoods.2.2.2.2 r).mp hradj
  obtain ⟨a, ha, haadj⟩ := hD 5
  have ha01 := (neighborhoods.2.1 a).mp haadj
  have count (b : Fin 12) (hb : b ∈ D)
      (hcard : 4 ≤ ({9, r, a, b} : Finset (Fin 12)).card) : 4 ≤ D.card := by
    apply hcard.trans
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hq
    · exact hr
    · exact ha
    · exact hb
  rcases ha01 with ha0 | ha1
  · subst a
    obtain ⟨b, hb, hbadj⟩ := hD 8
    have hb12 := (neighborhoods.2.2.1 b).mp hbadj
    apply count b hb
    rcases hr34 with rfl | rfl <;> rcases hb12 with rfl | rfl <;> decide
  · subst a
    obtain ⟨b, hb, hbadj⟩ := hD 9
    have hb0211 := (neighborhoods.2.2.2.1 b).mp hbadj
    apply count b hb
    rcases hr34 with rfl | rfl <;>
      rcases hb0211 with rfl | rfl | rfl <;> decide

/-- Total domination is exactly four. -/
theorem domination_certificate : witness.totalDominationNumber = 4 := by
  have four : ∃ D : Finset (Fin 12), witness.IsTotalNDominatingSet 4 D :=
    ⟨{0, 2, 3, 9}, total_domination_upper, by decide⟩
  unfold totalDominationNumber
  apply (csInf_eq_iff ⟨4, four⟩ 4).mpr
  refine ⟨four, ?_⟩
  rintro n ⟨D, hD⟩
  by_contra h
  have hc := hD.card_eq
  have lower := total_domination_lower D hD.isTotalDominating
  omega

/-- Complete negation of the universal inequality in the frozen declaration. -/
theorem counterexample : ¬∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected)
    (_hn : 2 < Fintype.card α),
    G.totalDominationNumber ≤ havelHakimiZeroStep G + freqMinTriangles G := by
  intro h
  have bad := h (Fin 12) witness witness_connected (by decide)
  rw [domination_certificate, zero_step_certificate, frequency_certificate] at bad
  omega

end ResearchWOWII291

namespace WrittenOnTheWallII.GraphConjecture291

open SimpleGraph

theorem conjecture291 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected) (_hn : 2 < Fintype.card α),
      G.totalDominationNumber ≤ havelHakimiZeroStep G + freqMinTriangles G :=
  ResearchWOWII291.counterexample

end WrittenOnTheWallII.GraphConjecture291

end
