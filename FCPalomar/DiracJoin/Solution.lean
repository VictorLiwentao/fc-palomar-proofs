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
# Dirac's joins of odd cycles

Let `m ≥ 3` be odd and `q ≥ 1`. The join of `q` disjoint copies of the cycle `C_m` (all edges
between different copies) is `3q`-critical: its chromatic number is `3q`, and deleting any
vertex or any edge lowers it. Every vertex has degree `(q - 1) m + 2`. Dirac (1952) used
`q = 2`; Erdős (1969) observed the general case.

This gives `erdos_917.variants.dirac`, `erdos_917.variants.erdos_three_dvd` and
`erdos_1032.variants.dirac_six` (`FormalConjectures/ErdosProblems/917.lean`, `1032.lean`), stated
here with the definitions `IsKCritical`, `f` and `conjecturedValue` unfolded.

Proof of criticality. A colouring of the join gives every copy at least three colours (an odd
cycle is not `2`-colourable), and different copies get disjoint colour sets; so at least `3q`
colours are needed. Colouring copy `l` with colours `3l, 3l + 1, 3l + 2` uses `3q`. After
deleting a vertex, or an edge inside a copy, that copy is a path and needs only `3l, 3l + 1`.
After deleting an edge `xy` between copies `l ≠ l'`, colour both `x` and `y` with `3l + 2`, the
rest of copies `l` and `l'` with `3l, 3l + 1` and `3l', 3l' + 1`; colour `3l' + 2` is unused.

*References:* G. A. Dirac, "A property of 4-chromatic graphs and some remarks on critical
graphs", J. London Math. Soc. 27 (1952), 85–92. P. Erdős, "Problems and results in chromatic
graph theory", Proof Techniques in Graph Theory (1969), 27–35.
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

namespace DiracJoin

open Finset SimpleGraph Filter

/-! ### The cycle `C_m` on `Fin m` -/

/-- `b` follows `a` on the cycle. -/
def Next (m : ℕ) (a b : Fin m) : Prop := a.val + 1 = b.val ∨ (b.val = 0 ∧ a.val + 1 = m)

/-- The cycle `C_m` on `Fin m`. -/
def cyc (m : ℕ) : SimpleGraph (Fin m) := SimpleGraph.fromRel (Next m)

variable {m q : ℕ}

lemma cyc_adj {a b : Fin m} : (cyc m).Adj a b ↔ a.val ≠ b.val ∧
    ((a.val + 1 = b.val ∨ (b.val = 0 ∧ a.val + 1 = m)) ∨
      (b.val + 1 = a.val ∨ (a.val = 0 ∧ b.val + 1 = m))) := by
  simp only [cyc, fromRel_adj, Next, ne_eq, Fin.ext_iff]

lemma cyc_adj_mk {i j : ℕ} (hi : i < m) (hj : j < m) :
    (cyc m).Adj ⟨i, hi⟩ ⟨j, hj⟩ ↔ i ≠ j ∧
      ((i + 1 = j ∨ (j = 0 ∧ i + 1 = m)) ∨ (j + 1 = i ∨ (i = 0 ∧ j + 1 = m))) :=
  cyc_adj

/-- A colouring of the cycle with `0, 1, 2`. -/
@[irreducible] def col3 (m : ℕ) (b : Fin m) : ℕ := if b.val + 1 = m then 2 else b.val % 2

/-- The distance from `a` to `b` going forward around the cycle. -/
@[irreducible] def gap (m : ℕ) (a b : Fin m) : ℕ := if a.val ≤ b.val then b.val - a.val else b.val + m - a.val

lemma col3_lt (b : Fin m) : col3 m b < 3 := by
  unfold col3
  split_ifs <;> omega

lemma col3_ne {a b : Fin m} (h : (cyc m).Adj a b) : col3 m a ≠ col3 m b := by
  rw [cyc_adj] at h
  have := a.isLt
  have := b.isLt
  unfold col3
  split_ifs <;> omega

/-- Without the vertex `a`, the cycle is a path, coloured by the parity of `gap m a`. -/
lemma gap_ne_of_vertex {a b b' : Fin m} (hb : b.val ≠ a.val) (hb' : b'.val ≠ a.val)
    (h : (cyc m).Adj b b') : gap m a b % 2 ≠ gap m a b' % 2 := by
  rw [cyc_adj] at h
  have := a.isLt
  have := b.isLt
  have := b'.isLt
  unfold gap
  split_ifs <;> omega

/-- Without the edge from `x` to the next vertex `y`, the cycle is a path, coloured by the
parity of `gap m y`. -/
lemma gap_ne_of_edge {x y b b' : Fin m} (hxy : Next m x y) (h : (cyc m).Adj b b')
    (hne : ¬ (b.val = x.val ∧ b'.val = y.val) ∧ ¬ (b.val = y.val ∧ b'.val = x.val)) :
    gap m y b % 2 ≠ gap m y b' % 2 := by
  rw [cyc_adj] at h
  unfold Next at hxy
  have := x.isLt
  have := y.isLt
  have := b.isLt
  have := b'.isLt
  unfold gap
  split_ifs <;> omega

/-- An odd cycle needs three colours: a proper colouring takes at least three values. -/
lemma three_le_card_image (hm : Odd m) (hm3 : 3 ≤ m) {γ : Type*} [DecidableEq γ]
    (d : Fin m → γ) (hd : ∀ a b, (cyc m).Adj a b → d a ≠ d b) : 3 ≤ (univ.image d).card := by
  by_contra hlt
  push Not at hlt
  have h0 : 0 < m := by omega
  have h1 : 1 < m := by omega
  have h01 : d ⟨0, h0⟩ ≠ d ⟨1, h1⟩ := hd _ _ ((cyc_adj_mk h0 h1).2 (by omega))
  have hsub : ({d ⟨0, h0⟩, d ⟨1, h1⟩} : Finset γ) ⊆ univ.image d := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
  have heq : univ.image d = {d ⟨0, h0⟩, d ⟨1, h1⟩} :=
    (eq_of_subset_of_card_le hsub (by rw [card_pair h01]; omega)).symm
  have hall : ∀ b, d b = d ⟨0, h0⟩ ∨ d b = d ⟨1, h1⟩ := fun b => by
    have : d b ∈ univ.image d := mem_image_of_mem _ (mem_univ _)
    rw [heq, mem_insert, mem_singleton] at this
    exact this
  have key : ∀ i (hi : i < m), d ⟨i, hi⟩ = if i % 2 = 0 then d ⟨0, h0⟩ else d ⟨1, h1⟩ := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
      intro hi
      have hne := hd ⟨i, by omega⟩ ⟨i + 1, hi⟩ ((cyc_adj_mk _ _).2 (by omega))
      rw [ih (by omega)] at hne
      by_cases hpar : i % 2 = 0
      · rw [ite_eq_left hpar] at hne
        rw [ite_eq_right (by omega)]
        exact (hall _).resolve_left (Ne.symm hne)
      · rw [ite_eq_right hpar] at hne
        rw [ite_eq_left (by omega)]
        exact (hall _).resolve_right (Ne.symm hne)
  have hlast := key (m - 1) (by omega)
  obtain ⟨t, ht⟩ := hm
  rw [ite_eq_left (by omega)] at hlast
  exact hd ⟨m - 1, by omega⟩ ⟨0, h0⟩ ((cyc_adj_mk _ _).2 (by omega)) hlast

/-! ### The join of `q` copies of `C_m` -/

/-- The join of `q` copies of `C_m`, on `Fin q × Fin m`. -/
def J (q m : ℕ) : SimpleGraph (Fin q × Fin m) :=
  SimpleGraph.fromRel fun p p' => p.1.val ≠ p'.1.val ∨ (p.1.val = p'.1.val ∧ (cyc m).Adj p.2 p'.2)

lemma J_adj {p p' : Fin q × Fin m} :
    (J q m).Adj p p' ↔ p.1.val ≠ p'.1.val ∨ (p.1.val = p'.1.val ∧ (cyc m).Adj p.2 p'.2) := by
  unfold J
  rw [fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · rcases h with h | ⟨h1, h2⟩
      · exact Or.inl (Ne.symm h)
      · exact Or.inr ⟨h1.symm, h2.symm⟩
  · intro h
    refine ⟨fun e => ?_, Or.inl h⟩
    rw [e] at h
    rcases h with h | ⟨-, h2⟩
    · exact h rfl
    · exact h2.ne rfl

/-- Colour of the whole join: copy `l` uses `3l, 3l + 1, 3l + 2`. -/
def cF (p : Fin q × Fin m) : ℕ := 3 * p.1.val + col3 m p.2

/-- Colour after deleting `p₀`. -/
def cV (p₀ p : Fin q × Fin m) : ℕ :=
  3 * p.1.val + if p.1.val = p₀.1.val then gap m p₀.2 p.2 % 2 else col3 m p.2

/-- Colour after deleting an edge inside copy `L` that ends at `y`. -/
def cE (L : ℕ) (y : Fin m) (p : Fin q × Fin m) : ℕ :=
  3 * p.1.val + if p.1.val = L then gap m y p.2 % 2 else col3 m p.2

/-- Colour after deleting the edge between `p₀` and `p₁` in different copies. -/
def cX (p₀ p₁ p : Fin q × Fin m) : ℕ :=
  if (p.1.val = p₀.1.val ∧ p.2.val = p₀.2.val) ∨ (p.1.val = p₁.1.val ∧ p.2.val = p₁.2.val) then
    3 * p₀.1.val + 2
  else
    3 * p.1.val + if p.1.val = p₀.1.val then gap m p₀.2 p.2 % 2
      else if p.1.val = p₁.1.val then gap m p₁.2 p.2 % 2 else col3 m p.2

lemma cF_lt (p : Fin q × Fin m) : cF p < 3 * q := by
  have := col3_lt p.2
  have := p.1.isLt
  unfold cF
  omega

lemma cF_ne {p p' : Fin q × Fin m} (h : (J q m).Adj p p') : cF p ≠ cF p' := by
  rw [J_adj] at h
  have h1 := col3_lt p.2
  have h2 := col3_lt p'.2
  unfold cF
  rcases h with h | ⟨h, hc⟩
  · omega
  · have := col3_ne hc
    omega

lemma cV_lt (p₀ p : Fin q × Fin m) : cV p₀ p < 3 * q := by
  have := col3_lt p.2
  have := p.1.isLt
  unfold cV
  split_ifs <;> omega

lemma cV_ne_top (p₀ p : Fin q × Fin m) : cV p₀ p ≠ 3 * p₀.1.val + 2 := by
  have := col3_lt p.2
  unfold cV
  split_ifs <;> omega

lemma cV_ne {p₀ p p' : Fin q × Fin m} (hp : ¬ (p.1.val = p₀.1.val ∧ p.2.val = p₀.2.val))
    (hp' : ¬ (p'.1.val = p₀.1.val ∧ p'.2.val = p₀.2.val)) (h : (J q m).Adj p p') :
    cV p₀ p ≠ cV p₀ p' := by
  rw [J_adj] at h
  have h1 := col3_lt p.2
  have h2 := col3_lt p'.2
  rcases h with h | ⟨h, hc⟩
  · unfold cV
    split_ifs <;> omega
  · have h3 := col3_ne hc
    have h4 : p.2.val ≠ p₀.2.val → p'.2.val ≠ p₀.2.val →
        gap m p₀.2 p.2 % 2 ≠ gap m p₀.2 p'.2 % 2 := fun a b => gap_ne_of_vertex a b hc
    unfold cV
    split_ifs <;> omega

lemma cE_lt (L : ℕ) (y : Fin m) (p : Fin q × Fin m) : cE L y p < 3 * q := by
  have := col3_lt p.2
  have := p.1.isLt
  unfold cE
  split_ifs <;> omega

lemma cE_ne_top (L : ℕ) (y : Fin m) (p : Fin q × Fin m) : cE L y p ≠ 3 * L + 2 := by
  have := col3_lt p.2
  unfold cE
  split_ifs <;> omega

lemma cE_ne {L : ℕ} {x y : Fin m} (hxy : Next m x y) {p p' : Fin q × Fin m}
    (h : (J q m).Adj p p')
    (hne : ¬ (p.1.val = L ∧ p'.1.val = L ∧
      ((p.2.val = x.val ∧ p'.2.val = y.val) ∨ (p.2.val = y.val ∧ p'.2.val = x.val)))) :
    cE L y p ≠ cE L y p' := by
  rw [J_adj] at h
  have h1 := col3_lt p.2
  have h2 := col3_lt p'.2
  rcases h with h | ⟨h, hc⟩
  · unfold cE
    split_ifs <;> omega
  · have h3 := col3_ne hc
    have h4 : (¬ (p.2.val = x.val ∧ p'.2.val = y.val) ∧ ¬ (p.2.val = y.val ∧ p'.2.val = x.val)) →
        gap m y p.2 % 2 ≠ gap m y p'.2 % 2 := fun a => gap_ne_of_edge hxy hc a
    unfold cE
    split_ifs <;> omega

lemma cX_lt (p₀ p₁ p : Fin q × Fin m) : cX p₀ p₁ p < 3 * q := by
  have := col3_lt p.2
  have := p.1.isLt
  have := p₀.1.isLt
  unfold cX
  split_ifs <;> omega

lemma cX_ne_top {p₀ p₁ : Fin q × Fin m} (h01 : p₀.1.val ≠ p₁.1.val) (p : Fin q × Fin m) :
    cX p₀ p₁ p ≠ 3 * p₁.1.val + 2 := by
  have := col3_lt p.2
  have := h01
  unfold cX
  split_ifs <;> omega

lemma cX_ne {p₀ p₁ p p' : Fin q × Fin m} (h01 : p₀.1.val ≠ p₁.1.val) (h : (J q m).Adj p p')
    (hne : ¬ ((p.1.val = p₀.1.val ∧ p.2.val = p₀.2.val ∧ p'.1.val = p₁.1.val ∧
        p'.2.val = p₁.2.val) ∨
      (p.1.val = p₁.1.val ∧ p.2.val = p₁.2.val ∧ p'.1.val = p₀.1.val ∧ p'.2.val = p₀.2.val))) :
    cX p₀ p₁ p ≠ cX p₀ p₁ p' := by
  rw [J_adj] at h
  have h1 := col3_lt p.2
  have h2 := col3_lt p'.2
  have hg : ∀ a b : Fin m, gap m a b % 2 < 2 := fun _ _ => Nat.mod_lt _ (by omega)
  have g0p := hg p₀.2 p.2
  have g1p := hg p₁.2 p.2
  have g0p' := hg p₀.2 p'.2
  have g1p' := hg p₁.2 p'.2
  unfold cX
  by_cases hp : (p.1.val = p₀.1.val ∧ p.2.val = p₀.2.val) ∨
      (p.1.val = p₁.1.val ∧ p.2.val = p₁.2.val) <;>
    by_cases hp' : (p'.1.val = p₀.1.val ∧ p'.2.val = p₀.2.val) ∨
      (p'.1.val = p₁.1.val ∧ p'.2.val = p₁.2.val)
  · -- Both are endpoints of the deleted edge: impossible.
    exfalso
    have := h01
    rcases h with h | ⟨h, hc⟩
    · omega
    · have hb : p.2.val ≠ p'.2.val := hc.ne ∘ Fin.ext
      omega
  · -- Only `p` is an endpoint: it has colour `3 p₀.1 + 2`, which `p'` does not get.
    rw [ite_eq_left hp, ite_eq_right hp']
    clear hne
    split_ifs <;> omega
  · rw [ite_eq_right hp, ite_eq_left hp']
    clear hne
    split_ifs <;> omega
  · rw [ite_eq_right hp, ite_eq_right hp']
    clear hne
    rcases h with h | ⟨h, hc⟩
    · split_ifs <;> omega
    · have h3 := col3_ne hc
      have k0 : p.2.val ≠ p₀.2.val → p'.2.val ≠ p₀.2.val →
          gap m p₀.2 p.2 % 2 ≠ gap m p₀.2 p'.2 % 2 := fun a b => gap_ne_of_vertex a b hc
      have k1 : p.2.val ≠ p₁.2.val → p'.2.val ≠ p₁.2.val →
          gap m p₁.2 p.2 % 2 ≠ gap m p₁.2 p'.2 % 2 := fun a b => gap_ne_of_vertex a b hc
      split_ifs <;> omega

/-- In a proper colouring of the join with `K` colours, `3q ≤ K`. -/
lemma le_of_coloring (hm : Odd m) (hm3 : 3 ≤ m) {K : ℕ} (c : Fin q × Fin m → Fin K)
    (hc : ∀ p p', (J q m).Adj p p' → c p ≠ c p') : 3 * q ≤ K := by
  let S : Fin q → Finset (Fin K) := fun l => univ.image fun b => c (l, b)
  have hS : ∀ l, 3 ≤ (S l).card := fun l => three_le_card_image hm hm3 (fun b => c (l, b))
    fun a b hab => hc _ _ (J_adj.2 (Or.inr ⟨rfl, hab⟩))
  have hdisj : ((univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint S := by
    intro l _ l' _ hll'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨b, -, rfl⟩ := mem_image.1 hx
    obtain ⟨b', -, hb'⟩ := mem_image.1 hx'
    exact hc (l, b) (l', b') (J_adj.2 (Or.inl fun h => hll' (Fin.ext h))) hb'.symm
  have h1 := card_biUnion hdisj
  have h2 : ∑ _l : Fin q, 3 ≤ ∑ l, (S l).card := sum_le_sum fun l _ => hS l
  have h3 := card_le_univ (univ.biUnion S)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h2 h3
  omega

/-- The successor on the cycle. -/
def succ' (b : Fin m) : Fin m := ⟨if b.val + 1 < m then b.val + 1 else 0, by
  have := b.isLt
  split_ifs <;> omega⟩

/-- The predecessor on the cycle. -/
def pred' (b : Fin m) : Fin m := ⟨if b.val = 0 then m - 1 else b.val - 1, by
  have := b.isLt
  split_ifs <;> omega⟩

lemma succ'_val (b : Fin m) : (succ' b).val = if b.val + 1 < m then b.val + 1 else 0 := rfl

lemma pred'_val (b : Fin m) : (pred' b).val = if b.val = 0 then m - 1 else b.val - 1 := rfl

/-! ### Colourings of graphs from natural-number colours -/

lemma colorable_of_nat {W : Type*} (H : SimpleGraph W) {N : ℕ} (c : W → ℕ) (hlt : ∀ w, c w < N)
    (hc : ∀ a b, H.Adj a b → c a ≠ c b) : H.Colorable N :=
  ⟨Coloring.mk (fun w => ⟨c w, hlt w⟩) fun hab h => hc _ _ hab (congrArg Fin.val h)⟩

/-- A colouring with colours `< N` that misses `z < N` uses `N - 1` colours. -/
lemma colorable_of_nat_avoid {W : Type*} (H : SimpleGraph W) {N z : ℕ} (hz : z < N)
    (c : W → ℕ) (hlt : ∀ w, c w < N) (hzc : ∀ w, c w ≠ z) (hc : ∀ a b, H.Adj a b → c a ≠ c b) :
    H.Colorable (N - 1) := by
  obtain ⟨d, hd⟩ : ∃ d : W → ℕ, ∀ w, d w = if c w < z then c w else c w - 1 := ⟨_, fun _ => rfl⟩
  refine colorable_of_nat H d (fun w => ?_) (fun a b hab => ?_)
  · have := hlt w
    have := hzc w
    rw [hd]
    split_ifs <;> omega
  · have := hc a b hab
    have := hzc a
    have := hzc b
    rw [hd, hd]
    split_ifs <;> omega

lemma pair_eq_iff {p p' : Fin q × Fin m} : p = p' ↔ p.1.val = p'.1.val ∧ p.2.val = p'.2.val := by
  rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]

/-! ### The join on an arbitrary vertex type -/

section Join

variable {V : Type*} (e : V ≃ Fin q × Fin m)

lemma colorable_join : ((J q m).comap e).Colorable (3 * q) :=
  colorable_of_nat _ (fun x => cF (e x)) (fun _ => cF_lt _) fun _ _ h => cF_ne h

lemma not_colorable_join (hq : 1 ≤ q) (hm : Odd m) (hm3 : 3 ≤ m) :
    ¬ ((J q m).comap e).Colorable (3 * q - 1) := by
  rintro ⟨C⟩
  have := le_of_coloring hm hm3 (fun p => C (e.symm p)) fun p p' h =>
    C.valid (by rwa [comap_adj, Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  omega

lemma chromaticNumber_join (hq : 1 ≤ q) (hm : Odd m) (hm3 : 3 ≤ m) :
    ((J q m).comap e).chromaticNumber = (3 * q : ℕ) :=
  le_antisymm (chromaticNumber_le_iff_colorable.2 (colorable_join e))
    ((le_chromaticNumber_iff_not_colorable (by omega)).2 (not_colorable_join e hq hm hm3))

/-- Deleting a vertex lowers the chromatic number. -/
lemma isCriticalVertex_join (hq : 1 ≤ q) (hm : Odd m) (hm3 : 3 ≤ m) (v : V) :
    (⊤ : ((J q m).comap e).Subgraph).IsCriticalVertex v := by
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
  have hcol : ((⊤ : ((J q m).comap e).Subgraph).deleteVerts {v}).coe.Colorable (3 * q - 1) := by
    refine colorable_of_nat_avoid _ (z := 3 * (e v).1.val + 2) (by have := (e v).1.isLt; omega)
      (fun w => cV (e v) (e w.1)) (fun w => cV_lt _ _) (fun w => cV_ne_top _ _) ?_
    intro a b hab
    have hab' : ((⊤ : ((J q m).comap e).Subgraph).deleteVerts {v}).Adj a b := hab
    rw [Subgraph.deleteVerts_adj] at hab'
    obtain ⟨-, ha, -, hb, hadj⟩ := hab'
    rw [Subgraph.top_adj, comap_adj] at hadj
    have ha' : e a.1 ≠ e v := fun h => ha (Set.mem_singleton_iff.2 (e.injective h))
    have hb' : e b.1 ≠ e v := fun h => hb (Set.mem_singleton_iff.2 (e.injective h))
    rw [Ne, pair_eq_iff] at ha' hb'
    exact cV_ne ha' hb' hadj
  have hnot : ¬ (⊤ : ((J q m).comap e).Subgraph).coe.Colorable (3 * q - 1) := fun h =>
    not_colorable_join e hq hm hm3 (h.of_hom ⟨fun x => ⟨x, Set.mem_univ x⟩, fun h => h⟩)
  exact lt_of_le_of_lt (chromaticNumber_le_iff_colorable.2 hcol)
    (lt_chromaticNumber_iff_not_colorable.2 hnot)

/-- Deleting an edge lowers the chromatic number. -/
lemma isCriticalEdge_join (hq : 1 ≤ q) (hm : Odd m) (hm3 : 3 ≤ m) {s : Sym2 V}
    (hs : s ∈ ((J q m).comap e).edgeSet) : ((J q m).comap e).IsCriticalEdge s := by
  unfold IsCriticalEdge IsCriticalEdges
  induction s using Sym2.ind with
  | h x y =>
    rw [mem_edgeSet, comap_adj] at hs
    have hdel : ∀ a b, (((J q m).comap e).deleteEdges {s(x, y)}).Adj a b →
        (J q m).Adj (e a) (e b) ∧
          ¬ (((e a).1.val = (e x).1.val ∧ (e a).2.val = (e x).2.val ∧
              (e b).1.val = (e y).1.val ∧ (e b).2.val = (e y).2.val) ∨
            ((e a).1.val = (e y).1.val ∧ (e a).2.val = (e y).2.val ∧
              (e b).1.val = (e x).1.val ∧ (e b).2.val = (e x).2.val)) := by
      intro a b hab
      rw [deleteEdges_adj, comap_adj, Set.mem_singleton_iff, Sym2.eq_iff] at hab
      refine ⟨hab.1, fun h => hab.2 ?_⟩
      rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact Or.inl ⟨e.injective (pair_eq_iff.2 ⟨h1, h2⟩), e.injective (pair_eq_iff.2 ⟨h3, h4⟩)⟩
      · exact Or.inr ⟨e.injective (pair_eq_iff.2 ⟨h1, h2⟩), e.injective (pair_eq_iff.2 ⟨h3, h4⟩)⟩
    have hcol : (((J q m).comap e).deleteEdges {s(x, y)}).Colorable (3 * q - 1) := by
      have hxy := J_adj.1 hs
      by_cases hl : (e x).1.val = (e y).1.val
      · have hc := (hxy.resolve_left (not_not.2 hl)).2
        rw [cyc_adj] at hc
        rcases hc.2 with hn | hn
        · -- `e y` follows `e x` in their copy.
          refine colorable_of_nat_avoid _ (z := 3 * (e x).1.val + 2)
            (by have := (e x).1.isLt; omega) (fun w => cE (e x).1.val (e y).2 (e w))
            (fun w => cE_lt _ _ _) (fun w => cE_ne_top _ _ _) fun a b hab => ?_
          obtain ⟨hadj, hne⟩ := hdel a b hab
          exact cE_ne (x := (e x).2) hn hadj (by omega)
        · refine colorable_of_nat_avoid _ (z := 3 * (e x).1.val + 2)
            (by have := (e x).1.isLt; omega) (fun w => cE (e x).1.val (e x).2 (e w))
            (fun w => cE_lt _ _ _) (fun w => cE_ne_top _ _ _) fun a b hab => ?_
          obtain ⟨hadj, hne⟩ := hdel a b hab
          exact cE_ne (x := (e y).2) hn hadj (by omega)
      · refine colorable_of_nat_avoid _ (z := 3 * (e y).1.val + 2)
          (by have := (e y).1.isLt; omega) (fun w => cX (e x) (e y) (e w))
          (fun w => cX_lt _ _ _) (fun w => cX_ne_top hl _) fun a b hab => ?_
        obtain ⟨hadj, hne⟩ := hdel a b hab
        exact cX_ne hl hadj hne
    exact lt_of_le_of_lt (chromaticNumber_le_iff_colorable.2 hcol)
      (lt_chromaticNumber_iff_not_colorable.2 (not_colorable_join e hq hm hm3))

/-- The join is `3q`-critical. -/
lemma isKCritical_join (hq : 1 ≤ q) (hm : Odd m) (hm3 : 3 ≤ m) {k : ℕ} (hk : k = 3 * q) :
    ((J q m).comap e).IsCritical k ∧
      ∀ s ∈ ((J q m).comap e).edgeSet, ((J q m).comap e).IsCriticalEdge s := by
  subst hk
  exact ⟨⟨chromaticNumber_join e hq hm hm3, isCriticalVertex_join e hq hm hm3⟩,
    fun s hs => isCriticalEdge_join e hq hm hm3 hs⟩

/-- Every vertex of the join has degree at least `(q - 1) m + 2`. -/
lemma le_degree_join [Fintype V] [DecidableRel ((J q m).comap e).Adj] (hm3 : 3 ≤ m) (x : V) :
    (q - 1) * m + 2 ≤ ((J q m).comap e).degree x := by
  classical
  rcases hp : e x with ⟨l, b⟩
  let A : Finset (Fin q × Fin m) := (univ.erase l) ×ˢ univ
  let B : Finset (Fin q × Fin m) := {(l, succ' b), (l, pred' b)}
  have hsp : succ' b ≠ pred' b := fun h => by
    have hv := congrArg Fin.val h
    rw [succ'_val, pred'_val] at hv
    have hb := b.isLt
    split_ifs at hv <;> omega
  have hA : A.card = (q - 1) * m := by
    simp only [A, card_product, card_erase_of_mem (mem_univ l), card_univ, Fintype.card_fin]
  have hB : B.card = 2 := card_pair fun h => hsp (congrArg Prod.snd h)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro t htA htB
    simp only [A, mem_product, mem_erase] at htA
    simp only [B, mem_insert, mem_singleton] at htB
    rcases htB with rfl | rfl <;> exact htA.1.1 rfl
  have hmaps : ∀ t ∈ A ∪ B, e.symm t ∈ ((J q m).comap e).neighborFinset x := by
    intro t ht
    rw [mem_neighborFinset, comap_adj, Equiv.apply_symm_apply, hp, J_adj]
    rcases mem_union.1 ht with ht | ht
    · simp only [A, mem_product, mem_erase] at ht
      exact Or.inl fun h => ht.1.1 (Fin.ext h).symm
    · simp only [B, mem_insert, mem_singleton] at ht
      have := b.isLt
      rcases ht with rfl | rfl
      · refine Or.inr ⟨rfl, cyc_adj.2 ?_⟩
        dsimp only
        rw [succ'_val]
        split_ifs <;> omega
      · refine Or.inr ⟨rfl, cyc_adj.2 ?_⟩
        dsimp only
        rw [pred'_val]
        split_ifs <;> omega
  calc (q - 1) * m + 2 = (A ∪ B).card := by rw [card_union_of_disjoint hAB, hA, hB]
    _ ≤ (((J q m).comap e).neighborFinset x).card :=
      card_le_card_of_injOn e.symm (fun t ht => mem_coe.2 (hmaps t (mem_coe.1 ht)))
        e.symm.injective.injOn
    _ = ((J q m).comap e).degree x := by rw [card_neighborFinset_eq_degree]

/-- Twice the number of edges is at least `q m ((q - 1) m + 2)`. -/
lemma le_two_mul_ncard_join [Fintype V] (hm3 : 3 ≤ m) :
    q * m * ((q - 1) * m + 2) ≤ 2 * ((J q m).comap e).edgeSet.ncard := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← sum_degrees_eq_twice_card_edges]
  have hcard : Fintype.card V = q * m := by
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  calc q * m * ((q - 1) * m + 2) = ∑ _x : V, ((q - 1) * m + 2) := by
        rw [sum_const, card_univ, hcard, smul_eq_mul]
    _ ≤ ∑ x, ((J q m).comap e).degree x := sum_le_sum fun x _ => le_degree_join e hm3 x

end Join

/-! ### The three targets -/

/-- `f k n ≥` the edge count of any `k`-critical graph on `Fin n`. -/
lemma ncard_le_sSup {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsCritical k ∧ ∀ s ∈ G.edgeSet, G.IsCriticalEdge s) :
    G.edgeSet.ncard ≤ sSup {x : ℕ | ∃ H : SimpleGraph (Fin n),
      (H.IsCritical k ∧ ∀ s ∈ H.edgeSet, H.IsCriticalEdge s) ∧ H.edgeSet.ncard = x} := by
  refine le_csSup ⟨Nat.card (Sym2 (Fin n)), ?_⟩ ⟨G, hG, rfl⟩
  rintro x ⟨H, -, rfl⟩
  exact Set.ncard_le_card _

/-- **Dirac (1952).** `f 6 (4n + 2) ≥ 4n² + 8n + 3` for `n ≥ 1` (`erdos_917.variants.dirac`). -/
theorem dirac (n : ℕ) (hn : 1 ≤ n) :
    4 * n ^ 2 + 8 * n + 3 ≤ sSup {x : ℕ | ∃ G : SimpleGraph (Fin (4 * n + 2)),
      (G.IsCritical 6 ∧ ∀ s ∈ G.edgeSet, G.IsCriticalEdge s) ∧ G.edgeSet.ncard = x} := by
  have hm : Odd (2 * n + 1) := odd_two_mul_add_one n
  let e : Fin (4 * n + 2) ≃ Fin 2 × Fin (2 * n + 1) :=
    (finCongr (by omega : 4 * n + 2 = 2 * (2 * n + 1))).trans finProdFinEquiv.symm
  have hcrit := isKCritical_join e (by omega) hm (by omega) (k := 6) rfl
  refine le_trans ?_ (ncard_le_sSup hcrit)
  have h := le_two_mul_ncard_join e (by omega : 3 ≤ 2 * n + 1)
  have h2 : 2 * (2 * n + 1) * ((2 - 1) * (2 * n + 1) + 2) = 2 * (4 * n ^ 2 + 8 * n + 3) := by ring
  rw [h2] at h
  linarith

/-- **Erdős (1969).** For `3 ∣ k` and odd `m ≥ 3`, the join of `k/3` copies of `C_m` gives
`f k (m k/3) ≥ ½ (1 - 3/k) (m k/3)² + m k/3` (`erdos_917.variants.erdos_three_dvd`). -/
theorem erdos_three_dvd (k : ℕ) (hk : 3 ≤ k) (h3 : 3 ∣ k) (m : ℕ) (hm : Odd m) (hm3 : 3 ≤ m) :
    1 / 2 * (1 - 1 / ((k / 3 : ℕ) : ℝ)) * ((m * (k / 3) : ℕ) : ℝ) ^ 2 +
        ((m * (k / 3) : ℕ) : ℝ) ≤
      ((sSup {x : ℕ | ∃ G : SimpleGraph (Fin (m * (k / 3))),
        (G.IsCritical k ∧ ∀ s ∈ G.edgeSet, G.IsCriticalEdge s) ∧ G.edgeSet.ncard = x} : ℕ) : ℝ) := by
  obtain ⟨q, rfl⟩ := h3
  have hq3 : 3 * q / 3 = q := by omega
  rw [hq3]
  have hq : 1 ≤ q := by omega
  let e : Fin (m * q) ≃ Fin q × Fin m := finProdFinEquiv.symm.trans (Equiv.prodComm _ _)
  have hcrit := isKCritical_join e hq hm hm3 (k := 3 * q) rfl
  have hle := ncard_le_sSup hcrit
  have h := le_two_mul_ncard_join e hm3
  have hle' := (Nat.cast_le (α := ℝ)).2 hle
  have h' : (q : ℝ) * m * (((q : ℝ) - 1) * m + 2) ≤ 2 * (((J q m).comap e).edgeSet.ncard : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast [Nat.cast_sub hq] at this
    linarith
  have hq0 : (q : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have key : 1 / 2 * (1 - 1 / (q : ℝ)) * ((m : ℝ) * q) ^ 2 + (m : ℝ) * q =
      (q : ℝ) * m * (((q : ℝ) - 1) * m + 2) / 2 := by
    field_simp
  push_cast
  linarith [key, h', hle']

open scoped Classical in
/-- **Dirac (1952).** For infinitely many `n` there is a `6`-critical graph on `n` vertices with
minimum degree greater than `n / 2` (`erdos_1032.variants.dirac_six`). -/
theorem dirac_six :
    ∃ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      (G.IsCritical 6 ∧ ∀ s ∈ G.edgeSet, G.IsCriticalEdge s) ∧
        (n : ℝ) / 2 < (G.minDegree : ℝ) := by
  rw [frequently_atTop]
  intro a
  have hm : Odd (2 * a + 3) := ⟨a + 1, by omega⟩
  let e : Fin (2 * (2 * a + 3)) ≃ Fin 2 × Fin (2 * a + 3) := finProdFinEquiv.symm
  refine ⟨2 * (2 * a + 3), by omega, (J 2 (2 * a + 3)).comap e,
    isKCritical_join e (by omega) hm (by omega) rfl, ?_⟩
  have : Nonempty (Fin (2 * (2 * a + 3))) := ⟨⟨0, by omega⟩⟩
  have hmin : (2 - 1) * (2 * a + 3) + 2 ≤ ((J 2 (2 * a + 3)).comap e).minDegree :=
    le_minDegree_of_forall_le_degree _ _ fun x => le_degree_join e (by omega) x
  have hreal : ((2 * (2 * a + 3) : ℕ) : ℝ) / 2 < (((J 2 (2 * a + 3)).comap e).minDegree : ℝ) := by
    have h5 : ((2 * a + 5 : ℕ) : ℝ) ≤ (((J 2 (2 * a + 3)).comap e).minDegree : ℝ) :=
      Nat.cast_le.2 (by omega)
    push_cast at h5 ⊢
    linarith
  convert hreal

end DiracJoin

open Filter

namespace Erdos917

def IsKCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.IsCritical k ∧ ∀ e ∈ G.edgeSet, G.IsCriticalEdge e

noncomputable def f (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), IsKCritical G k ∧ G.edgeSet.ncard = m}

noncomputable def conjecturedValue (k n : ℕ) : ℝ :=
  1 / 2 * (1 - 1 / ((k / 3 : ℕ) : ℝ)) * (n : ℝ) ^ 2

theorem erdos_917.variants.dirac (n : ℕ) (hn : 1 ≤ n) :
    4 * n ^ 2 + 8 * n + 3 ≤ f 6 (4 * n + 2) :=
  DiracJoin.dirac n hn

theorem erdos_917.variants.erdos_three_dvd (k : ℕ) (hk : 3 ≤ k) (h3 : 3 ∣ k) (m : ℕ)
    (hm : Odd m) (hm3 : 3 ≤ m) :
    conjecturedValue k (m * (k / 3)) + ((m * (k / 3) : ℕ) : ℝ) ≤ (f k (m * (k / 3)) : ℝ) :=
  DiracJoin.erdos_three_dvd k hk h3 m hm hm3

end Erdos917

namespace Erdos1032

def IsKCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.IsCritical k ∧ ∀ e ∈ G.edgeSet, G.IsCriticalEdge e

open scoped Classical in
theorem erdos_1032.variants.dirac_six :
    ∃ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n), IsKCritical G 6 ∧ (n : ℝ) / 2 < (G.minDegree : ℝ) :=
  DiracJoin.dirac_six

end Erdos1032

end
