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
# Erdős Problem 1111: Wagon's bound

If a finite graph has no clique of size $t$ and chromatic number at least $\binom{t}{2} + 1$,
then it has two anticomplete vertex sets that each contain an edge.

The definition `Anticomplete` is copied verbatim from `FormalConjectures/ErdosProblems/1111.lean`
(Copyright 2026 The Formal Conjectures Authors, Apache 2.0) at upstream commit
`691719db2653905d5fa0775408370fb058e4c59f`. The theorem `wagon` is the statement of
`erdos_1111.variants.wagon` there.

*Reference:* S. Wagon, "A bound on the chromatic number of graphs without certain induced
subgraphs", *J. Combin. Theory Ser. B* 29 (1980), 345--346.

## Proof

Suppose there are no such sets, i.e. no induced $2K_2$. Let $K$ be a clique of maximum size;
$|K| < t$. Every vertex $u \notin K$ misses some vertex $a(u) \in K$; let $b(u) \in K$ be a second
missed vertex if there is one, and $b(u) = a(u)$ otherwise. Colour $u \in K$ by $\{u, u\}$ and
$u \notin K$ by $\{a(u), b(u)\}$, an element of `K.sym2`. This colouring is proper:

* two adjacent vertices with colour $\{x, x\}$ outside $K$ would extend $K \setminus \{x\}$ to a
  larger clique;
* two adjacent vertices with colour $\{x, y\}$, $x \ne y$, together with the edge $xy$ would form
  an induced $2K_2$.

Hence $\chi(G) \le \binom{|K| + 1}{2} \le \binom{t}{2}$.
-/

@[expose] public section

namespace Erdos1111

open Finset

/-- Two sets `A` and `B` of vertices of `G` are *anticomplete* if they are disjoint and `G` has
no edge between `A` and `B`. -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

/-- **Wagon (1980).** A finite graph with no clique of size `t` and chromatic number at least
`t.choose 2 + 1` has two anticomplete sets that each induce a graph with an edge. -/
theorem wagon (t : ℕ) :
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      ((t.choose 2 + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
        ∃ A B : Set V, Anticomplete G A B ∧
          2 ≤ (G.induce A).chromaticNumber ∧ 2 ≤ (G.induce B).chromaticNumber := by
  intro V _ G hχ hfree
  classical
  cases nonempty_fintype V
  rcases isEmpty_or_nonempty V with hV | hV
  · exact absurd (by exact_mod_cast hχ.trans (G.colorable_zero_iff.mpr hV).chromaticNumber_le :
      t.choose 2 + 1 ≤ 0) (by omega)
  by_contra hno
  -- A clique of maximum size.
  obtain ⟨K, hK, hmax⟩ :=
    (univ.powerset.filter fun s : Finset V => G.IsClique (s : Set V)).exists_max_image
      card ⟨∅, by simp⟩
  simp only [mem_filter, mem_powerset, subset_univ, true_and] at hK hmax
  have hKt : #K < t := by
    by_contra h
    obtain ⟨s, hs, hcard⟩ := exists_subset_card_eq (not_lt.mp h)
    exact hfree s ⟨hK.subset (by exact_mod_cast hs), hcard⟩
  -- Every vertex outside `K` misses some vertex of `K`.
  have hnon : ∀ u ∉ K, ∃ x ∈ K, ¬ G.Adj u x := by
    intro u hu
    by_contra h
    push Not at h
    have hcl : G.IsClique ((insert u K : Finset V) : Set V) := by
      rw [coe_insert, SimpleGraph.isClique_insert]
      exact ⟨hK, fun x hx _ => h x hx⟩
    have := hmax _ hcl
    rw [card_insert_of_notMem hu] at this
    omega
  choose! a ha using hnon
  -- A second missed vertex, if there is one.
  have hsecond : ∀ u ∉ K, ∃ y ∈ K, ¬ G.Adj u y ∧ (y = a u → ∀ z ∈ K, ¬ G.Adj u z → z = a u) := by
    intro u hu
    by_cases h : ∃ z ∈ K, z ≠ a u ∧ ¬ G.Adj u z
    · obtain ⟨z, hz, hza, hzu⟩ := h
      exact ⟨z, hz, hzu, fun h' => absurd h' hza⟩
    · push Not at h
      exact ⟨a u, (ha u hu).1, (ha u hu).2, fun _ z hz hzu =>
        by_contra fun hne => hzu (h z hz hne)⟩
  choose! b hb using hsecond
  -- The colouring.
  let col : V → Sym2 V := fun u => if u ∈ K then s(u, u) else s(a u, b u)
  have hcol : ∀ u, col u ∈ K.sym2 := by
    intro u
    by_cases hu : u ∈ K
    · simp only [col, hu, ↓reduceIte]
      exact mk_mem_sym2_iff.mpr ⟨hu, hu⟩
    · simp only [col, hu, ↓reduceIte]
      exact mk_mem_sym2_iff.mpr ⟨(ha u hu).1, (hb u hu).1⟩
  have hproper : ∀ u w, G.Adj u w → col u ≠ col w := by
    intro u w huw heq
    by_cases hu : u ∈ K <;> by_cases hw : w ∈ K
    · simp only [col, hu, hw, ↓reduceIte, Sym2.eq_iff, and_self, or_self] at heq
      exact G.ne_of_adj huw heq
    · simp only [col, hu, hw, ↓reduceIte, Sym2.eq_iff] at heq
      have h : a w = u := by rcases heq with ⟨h1, -⟩ | ⟨-, h1⟩ <;> exact h1.symm
      exact (ha w hw).2 (by rw [h]; exact huw.symm)
    · simp only [col, hu, hw, ↓reduceIte, Sym2.eq_iff] at heq
      have h : a u = w := by rcases heq with h1 | h1 <;> exact h1.1
      exact (ha u hu).2 (by rw [h]; exact huw)
    · simp only [col, hu, hw, ↓reduceIte] at heq
      by_cases hd : a u = b u
      · -- Both colours are `{x, x}`: `K - x` plus `u, w` is a larger clique.
        have hw' : a w = a u ∧ b w = a u := by
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1.symm, hd ▸ h2.symm⟩
          · exact ⟨hd ▸ h2.symm, h1.symm⟩
        have hxK : a u ∈ K := (ha u hu).1
        have hu' : ∀ z ∈ K, z ≠ a u → G.Adj u z := fun z hz hne =>
          by_contra fun h => hne ((hb u hu).2.2 hd.symm z hz h)
        have hw'' : ∀ z ∈ K, z ≠ a u → G.Adj w z := fun z hz hne => by_contra fun h =>
          hne (((hb w hw).2.2 (hw'.2.trans hw'.1.symm) z hz h).trans hw'.1)
        have hcl : G.IsClique ((insert u (insert w (K.erase (a u))) : Finset V) : Set V) := by
          rw [coe_insert, coe_insert, SimpleGraph.isClique_insert, SimpleGraph.isClique_insert]
          refine ⟨⟨hK.subset (by simp), fun z hz _ => ?_⟩, fun z hz _ => ?_⟩
          · obtain ⟨hzx, hzK⟩ := mem_erase.mp (mem_coe.mp hz)
            exact hw'' z hzK hzx
          · rcases (Set.mem_insert_iff.mp hz) with rfl | hz
            · exact huw
            · obtain ⟨hzx, hzK⟩ := mem_erase.mp (mem_coe.mp hz)
              exact hu' z hzK hzx
        have := hmax _ hcl
        have hwK : w ∉ K.erase (a u) := fun h => hw (mem_of_mem_erase h)
        have huK : u ∉ insert w (K.erase (a u)) := by
          rw [mem_insert, not_or]
          exact ⟨G.ne_of_adj huw, fun h => hu (mem_of_mem_erase h)⟩
        rw [card_insert_of_notMem huK, card_insert_of_notMem hwK, card_erase_of_mem hxK] at this
        have : 0 < #K := card_pos.mpr ⟨_, hxK⟩
        omega
      · -- Colour `{x, y}` with `x ≠ y`: `{u, w}` and `{x, y}` give an induced `2K₂`.
        have hwa : ¬ G.Adj w (a u) ∧ ¬ G.Adj w (b u) := by
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1 ▸ (ha w hw).2, h2 ▸ (hb w hw).2.1⟩
          · exact ⟨h1 ▸ (hb w hw).2.1, h2 ▸ (ha w hw).2⟩
        have hab : G.Adj (a u) (b u) :=
          hK (mem_coe.mpr (ha u hu).1) (mem_coe.mpr (hb u hu).1) hd
        refine hno ⟨{u, w}, {a u, b u}, ⟨?_, ?_⟩, ?_, ?_⟩
        · rw [Set.disjoint_left]
          intro x hx hx'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
          have hxK : x ∈ K := by
            rcases hx' with h | h <;> rw [h]
            · exact (ha u hu).1
            · exact (hb u hu).1
          rcases hx with h | h <;> rw [h] at hxK
          · exact hu hxK
          · exact hw hxK
        · intro x hx y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
          rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
          · exact (ha u hu).2
          · exact (hb u hu).2.1
          · exact hwa.1
          · exact hwa.2
        · exact SimpleGraph.two_le_chromaticNumber_of_adj
            (G := G.induce {u, w}) (u := ⟨u, by simp⟩) (v := ⟨w, by simp⟩) huw
        · exact SimpleGraph.two_le_chromaticNumber_of_adj
            (G := G.induce {a u, b u}) (u := ⟨a u, by simp⟩) (v := ⟨b u, by simp⟩) hab
  -- The colouring uses at most `t.choose 2` colours.
  let C : G.Coloring K.sym2 :=
    SimpleGraph.Coloring.mk (fun u => ⟨col u, hcol u⟩) fun {u w} huw h =>
      hproper u w huw (congrArg Subtype.val h)
  have hle : G.chromaticNumber ≤ (t.choose 2 : ℕ∞) := by
    refine C.colorable.chromaticNumber_le.trans ?_
    rw [Fintype.card_coe, card_sym2]
    exact_mod_cast Nat.choose_le_choose 2 hKt
  exact absurd (by exact_mod_cast hχ.trans hle : t.choose 2 + 1 ≤ t.choose 2) (by omega)

end Erdos1111

namespace Erdos1111

theorem erdos_1111.variants.wagon (t : ℕ) :
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      ((t.choose 2 + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
        ∃ A B : Set V, Anticomplete G A B ∧
          2 ≤ (G.induce A).chromaticNumber ∧ 2 ≤ (G.induce B).chromaticNumber :=
  _root_.Erdos1111.wagon t

end Erdos1111

end
