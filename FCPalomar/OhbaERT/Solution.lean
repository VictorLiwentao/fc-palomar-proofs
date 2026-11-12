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
# Erdős–Rubin–Taylor: complete multipartite graphs with parts of size at most two

Erdős, Rubin and Taylor (1979) proved that a complete multipartite graph with `m` parts, each of
size at most two, is `m`-choosable. `OhbaERT.exists_coloring` proves this for the vertices in a
finite set `T`, with the parts given by a function `p`. `OhbaERT.erdos_rubin_taylor` specialises
it to `completeMultipartiteGraph (fun _ : Fin k => Fin 2)` with lists of exactly `k` natural
numbers, which is the body of `OhbaConjecture.Choosable` in
`FormalConjectures/Wikipedia/OhbaConjecture.lean`.

Proof. Induct on `T`. If two vertices of one part have a common colour `a` on their lists, give
both of them `a`, delete the part, and delete `a` from every other list. Each list loses at most
one colour and the number of parts drops by one. Otherwise the two lists of every part are
disjoint, and Hall's theorem gives distinct colours for all vertices: a set `S` of at most `m`
vertices sees a full list of size at least `m`, and a larger set contains a whole part, whose two
lists already have `2m` colours.

*Reference:* P. Erdős, A. L. Rubin and H. Taylor, "Choosability in graphs", *Congr. Numer.* 26
(1979), pp. 125–157.
-/

@[expose] public section

namespace OhbaERT

open Finset

variable {V ι α : Type*} [DecidableEq V] [DecidableEq ι] [DecidableEq α] [Inhabited α]

/-- **Erdős–Rubin–Taylor.** Let `p` split a finite set `T` of vertices into parts of size at most
two. If every list has at least as many colours as there are parts, then there is a choice of
colours from the lists such that vertices in different parts get different colours. -/
theorem exists_coloring (p : V → ι) (T : Finset V) (hT : ∀ i, #{v ∈ T | p v = i} ≤ 2)
    (L : V → Finset α) (hL : ∀ v ∈ T, #(T.image p) ≤ #(L v)) :
    ∃ c : V → α, (∀ v ∈ T, c v ∈ L v) ∧ ∀ u ∈ T, ∀ v ∈ T, p u ≠ p v → c u ≠ c v := by
  induction T using Finset.strongInduction generalizing L with
  | H T ih =>
  by_cases hmeet : ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ p u = p v ∧ ∃ a, a ∈ L u ∧ a ∈ L v
  · -- Two vertices of one part share the colour `a`: colour the part with `a` and recurse.
    obtain ⟨u, hu, v, hv, huv, hpuv, a, hau, hav⟩ := hmeet
    set T' := {w ∈ T | p w ≠ p u} with hT'
    have hsub : T' ⊂ T := filter_ssubset.2 ⟨u, hu, by simp⟩
    have himage : T'.image p = (T.image p).erase (p u) := by
      ext i
      simp only [hT', mem_image, mem_erase, mem_filter]
      constructor
      · rintro ⟨w, ⟨hw, hne⟩, rfl⟩
        exact ⟨hne, w, hw, rfl⟩
      · rintro ⟨hne, w, hw, rfl⟩
        exact ⟨w, ⟨hw, hne⟩, rfl⟩
    have hcard : #(T'.image p) = #(T.image p) - 1 := by
      rw [himage, card_erase_of_mem (mem_image_of_mem p hu)]
    obtain ⟨c', hc'L, hc'⟩ := ih T' hsub
      (fun i => (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hT i))
      (fun w => (L w).erase a) (fun w hw => by
        show #(T'.image p) ≤ #((L w).erase a)
        have := hL w (filter_subset _ _ hw)
        have := pred_card_le_card_erase (s := L w) (a := a)
        rw [hcard]
        omega)
    have hpart : ∀ w ∈ T, p w = p u → a ∈ L w := by
      intro w hw hpw
      by_cases hwu : w = u
      · exact hwu ▸ hau
      by_cases hwv : w = v
      · exact hwv ▸ hav
      have := hT (p u)
      have : 2 < #{x ∈ T | p x = p u} := two_lt_card_iff.2 ⟨u, v, w, by simp [hu],
        by simp [hv, hpuv.symm], by simp [hw, hpw], huv, Ne.symm hwu, Ne.symm hwv⟩
      omega
    refine ⟨fun w => if p w = p u then a else c' w, fun w hw => ?_, fun w₁ hw₁ w₂ hw₂ hne => ?_⟩
    · show (if p w = p u then a else c' w) ∈ L w
      by_cases hpw : p w = p u
      · rw [ite_eq_left hpw]
        exact hpart w hw hpw
      · rw [ite_eq_right hpw]
        exact mem_of_mem_erase (hc'L w (mem_filter.2 ⟨hw, hpw⟩))
    · have hmem : ∀ w ∈ T, p w ≠ p u → w ∈ T' := fun w hw hpw => mem_filter.2 ⟨hw, hpw⟩
      show (if p w₁ = p u then a else c' w₁) ≠ (if p w₂ = p u then a else c' w₂)
      by_cases h₁ : p w₁ = p u
      · by_cases h₂ : p w₂ = p u
        · exact absurd (h₁.trans h₂.symm) hne
        · rw [ite_eq_left h₁, ite_eq_right h₂]
          exact (ne_of_mem_erase (hc'L w₂ (hmem w₂ hw₂ h₂))).symm
      · by_cases h₂ : p w₂ = p u
        · rw [ite_eq_right h₁, ite_eq_left h₂]
          exact ne_of_mem_erase (hc'L w₁ (hmem w₁ hw₁ h₁))
        · rw [ite_eq_right h₁, ite_eq_right h₂]
          exact hc' w₁ (hmem w₁ hw₁ h₁) w₂ (hmem w₂ hw₂ h₂) hne
  · -- The two lists of every part are disjoint: Hall's theorem gives distinct colours.
    push Not at hmeet
    have hdisj : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → p u = p v → Disjoint (L u) (L v) :=
      fun u hu v hv huv hp => disjoint_left.2 fun a hau => hmeet u hu v hv huv hp a hau
    have hhall : ∀ S : Finset T, #S ≤ #(S.biUnion fun x => L x) := by
      intro S
      by_cases hS : #S ≤ #(T.image p)
      · rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
        · simp
        exact hS.trans ((hL x x.2).trans
          (card_le_card (subset_biUnion_of_mem (fun x : T => L x) hx)))
      push Not at hS
      obtain ⟨x, hx, y, hy, hxy, hpxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hS
        (f := fun x : T => p x) fun x _ => mem_coe.2 (mem_image_of_mem p x.2)
      have hxy' : (x : V) ≠ y := fun h => hxy (Subtype.ext h)
      calc #S ≤ Fintype.card T := card_le_univ S
        _ = #T := Fintype.card_coe T
        _ ≤ 2 * #(T.image p) := card_le_mul_card_image T 2 fun i _ => hT i
        _ ≤ #(L x) + #(L y) := by have := hL x x.2; have := hL y y.2; omega
        _ = #(L x ∪ L y) := (card_union_of_disjoint (hdisj x x.2 y y.2 hxy' hpxy)).symm
        _ ≤ #(S.biUnion fun x => L x) := card_le_card
          (union_subset (subset_biUnion_of_mem (fun x : T => L x) hx)
            (subset_biUnion_of_mem (fun x : T => L x) hy))
    obtain ⟨f, hf, hfL⟩ := (all_card_le_biUnion_card_iff_existsInjective' _).1 hhall
    refine ⟨fun v => if hv : v ∈ T then f ⟨v, hv⟩ else default, fun v hv => ?_,
      fun u hu v hv hne => ?_⟩
    · show (if hv : v ∈ T then f ⟨v, hv⟩ else default) ∈ L v
      rw [dite_eq_left hv]
      exact hfL ⟨v, hv⟩
    · show (if hu : u ∈ T then f ⟨u, hu⟩ else default) ≠
        (if hv : v ∈ T then f ⟨v, hv⟩ else default)
      rw [dite_eq_left hu, dite_eq_left hv]
      exact hf.ne fun h => hne (congrArg p (congrArg Subtype.val h))

/-- **Erdős–Rubin–Taylor (1979).** The complete `k`-partite graph with all parts of size two is
`k`-choosable: every assignment of lists of `k` natural numbers has a proper colouring from the
lists. The statement is the body of `OhbaConjecture.Choosable` for this graph. -/
theorem erdos_rubin_taylor (k : ℕ) (L : (Σ _ : Fin k, Fin 2) → Finset ℕ)
    (hL : ∀ v, #(L v) = k) :
    ∃ c : (Σ _ : Fin k, Fin 2) → ℕ, (∀ v, c v ∈ L v) ∧
      ∀ u v, (SimpleGraph.completeMultipartiteGraph fun _ : Fin k => Fin 2).Adj u v →
        c u ≠ c v := by
  have himage : (univ : Finset (Σ _ : Fin k, Fin 2)).image Sigma.fst = univ :=
    eq_univ_of_forall fun i => mem_image.2 ⟨⟨i, 0⟩, mem_univ _, rfl⟩
  have hparts : ∀ i, #{v ∈ (univ : Finset (Σ _ : Fin k, Fin 2)) | v.1 = i} ≤ 2 := by
    intro i
    calc #{v ∈ (univ : Finset (Σ _ : Fin k, Fin 2)) | v.1 = i}
        ≤ #(univ : Finset (Fin 2)) := card_le_card_of_injOn Sigma.snd
          (fun _ _ => mem_coe.2 (mem_univ _)) (by
            rintro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ (h : j₁ = j₂)
            simp at h₁ h₂
            subst h₁ h₂ h
            rfl)
      _ = 2 := by simp
  obtain ⟨c, hcL, hc⟩ := exists_coloring Sigma.fst univ hparts L fun v _ => by
    rw [himage, card_univ, Fintype.card_fin, hL]
  exact ⟨c, fun v => hcL v (mem_univ v), fun u v huv => hc u (mem_univ u) v (mem_univ v) huv⟩

end OhbaERT

open SimpleGraph Finset

namespace OhbaConjecture

variable {V : Type*}

def Choosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) →
    ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

theorem ohba_conjecture.variants.erdos_rubin_taylor (k : ℕ) :
    Choosable (completeMultipartiteGraph (fun _ : Fin k => Fin 2)) k :=
  OhbaERT.erdos_rubin_taylor k

end OhbaConjecture

end
