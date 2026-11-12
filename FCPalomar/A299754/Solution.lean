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
# OEIS A299754: distinct sums of `p` complex `p`-th roots of unity

For a prime $p$, the number of distinct sums $z_1 + \dots + z_p$ with every $z_i^p = 1$ is
$\binom{2p-1}{p}$. Conjectured by Robert Israel (Feb 18 2018), proved by Max Alekseyev
(Feb 20 2018) in the OEIS entry.

Proof (Alekseyev). Let $\zeta = e^{2\pi i/p}$. A sum is $\sum_k c_k\zeta^k$ where $c_k$ counts
the $z_i$ equal to $\zeta^k$, so sums are images of multisets of size $p$ on $\{0, \dots, p-1\}$.
If two multisets give the same sum, the difference of their counts is an integer polynomial of
degree $< p$ vanishing at $\zeta$. It is a multiple of the minimal polynomial
$\Phi_p = 1 + X + \dots + X^{p-1}$, so all differences are equal; they sum to $p - p = 0$, so
they vanish. There are $\binom{2p-1}{p}$ multisets of size $p$ on $p$ elements.

*References:*
- [A299754](https://oeis.org/A299754): conjecture of Robert Israel, proof by Max Alekseyev.
-/

@[expose] public section

namespace OeisA299754

open Finset Polynomial

/-- The set of sums of `n` complex `n`-th roots of unity. -/
def rootSums (n : ℕ) : Set ℂ :=
  {s | ∃ z : Fin n → ℂ, (∀ i, z i ^ n = 1) ∧ ∑ i, z i = s}

/-- A299754: the number of distinct sums of `n` complex `n`-th roots of unity. -/
noncomputable def a (n : ℕ) : ℕ := (rootSums n).ncard

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- The primitive `p`-th root `e^{2πi/p}`. -/
noncomputable def zeta (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

lemma isPrimitiveRoot_zeta : IsPrimitiveRoot (zeta p) p :=
  Complex.isPrimitiveRoot_exp p hp.out.ne_zero

/-- The sum attached to a multiset of exponents. -/
noncomputable def sumOf (m : Sym (Fin p) p) : ℂ :=
  ((m : Multiset (Fin p)).map fun k : Fin p => zeta p ^ (k : ℕ)).sum

lemma exists_fun_map_eq {α : Type*} {n : ℕ} (s : Multiset α) (hs : Multiset.card s = n) :
    ∃ z : Fin n → α, (univ : Finset (Fin n)).val.map z = s := by
  obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := Quot.exists_rep s
  rw [Multiset.coe_card] at hs
  subst hs
  refine ⟨fun i : Fin l.length => l[(i : ℕ)], ?_⟩
  rw [Fin.univ_val_map, List.ofFn_getElem]

lemma rootSums_eq_range : rootSums p = Set.range (sumOf (p := p)) := by
  have hζ := isPrimitiveRoot_zeta (p := p)
  have : NeZero p := ⟨hp.out.ne_zero⟩
  ext s
  constructor
  · rintro ⟨z, hz, rfl⟩
    choose e he using fun i => hζ.eq_pow_of_pow_eq_one (hz i)
    refine ⟨⟨(univ : Finset (Fin p)).val.map fun i => (⟨e i, (he i).1⟩ : Fin p), by simp⟩, ?_⟩
    change (((univ : Finset (Fin p)).val.map fun i => (⟨e i, (he i).1⟩ : Fin p)).map
      (fun k : Fin p => zeta p ^ (k : ℕ))).sum = ∑ i, z i
    rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
    exact Multiset.map_congr rfl fun i _ => (he i).2
  · rintro ⟨m, rfl⟩
    obtain ⟨z₀, hz₀⟩ := exists_fun_map_eq (m : Multiset (Fin p)) m.2
    refine ⟨fun i => zeta p ^ (z₀ i : ℕ), fun i => ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · unfold sumOf
      rw [← hz₀, Multiset.map_map, Finset.sum_eq_multiset_sum]
      rfl

omit hp in
lemma sumOf_eq_sum_count (m : Sym (Fin p) p) :
    sumOf m = ∑ k : Fin p, ((m : Multiset (Fin p)).count k : ℂ) * zeta p ^ (k : ℕ) := by
  classical
  rw [sumOf, Finset.sum_multiset_map_count]
  rw [Finset.sum_subset (subset_univ _)]
  · simp [nsmul_eq_mul]
  · intro k _ hk
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hk
    simp [hk]

/-- Equal sums force equal counts. -/
lemma count_eq_of_sum_eq {c d : Fin p → ℕ} (hc : ∑ k, c k = p) (hd : ∑ k, d k = p)
    (h : ∑ k, (c k : ℂ) * zeta p ^ (k : ℕ) = ∑ k, (d k : ℂ) * zeta p ^ (k : ℕ)) : c = d := by
  have hζ := isPrimitiveRoot_zeta (p := p)
  let f : ℚ[X] := ∑ k : Fin p, C ((c k : ℚ) - d k) * X ^ (k : ℕ)
  have hf : aeval (zeta p) f = 0 := by
    simp only [f, map_sum, map_mul, aeval_C, map_pow, aeval_X, eq_ratCast]
    push_cast
    simp only [sub_mul, sum_sub_distrib, h, sub_self]
  have hdvd : cyclotomic p ℚ ∣ f := by
    rw [cyclotomic_eq_minpoly_rat hζ hp.out.pos]
    exact minpoly.dvd ℚ (zeta p) hf
  obtain ⟨q, hq⟩ := hdvd
  have hdeg : f.natDegree ≤ p - 1 :=
    natDegree_sum_le_of_forall_le _ _ fun k _ =>
      (natDegree_C_mul_X_pow_le _ _).trans (by have := k.isLt; omega)
  have hq0 : q.natDegree = 0 := by
    by_cases hq' : q = 0
    · simp [hq']
    have := natDegree_mul (cyclotomic_ne_zero p ℚ) hq'
    rw [← hq, natDegree_cyclotomic, Nat.totient_prime hp.out] at this
    omega
  have hcoef : ∀ k : Fin p, (c k : ℚ) - d k = q.coeff 0 := by
    intro k
    have h1 : f.coeff k = (c k : ℚ) - d k := by
      simp only [f, finsetSum_coeff, coeff_C_mul_X_pow]
      rw [sum_eq_single k]
      · simp
      · intro j _ hj
        rw [ite_eq_right (fun h => hj (Fin.ext h.symm))]
      · simp
    have h2 : f.coeff k = q.coeff 0 := by
      have hqC := eq_C_of_natDegree_eq_zero hq0
      rw [hq, hqC, coeff_mul_C, coeff_C_zero, cyclotomic_prime, finsetSum_coeff]
      simp [coeff_X_pow, k.isLt]
    rw [← h1, h2]
  have hsum : ∑ k : Fin p, ((c k : ℚ) - d k) = 0 := by
    rw [sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, hc, hd, sub_self]
  simp only [hcoef, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have ht : q.coeff 0 = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h (by exact_mod_cast hp.out.ne_zero)
    · exact h
  funext k
  have := hcoef k
  rw [ht, sub_eq_zero] at this
  exact_mod_cast this

lemma sumOf_injective : Function.Injective (sumOf (p := p)) := by
  intro m m' h
  rw [sumOf_eq_sum_count, sumOf_eq_sum_count] at h
  have hc : ∀ s : Sym (Fin p) p, ∑ k, (s : Multiset (Fin p)).count k = p := fun s => by
    rw [Multiset.sum_count_eq_card (fun a _ => mem_univ a)]
    exact s.2
  have := count_eq_of_sum_eq (hc m) (hc m') h
  exact Subtype.ext (Multiset.ext' fun k => congrFun this k)

end Prime

/-- **OEIS A299754** (Israel's conjecture, proved by Alekseyev): for a prime `p`, there are
`C(2p - 1, p)` distinct sums of `p` complex `p`-th roots of unity. -/
theorem a_prime (p : ℕ) (hp : p.Prime) : a p = (2 * p - 1).choose p := by
  have := Fact.mk hp
  rw [a, rootSums_eq_range, Set.ncard_range_of_injective sumOf_injective, Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_fin, show p + p - 1 = 2 * p - 1 by omega]

end OeisA299754



end
