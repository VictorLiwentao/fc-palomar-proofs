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
# The burning number of a path

We prove that the path on $n \ge 1$ vertices has burning number $\lceil \sqrt n \rceil$.

The definitions `IsBurningSequence` and `burningNumber` are copied verbatim from
`FormalConjectures/Paper/BurningNumberConjecture.lean` (Copyright 2026 The Formal Conjectures
Authors, Apache 2.0) at upstream commit `7bdc4a42f24c0316f81c73b26121794b2bed96a3`, in the
namespace `BurningPath` instead of `BurningNumberConjecture`. The final theorem is the
statement of `burning_number_conjecture.variants.path` there.

*Reference:* A. Bonato, J. Janssen and E. Roshanbin, "How to burn a graph",
*Internet Math.* 12 (2016), 85--100, [arXiv:1507.06524](https://arxiv.org/abs/1507.06524).

## Proof

* Lower bound. In the path, a ball of radius $r$ has at most $2r + 1$ vertices. The ball of
  index $i$ in a burning sequence of length $k$ has radius $k - 1 - i$, so the balls cover at
  most $\sum_{i < k} (2(k - 1 - i) + 1) = k^2$ vertices. Hence $n \le k^2$.
* Upper bound. Let $k^2 \ge n$. Read the path $0, \dots, k^2 - 1$ from its right end. The
  ball of radius $r$ centred at distance $r^2 + r$ from the right end covers the distances
  $r^2, \dots, (r + 1)^2 - 1$. A vertex at distance $m$ is covered by the ball of radius
  $\lfloor \sqrt m \rfloor$. Centres beyond vertex $n - 1$ are moved to vertex $n - 1$.
-/

@[expose] public section

namespace BurningNumberConjecture

open Finset SimpleGraph

variable {V : Type*}

/-- The ball-cover condition for burning a graph: every vertex is reachable from some
centre `x i` at distance at most `k - 1 - i`. The centres may repeat or already be burning
when their round starts. For finite graphs, the least such `k` is the usual burning number
[BJR16, Corollary 3]. -/
def IsBurningSequence (G : SimpleGraph V) {k : ℕ} (x : Fin k → V) : Prop :=
  ∀ v, ∃ i, G.Reachable (x i) v ∧ G.dist (x i) v + (i : ℕ) < k

/-- The **burning number** `b(G)`: the least number of rounds needed to burn every vertex
of `G`. -/
noncomputable def burningNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ x : Fin k → V, IsBurningSequence G x}

/-! ### Distance in a path -/

/-- A walk in the path changes the vertex index by at most its length. -/
lemma le_add_length {n : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v) :
    (u : ℕ) ≤ v + p.length ∧ (v : ℕ) ≤ u + p.length := by
  induction p with
  | nil => simp
  | cons h _ ih =>
    rw [pathGraph_adj] at h
    rw [Walk.length_cons]
    omega

lemma le_add_dist {n : ℕ} (u v : Fin n) :
    (u : ℕ) ≤ v + (pathGraph n).dist u v ∧ (v : ℕ) ≤ u + (pathGraph n).dist u v := by
  obtain ⟨p, hp⟩ := (preconnected_pathGraph n u v).exists_walk_length_eq_dist
  rw [← hp]
  exact le_add_length p

lemma exists_walk_of_eq_add {n : ℕ} :
    ∀ (d : ℕ) (u v : Fin n), (v : ℕ) = u + d → ∃ p : (pathGraph n).Walk u v, p.length = d
  | 0, u, v, h => by
    obtain rfl : u = v := Fin.ext (by omega)
    exact ⟨Walk.nil, rfl⟩
  | d + 1, u, v, h => by
    have hw : (u : ℕ) + d < n := by have := v.isLt; omega
    obtain ⟨p, hp⟩ := exists_walk_of_eq_add d u ⟨u + d, hw⟩ rfl
    have hadj : (pathGraph n).Adj ⟨u + d, hw⟩ v := by
      rw [pathGraph_adj]
      exact Or.inl (by simp only; omega)
    exact ⟨p.concat hadj, by rw [Walk.length_concat, hp]⟩

lemma dist_le_sub_of_le {n : ℕ} {u v : Fin n} (h : (u : ℕ) ≤ v) :
    (pathGraph n).dist u v ≤ v - u := by
  obtain ⟨p, hp⟩ := exists_walk_of_eq_add ((v : ℕ) - u) u v (by omega)
  exact (dist_le p).trans hp.le

lemma dist_le_sub_add_sub {n : ℕ} (u v : Fin n) :
    (pathGraph n).dist u v ≤ ((u : ℕ) - v) + ((v : ℕ) - u) := by
  rcases le_total (u : ℕ) v with h | h
  · have := dist_le_sub_of_le h
    omega
  · have := dist_le_sub_of_le h
    rw [dist_comm] at this
    omega

/-! ### Lower bound -/

lemma sum_odd (k : ℕ) : ∑ i ∈ range k, (2 * i + 1) = k * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

lemma sum_radii (k : ℕ) : ∑ i : Fin k, (2 * (k - 1 - (i : ℕ)) + 1) = k * k :=
  (Fin.sum_univ_eq_sum_range (fun i => 2 * (k - 1 - i) + 1) k).trans
    ((sum_range_reflect (fun i => 2 * i + 1) k).trans (sum_odd k))

/-- A burning sequence of length `k` for the path on `n` vertices has `n ≤ k * k`. -/
lemma le_mul_self_of_isBurningSequence {n k : ℕ} {x : Fin k → Fin n}
    (hx : IsBurningSequence (pathGraph n) x) : n ≤ k * k := by
  let ball : Fin k → Finset (Fin n) := fun i =>
    univ.filter fun v => (pathGraph n).dist (x i) v + i < k
  have hcover : (univ : Finset (Fin n)) ⊆ univ.biUnion ball := by
    intro v _
    obtain ⟨i, -, hi⟩ := hx v
    exact mem_biUnion.mpr ⟨i, mem_univ _, by simp [ball, hi]⟩
  have hball : ∀ i : Fin k, (ball i).card ≤ 2 * (k - 1 - i) + 1 := by
    intro i
    have hsub : (ball i).map Fin.valEmbedding ⊆
        Icc ((x i : ℕ) - (k - 1 - i)) ((x i : ℕ) + (k - 1 - i)) := by
      intro a ha
      simp only [ball, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply] at ha
      obtain ⟨v, hv, rfl⟩ := ha
      have h := le_add_dist (x i) v
      rw [mem_Icc]
      omega
    have h := card_le_card hsub
    rw [card_map, Nat.card_Icc] at h
    omega
  calc n = (univ : Finset (Fin n)).card := (card_fin n).symm
    _ ≤ (univ.biUnion ball).card := card_le_card hcover
    _ ≤ ∑ i, (ball i).card := card_biUnion_le
    _ ≤ ∑ i : Fin k, (2 * (k - 1 - (i : ℕ)) + 1) := sum_le_sum fun i _ => hball i
    _ = k * k := sum_radii k

/-! ### Upper bound -/

/-- The centre of the ball of radius `r` in the cover of the path on `k * k` vertices. -/
def centre (k r : ℕ) : ℕ := k * k - 1 - (r * r + r)

lemma exists_radius {k v : ℕ} (hv : v < k * k) :
    ∃ r < k, centre k r - v ≤ r ∧ v - centre k r ≤ r := by
  obtain ⟨r, hr⟩ : ∃ r, r = Nat.sqrt (k * k - 1 - v) := ⟨_, rfl⟩
  obtain ⟨h1, h2⟩ := Nat.eq_sqrt.mp hr
  have hrk : r < k := by
    rw [hr, Nat.sqrt_lt]
    omega
  have h3 : (r + 1) * (r + 1) ≤ k * k := Nat.mul_self_le_mul_self hrk
  have h4 : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by ring
  refine ⟨r, hrk, ?_⟩
  unfold centre
  omega

/-- If `n ≤ k * k`, the path on `n ≥ 1` vertices has a burning sequence of length `k`. -/
lemma exists_isBurningSequence {n k : ℕ} (hn : 1 ≤ n) (hk : n ≤ k * k) :
    ∃ x : Fin k → Fin n, IsBurningSequence (pathGraph n) x := by
  refine ⟨fun i => ⟨min (centre k (k - 1 - i)) (n - 1), by omega⟩, fun v => ?_⟩
  have hv := v.isLt
  obtain ⟨r, hrk, hr1, hr2⟩ := exists_radius (k := k) (v := v) (by omega)
  refine ⟨⟨k - 1 - r, by omega⟩, preconnected_pathGraph n _ v, ?_⟩
  refine lt_of_le_of_lt (Nat.add_le_add_right (dist_le_sub_add_sub _ v) _) ?_
  have hkr : k - 1 - (k - 1 - r) = r := by omega
  simp only [hkr]
  omega

/-! ### The burning number of a path -/

lemma ceil_sqrt_le_iff (n k : ℕ) : ⌈Real.sqrt n⌉₊ ≤ k ↔ n ≤ k * k := by
  rw [Nat.ceil_le, Real.sqrt_le_left (Nat.cast_nonneg k), sq]
  norm_cast

/-- **The burning number of a path** (Bonato–Janssen–Roshanbin). The path on `n ≥ 1` vertices
has burning number `⌈√n⌉`. -/
theorem burningNumber_pathGraph (n : ℕ) (hn : 1 ≤ n) :
    burningNumber (SimpleGraph.pathGraph n) = ⌈Real.sqrt n⌉₊ := by
  obtain ⟨x, hx⟩ := exists_isBurningSequence hn ((ceil_sqrt_le_iff n _).mp le_rfl)
  refine le_antisymm (Nat.sInf_le ⟨x, hx⟩) (le_csInf ⟨_, x, hx⟩ ?_)
  rintro k ⟨y, hy⟩
  exact (ceil_sqrt_le_iff n k).mpr (le_mul_self_of_isBurningSequence hy)

end BurningNumberConjecture

namespace BurningNumberConjecture

theorem burning_number_conjecture.variants.path (n : ℕ) (hn : 1 ≤ n) :
    burningNumber (SimpleGraph.pathGraph n) = ⌈Real.sqrt n⌉₊ :=
  burningNumber_pathGraph n hn

end BurningNumberConjecture

end
