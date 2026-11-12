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
# Erdős Problem 506: eight points with fewer than $\binom{7}{2}$ circles

There are $8$ points in the plane, not all on a line and not all on a circle, that determine
fewer than $\binom{7}{2} = 21$ circles. The witness is two concentric squares with aligned sides,
$(\pm 1, \pm 1)$ and $(\pm \frac12, \pm \frac12)$; they determine $18$ circles.

The definition `numCircles` is copied verbatim from `FormalConjectures/ErdosProblems/506.lean`
(Copyright 2026 The Formal Conjectures Authors, Apache 2.0) at upstream commit
`7bdc4a42f24c0316f81c73b26121794b2bed96a3`, in the namespace `Erdos506Segre` instead of
`Erdos506`, with a local copy of the notation `ℝ²`. The theorem `segre_n_eq_eight` is the
statement of `erdos_506.variants.segre_n_eq_eight` there.

*References:* [erdosproblems.com/506](https://www.erdosproblems.com/506); P. D. T. A. Elliott,
"On the number of circles determined by $n$ points", *Acta Math. Acad. Sci. Hungar.* 18 (1967),
181--188.

## Proof

Every point is $(x, x)$ or $(x, -x)$ with $x \in X = \{1, -1, \frac12, -\frac12\}$. For a circle
with centre $(a, b)$ and radius $r$ put $u = a + b$, $v = a - b$, $c = a^2 + b^2 - r^2$ (`φ`).
Then $(x, x)$ lies on the circle iff $2x^2 - 2ux + c = 0$, and $(x, -x)$ iff $2x^2 - 2vx + c = 0$
(`eq₁`, `eq₂`). A quadratic has at most two roots, so a circle through three of the points
contains two points $x_1 \ne x_2$ on one diagonal and a point $y$ on the other. Vieta's formulas
give $(u, v, c) = (x_1 + x_2, y + x_1 x_2 / y, 2 x_1 x_2)$ or the same with $u$ and $v$
exchanged (`vieta`). These triples form a set `F` of $18$ elements (`mem_F₁`, `mem_F₂`), and
`φ` is injective on circles (`φ_injOn`). So there are at most $18$ circles.
-/

@[expose] public section

namespace Erdos506

open EuclideanGeometry Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/--
The number of circles determined by a set of points `P` in the plane: the number of distinct
circles (spheres) passing through at least three of the points of `P`. (Three distinct points lie
on a common circle precisely when they are not collinear, so this counts exactly the circumcircles
of the non-collinear triples of `P`.)
-/
noncomputable def numCircles (P : Set ℝ²) : ℕ :=
  Set.ncard { s : Sphere ℝ² | 3 ≤ {p ∈ P | p ∈ s}.ncard }

/-- The point $(x, y)$. -/
noncomputable def pt (x y : ℝ) : ℝ² := !₂[x, y]

@[simp] lemma pt_zero (x y : ℝ) : pt x y 0 = x := rfl

@[simp] lemma pt_one (x y : ℝ) : pt x y 1 = y := rfl

/-- The coordinates used on each diagonal. -/
noncomputable def X : Finset ℝ := {1, -1, 1 / 2, -1 / 2}

lemma ne_zero_of_mem_X {x : ℝ} (hx : x ∈ X) : x ≠ 0 := by
  simp only [X, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> norm_num

lemma card_X : #X = 4 := by
  have h₁ : (1 : ℝ) ∉ ({-1, 1 / 2, -1 / 2} : Finset ℝ) := by norm_num
  have h₂ : (-1 : ℝ) ∉ ({1 / 2, -1 / 2} : Finset ℝ) := by norm_num
  have h₃ : (1 / 2 : ℝ) ≠ -1 / 2 := by norm_num
  rw [X, card_insert_of_notMem h₁, card_insert_of_notMem h₂, card_pair_eq_two_iff.mpr h₃]

/-- The diagonal $y = x$. -/
noncomputable def diag₁ : ℝ ↪ ℝ² :=
  ⟨fun x => pt x x, fun x y h => by simpa using congrArg (· 0) h⟩

/-- The diagonal $y = -x$. -/
noncomputable def diag₂ : ℝ ↪ ℝ² :=
  ⟨fun x => pt x (-x), fun x y h => by simpa using congrArg (· 0) h⟩

@[simp] lemma diag₁_apply (x : ℝ) : diag₁ x = pt x x := rfl

@[simp] lemma diag₂_apply (x : ℝ) : diag₂ x = pt x (-x) := rfl

lemma disjoint_diag : Disjoint (X.map diag₁) (X.map diag₂) := by
  rw [disjoint_left]
  intro p hp hp'
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hp
  obtain ⟨y, -, hxy⟩ := mem_map.mp hp'
  have h₀ := congrArg (· 0) hxy
  have h₁ := congrArg (· 1) hxy
  simp only [diag₁_apply, diag₂_apply, pt_zero, pt_one] at h₀ h₁
  exact ne_zero_of_mem_X hx (by linarith)

/-- Two concentric squares with aligned sides: the points $(x, \pm x)$ for $x \in X$. -/
noncomputable def squares : Finset ℝ² := (X.map diag₁).disjUnion (X.map diag₂) disjoint_diag

lemma mem_squares {p : ℝ²} :
    p ∈ squares ↔ (∃ x ∈ X, pt x x = p) ∨ ∃ x ∈ X, pt x (-x) = p := by
  simp only [squares, mem_disjUnion, mem_map, diag₁_apply, diag₂_apply]

lemma card_squares : #squares = 8 := by
  rw [squares, card_disjUnion, card_map, card_map, card_X]

/-- The circle data $(a + b, a - b, a^2 + b^2 - r^2)$ of a sphere with centre $(a, b)$ and
radius $r$. -/
noncomputable def φ (S : Sphere ℝ²) : ℝ × ℝ × ℝ :=
  (S.center 0 + S.center 1, S.center 0 - S.center 1,
    S.center 0 ^ 2 + S.center 1 ^ 2 - S.radius ^ 2)

lemma sq_of_mem {S : Sphere ℝ²} {x y : ℝ} (h : pt x y ∈ S) :
    (x - S.center 0) ^ 2 + (y - S.center 1) ^ 2 = S.radius ^ 2 ∧ 0 ≤ S.radius := by
  rw [mem_sphere, EuclideanSpace.dist_eq, Fin.sum_univ_two, pt_zero, pt_one, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs] at h
  rw [← h]
  exact ⟨(Real.sq_sqrt (by positivity)).symm, Real.sqrt_nonneg _⟩

lemma eq₁ {S : Sphere ℝ²} {x : ℝ} (h : pt x x ∈ S) :
    2 * x ^ 2 - 2 * (φ S).1 * x + (φ S).2.2 = 0 := by
  obtain ⟨h, -⟩ := sq_of_mem h
  simp only [φ]
  linear_combination h

lemma eq₂ {S : Sphere ℝ²} {x : ℝ} (h : pt x (-x) ∈ S) :
    2 * x ^ 2 - 2 * (φ S).2.1 * x + (φ S).2.2 = 0 := by
  obtain ⟨h, -⟩ := sq_of_mem h
  simp only [φ]
  linear_combination h

/-- Vieta's formulas for two distinct roots of $2x^2 - 2ux + c$. -/
lemma vieta {u c x₁ x₂ : ℝ} (hne : x₁ ≠ x₂) (h₁ : 2 * x₁ ^ 2 - 2 * u * x₁ + c = 0)
    (h₂ : 2 * x₂ ^ 2 - 2 * u * x₂ + c = 0) : u = x₁ + x₂ ∧ c = 2 * x₁ * x₂ := by
  have h : (x₁ - x₂) * (2 * (x₁ + x₂) - 2 * u) = 0 := by linear_combination h₁ - h₂
  have hu : u = x₁ + x₂ := by
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · linarith
  refine ⟨hu, ?_⟩
  subst hu
  linear_combination h₁

lemma not_three_roots {u c x₁ x₂ x₃ : ℝ} (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃)
    (h₁ : 2 * x₁ ^ 2 - 2 * u * x₁ + c = 0) (h₂ : 2 * x₂ ^ 2 - 2 * u * x₂ + c = 0)
    (h₃ : 2 * x₃ ^ 2 - 2 * u * x₃ + c = 0) : False := by
  have e₁ := (vieta h₁₂ h₁ h₂).1
  have e₂ := (vieta h₁₃ h₁ h₃).1
  exact h₂₃ (by linarith)

/-- The $18$ possible values of `φ` on circles through three of the points. -/
noncomputable def Flist : List (ℝ × ℝ × ℝ) :=
  [(-3 / 2, -3 / 2, 1), (-3 / 2, 0, -2), (-3 / 2, 3 / 2, 1), (-3 / 4, 0, -1 / 2),
    (-1 / 2, -1 / 2, -1), (-1 / 2, 1 / 2, -1), (0, -3 / 2, -2), (0, -3 / 4, -1 / 2),
    (0, 0, -2), (0, 0, -1 / 2), (0, 3 / 4, -1 / 2), (0, 3 / 2, -2), (1 / 2, -1 / 2, -1),
    (1 / 2, 1 / 2, -1), (3 / 4, 0, -1 / 2), (3 / 2, -3 / 2, 1), (3 / 2, 0, -2),
    (3 / 2, 3 / 2, 1)]

/-- `Flist` as a finset. -/
noncomputable def F : Finset (ℝ × ℝ × ℝ) := Flist.toFinset

lemma card_F : #F ≤ 18 := by
  unfold F Flist
  exact List.toFinset_card_le _

set_option maxHeartbeats 2000000 in
lemma mem_F₁ {x₁ x₂ y : ℝ} (h₁ : x₁ ∈ X) (h₂ : x₂ ∈ X) (hy : y ∈ X) (hne : x₁ ≠ x₂) :
    (x₁ + x₂, y + x₁ * x₂ / y, 2 * x₁ * x₂) ∈ F := by
  rw [F, List.mem_toFinset]
  simp only [X, mem_insert, mem_singleton] at h₁ h₂ hy
  rcases h₁ with rfl | rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    first
    | (norm_num at hne; done)
    | norm_num [Flist]

set_option maxHeartbeats 2000000 in
lemma mem_F₂ {x₁ x₂ y : ℝ} (h₁ : x₁ ∈ X) (h₂ : x₂ ∈ X) (hy : y ∈ X) (hne : x₁ ≠ x₂) :
    (y + x₁ * x₂ / y, x₁ + x₂, 2 * x₁ * x₂) ∈ F := by
  rw [F, List.mem_toFinset]
  simp only [X, mem_insert, mem_singleton] at h₁ h₂ hy
  rcases h₁ with rfl | rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    first
    | (norm_num at hne; done)
    | norm_num [Flist]

/-- A root `y ∈ X` of $2y^2 - 2wy + 2x_1x_2$ gives $w = y + x_1 x_2 / y$. -/
lemma eq_of_root {w c x₁ x₂ y : ℝ} (hy : y ∈ X) (hc : c = 2 * x₁ * x₂)
    (h : 2 * y ^ 2 - 2 * w * y + c = 0) : w = y + x₁ * x₂ / y := by
  have h' : (w - y) * y = x₁ * x₂ := by linear_combination -h / 2 + hc / 2
  rw [← eq_div_iff (ne_zero_of_mem_X hy)] at h'
  linarith

lemma φ_mem_F {S : Sphere ℝ²} (hS : 3 ≤ {p ∈ (squares : Set ℝ²) | p ∈ S}.ncard) : φ S ∈ F := by
  classical
  obtain ⟨R₁, hR₁⟩ : ∃ R : Finset ℝ, ∀ x, x ∈ R ↔ x ∈ X ∧ pt x x ∈ S :=
    ⟨X.filter fun x => pt x x ∈ S, fun x => mem_filter⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R : Finset ℝ, ∀ x, x ∈ R ↔ x ∈ X ∧ pt x (-x) ∈ S :=
    ⟨X.filter fun x => pt x (-x) ∈ S, fun x => mem_filter⟩
  have hsub : {p ∈ (squares : Set ℝ²) | p ∈ S} ⊆
      (fun x => pt x x) '' (R₁ : Set ℝ) ∪ (fun x => pt x (-x)) '' (R₂ : Set ℝ) := by
    rintro p ⟨hp, hpS⟩
    rcases mem_squares.mp hp with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact Or.inl ⟨x, (hR₁ x).mpr ⟨hx, hpS⟩, rfl⟩
    · exact Or.inr ⟨x, (hR₂ x).mpr ⟨hx, hpS⟩, rfl⟩
  have hcard : 3 ≤ #R₁ + #R₂ := by
    refine hS.trans ((Set.ncard_le_ncard hsub ((R₁.finite_toSet.image _).union
      (R₂.finite_toSet.image _))).trans ((Set.ncard_union_le _ _).trans (add_le_add ?_ ?_)))
    · exact (Set.ncard_image_le R₁.finite_toSet).trans (Set.ncard_coe_finset R₁).le
    · exact (Set.ncard_image_le R₂.finite_toSet).trans (Set.ncard_coe_finset R₂).le
  have h₁ : ∀ x ∈ R₁, x ∈ X ∧ 2 * x ^ 2 - 2 * (φ S).1 * x + (φ S).2.2 = 0 := fun x hx =>
    ⟨((hR₁ x).mp hx).1, eq₁ ((hR₁ x).mp hx).2⟩
  have h₂ : ∀ x ∈ R₂, x ∈ X ∧ 2 * x ^ 2 - 2 * (φ S).2.1 * x + (φ S).2.2 = 0 := fun x hx =>
    ⟨((hR₂ x).mp hx).1, eq₂ ((hR₂ x).mp hx).2⟩
  have hR₁le : #R₁ ≤ 2 := by
    by_contra h
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.mp (show 2 < #R₁ by omega)
    exact not_three_roots hxy hxz hyz (h₁ x hx).2 (h₁ y hy).2 (h₁ z hz).2
  have hR₂le : #R₂ ≤ 2 := by
    by_contra h
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.mp (show 2 < #R₂ by omega)
    exact not_three_roots hxy hxz hyz (h₂ x hx).2 (h₂ y hy).2 (h₂ z hz).2
  rcases (by omega : (2 ≤ #R₁ ∧ 1 ≤ #R₂) ∨ (2 ≤ #R₂ ∧ 1 ≤ #R₁)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := one_lt_card.mp (show 1 < #R₁ by omega)
    obtain ⟨y, hy⟩ := card_pos.mp (show 0 < #R₂ by omega)
    obtain ⟨hx₁X, e₁⟩ := h₁ x₁ hx₁
    obtain ⟨hx₂X, e₂⟩ := h₁ x₂ hx₂
    obtain ⟨hyX, e₃⟩ := h₂ y hy
    obtain ⟨hu, hc⟩ := vieta hne e₁ e₂
    have hv := eq_of_root hyX hc e₃
    have : φ S = (x₁ + x₂, y + x₁ * x₂ / y, 2 * x₁ * x₂) := Prod.ext hu (Prod.ext hv hc)
    rw [this]
    exact mem_F₁ hx₁X hx₂X hyX hne
  · obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := one_lt_card.mp (show 1 < #R₂ by omega)
    obtain ⟨y, hy⟩ := card_pos.mp (show 0 < #R₁ by omega)
    obtain ⟨hx₁X, e₁⟩ := h₂ x₁ hx₁
    obtain ⟨hx₂X, e₂⟩ := h₂ x₂ hx₂
    obtain ⟨hyX, e₃⟩ := h₁ y hy
    obtain ⟨hv, hc⟩ := vieta hne e₁ e₂
    have hu := eq_of_root hyX hc e₃
    have : φ S = (y + x₁ * x₂ / y, x₁ + x₂, 2 * x₁ * x₂) := Prod.ext hu (Prod.ext hv hc)
    rw [this]
    exact mem_F₂ hx₁X hx₂X hyX hne

lemma radius_nonneg {S : Sphere ℝ²} (hS : 3 ≤ {p ∈ (squares : Set ℝ²) | p ∈ S}.ncard) :
    0 ≤ S.radius := by
  obtain ⟨p, -, hp⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
    {p ∈ (squares : Set ℝ²) | p ∈ S}.ncard ≠ 0)
  rw [mem_sphere] at hp
  rw [← hp]
  exact dist_nonneg

lemma φ_injOn : Set.InjOn φ {S : Sphere ℝ² | 3 ≤ {p ∈ (squares : Set ℝ²) | p ∈ S}.ncard} := by
  intro S hS S' hS' h
  simp only [φ, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  have ha : S.center 0 = S'.center 0 := by linarith
  have hb : S.center 1 = S'.center 1 := by linarith
  have hr : S.radius ^ 2 = S'.radius ^ 2 := by
    rw [ha, hb] at h₃
    linarith
  refine Sphere.ext (PiLp.ext fun i => ?_) ((pow_left_inj₀ (radius_nonneg hS)
    (radius_nonneg hS') two_ne_zero).mp hr)
  fin_cases i
  · exact ha
  · exact hb

lemma numCircles_squares : numCircles (squares : Set ℝ²) ≤ 18 := by
  unfold numCircles
  calc _ ≤ (F : Set (ℝ × ℝ × ℝ)).ncard :=
        Set.ncard_le_ncard_of_injOn φ (fun S hS => φ_mem_F hS) φ_injOn F.finite_toSet
    _ = #F := Set.ncard_coe_finset F
    _ ≤ 18 := card_F

lemma not_collinear_squares : ¬ Collinear ℝ (squares : Set ℝ²) := by
  intro h
  have h₁ : pt 1 1 ∈ (squares : Set ℝ²) := mem_squares.mpr (Or.inl ⟨1, by simp [X], rfl⟩)
  have h₂ : pt 1 (-1) ∈ (squares : Set ℝ²) := mem_squares.mpr (Or.inr ⟨1, by simp [X], rfl⟩)
  have h₃ : pt (-1) 1 ∈ (squares : Set ℝ²) :=
    mem_squares.mpr (Or.inr ⟨-1, by simp [X], by norm_num⟩)
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem h₁).mp h
  obtain ⟨r₂, hr₂⟩ := hv _ h₂
  obtain ⟨r₃, hr₃⟩ := hv _ h₃
  have a₀ := congrArg (· 0) hr₂
  have a₁ := congrArg (· 1) hr₂
  have b₀ := congrArg (· 0) hr₃
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_zero,
    pt_one] at a₀ a₁ b₀
  have h₄ : (4 : ℝ) = 0 := by
    linear_combination (r₃ * v 0) * a₁ - 2 * b₀ - (r₃ * v 1) * a₀
  norm_num at h₄

lemma not_cospherical_squares : ¬ Cospherical (squares : Set ℝ²) := by
  rintro ⟨c, r, h⟩
  have hmem : ∀ x ∈ X, pt x x ∈ (⟨c, r⟩ : Sphere ℝ²) := fun x hx =>
    mem_sphere.mpr (h _ (mem_squares.mpr (Or.inl ⟨x, hx, rfl⟩)))
  have e₁ := eq₁ (hmem 1 (by simp [X]))
  have e₂ := eq₁ (hmem (-1) (by simp [X]))
  have e₃ := eq₁ (hmem (1 / 2) (by simp [X]))
  have h : (-3 / 2 : ℝ) = 0 := by linear_combination e₃ - 3 / 4 * e₁ - 1 / 4 * e₂
  norm_num at h

/-- **Erdős Problem 506, Segre's observation.** Some $8$ points in the plane, not all on a line
and not all on a circle, determine fewer than $\binom{7}{2}$ circles. -/
theorem segre_n_eq_eight :
    ∃ P : Finset ℝ²,
      P.card = 8 ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
      numCircles (P : Set ℝ²) < (8 - 1).choose 2 :=
  ⟨squares, card_squares, not_collinear_squares, not_cospherical_squares,
    numCircles_squares.trans_lt (by decide)⟩

end Erdos506

namespace Erdos506

open EuclideanGeometry

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

theorem erdos_506.variants.segre_n_eq_eight :
    ∃ P : Finset ℝ²,
      P.card = 8 ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
      numCircles (P : Set ℝ²) < (8 - 1).choose 2 :=
  _root_.Erdos506.segre_n_eq_eight

end Erdos506

end
