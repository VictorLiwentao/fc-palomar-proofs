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
# Sun's determinants $\det[(i-j)^m + \delta_{ij}]$ for $m = 1, 2, 3$

Let $D_m(n) = \det[(i-j)^m + \delta_{ij}]_{1 \le i, j \le n}$. Then
- $D_1(n) = (n^4 - n^2 + 12)/12$ (OEIS A079034; Wang–Sun 2022);
- $D_2(n) = (n^2-4)(n^2+2n+3)(n^5-2n^4-n^3-28n^2+60n-90)/1080$ (OEIS A355175, Sun's
  conjecture);
- $D_3(n) = 1 + P(n^2)\, n^2 (n^2-1)/672000$ with
  $P(x) = x^6 - 19x^5 + 123x^4 - 337x^3 + 12376x^2 - 44144x + 40000$ (OEIS A355326,
  Conjecture 1).

Proof: by the binomial theorem the matrix is $I + U V^{\mathsf T}$ with $m + 1$ columns,
$U_{ik} = \binom{m}{k} i^{m-k}$ and $V_{jk} = (-j)^k$. The Weinstein–Aronszajn identity gives
$\det(I + U V^{\mathsf T}) = \det(I + V^{\mathsf T} U)$, an $(m+1) \times (m+1)$ determinant whose
entries are $\delta_{kl} + (-1)^k \binom{m}{l} s_{k+m-l}(n)$ with $s_r(n) = \sum_{i<n} i^r$.
Closed forms for $s_0, \dots, s_6$ finish the computation.

*References:*
- Z.-W. Sun, OEIS [A355175](https://oeis.org/A355175) and [A355326](https://oeis.org/A355326),
  June 28, 2022; B. Cloitre, [A079034](https://oeis.org/A079034).
- H. Wang and Z.-W. Sun, *Evaluations of three determinants*, arXiv:2206.12317 (2022).
- S. Fried, *Proofs of several OEIS conjectures on determinants and permanents*,
  arXiv:2606.09913 (2026), Theorem 9 and Corollary 4.
-/

@[expose] public section

namespace OeisA79034

/-- The matrix $[(i-j)^m + \delta_{ij}]_{1 \le i,j \le n}$. -/
def M (m n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (((i : ℕ) + 1 : ℤ) - ((j : ℕ) + 1 : ℤ)) ^ m + if i = j then 1 else 0

/-- The polynomial of A355326, Conjecture 1. -/
def P (x : ℚ) : ℚ :=
  x ^ 6 - 19 * x ^ 5 + 123 * x ^ 4 - 337 * x ^ 3 + 12376 * x ^ 2 - 44144 * x + 40000

end OeisA79034

namespace SunDet

open Matrix Finset

/-- The matrix $[(i-j)^m + \delta_{ij}]_{0 \le i, j < n}$. Shifting both indices by one, as in
OEIS, does not change $i - j$. -/
def sunMatrix (m n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ m + if i = j then 1 else 0

/-- The power sum $s_r(n) = \sum_{i < n} i^r$. -/
def s (r n : ℕ) : ℚ := ∑ i ∈ range n, (i : ℚ) ^ r

/-- The left factor, $U_{ik} = \binom{m}{k} i^{m-k}$. -/
def U (m n : ℕ) : Matrix (Fin n) (Fin (m + 1)) ℚ :=
  Matrix.of fun i k => (m.choose k : ℚ) * ((i : ℕ) : ℚ) ^ (m - k)

/-- The right factor, $V_{jk} = (-j)^k$. -/
def V (m n : ℕ) : Matrix (Fin n) (Fin (m + 1)) ℚ :=
  Matrix.of fun j k => (-((j : ℕ) : ℚ)) ^ (k : ℕ)

theorem map_sunMatrix (m n : ℕ) :
    (sunMatrix m n).map (Int.cast : ℤ → ℚ) = 1 + U m n * (V m n)ᵀ := by
  ext i j
  have hsum : ∑ k : Fin (m + 1),
      (m.choose k : ℚ) * ((i : ℕ) : ℚ) ^ (m - k) * (-((j : ℕ) : ℚ)) ^ (k : ℕ) =
      (((i : ℕ) : ℚ) - ((j : ℕ) : ℚ)) ^ m := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k => (m.choose k : ℚ) * ((i : ℕ) : ℚ) ^ (m - k) * (-((j : ℕ) : ℚ)) ^ k) (m + 1),
      show ((i : ℕ) : ℚ) - ((j : ℕ) : ℚ) = -((j : ℕ) : ℚ) + ((i : ℕ) : ℚ) by ring, add_pow]
    exact sum_congr rfl fun k _ => by ring
  simp only [sunMatrix, Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.mul_apply, Matrix.transpose_apply, U, V]
  push_cast
  rw [hsum, add_comm]

theorem det_sunMatrix (m n : ℕ) :
    ((sunMatrix m n).det : ℚ) = (1 + (V m n)ᵀ * U m n).det := by
  have h := RingHom.map_det (Int.castRingHom ℚ) (sunMatrix m n)
  rw [RingHom.mapMatrix_apply] at h
  rw [← det_one_add_mul_comm, ← map_sunMatrix]
  exact h

theorem VtU_apply (m n : ℕ) (k l : Fin (m + 1)) :
    ((V m n)ᵀ * U m n) k l = (-1) ^ (k : ℕ) * (m.choose l : ℚ) * s ((k : ℕ) + (m - l)) n := by
  simp only [mul_apply, transpose_apply, U, V, of_apply, s, Finset.sum_range, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [neg_pow, pow_add]
  ring

theorem s_zero (n : ℕ) : s 0 n = n := by
  simp [s]

theorem s_one (n : ℕ) : s 1 n = n * (n - 1) / 2 := by
  induction n with
  | zero => simp [s]
  | succ n ih =>
    simp only [s] at ih ⊢
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem s_two (n : ℕ) : s 2 n = n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp [s]
  | succ n ih =>
    simp only [s] at ih ⊢
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem s_three (n : ℕ) : s 3 n = (n * (n - 1) / 2) ^ 2 := by
  induction n with
  | zero => simp [s]
  | succ n ih =>
    simp only [s] at ih ⊢
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem s_four (n : ℕ) : s 4 n = n * (n - 1) * (2 * n - 1) * (3 * n ^ 2 - 3 * n - 1) / 30 := by
  induction n with
  | zero => simp [s]
  | succ n ih =>
    simp only [s] at ih ⊢
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem s_five (n : ℕ) : s 5 n = n ^ 2 * (n - 1) ^ 2 * (2 * n ^ 2 - 2 * n - 1) / 12 := by
  induction n with
  | zero => simp [s]
  | succ n ih =>
    simp only [s] at ih ⊢
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem s_six (n : ℕ) :
    s 6 n = n * (n - 1) * (2 * n - 1) * (3 * n ^ 4 - 6 * n ^ 3 + 3 * n + 1) / 42 := by
  induction n with
  | zero => simp [s]
  | succ n ih =>
    simp only [s] at ih ⊢
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem one_add_VtU_one (n : ℕ) :
    1 + (V 1 n)ᵀ * U 1 n = !![1 + s 1 n, s 0 n; -s 2 n, 1 - s 1 n] := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [VtU_apply, one_apply]
  ring

theorem one_add_VtU_two (n : ℕ) :
    1 + (V 2 n)ᵀ * U 2 n =
      !![1 + s 2 n, 2 * s 1 n, s 0 n; -s 3 n, 1 - 2 * s 2 n, -s 1 n;
        s 4 n, 2 * s 3 n, 1 + s 2 n] := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [VtU_apply, one_apply]
  ring

theorem one_add_VtU_three (n : ℕ) :
    1 + (V 3 n)ᵀ * U 3 n =
      !![1 + s 3 n, 3 * s 2 n, 3 * s 1 n, s 0 n; -s 4 n, 1 - 3 * s 3 n, -3 * s 2 n, -s 1 n;
        s 5 n, 3 * s 4 n, 1 + 3 * s 3 n, s 2 n; -s 6 n, -3 * s 5 n, -3 * s 4 n, 1 - s 3 n] := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [VtU_apply, one_apply, Nat.choose] <;> ring

/-- The Leibniz formula for a $4 \times 4$ determinant. -/
theorem det_fin_four {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2
      - A 0 0 * A 1 2 * A 2 1 * A 3 3 + A 0 0 * A 1 2 * A 2 3 * A 3 1
      + A 0 0 * A 1 3 * A 2 1 * A 3 2 - A 0 0 * A 1 3 * A 2 2 * A 3 1
      - A 0 1 * A 1 0 * A 2 2 * A 3 3 + A 0 1 * A 1 0 * A 2 3 * A 3 2
      + A 0 1 * A 1 2 * A 2 0 * A 3 3 - A 0 1 * A 1 2 * A 2 3 * A 3 0
      - A 0 1 * A 1 3 * A 2 0 * A 3 2 + A 0 1 * A 1 3 * A 2 2 * A 3 0
      + A 0 2 * A 1 0 * A 2 1 * A 3 3 - A 0 2 * A 1 0 * A 2 3 * A 3 1
      - A 0 2 * A 1 1 * A 2 0 * A 3 3 + A 0 2 * A 1 1 * A 2 3 * A 3 0
      + A 0 2 * A 1 3 * A 2 0 * A 3 1 - A 0 2 * A 1 3 * A 2 1 * A 3 0
      - A 0 3 * A 1 0 * A 2 1 * A 3 2 + A 0 3 * A 1 0 * A 2 2 * A 3 1
      + A 0 3 * A 1 1 * A 2 0 * A 3 2 - A 0 3 * A 1 1 * A 2 2 * A 3 0
      - A 0 3 * A 1 2 * A 2 0 * A 3 1 + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  have c0 : Fin.succ (0 : Fin 3) = 1 := rfl
  have c1 : Fin.succ (1 : Fin 3) = 2 := rfl
  have c2 : Fin.succ (2 : Fin 3) = 3 := rfl
  have a00 : (0 : Fin 4).succAbove (0 : Fin 3) = 1 := rfl
  have a01 : (0 : Fin 4).succAbove (1 : Fin 3) = 2 := rfl
  have a02 : (0 : Fin 4).succAbove (2 : Fin 3) = 3 := rfl
  have a10 : (1 : Fin 4).succAbove (0 : Fin 3) = 0 := rfl
  have a11 : (1 : Fin 4).succAbove (1 : Fin 3) = 2 := rfl
  have a12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := rfl
  have a20 : (2 : Fin 4).succAbove (0 : Fin 3) = 0 := rfl
  have a21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := rfl
  have a22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := rfl
  have a30 : (3 : Fin 4).succAbove (0 : Fin 3) = 0 := rfl
  have a31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := rfl
  have a32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := rfl
  rw [det_succ_row_zero, Fin.sum_univ_four]
  simp only [det_fin_three, submatrix_apply, v0, v1, v2, v3, c0, c1, c2, a00, a01, a02, a10,
    a11, a12, a20, a21, a22, a30, a31, a32]
  ring

/-- **OEIS A079034** (Wang–Sun 2022): $\det[(i-j) + \delta_{ij}]_{1 \le i,j \le n} =
(n^4 - n^2 + 12)/12$. -/
theorem a079034 (n : ℕ) :
    ((sunMatrix 1 n).det : ℚ) = ((n : ℚ) ^ 4 - (n : ℚ) ^ 2 + 12) / 12 := by
  rw [det_sunMatrix, one_add_VtU_one, det_fin_two_of, s_zero, s_one, s_two]
  ring

/-- **OEIS A355175** (Sun's conjecture): $\det[(i-j)^2 + \delta_{ij}]_{1 \le i,j \le n} =
(n^2-4)(n^2+2n+3)(n^5-2n^4-n^3-28n^2+60n-90)/1080$. -/
theorem a355175 (n : ℕ) :
    ((sunMatrix 2 n).det : ℚ) = ((n : ℚ) ^ 2 - 4) * ((n : ℚ) ^ 2 + 2 * n + 3) *
      ((n : ℚ) ^ 5 - 2 * (n : ℚ) ^ 4 - (n : ℚ) ^ 3 - 28 * (n : ℚ) ^ 2 + 60 * n - 90) / 1080 := by
  rw [det_sunMatrix, one_add_VtU_two, det_fin_three]
  simp
  simp only [s_zero, s_one, s_two, s_three, s_four]
  ring

/-- The polynomial $P(x) = x^6 - 19x^5 + 123x^4 - 337x^3 + 12376x^2 - 44144x + 40000$ of
A355326, Conjecture 1. -/
def P (x : ℚ) : ℚ :=
  x ^ 6 - 19 * x ^ 5 + 123 * x ^ 4 - 337 * x ^ 3 + 12376 * x ^ 2 - 44144 * x + 40000

/-- **OEIS A355326, Conjecture 1** (Sun): $\det[(i-j)^3 + \delta_{ij}]_{1 \le i,j \le n} =
1 + P(n^2)\, n^2 (n^2 - 1)/672000$. -/
theorem a355326 (n : ℕ) :
    ((sunMatrix 3 n).det : ℚ) =
      1 + P ((n : ℚ) ^ 2) * (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) / 672000 := by
  rw [det_sunMatrix, one_add_VtU_three, det_fin_four]
  simp
  simp only [s_zero, s_one, s_two, s_three, s_four, s_five, s_six, P]
  ring

end SunDet

/-! Separately written source statements for OEIS A079034, A355175 and A355326 (Conjecture 1).
They assert no theorem.

Sources, retrieved 2026-11-03 (offset 0; the empty determinant is 1):
- A079034 (revision #46): "Determinant of M(n), the n X n matrix defined by m(i,i) = 1,
  m(i,j) = i-j." Formula: "a(n) = (n^4-n^2+12)/12". Comment (Z.-W. Sun): Wang and Sun proved
  "a(n) = 1 + n^2*(n^2-1)/12".
- A355175 (revision #52): "Determinant of the n X n matrix [(i-j)^2 + d(i,j)]_{1<=i,j<=n}, where
  d(i,j) is 1 or 0 according as i = j or not." "Conjecture: a(n) =
  (n^2-4)*(n^2+2*n+3)*(n^5-2*n^4-n^3-28*n^2+60*n-90)/1080."
- A355326 (revision #33): the same with (i-j)^3. "Conjecture 1: a(n) = 1 +
  P(n^2)*n^2*(n^2-1)/672000, where P(n) = n^6 - 19*n^5 + 123*n^4 - 337*n^3 + 12376*n^2 -
  44144*n + 40000."

Row and column `i j : Fin n` stand for the OEIS indices `i + 1` and `j + 1`. -/
namespace SunDetFrozen

/-- The OEIS matrix $[(i-j)^m + d(i,j)]_{1 \le i,j \le n}$. -/
def M (m n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (((i : ℕ) + 1 : ℤ) - ((j : ℕ) + 1 : ℤ)) ^ m + if i = j then 1 else 0

/-- A079034, formula line. -/
def a079034 : Prop := ∀ n : ℕ, ((M 1 n).det : ℚ) = ((n : ℚ) ^ 4 - (n : ℚ) ^ 2 + 12) / 12

/-- A079034, the Wang–Sun form. -/
def a079034_sun : Prop := ∀ n : ℕ, ((M 1 n).det : ℚ) = 1 + (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) / 12

/-- A355175, Sun's conjecture. -/
def a355175 : Prop :=
  ∀ n : ℕ, ((M 2 n).det : ℚ) = ((n : ℚ) ^ 2 - 4) * ((n : ℚ) ^ 2 + 2 * n + 3) *
    ((n : ℚ) ^ 5 - 2 * (n : ℚ) ^ 4 - (n : ℚ) ^ 3 - 28 * (n : ℚ) ^ 2 + 60 * n - 90) / 1080

/-- The polynomial of A355326, Conjecture 1. -/
def P (x : ℚ) : ℚ :=
  x ^ 6 - 19 * x ^ 5 + 123 * x ^ 4 - 337 * x ^ 3 + 12376 * x ^ 2 - 44144 * x + 40000

/-- A355326, Conjecture 1. -/
def a355326 : Prop :=
  ∀ n : ℕ, ((M 3 n).det : ℚ) = 1 + P ((n : ℚ) ^ 2) * (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) / 672000

end SunDetFrozen

/-! Kernel checks for the Sun-determinant candidate: the separately frozen statements, the OEIS
examples, and a Lean-side axiom check. This file is not Comparator. -/

open SunDet

/-- The 1-based OEIS matrix is `sunMatrix`. -/
theorem frozen_M_eq (m n : ℕ) : SunDetFrozen.M m n = sunMatrix m n := by
  ext i j
  simp only [SunDetFrozen.M, sunMatrix, Matrix.of_apply]
  rw [show (((i : ℕ) : ℤ) + 1 - (((j : ℕ) : ℤ) + 1)) = ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) by ring]

theorem frozen_a079034 : SunDetFrozen.a079034 := fun n => by
  rw [frozen_M_eq]
  exact a079034 n

theorem frozen_a079034_sun : SunDetFrozen.a079034_sun := fun n => by
  rw [frozen_M_eq, a079034]
  ring

theorem frozen_a355175 : SunDetFrozen.a355175 := fun n => by
  rw [frozen_M_eq]
  exact a355175 n

theorem frozen_a355326 : SunDetFrozen.a355326 := fun n => by
  rw [frozen_M_eq]
  exact a355326 n

namespace OeisA79034

theorem det_one :
    ∀ n : ℕ, ((M 1 n).det : ℚ) = ((n : ℚ) ^ 4 - (n : ℚ) ^ 2 + 12) / 12 :=
  _root_.frozen_a079034

theorem det_two :
    ∀ n : ℕ, ((M 2 n).det : ℚ) = ((n : ℚ) ^ 2 - 4) * ((n : ℚ) ^ 2 + 2 * n + 3) *
      ((n : ℚ) ^ 5 - 2 * (n : ℚ) ^ 4 - (n : ℚ) ^ 3 - 28 * (n : ℚ) ^ 2 + 60 * n - 90) / 1080 :=
  _root_.frozen_a355175

theorem det_three :
    ∀ n : ℕ, ((M 3 n).det : ℚ) = 1 + P ((n : ℚ) ^ 2) * (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) / 672000 :=
  _root_.frozen_a355326

end OeisA79034

end
