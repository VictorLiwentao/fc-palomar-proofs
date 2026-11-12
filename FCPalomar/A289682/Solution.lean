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
# Catalan numbers modulo 16 at $2^n - 1$ and $2^n$ (OEIS A289682)

For $n \ge 3$, $C(2^n - 1) \equiv 13$ and $C(2^n) \equiv 6 \pmod{16}$ (conjecture of
R. Israel in OEIS A289682).

Proof: write $B(m) = \binom{2m}{m}$, $O(m) = \prod_{i<m} (2i+1)$ and
$O'(m) = \prod_{i<m} (2m+2i+1)$. From $(2m)! = 2^m m!\, O(m)$ we get
$B(2m)\, O(m) = B(m)\, O'(m)$. If $8 \mid m$, each factor of $O'(m)$ is congruent modulo 16 to
the corresponding factor of $O(m)$; since $B(m)$ is even and $O(m)$ is odd,
$B(2m) \equiv B(m) \pmod{32}$. With $B(8) = 12870 \equiv 6$, this gives $B(2^n) \equiv 6 \pmod{32}$
for $n \ge 3$. Finally $B(2^n) = 2(2^{n+1}-1)\, C(2^n-1)$ and $B(2^n) = (2^n+1)\, C(2^n)$.

*References:*
- R. J. Mathar, OEIS [A289682](https://oeis.org/A289682), July 9, 2017; conjecture by R. Israel.
- H.-Y. Lin, *The odd Catalan numbers modulo $2^k$*, arXiv:1012.1756.
- S.-C. Liu and J. C.-C. Yeh, *Catalan numbers modulo $2^k$*, J. Integer Seq. 13 (2010),
  Article 10.5.4.
-/

@[expose] public section

namespace OeisA289682

open Nat Finset

/-- The product $O(m) = 1 \cdot 3 \cdots (2m-1)$ of the first `m` odd numbers. -/
def oddProd (m : ℕ) : ℕ := ∏ i ∈ range m, (2 * i + 1)

/-- The product $O'(m) = (2m+1)(2m+3) \cdots (4m-1)$. -/
def oddProd' (m : ℕ) : ℕ := ∏ i ∈ range m, (2 * m + 2 * i + 1)

theorem factorial_two_mul (m : ℕ) : (2 * m)! = 2 ^ m * m ! * oddProd m := by
  induction m with
  | zero => simp [oddProd]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ (2 * m + 1),
      Nat.factorial_succ (2 * m), ih, Nat.factorial_succ m]
    simp only [oddProd, prod_range_succ]
    ring

theorem oddProd_two_mul (m : ℕ) : oddProd (2 * m) = oddProd m * oddProd' m := by
  unfold oddProd oddProd'
  rw [two_mul, prod_range_add]
  congr 1
  exact prod_congr rfl fun i _ => by ring

theorem oddProd_odd (m : ℕ) : Odd (oddProd m) := by
  unfold oddProd
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ]
    exact ih.mul (odd_two_mul_add_one m)

theorem centralBinom_mul_sq (k : ℕ) : centralBinom k * (k !) ^ 2 = (2 * k)! := by
  have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  rw [show 2 * k - k = k by omega] at h
  rw [Nat.centralBinom_eq_two_mul_choose, sq, ← mul_assoc, h]

/-- $B(2m)\, O(m) = B(m)\, O'(m)$. -/
theorem centralBinom_two_mul_mul (m : ℕ) :
    centralBinom (2 * m) * oddProd m = centralBinom m * oddProd' m := by
  have e1 := centralBinom_mul_sq (2 * m)
  have e2 := factorial_two_mul (2 * m)
  rw [oddProd_two_mul] at e2
  have e3 := factorial_two_mul m
  have e4 := centralBinom_mul_sq m
  have hp : (2 : ℕ) ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  have h5 : centralBinom m * m ! = 2 ^ m * oddProd m := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos m)
    calc centralBinom m * m ! * m ! = centralBinom m * (m !) ^ 2 := by ring
      _ = (2 * m)! := e4
      _ = 2 ^ m * oddProd m * m ! := by rw [e3]; ring
  have hpos : 0 < 2 ^ m * m ! * (2 * m)! :=
    Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos m) (Nat.factorial_pos m)) (Nat.factorial_pos (2 * m))
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc centralBinom (2 * m) * oddProd m * (2 ^ m * m ! * (2 * m)!)
      = centralBinom (2 * m) * ((2 ^ m * m ! * oddProd m) * (2 * m)!) := by ring
    _ = centralBinom (2 * m) * ((2 * m)! ^ 2) := by rw [← e3]; ring
    _ = (2 * (2 * m))! := e1
    _ = 2 ^ (2 * m) * (2 * m)! * (oddProd m * oddProd' m) := e2
    _ = oddProd' m * 2 ^ m * (2 * m)! * (2 ^ m * oddProd m) := by rw [hp]; ring
    _ = oddProd' m * 2 ^ m * (2 * m)! * (centralBinom m * m !) := by rw [h5]
    _ = centralBinom m * oddProd' m * (2 ^ m * m ! * (2 * m)!) := by ring

/-- If $8 \mid m$ then $O'(m) \equiv O(m) \pmod{16}$. -/
theorem oddProd'_cast (m : ℕ) (hm : 8 ∣ m) : (oddProd' m : ZMod 16) = oddProd m := by
  have h : ((2 * m : ℕ) : ZMod 16) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (by omega)
  push_cast at h
  unfold oddProd oddProd'
  push_cast
  refine prod_congr rfl fun i _ => ?_
  rw [h, zero_add]

/-- If $8 \mid m$ and $m > 0$ then $B(2m) \equiv B(m) \pmod{32}$. -/
theorem centralBinom_two_mul_mod (m : ℕ) (hm : 8 ∣ m) (hpos : 0 < m) :
    centralBinom (2 * m) % 32 = centralBinom m % 32 := by
  have hkey : (centralBinom (2 * m) : ℤ) * oddProd m = centralBinom m * oddProd' m := by
    exact_mod_cast centralBinom_two_mul_mul m
  have h16 : (16 : ℤ) ∣ (oddProd' m : ℤ) - oddProd m := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((oddProd' m : ℤ) - oddProd m) 16).1
      (by push_cast; rw [oddProd'_cast m hm, sub_self])
    exact_mod_cast this
  have h2 : (2 : ℤ) ∣ centralBinom m := by
    exact_mod_cast Nat.two_dvd_centralBinom_of_one_le hpos
  have h32 : (32 : ℤ) ∣ ((centralBinom (2 * m) : ℤ) - centralBinom m) * oddProd m := by
    have := mul_dvd_mul h2 h16
    rw [show (centralBinom m : ℤ) * (oddProd' m - oddProd m) =
      ((centralBinom (2 * m) : ℤ) - centralBinom m) * oddProd m by rw [sub_mul, hkey]; ring]
      at this
    rwa [show (2 : ℤ) * 16 = 32 by norm_num] at this
  have hcop : IsCoprime (32 : ℤ) (oddProd m : ℤ) := by
    have h : Nat.Coprime 32 (oddProd m) := by
      have := (Nat.coprime_two_left.2 (oddProd_odd m)).pow_left 5
      rwa [show (2 : ℕ) ^ 5 = 32 by norm_num] at this
    exact_mod_cast Nat.isCoprime_iff_coprime.2 h
  have := hcop.dvd_of_dvd_mul_right h32
  omega

/-- $B(2^n) \equiv 6 \pmod{32}$ for $n \ge 3$. -/
theorem centralBinom_two_pow (n : ℕ) (hn : 3 ≤ n) : centralBinom (2 ^ n) % 32 = 6 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h8 : 8 ∣ 2 ^ n := (by norm_num : (8 : ℕ) ∣ 2 ^ 3).trans (pow_dvd_pow 2 hn)
    rw [pow_succ', centralBinom_two_mul_mod _ h8 (by positivity), ih]

theorem centralBinom_succ_eq (k : ℕ) : centralBinom (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := Nat.succ_mul_centralBinom_succ k
  have h2 := succ_mul_catalan_eq_centralBinom k
  apply Nat.eq_of_mul_eq_mul_left (show 0 < k + 1 by omega)
  rw [h1, ← h2]
  ring

theorem mod_of_cast {a : ℕ} {b : ZMod 16} (h : (a : ZMod 16) = b) : a % 16 = b.val := by
  rw [← ZMod.val_natCast, h]

/-- **OEIS A289682** (R. Israel's conjecture): for $n \ge 3$,
$C(2^n - 1) \equiv 13 \pmod{16}$ and $C(2^n) \equiv 6 \pmod{16}$. -/
theorem a289682 (n : ℕ) (hn : 3 ≤ n) :
    catalan (2 ^ n - 1) % 16 = 13 ∧ catalan (2 ^ n) % 16 = 6 := by
  have hB := centralBinom_two_pow n hn
  have h8 : 8 ∣ 2 ^ n := (by norm_num : (8 : ℕ) ∣ 2 ^ 3).trans (pow_dvd_pow 2 hn)
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
  constructor
  · rw [hk, Nat.add_sub_cancel]
    have hB' := hB
    rw [hk, centralBinom_succ_eq, mul_assoc] at hB'
    generalize hX : (2 * k + 1) * catalan k = X at hB'
    have h1 : ((2 * k + 1 : ℕ) : ZMod 16) * (catalan k : ZMod 16) = 3 := by
      rw [← Nat.cast_mul, hX, ← ZMod.natCast_mod, show X % 16 = 3 by omega]
      rfl
    have h2 : ((2 * k + 1 : ℕ) : ZMod 16) = 15 := by
      rw [← ZMod.natCast_mod, show (2 * k + 1) % 16 = 15 by omega]
      rfl
    rw [h2] at h1
    have key : ∀ x : ZMod 16, 15 * x = 3 → x = 13 := by decide
    exact (mod_of_cast (key _ h1)).trans (by decide)
  · have h := succ_mul_catalan_eq_centralBinom (2 ^ n)
    have h1 : ((2 ^ n + 1 : ℕ) : ZMod 16) * (catalan (2 ^ n) : ZMod 16) = 6 := by
      rw [← Nat.cast_mul, h, ← ZMod.natCast_mod, show centralBinom (2 ^ n) % 16 = 6 by omega]
      rfl
    have h2 : ((2 ^ n + 1 : ℕ) : ZMod 16) = 1 ∨ ((2 ^ n + 1 : ℕ) : ZMod 16) = 9 := by
      rcases (by omega : (2 ^ n + 1) % 16 = 1 ∨ (2 ^ n + 1) % 16 = 9) with h3 | h3
      · left
        rw [← ZMod.natCast_mod, h3]
        rfl
      · right
        rw [← ZMod.natCast_mod, h3]
        rfl
    have key : ∀ a x : ZMod 16, (a = 1 ∨ a = 9) → a * x = 6 → x = 6 := by decide
    exact (mod_of_cast (key _ _ h2 h1)).trans (by decide)

end OeisA289682

namespace OeisA289682

theorem catalan_two_pow_mod_sixteen :
    ∀ n : ℕ, 3 ≤ n → catalan (2 ^ n - 1) % 16 = 13 ∧ catalan (2 ^ n) % 16 = 6 :=
  fun n hn => a289682 n hn

end OeisA289682

end
