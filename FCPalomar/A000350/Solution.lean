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
# Fibonacci numbers whose binary expansion ends with their index (OEIS A000350)

The binary expansion of $F(m)$ ends with the binary expansion of $m$ only for $m = 0, 1, 5$
(conjecture of R. Stephan, 2006; proof sketch by M. Alekseyev, 2009). Here "ends with" means
$F(m) \equiv m \pmod{2^L}$, where $L$ is the number of binary digits of $m$, or equivalently that
the little-endian digit list of $m$ is a prefix of that of $F(m)$. For $m = 0$ the digit list is
empty, so $m = 0$ is a (trivial) solution.

Proof (Alekseyev): $F(3 \cdot 2^k + n) \equiv F(n) \pmod{2^{k+1}}$. By induction on $k$, if
$F(m) \equiv m \pmod{2^k}$ then $m \equiv 0, 1$ or $5 \pmod{3 \cdot 2^k}$. With $k = L$ and
$m < 2^L$ this forces $m \in \{0, 1, 5\}$.

*References:*
- N. J. A. Sloane, OEIS [A000350](https://oeis.org/A000350); comments by R. Stephan (2006),
  T. D. Noe (2007) and M. Alekseyev (2009).
-/

@[expose] public section

namespace OeisA350

open Nat

/-- $2^{k+1} \mid F(3 \cdot 2^k)$ and $F(3 \cdot 2^k + 1) \equiv 1 \pmod{2^{k+1}}$. -/
theorem fib_three_mul_two_pow (k : ℕ) :
    (2 : ℤ) ^ (k + 1) ∣ (fib (3 * 2 ^ k) : ℤ) ∧
      (2 : ℤ) ^ (k + 1) ∣ (fib (3 * 2 ^ k + 1) : ℤ) - 1 := by
  induction k with
  | zero =>
    have h3 : fib 3 = 2 := rfl
    have h4 : fib 4 = 3 := rfl
    norm_num [h3, h4]
  | succ k ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    have hle : fib (3 * 2 ^ k) ≤ 2 * fib (3 * 2 ^ k + 1) :=
      le_trans Nat.fib_le_fib_succ (by omega)
    have d1 : (fib (2 * (3 * 2 ^ k)) : ℤ) =
        fib (3 * 2 ^ k) * (2 * fib (3 * 2 ^ k + 1) - fib (3 * 2 ^ k)) := by
      rw [Nat.fib_two_mul, Nat.cast_mul, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]
    have d2 : (fib (2 * (3 * 2 ^ k) + 1) : ℤ) =
        fib (3 * 2 ^ k + 1) ^ 2 + fib (3 * 2 ^ k) ^ 2 := by
      rw [Nat.fib_two_mul_add_one, Nat.cast_add, Nat.cast_pow, Nat.cast_pow]
    have hb' : (fib (3 * 2 ^ k + 1) : ℤ) = 1 + 2 ^ (k + 1) * b := by linarith
    rw [show 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) by ring, d1, d2, ha, hb']
    exact ⟨⟨a * (1 + 2 ^ (k + 1) * b - 2 ^ k * a), by ring⟩,
      ⟨b + 2 ^ k * b ^ 2 + 2 ^ k * a ^ 2, by ring⟩⟩

/-- The Fibonacci numbers modulo $2^{k+1}$ have period dividing $3 \cdot 2^k$. -/
theorem fib_add_period (k n : ℕ) :
    (2 : ℤ) ^ (k + 1) ∣ (fib (3 * 2 ^ k + n) : ℤ) - fib n := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := fib_three_mul_two_pow k
  rcases n with _ | n
  · simp [ha]
  · rw [show 3 * 2 ^ k + (n + 1) = 3 * 2 ^ k + n + 1 by ring, Nat.fib_add]
    push_cast
    rw [ha, show (fib (3 * 2 ^ k + 1) : ℤ) = 1 + 2 ^ (k + 1) * b by linarith]
    exact ⟨a * fib n + b * fib (n + 1), by ring⟩

theorem fib_mod_period (k m : ℕ) :
    (2 : ℤ) ^ (k + 1) ∣ (fib m : ℤ) - fib (m % (3 * 2 ^ k)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h : m < 3 * 2 ^ k
    · rw [Nat.mod_eq_of_lt h, sub_self]
      exact dvd_zero _
    · obtain ⟨j, rfl⟩ : ∃ j, m = 3 * 2 ^ k + j := ⟨m - 3 * 2 ^ k, by omega⟩
      have hpos : 0 < 3 * 2 ^ k := by positivity
      have h2 := ih j (by omega)
      rw [Nat.add_mod_left]
      have := dvd_add (fib_add_period k j) h2
      rwa [sub_add_sub_cancel] at this

/-- **Alekseyev's induction.** If $F(m) \equiv m \pmod{2^k}$, then $m \equiv 0, 1$ or $5$
modulo $3 \cdot 2^k$. -/
theorem residue (k m : ℕ) (h : (2 : ℤ) ^ k ∣ (fib m : ℤ) - m) :
    ∃ r : ℕ, (r = 0 ∨ r = 1 ∨ r = 5) ∧ (3 * 2 ^ k : ℤ) ∣ (m : ℤ) - r := by
  induction k with
  | zero =>
    rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h0 | h0 | h0
    · exact ⟨0, by simp, by norm_num; omega⟩
    · exact ⟨1, by simp, by norm_num; omega⟩
    · exact ⟨5, by simp, by norm_num; omega⟩
  | succ k ih =>
    have h' : (2 : ℤ) ^ k ∣ (fib m : ℤ) - m := (pow_dvd_pow 2 (Nat.le_succ k)).trans h
    obtain ⟨r, hr, t, ht⟩ := ih h'
    have hmod : m % (3 * 2 ^ k) = r % (3 * 2 ^ k) :=
      (Nat.modEq_iff_dvd.2 (by push_cast; exact ⟨t, ht⟩)).symm
    have hp1 := fib_mod_period k m
    have hp2 := fib_mod_period k r
    rw [hmod] at hp1
    have hF : (2 : ℤ) ^ (k + 1) ∣ (fib m : ℤ) - fib r := by
      have := dvd_sub hp1 hp2
      rwa [sub_sub_sub_cancel_right] at this
    have hFr : (fib r : ℤ) = r := by
      rcases hr with rfl | rfl | rfl <;> decide
    rw [hFr] at hF
    have hmr : (2 : ℤ) ^ (k + 1) ∣ (m : ℤ) - r := by
      have := dvd_sub hF h
      rwa [show (fib m : ℤ) - r - ((fib m : ℤ) - m) = m - r by ring] at this
    rw [ht, show (2 : ℤ) ^ (k + 1) = 2 ^ k * 2 by ring,
      show (3 : ℤ) * 2 ^ k * t = 2 ^ k * (3 * t) by ring] at hmr
    have h2 : (2 : ℤ) ∣ 3 * t := (mul_dvd_mul_iff_left (pow_ne_zero k two_ne_zero)).1 hmr
    obtain ⟨s, hs⟩ : (2 : ℤ) ∣ t := by omega
    exact ⟨r, hr, s, by rw [ht, hs]; ring⟩

/-- $F(m) \equiv m \pmod{2^L}$, with $L$ the number of binary digits of $m$, only for
$m = 0, 1, 5$. -/
theorem fib_mod_iff (m : ℕ) :
    fib m % 2 ^ (Nat.digits 2 m).length = m ↔ m = 0 ∨ m = 1 ∨ m = 5 := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ : ∃ q, fib m = m + 2 ^ (Nat.digits 2 m).length * q :=
      ⟨fib m / 2 ^ (Nat.digits 2 m).length, by
        have := Nat.mod_add_div (fib m) (2 ^ (Nat.digits 2 m).length)
        rw [h] at this
        exact this.symm⟩
    have hd : (2 : ℤ) ^ (Nat.digits 2 m).length ∣ (fib m : ℤ) - m :=
      ⟨q, by rw [hq, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; ring⟩
    obtain ⟨r, hr, t, ht⟩ := residue _ m hd
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exact Or.inl h0
    have hlt : (m : ℤ) < 2 ^ (Nat.digits 2 m).length := by
      exact_mod_cast Nat.lt_base_pow_length_digits (b := 2) (m := m) (by norm_num)
    have hL : 1 ≤ (Nat.digits 2 m).length :=
      List.length_pos_iff.2 (Nat.digits_ne_nil_iff_ne_zero.2 (by omega))
    have h2L : (2 : ℤ) ≤ 2 ^ (Nat.digits 2 m).length := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hL
      rwa [pow_one] at this
    have hr5 : (r : ℤ) ≤ 5 := by rcases hr with rfl | rfl | rfl <;> norm_num
    have hr0 : (0 : ℤ) ≤ r := Nat.cast_nonneg r
    have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hpos
    generalize (2 : ℤ) ^ (Nat.digits 2 m).length = P at ht hlt h2L
    have ht0 : t = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with htn | htp
      · have : t ≤ -1 := by omega
        nlinarith
      · have : 1 ≤ t := by omega
        nlinarith
    rw [ht0, mul_zero, sub_eq_zero] at ht
    have hmr : m = r := by exact_mod_cast ht
    subst hmr
    exact hr
  · rintro (rfl | rfl | rfl)
    · simp
    · have h1 : Nat.digits 2 1 = [1] := by norm_num [Nat.digits_def']
      rw [h1]
      decide
    · have h5 : Nat.digits 2 5 = [1, 0, 1] := by norm_num [Nat.digits_def']
      rw [h5]
      decide

/-- In base $b \ge 2$, the digit list of `m` is a prefix of that of `n` (that is, `n` ends with
`m`) iff $n \equiv m$ modulo $b^L$, where $L$ is the number of digits of `m`. -/
theorem digits_prefix_iff {b : ℕ} (hb : 1 < b) (m n : ℕ) :
    Nat.digits b m <+: Nat.digits b n ↔ n % b ^ (Nat.digits b m).length = m := by
  constructor
  · rintro ⟨l, hl⟩
    have h := congrArg (Nat.ofDigits b) hl
    rw [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.ofDigits_digits] at h
    rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.lt_base_pow_length_digits hb)]
  · intro h
    have e : m + b ^ (Nat.digits b m).length * (n / b ^ (Nat.digits b m).length) = n := by
      have := Nat.mod_add_div n (b ^ (Nat.digits b m).length)
      rw [h] at this
      exact this
    exact ⟨Nat.digits b (n / b ^ (Nat.digits b m).length), by
      rw [Nat.digits_append_digits (b := b) (by omega), e]⟩

/-- **OEIS A000350, binary comment** (Stephan's conjecture, Alekseyev's proof): the binary
expansion of $F(m)$ ends with that of $m$ iff $m \in \{0, 1, 5\}$. -/
theorem a000350_binary (m : ℕ) :
    Nat.digits 2 m <+: Nat.digits 2 (fib m) ↔ m = 0 ∨ m = 1 ∨ m = 5 := by
  rw [digits_prefix_iff (b := 2) (by norm_num), fib_mod_iff]

/-- The comment's form: other than $1$ and $5$, no $m \ge 1$ has this property. -/
theorem a000350_binary_pos (m : ℕ) (hm : 0 < m) :
    Nat.digits 2 m <+: Nat.digits 2 (fib m) ↔ m = 1 ∨ m = 5 := by
  rw [a000350_binary]
  omega

end OeisA350

namespace OeisA350

theorem digits_prefix_fib_iff :
    ∀ m : ℕ, Nat.digits 2 m <+: Nat.digits 2 (Nat.fib m) ↔ m = 0 ∨ m = 1 ∨ m = 5 :=
  fun m => a000350_binary m

end OeisA350

end
