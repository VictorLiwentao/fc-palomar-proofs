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
# OEIS A088041: the least `k > 1` with `k⁴ - 1` divisible by an `n`-th power

For `n ≥ 4` the least `k > 1` such that `mⁿ ∣ k⁴ - 1` for some `m > 1` is `2^(n-2) - 1`
(conjectured in the entry; proved by Robert Israel, Aug 19 2019). We also prove the first terms
`2, 3, 3` and Colin Barker's recurrence `a(n) = 3a(n-1) - 2a(n-2)` for `n > 5`.

The proof is Israel's. Write `k = j + 1`, so `k⁴ - 1 = j (j + 2) (j² + 2j + 2)`. If `pⁿ` divides
this for a prime `p`:

* `p = 2`: `j = 2t` and `k⁴ - 1 = 8 t (t + 1) (2t² + 2t + 1)`, so `2^(n-3)` divides `t` or
  `t + 1`, and `k ≥ 2^(n-2) - 1`.
* `p` odd: two of the factors share only the divisor 2, so `pⁿ` divides one of them. For `j` or
  `j + 2`, `k + 1 ≥ 3ⁿ`. For `j² + 2j + 2 = k² + 1`, `p ≠ 3` (no square is `-1` mod 3), so
  `k² + 1 ≥ 5ⁿ > 4^(n-2)`.

*References:*
- [A088041](https://oeis.org/A088041); R. Israel, *Proof of conjectured formula* (2019),
  https://oeis.org/A088041/a088041.pdf
-/

@[expose] public section

namespace OeisA88041

/-- The `k > 1` such that `k⁴ - 1` is divisible by `mⁿ` for some `m > 1`. -/
def S (n : ℕ) : Set ℕ := {k | 1 < k ∧ ∃ m, 1 < m ∧ m ^ n ∣ k ^ 4 - 1}

/-- The sequence: the least such `k`. -/
noncomputable def a (n : ℕ) : ℕ := sInf (S n)

lemma pow_four_sub_one (j : ℕ) : (j + 1) ^ 4 - 1 = j * (j + 2) * (j ^ 2 + 2 * j + 2) :=
  Nat.sub_eq_of_eq_add (by ring)

lemma two_pow_eq (n : ℕ) (hn : 3 ≤ n) : 2 ^ n = 8 * 2 ^ (n - 3) := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
  congr 1
  omega

lemma two_pow_sub_two (n : ℕ) (hn : 3 ≤ n) : 2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
  rw [← pow_succ']
  congr 1
  omega

/-- The value `2^(n-2) - 1` works, with `m = 2`. -/
lemma mem_S (n : ℕ) (hn : 4 ≤ n) : 2 ^ (n - 2) - 1 ∈ S n := by
  have hP : 2 ≤ 2 ^ (n - 3) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ (n - 3) = Q + 1 := ⟨2 ^ (n - 3) - 1, by omega⟩
  have hK : 2 ^ (n - 2) - 1 = 2 * Q + 1 := by
    rw [two_pow_sub_two n (by omega), hQ]
    omega
  refine ⟨by omega, 2, by norm_num, ?_⟩
  rw [hK, pow_four_sub_one, two_pow_eq n (by omega), hQ]
  exact ⟨Q * (2 * Q ^ 2 + 2 * Q + 1), by ring⟩

lemma prime_not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

lemma coprime_pow {p n x : ℕ} (hp : p.Prime) (h : ¬ p ∣ x) : (p ^ n).Coprime x :=
  Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)

lemma not_three_dvd (j : ℕ) : ¬ 3 ∣ j ^ 2 + 2 * j + 2 := by
  intro h
  have h0 : ((j ^ 2 + 2 * j + 2 : ℕ) : ZMod 3) = 0 := (CharP.cast_eq_zero_iff (ZMod 3) 3 _).mpr h
  push_cast at h0
  generalize (j : ZMod 3) = x at h0
  revert x
  decide

/-- The case `p = 2`. -/
lemma le_of_two_pow_dvd (n j : ℕ) (hn : 4 ≤ n) (hj : 1 ≤ j)
    (h : 2 ^ n ∣ j * (j + 2) * (j ^ 2 + 2 * j + 2)) : 2 ^ (n - 2) - 1 ≤ j + 1 := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
  · have e : 2 * t * (2 * t + 2) * ((2 * t) ^ 2 + 2 * (2 * t) + 2) =
        8 * (t * (t + 1) * (2 * t ^ 2 + 2 * t + 1)) := by ring
    rw [e, two_pow_eq n (by omega)] at h
    have h1 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    have hodd : (2 ^ (n - 3)).Coprime (2 * t ^ 2 + 2 * t + 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ⟨t ^ 2 + t, by ring⟩)
    have h2 := hodd.dvd_of_dvd_mul_right h1
    rw [two_pow_sub_two n (by omega)]
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' t
    · have hc : (2 ^ (n - 3)).Coprime (2 * s + 1) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ⟨s, rfl⟩)
      have := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h2)
      omega
    · have hc : (2 ^ (n - 3)).Coprime (2 * s + 1) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ⟨s, rfl⟩)
      have := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left h2)
      omega
  · exfalso
    have h2 : 2 ∣ (2 * t + 1) * (2 * t + 1 + 2) * ((2 * t + 1) ^ 2 + 2 * (2 * t + 1) + 2) :=
      (dvd_pow_self 2 (by omega)).trans h
    have e : (2 * t + 1) ^ 2 + 2 * (2 * t + 1) + 2 = 2 * (2 * t ^ 2 + 4 * t + 2) + 1 := by ring
    rw [e] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h3 | h3
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h3 with h4 | h4 <;> omega
    · omega

/-- The case of an odd prime. -/
lemma le_of_odd_prime_pow_dvd (n j p : ℕ) (hn : 4 ≤ n) (hj : 1 ≤ j) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ n ∣ j * (j + 2) * (j ^ 2 + 2 * j + 2)) : 2 ^ (n - 2) - 1 ≤ j + 1 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h2 := prime_not_dvd_two hp hp2
  have hB : 2 ^ (n - 2) ≤ p ^ n :=
    calc 2 ^ (n - 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p ^ n := Nat.pow_le_pow_left (by omega) n
  have hpd : p ∣ j * (j + 2) * (j ^ 2 + 2 * j + 2) := (dvd_pow_self p (by omega)).trans h
  have e1 : j ^ 2 + 2 * j + 2 = j * (j + 2) + 2 := by ring
  have e2 : j ^ 2 + 2 * j + 2 = (j + 2) * j + 2 := by ring
  rcases (Nat.Prime.dvd_mul hp).mp hpd with h12 | h3
  · rcases (Nat.Prime.dvd_mul hp).mp h12 with h1 | h1
    · -- `p ∣ j`
      have n2 : ¬ p ∣ j + 2 := fun h' => h2 ((Nat.dvd_add_right h1).mp h')
      have n3 : ¬ p ∣ j ^ 2 + 2 * j + 2 := fun h' =>
        h2 ((Nat.dvd_add_right (Dvd.dvd.mul_right h1 _)).mp (e1 ▸ h'))
      have hc : (p ^ n).Coprime ((j + 2) * (j ^ 2 + 2 * j + 2)) :=
        coprime_pow hp fun h' => (hp.dvd_mul.mp h').elim n2 n3
      rw [mul_assoc] at h
      have := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h)
      omega
    · -- `p ∣ j + 2`
      have n1 : ¬ p ∣ j := fun h' => h2 ((Nat.dvd_add_right h').mp h1)
      have n3 : ¬ p ∣ j ^ 2 + 2 * j + 2 := fun h' =>
        h2 ((Nat.dvd_add_right (Dvd.dvd.mul_right h1 _)).mp (e2 ▸ h'))
      have h4 := (coprime_pow hp n3).dvd_of_dvd_mul_right h
      have h5 := (coprime_pow hp n1).dvd_of_dvd_mul_left h4
      have := Nat.le_of_dvd (by omega) h5
      omega
  · -- `p ∣ j² + 2j + 2`
    have n1 : ¬ p ∣ j := fun h' =>
      h2 ((Nat.dvd_add_right (Dvd.dvd.mul_right h' _)).mp (e1 ▸ h3))
    have n2 : ¬ p ∣ j + 2 := fun h' =>
      h2 ((Nat.dvd_add_right (Dvd.dvd.mul_right h' _)).mp (e2 ▸ h3))
    have hp5 : 5 ≤ p := by
      have : p ≠ 3 := fun h' => not_three_dvd j (h' ▸ h3)
      have : p ≠ 4 := fun h' => by
        rw [h'] at hp
        norm_num at hp
      omega
    have hc : (p ^ n).Coprime (j * (j + 2)) :=
      coprime_pow hp fun h' => (hp.dvd_mul.mp h').elim n1 n2
    have h4 := hc.dvd_of_dvd_mul_left h
    have h5 := Nat.le_of_dvd (by positivity) h4
    by_contra hlt
    have hlt := not_le.mp hlt
    have h6 : (j + 2) ^ 2 < (2 ^ (n - 2)) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    have h7 : (2 ^ (n - 2)) ^ 2 ≤ 5 ^ n :=
      calc (2 ^ (n - 2)) ^ 2 = 4 ^ (n - 2) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 5 ^ n := Nat.pow_le_pow_left (by norm_num) n
    have h8 : 5 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp5 n
    have h9 : j ^ 2 + 2 * j + 2 < (j + 2) ^ 2 := by nlinarith
    omega

/-- No `k < 2^(n-2) - 1` works. -/
lemma le_of_mem_S (n : ℕ) (hn : 4 ≤ n) {k : ℕ} (hk : k ∈ S n) : 2 ^ (n - 2) - 1 ≤ k := by
  obtain ⟨hk1, m, hm1, hdvd⟩ := hk
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  have hpn : p ^ n ∣ k ^ 4 - 1 := (pow_dvd_pow_of_dvd hpm n).trans hdvd
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_four_sub_one] at hpn
  by_cases hp2 : p = 2
  · subst hp2
    exact le_of_two_pow_dvd n j hn (by omega) hpn
  · exact le_of_odd_prime_pow_dvd n j p hn (by omega) hp hp2 hpn

/-- **A088041**: for `n ≥ 4`, the least `k > 1` with `k⁴ - 1` divisible by an `n`-th power
`mⁿ`, `m > 1`, is `2^(n-2) - 1` (Israel). -/
theorem isLeast_S (n : ℕ) (hn : 4 ≤ n) : IsLeast (S n) (2 ^ (n - 2) - 1) :=
  ⟨mem_S n hn, fun _ hk => le_of_mem_S n hn hk⟩

theorem a_eq (n : ℕ) (hn : 4 ≤ n) : a n = 2 ^ (n - 2) - 1 :=
  (isLeast_S n hn).csInf_eq

/-! ### The first terms and Barker's recurrence -/

lemma isLeast_S_one : IsLeast (S 1) 2 :=
  ⟨⟨by norm_num, 15, by norm_num, by norm_num⟩, fun _ hk => hk.1⟩

lemma isLeast_S_small (n : ℕ) (hn2 : 2 ≤ n) (hn4 : n ≤ 4) : IsLeast (S n) 3 := by
  refine ⟨⟨by norm_num, 2, by norm_num, ?_⟩, fun k hk => ?_⟩
  · interval_cases n <;> norm_num
  · obtain ⟨hk1, m, hm1, hdvd⟩ := hk
    by_contra hlt
    obtain rfl : k = 2 := by omega
    have hm2 : m ^ 2 ∣ 15 := (pow_dvd_pow m hn2).trans (by norm_num at hdvd ⊢; exact hdvd)
    have hle : m ^ 2 ≤ 15 := Nat.le_of_dvd (by norm_num) hm2
    have hm3 : m ≤ 3 := by nlinarith
    interval_cases m <;> norm_num at hm2

theorem a_small : a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 3 :=
  ⟨isLeast_S_one.csInf_eq, (isLeast_S_small 2 le_rfl (by norm_num)).csInf_eq,
    (isLeast_S_small 3 (by norm_num) (by norm_num)).csInf_eq⟩

/-- Barker's recurrence `a(n) = 3 a(n-1) - 2 a(n-2)` for `n > 5`. -/
theorem a_recurrence (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 6 := ⟨n - 6, by omega⟩
  rw [a_eq (r + 6) (by omega), a_eq (r + 6 - 1) (by omega), a_eq (r + 6 - 2) (by omega)]
  have e1 : r + 6 - 2 = r + 4 := rfl
  have e2 : r + 6 - 1 - 2 = r + 3 := rfl
  have e3 : r + 4 - 2 = r + 2 := rfl
  rw [e1, e2, e3, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_sub Nat.one_le_two_pow,
    Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  ring

end OeisA88041



end
