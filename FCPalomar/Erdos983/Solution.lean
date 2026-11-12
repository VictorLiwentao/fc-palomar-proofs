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
# Erdős Problem 983: $f(\pi(n) + 1, n) \le 2\pi(\sqrt n) + 1$

Let $f(k, n)$ be the least $r$ such that every $A \subseteq \{1, \ldots, n\}$ with $|A| = k$ has a
set $S$ of $r$ primes with more than $r$ elements of $A$ divisible only by primes in $S$. Erdős and
Straus proved $f(\pi(n) + 1, n) \le 2\pi(n^{1/2}) + 1$. This file proves it with the definitions
of `FormalConjectures/ErdosProblems/983.lean`, copied verbatim.

Let $s = \pi(\sqrt n)$. If $\pi(n) \le 2s + 1$, all primes up to $n$ work. Otherwise, call a prime
$q > \sqrt n$ large and let $c_q$ be the number of elements of $A$ divisible by $q$. An element
of $A$ has at most one large prime factor, so $|A| \le t + \sum_q c_q$, where $t$ counts the
elements with only small prime factors, and $S = \{p \le \sqrt n\} \cup Q$ has at least
$t + \sum_{q \in Q} c_q$ smooth elements. A set $Q$ of $s + 1$ large primes either has
$c_q \ge 2$ for all $q \in Q$, or contains every large prime with $c_q \ge 2$. In both cases
$t + \sum_{q \in Q} c_q \ge 2s + 2$. This is the argument of Erdős and Straus
[Er70b, pp. 138–139].

*References:*
- [erdosproblems.com/983](https://www.erdosproblems.com/983)
- P. Erdős, *Some applications of graph theory to number theory*, Proc. Second Chapel Hill Conf.
  on Combinatorial Mathematics and its Applications (1970), 136–145, p. 139, (14).
-/

@[expose] public section

namespace Erdos983

/-- `numSmooth A S` is the number of elements of `A` all of whose prime factors lie in `S`.
The element `1` has no prime factors, so it is counted for every `S`. -/
def numSmooth (A S : Finset ℕ) : ℕ :=
  (A.filter fun a => ∀ p ∈ a.primeFactors, p ∈ S).card

/-- $f(k,n)$ is the least $r$ such that every $A\subseteq\{1,\ldots,n\}$ with $|A|=k$ has a set
$S$ of $r$ primes with more than $r$ elements of $A$ divisible only by primes from $S$.

For $\pi(n)<k\leq n$ the value $r=\pi(n)$ is admissible (take all primes $\leq n$), so `sInf` is
a minimum. Outside this range `f k n = 0` is a junk value: for $k\leq\pi(n)$ no $r$ is
admissible, and for $k>n$ every $r$ is. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
    ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < numSmooth A S}

theorem f_le {k n r : ℕ}
    (h : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
      ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < numSmooth A S) :
    f k n ≤ r :=
  Nat.sInf_le h

/-- Two distinct primes above $\sqrt n$ do not both divide a number $a \in [1, n]$. -/
theorem not_two_large {n a p q : ℕ} (ha : a ≤ n) (ha0 : a ≠ 0) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpa : p ∣ a) (hqa : q ∣ a) (hsp : Nat.sqrt n < p) (hsq : Nat.sqrt n < q) :
    False := by
  have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0)
    (((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd hpa hqa)
  have h2 := (Nat.lt_succ_sqrt n).trans_le
    (Nat.mul_le_mul (Nat.succ_le_of_lt hsp) (Nat.succ_le_of_lt hsq))
  omega

/-- Every element of $A$ is $\sqrt n$-smooth or divisible by a prime in $(\sqrt n, n]$. -/
theorem card_le_numSmooth_add (n : ℕ) {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n) :
    A.card ≤ numSmooth A (Nat.primesLE (Nat.sqrt n)) +
      ∑ q ∈ (Nat.primesLE n).filter (Nat.sqrt n < ·), (A.filter (q ∣ ·)).card := by
  unfold numSmooth
  calc A.card ≤ (A.filter (fun a => ∀ p ∈ a.primeFactors, p ∈ Nat.primesLE (Nat.sqrt n)) ∪
        ((Nat.primesLE n).filter (Nat.sqrt n < ·)).biUnion (fun q => A.filter (q ∣ ·))).card := by
        refine Finset.card_le_card fun a ha => ?_
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
        by_cases h : ∀ p ∈ a.primeFactors, p ∈ Nat.primesLE (Nat.sqrt n)
        · exact Or.inl ⟨ha, h⟩
        · push Not at h
          obtain ⟨p, hp, hpS⟩ := h
          have han := (Finset.mem_Icc.mp (hA ha)).2
          have hpp := Nat.prime_of_mem_primeFactors hp
          refine Or.inr ⟨p, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr
            ⟨(Nat.le_of_mem_primeFactors hp).trans han, hpp⟩, ?_⟩,
            Finset.mem_filter.mpr ⟨ha, Nat.dvd_of_mem_primeFactors hp⟩⟩
          by_contra hle
          exact hpS (Nat.mem_primesLE.mpr ⟨not_lt.mp hle, hpp⟩)
    _ ≤ _ := (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)

/-- With $S = \{p \le \sqrt n\} \cup Q$ for large primes $Q$, the smooth elements of $A$ include
the $\sqrt n$-smooth ones and, disjointly, the multiples of each $q \in Q$. -/
theorem numSmooth_add_sum_le (n : ℕ) {A Q : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n)
    (hQ : Q ⊆ (Nat.primesLE n).filter (Nat.sqrt n < ·)) :
    numSmooth A (Nat.primesLE (Nat.sqrt n)) + ∑ q ∈ Q, (A.filter (q ∣ ·)).card ≤
      numSmooth A (Nat.primesLE (Nat.sqrt n) ∪ Q) := by
  have hQ' : ∀ q ∈ Q, q.Prime ∧ Nat.sqrt n < q := fun q hq => by
    have h := Finset.mem_filter.mp (hQ hq)
    exact ⟨(Nat.mem_primesLE.mp h.1).2, h.2⟩
  have hdisj : (Q : Set ℕ).PairwiseDisjoint (fun q => A.filter (q ∣ ·)) := by
    intro q hq q' hq' hqq'
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_filter] at ha ha'
    have han := Finset.mem_Icc.mp (hA ha.1)
    exact not_two_large han.2 (by omega) (hQ' q hq).1 (hQ' q' hq').1 hqq' ha.2 ha'.2
      (hQ' q hq).2 (hQ' q' hq').2
  have hdisj2 : Disjoint
      (A.filter fun a => ∀ p ∈ a.primeFactors, p ∈ Nat.primesLE (Nat.sqrt n))
      (Q.biUnion fun q => A.filter (q ∣ ·)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_filter] at ha
    obtain ⟨q, hq, ha'⟩ := Finset.mem_biUnion.mp ha'
    rw [Finset.mem_filter] at ha'
    have han := Finset.mem_Icc.mp (hA ha.1)
    have hqf : q ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨(hQ' q hq).1, ha'.2, by omega⟩
    exact absurd (hQ' q hq).2 (not_lt.mpr (Nat.mem_primesLE.mp (ha.2 q hqf)).1)
  unfold numSmooth
  rw [← Finset.card_biUnion hdisj, ← Finset.card_union_eq_card_add_card.mpr hdisj2]
  refine Finset.card_le_card fun a ha => ?_
  rw [Finset.mem_union, Finset.mem_biUnion] at ha
  rw [Finset.mem_filter]
  rcases ha with ha | ⟨q, hq, ha⟩
  · rw [Finset.mem_filter] at ha
    exact ⟨ha.1, fun p hp => Finset.mem_union_left _ (ha.2 p hp)⟩
  · rw [Finset.mem_filter] at ha
    refine ⟨ha.1, fun p hp => ?_⟩
    by_cases hpq : p = q
    · exact Finset.mem_union_right _ (hpq ▸ hq)
    · have han := Finset.mem_Icc.mp (hA ha.1)
      have hpp := Nat.prime_of_mem_primeFactors hp
      refine Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨not_lt.mp fun hlt => ?_, hpp⟩)
      exact not_two_large han.2 (by omega) hpp (hQ' q hq).1 hpq
        (Nat.dvd_of_mem_primeFactors hp) ha.2 hlt (hQ' q hq).2

/-- From any finite set `P` one can choose `K ≤ |P|` elements `Q` such that either every chosen
weight is at least `2`, or every unchosen weight is at most `1`. -/
theorem exists_subset_sum_ge (P : Finset ℕ) (c : ℕ → ℕ) {K : ℕ} (hK : K ≤ P.card) :
    ∃ Q ⊆ P, Q.card = K ∧
      (2 * K ≤ ∑ q ∈ Q, c q ∨ ∑ q ∈ P, c q ≤ ∑ q ∈ Q, c q + (P.card - K)) := by
  by_cases hD : K ≤ (P.filter fun q => 2 ≤ c q).card
  · obtain ⟨Q, hQD, hQ⟩ := Finset.exists_subset_card_eq hD
    refine ⟨Q, hQD.trans (Finset.filter_subset _ _), hQ, Or.inl ?_⟩
    calc 2 * K = ∑ _q ∈ Q, 2 := by rw [Finset.sum_const, smul_eq_mul, hQ, mul_comm]
      _ ≤ ∑ q ∈ Q, c q := Finset.sum_le_sum fun q hq => (Finset.mem_filter.mp (hQD hq)).2
  · push Not at hD
    obtain ⟨Q, hDQ, hQP, hQ⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.filter_subset _ P) hD.le hK
    refine ⟨Q, hQP, hQ, Or.inr ?_⟩
    have hrest : ∑ q ∈ P \ Q, c q ≤ (P \ Q).card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun q hq => ?_
      rw [Finset.mem_sdiff] at hq
      by_contra h
      exact hq.2 (hDQ (Finset.mem_filter.mpr ⟨hq.1, by omega⟩))
    have hsplit := Finset.sum_sdiff hQP (f := c)
    have hcard := Finset.card_sdiff_of_subset hQP
    omega

/-- **Erdős–Straus.** $f(\pi(n) + 1, n) \le 2\pi(n^{1/2}) + 1$. -/
theorem upper_bound (n : ℕ) :
    f (Nat.primeCounting n + 1) n ≤ 2 * Nat.primeCounting (Nat.sqrt n) + 1 := by
  by_cases hsmall : Nat.primeCounting n ≤ 2 * Nat.primeCounting (Nat.sqrt n) + 1
  · refine le_trans (f_le fun A hA hcard => ⟨Nat.primesLE n,
      Nat.primesLE_card_eq_primeCounting n, fun p hp => (Nat.mem_primesLE.mp hp).2, ?_⟩) hsmall
    have h : numSmooth A (Nat.primesLE n) = A.card := by
      unfold numSmooth
      rw [Finset.filter_true_of_mem]
      intro a ha p hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans
        (Finset.mem_Icc.mp (hA ha)).2, Nat.prime_of_mem_primeFactors hp⟩
    omega
  · push Not at hsmall
    apply f_le
    intro A hA hcard
    have hsn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
    have hcardPs := Nat.primesLE_card_eq_primeCounting (Nat.sqrt n)
    have hfilt : (Nat.primesLE n).filter (fun q => ¬ Nat.sqrt n < q) =
        Nat.primesLE (Nat.sqrt n) := by
      ext q
      simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
      constructor
      · rintro ⟨⟨-, hq⟩, hle⟩
        exact ⟨hle, hq⟩
      · rintro ⟨hle, hq⟩
        exact ⟨⟨hle.trans hsn, hq⟩, hle⟩
    have hcardPL : ((Nat.primesLE n).filter (Nat.sqrt n < ·)).card +
        Nat.primeCounting (Nat.sqrt n) = Nat.primeCounting n := by
      rw [← hcardPs, ← hfilt, Finset.card_filter_add_card_filter_not,
        Nat.primesLE_card_eq_primeCounting]
    obtain ⟨Q, hQPL, hQcard, hQsum⟩ := exists_subset_sum_ge
      ((Nat.primesLE n).filter (Nat.sqrt n < ·)) (fun q => (A.filter (q ∣ ·)).card)
      (K := Nat.primeCounting (Nat.sqrt n) + 1) (by omega)
    have hdisjPQ : Disjoint (Nat.primesLE (Nat.sqrt n)) Q := by
      rw [Finset.disjoint_left]
      intro q hq hq'
      have h1 := (Nat.mem_primesLE.mp hq).1
      have h2 := (Finset.mem_filter.mp (hQPL hq')).2
      omega
    refine ⟨Nat.primesLE (Nat.sqrt n) ∪ Q, ?_, ?_, ?_⟩
    · rw [Finset.card_union_eq_card_add_card.mpr hdisjPQ, hcardPs, hQcard]
      omega
    · intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Nat.mem_primesLE.mp hp).2
      · exact (Nat.mem_primesLE.mp (Finset.mem_filter.mp (hQPL hp)).1).2
    · have h1 := card_le_numSmooth_add n hA
      have h2 := numSmooth_add_sum_le n hA hQPL
      rcases hQsum with h | h <;> omega

end Erdos983

namespace Erdos983

theorem erdos_983.variants.upper_bound (n : ℕ) :
    f (Nat.primeCounting n + 1) n ≤ 2 * Nat.primeCounting (Nat.sqrt n) + 1 :=
  _root_.Erdos983.upper_bound n

end Erdos983

end
