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
# OEIS A003024 and A188457: Gauss congruences and Bala's integrality conjectures

For an integer $q$ let $a_q(0) = 1$ and
$a_q(n) = \sum_{k=1}^{n} (-1)^{k+1} \binom{n}{k} q^{k(n-k)} a_q(n-k)$ for $n \ge 1$. Then $a_2$ is
OEIS A003024 (labeled acyclic digraphs) and $a_3$ is OEIS A188457 (acyclic 2-multidigraphs).
This file proves, for every integer $q$:

- **Theorem 1** (`gauss_congruence`): $a_q(n p^r) \equiv a_q(n p^{r-1}) \pmod{p^r}$ for every
  prime $p$ and all $n, r \ge 1$;
- **Corollary 2** (`exp_integral`): $\exp\left(\sum_{n \ge 1} a_q(n) x^n / n\right)$ has integer
  coefficients. The cases $q = 2$ and $q = 3$ are Peter Bala's conjectures (2016) in A003024 and
  A188457. The case $q = 2$ also shows that every term of A188490 is an integer.

For a tuple $k = (k_1, \dots, k_l)$ of natural numbers write $\binom{N}{k}$ for its multinomial
coefficient, $N = \sum k_i$, and $e(k) = \sum_{i < j} k_i k_j$ (`cross`). Let
$T_l(N, Q) = \sum_k \binom{N}{k} Q^{e(k)}$ over the tuples of $l$ positive integers with sum
$N$ (`blockSum`; the weight of a tuple with a zero entry is $0$). This is the number of ordered
set partitions of $\{1, \dots, N\}$ into $l$ blocks, weighted by $Q^{e(k)}$ and grouped by the
block sizes.

*Step 1 (`a_eq_sum`).* Splitting off the first entry gives
$T_{l+1}(N, Q) = \sum_{j=1}^{N} \binom{N}{j} Q^{j(N-j)} T_l(N-j, Q)$ (`blockSum_succ`). By strong
induction on $N$, this and the recurrence give $a_q(N) = \sum_l (-1)^{N+l} T_l(N, q)$.

*Step 2 (Frobenius step, `blockSum_frobenius`).* Work in the monoid algebra
$\mathbb{Z}[\mathbb{N}^l]$ with variables $x_i$. By the multinomial theorem,
$(\sum_i x_i)^M = \sum_k \binom{M}{k} x^k$ and $(\sum_i x_i^p)^M = \sum_k \binom{M}{k} x^{pk}$.
Since $(\sum_i x_i)^p \equiv \sum_i x_i^p \pmod p$, `dvd_sub_pow_of_dvd_sub` gives
$(\sum_i x_i)^{pN} \equiv (\sum_i x_i^p)^N \pmod{p^{v+1}}$ when $p^v \mid N$
(`pow_dvd_sum_xPow_sub`). The $\mathbb{Z}$-linear map $x^k \mapsto Q^{e(k)}$ (or $0$ if some
$k_i = 0$) sends the two sides to $T_l(pN, Q)$ and $T_l(N, Q^{p^2})$, because
$e(pk) = p^2 e(k)$. So $T_l(pN, Q) \equiv T_l(N, Q^{p^2}) \pmod{p^{v+1}}$.

*Step 3 (removing the twist, `term_dvd` and `blockSum_twist`).* Let $p^s \mid m$, and let $k$ be
a tuple of $l \ge 1$ positive integers with sum $m$. Choose $i$ with $g = v_p(k_i)$ minimal. Then
$p^g$ divides every $k_j$, so $p^g \mid e(k)$, and Fermat's little theorem with
`dvd_sub_pow_of_dvd_sub` gives $p^{g+1} \mid Q^{p^2 e(k)} - Q^{e(k)}$. Next,
$k_i \binom{m}{k_i} = m \binom{m-1}{k_i-1}$ and $\binom{m}{k_i} \mid \binom{m}{k}$, so
$p^s \mid p^g \binom{m}{k}$. Hence $p^{s+1} \mid \binom{m}{k} (Q^{p^2 e(k)} - Q^{e(k)})$, and
$T_l(m, Q^{p^2}) \equiv T_l(m, Q) \pmod{p^{s+1}}$.

*Step 4 (Theorem 1, `a_dvd`).* Let $p^v \mid N$. Steps 2 and 3 with $s = v$ give
$T_l(pN, q) \equiv T_l(N, q) \pmod{p^{v+1}}$ for every $l$. By Step 1,
$a_q(pN) \equiv \varepsilon\, a_q(N) \pmod{p^{v+1}}$ with $\varepsilon = (-1)^{(p+1)N}$. Here
$\varepsilon = 1$ unless $p = 2$ and $N$ is odd, and then $v = 0$ and the modulus is $2$. The
case $N = n p^{r-1}$, $v = r - 1$ is Theorem 1.

*Step 5 (Corollary 2, `exp_integral`).* Theorem 1 says that $a_q$ is a Gauss sequence:
$a_q(pM) \equiv a_q(M) \pmod{p^k}$ whenever $p$ is prime and $p^k \mid pM$. Dold's criterion
then gives integrality. Pairing the divisors $p^i e$ and $p^{i+1} e$ of $n$ shows
$n \mid \sum_{d \mid n} \mu(d)\, a_q(n/d)$. Möbius inversion gives
$a_q(n) = \sum_{d \mid n} d\, c(d)$ with integers $c(d)$. Up to degree $N$ the exponential
equals $\prod_{d=1}^{N} (1 - x^d)^{-c(d)}$, which has integer coefficients: both sides have
constant term $1$ and the same logarithmic derivative below degree $N$. This step is copied
from the package `FCPalomar/OeisA181316`, which adapts `FCPalomar/A158110`.

Steps 2 and 3 replace the group actions on ordered set partitions in the informal proof
(its Lemmas 3–5) by a polynomial congruence and a divisibility of multinomial coefficients.

The file ends with the first terms $1, 1, 3, 25, 543$ of A003024 and $1, 1, 5, 109, 9449$ of
A188457, and the coefficients $1, 1, 2, 10$ (A188490) and $1, 1, 3, 39$ of the two exponentials.

*References:*
- [A003024](https://oeis.org/A003024), [A188457](https://oeis.org/A188457) and
  [A188490](https://oeis.org/A188490); the conjectures are Peter Bala's, January 14, 2016.
- R. W. Robinson, *Counting labeled acyclic digraphs*, in New Directions in the Theory of
  Graphs, Academic Press, 1973, 239–273.
- R. P. Stanley, *Acyclic orientations of graphs*, Discrete Math. 5 (1973), 171–178.
- A. Dold, *Fixed point indices of iterated maps*, Invent. Math. 74 (1983), 419–435.
- R. P. Stanley, *Enumerative Combinatorics*, Vol. 2, Cambridge Univ. Press, 1999,
  Exercise 5.2(a).
-/

@[expose] public section

namespace OeisA003024

open PowerSeries Finset
open scoped ArithmeticFunction.Moebius Pointwise

/-- The sequence $a_q$, defined by $a_q(0) = 1$ and the recurrence (R)
$a_q(n) = \sum_{k=1}^{n} (-1)^{k+1} \binom{n}{k} q^{k(n-k)} a_q(n-k)$ for $n \ge 1$.
The sum runs over `(Finset.Icc 1 n).attach` so that the recursive call is visibly on a
smaller argument. -/
def a (q : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1 else
    ∑ k ∈ (Finset.Icc 1 n).attach,
      (-1) ^ (k.1 + 1) * (n.choose k.1 : ℤ) * q ^ (k.1 * (n - k.1)) * a q (n - k.1)
decreasing_by have := Finset.mem_Icc.mp k.2; omega

/-- The series $\sum_{n \ge 1} a_q(n) x^n / n$ over $\mathbb{Q}$. -/
noncomputable def logSeries (q : ℤ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (a q n : ℚ) / n

/-! ## The recurrence -/

theorem a_zero (q : ℤ) : a q 0 = 1 := by rw [a, ite_eq_left rfl]

theorem a_succ (q : ℤ) (n : ℕ) : a q (n + 1) = ∑ k ∈ Icc 1 (n + 1),
    (-1) ^ (k + 1) * ((n + 1).choose k : ℤ) * q ^ (k * (n + 1 - k)) * a q (n + 1 - k) := by
  rw [a, ite_eq_right (Nat.succ_ne_zero n)]
  exact Finset.sum_attach (Icc 1 (n + 1)) fun k =>
    (-1) ^ (k + 1) * ((n + 1).choose k : ℤ) * q ^ (k * (n + 1 - k)) * a q (n + 1 - k)

/-! ## Step 1: ordered set partitions grouped by block sizes -/

/-- $e(k) = \sum_{i < j} k_i k_j$, the number of pairs in different blocks. -/
def cross {l : ℕ} (k : Fin l → ℕ) : ℕ := ∑ i, ∑ j, if i < j then k i * k j else 0

/-- The weight $Q^{e(k)}$ of a tuple of positive block sizes, and $0$ if some entry is $0$. -/
def weight (Q : ℤ) {l : ℕ} (k : Fin l → ℕ) : ℤ := if ∀ i, 0 < k i then Q ^ cross k else 0

/-- $T_l(N, Q) = \sum_k \binom{N}{k} Q^{e(k)}$ over the tuples of $l$ positive integers with
sum $N$. -/
def blockSum (Q : ℤ) (l N : ℕ) : ℤ :=
  ∑ k ∈ piAntidiag (univ : Finset (Fin l)) N, (Nat.multinomial univ k : ℤ) * weight Q k

theorem cross_cons {l : ℕ} (j : ℕ) (k : Fin l → ℕ) :
    cross (Fin.cons j k : Fin (l + 1) → ℕ) = j * ∑ i, k i + cross k := by
  simp only [cross, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ite_false, Fin.succ_pos,
    ite_true, Fin.succ_lt_succ_iff, Fin.not_lt_zero, zero_add, mul_sum]

theorem weight_cons (Q : ℤ) {l : ℕ} (j : ℕ) (k : Fin l → ℕ) :
    weight Q (Fin.cons j k : Fin (l + 1) → ℕ) =
      if 0 < j then Q ^ (j * ∑ i, k i) * weight Q k else 0 := by
  simp only [weight, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, cross_cons, pow_add]
  by_cases hj : 0 < j <;> by_cases hk : ∀ i, 0 < k i <;> simp [hj, hk]

theorem multinomial_fin_cons {l : ℕ} (j : ℕ) (k : Fin l → ℕ) :
    Nat.multinomial univ (Fin.cons j k : Fin (l + 1) → ℕ) =
      (j + ∑ i, k i).choose j * Nat.multinomial univ k := by
  rw [Fin.univ_succ, Nat.multinomial_cons]
  simp [Nat.multinomial, sum_map, prod_map]

/-- A sum over the tuples in `Fin (l + 1) → ℕ` with sum `N`, split by the first entry. -/
theorem sum_piAntidiag_succ {l : ℕ} (N : ℕ) (f : (Fin (l + 1) → ℕ) → ℤ) :
    ∑ k ∈ piAntidiag univ N, f k =
      ∑ j ∈ range (N + 1), ∑ k ∈ piAntidiag (univ : Finset (Fin l)) (N - j),
        f (Fin.cons j k) := by
  rw [sum_sigma']
  refine sum_bij' (fun k _ => ⟨k 0, Fin.tail k⟩) (fun x _ => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_piAntidiag, mem_univ, imp_true_iff, and_true, Fin.sum_univ_succ] at hk
    simp only [mem_sigma, mem_range, mem_piAntidiag, mem_univ, imp_true_iff, and_true]
    refine ⟨by omega, ?_⟩
    change ∑ i : Fin l, k i.succ = N - k 0
    omega
  · rintro ⟨j, k⟩ hx
    simp only [mem_sigma, mem_range, mem_piAntidiag, mem_univ, imp_true_iff, and_true] at hx
    simp only [mem_piAntidiag, mem_univ, imp_true_iff, and_true, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [show ∑ i : Fin l, k i = N - j from hx.2]
    omega
  · intro k _
    simp
  · intro x _
    simp
  · intro k _
    simp

/-- $T_{l+1}(N, Q) = \sum_{j=1}^{N} \binom{N}{j} Q^{j(N-j)} T_l(N-j, Q)$. -/
theorem blockSum_succ (Q : ℤ) (l N : ℕ) :
    blockSum Q (l + 1) N =
      ∑ j ∈ Icc 1 N, (N.choose j : ℤ) * Q ^ (j * (N - j)) * blockSum Q l (N - j) := by
  rw [blockSum, sum_piAntidiag_succ]
  have hIcc : Icc 1 N = (range (N + 1)).filter (0 < ·) := by
    ext j
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [hIcc, sum_filter]
  refine sum_congr rfl fun j hj => ?_
  have hjN : j ≤ N := by simp only [mem_range] at hj; omega
  split_ifs with h0
  · rw [blockSum, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : ∑ i, k i = N - j := by simpa using (mem_piAntidiag.mp hk).1
    rw [multinomial_fin_cons, weight_cons, ite_eq_left h0, hk', Nat.add_sub_cancel' hjN]
    push_cast
    ring
  · exact sum_eq_zero fun k _ => by rw [weight_cons, ite_eq_right h0, mul_zero]

theorem blockSum_zero_succ (Q : ℤ) (n : ℕ) : blockSum Q 0 (n + 1) = 0 := by
  rw [blockSum, univ_eq_empty, piAntidiag_empty_of_ne_zero (Nat.succ_ne_zero n), sum_empty]

theorem blockSum_zero_zero (Q : ℤ) : blockSum Q 0 0 = 1 := by
  simp [blockSum, weight, cross]

theorem blockSum_succ_zero (Q : ℤ) (l : ℕ) : blockSum Q (l + 1) 0 = 0 := by
  rw [blockSum_succ]
  simp

/-- $a_q(N) = \sum_{l < B} (-1)^{N+l} T_l(N, q)$ for every $B > N$. -/
theorem a_eq_sum (q : ℤ) (N : ℕ) :
    ∀ B, N < B → a q N = ∑ l ∈ range B, (-1) ^ (N + l) * blockSum q l N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro B hB
    obtain ⟨B, rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    rw [sum_range_succ']
    rcases N with _ | n
    · rw [a_zero, blockSum_zero_zero,
        sum_eq_zero fun l _ => by rw [blockSum_succ_zero, mul_zero]]
      simp
    · rw [blockSum_zero_succ, mul_zero, add_zero, a_succ]
      simp only [blockSum_succ, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_Icc.mp hj
      rw [ih (n + 1 - j) (by omega) B (by omega), mul_sum]
      refine sum_congr rfl fun l _ => ?_
      have hs : ((-1 : ℤ)) ^ (n + 1 + (l + 1)) = (-1) ^ (j + 1) * (-1) ^ (n + 1 - j + l) := by
        rw [← pow_add, show j + 1 + (n + 1 - j + l) = n + 1 + (l + 1) by omega]
      rw [hs]
      ring

/-! ## Step 2: the Frobenius step -/

section Frobenius

open AddMonoidAlgebra

variable {l : ℕ}

/-- The monomial $x_i^c$ in the monoid algebra $\mathbb{Z}[\mathbb{N}^l]$. -/
noncomputable def xPow (c : ℕ) (i : Fin l) : AddMonoidAlgebra ℤ (Fin l → ℕ) :=
  single (c • Pi.single i 1) 1

/-- The multinomial theorem: $(\sum_i x_i^c)^M = \sum_k \binom{M}{k} x^{ck}$. -/
theorem sum_xPow_pow (c M : ℕ) :
    (∑ i : Fin l, xPow c i) ^ M = ∑ k ∈ piAntidiag (univ : Finset (Fin l)) M,
      single (c • k) (Nat.multinomial univ k : ℤ) := by
  rw [sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun k _ => ?_
  simp only [xPow, single_pow, one_pow, prod_single, prod_const_one]
  rw [natCast_def, single_mul_single, zero_add, mul_one]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.single_apply, mul_comm]

/-- $(\sum_{i \in s} f_i)^p \equiv \sum_{i \in s} f_i^p \pmod p$. -/
theorem prime_dvd_sum_pow_sub {R ι : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (s : Finset ι)
    (f : ι → R) : (p : R) ∣ (∑ i ∈ s, f i) ^ p - ∑ i ∈ s, f i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_pow hp.ne_zero]
  | insert b s hb ih =>
    rw [sum_insert hb, sum_insert hb]
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (f b) (∑ i ∈ s, f i)
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + f b * (∑ i ∈ s, f i) * r, by rw [hr]; linear_combination ht⟩

/-- $(\sum_i x_i)^{pN} \equiv (\sum_i x_i^p)^N \pmod{p^{v+1}}$ when $p^v \mid N$. -/
theorem pow_dvd_sum_xPow_sub {p : ℕ} (hp : p.Prime) {v N : ℕ} (hv : p ^ v ∣ N) :
    ((p : AddMonoidAlgebra ℤ (Fin l → ℕ))) ^ (v + 1) ∣
      (∑ i : Fin l, xPow 1 i) ^ (p * N) - (∑ i : Fin l, xPow p i) ^ N := by
  have h1 : ∀ i : Fin l, xPow 1 i ^ p = xPow p i := fun i => by
    simp [xPow, single_pow]
  have hfrob := prime_dvd_sum_pow_sub hp univ (xPow (l := l) 1)
  simp only [h1] at hfrob
  have h2 := dvd_sub_pow_of_dvd_sub hfrob v
  obtain ⟨c, rfl⟩ := hv
  rw [pow_mul, pow_mul, pow_mul (∑ i : Fin l, xPow p i)]
  exact h2.trans (sub_dvd_pow_sub_pow _ _ c)

/-- The $\mathbb{Z}$-linear map $x^k \mapsto$ `weight Q k`. -/
noncomputable def evalWeight (Q : ℤ) : AddMonoidAlgebra ℤ (Fin l → ℕ) →+ ℤ :=
  (Finsupp.linearCombination ℤ (weight Q)).toAddMonoidHom.comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem evalWeight_single (Q : ℤ) (k : Fin l → ℕ) (c : ℤ) :
    evalWeight Q (single k c) = c * weight Q k := by
  simp [evalWeight, AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single]

theorem evalWeight_sum_xPow_pow (Q : ℤ) (c M : ℕ) :
    evalWeight Q ((∑ i : Fin l, xPow c i) ^ M) =
      ∑ k ∈ piAntidiag (univ : Finset (Fin l)) M,
        (Nat.multinomial univ k : ℤ) * weight Q (c • k) := by
  rw [sum_xPow_pow, map_sum]
  simp only [evalWeight_single]

theorem cross_smul (p : ℕ) (k : Fin l → ℕ) : cross (p • k) = p ^ 2 * cross k := by
  simp only [cross, mul_sum, Pi.smul_apply, smul_eq_mul]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem weight_smul (Q : ℤ) {p : ℕ} (hp : 0 < p) (k : Fin l → ℕ) :
    weight Q (p • k) = weight (Q ^ (p ^ 2)) k := by
  simp only [weight, cross_smul, Pi.smul_apply, smul_eq_mul, pow_mul,
    Nat.mul_pos_iff_of_pos_left hp]

/-- **Frobenius step.** $T_l(pN, Q) \equiv T_l(N, Q^{p^2}) \pmod{p^{v+1}}$ when
$p^v \mid N$. -/
theorem blockSum_frobenius (Q : ℤ) {p : ℕ} (hp : p.Prime) (l : ℕ) {v N : ℕ} (hv : p ^ v ∣ N) :
    (p : ℤ) ^ (v + 1) ∣ blockSum Q l (p * N) - blockSum (Q ^ (p ^ 2)) l N := by
  obtain ⟨G, hG⟩ := pow_dvd_sum_xPow_sub (l := l) hp hv
  have h := congrArg (evalWeight Q) hG
  rw [map_sub, evalWeight_sum_xPow_pow, evalWeight_sum_xPow_pow, ← Nat.cast_pow,
    ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul] at h
  refine ⟨evalWeight Q G, ?_⟩
  have e1 : blockSum Q l (p * N) = ∑ k ∈ piAntidiag (univ : Finset (Fin l)) (p * N),
      (Nat.multinomial univ k : ℤ) * weight Q (1 • k) := by simp [blockSum]
  have e2 : blockSum (Q ^ (p ^ 2)) l N = ∑ k ∈ piAntidiag (univ : Finset (Fin l)) N,
      (Nat.multinomial univ k : ℤ) * weight Q (p • k) := by
    simp only [blockSum, weight_smul Q hp.pos]
  rw [e1, e2, h]
  push_cast
  ring

end Frobenius

/-! ## Step 3: removing the twist -/

/-- For a tuple $k$ of positive integers with sum $m$ and $p^s \mid m$,
$p^{s+1} \mid \binom{m}{k} (Q^{p^2 e(k)} - Q^{e(k)})$. -/
theorem term_dvd (Q : ℤ) {p : ℕ} (hp : p.Prime) {l s m : ℕ} {k : Fin l → ℕ}
    (hsum : ∑ i, k i = m) (hpos : ∀ i, 0 < k i) (hs : p ^ s ∣ m) :
    (p : ℤ) ^ (s + 1) ∣
      (Nat.multinomial univ k : ℤ) * ((Q ^ (p ^ 2)) ^ cross k - Q ^ cross k) := by
  rcases isEmpty_or_nonempty (Fin l) with hl | hl
  · have : cross k = 0 := by simp [cross]
    simp [this]
  obtain ⟨i, -, hi⟩ := exists_min_image univ (fun i => (k i).factorization p) univ_nonempty
  set g := (k i).factorization p with hg
  have hdvd : ∀ j, p ^ g ∣ k j := fun j =>
    (Nat.pow_dvd_pow p (hi j (mem_univ j))).trans (Nat.ordProj_dvd (k j) p)
  have hcross : p ^ g ∣ cross k := dvd_sum fun i _ => dvd_sum fun j _ => by
    split_ifs
    · exact dvd_mul_of_dvd_left (hdvd i) _
    · exact dvd_zero _
  obtain ⟨e, he⟩ := hcross
  -- the power of `Q`
  have hQ : (p : ℤ) ^ (g + 1) ∣ (Q ^ (p ^ 2)) ^ cross k - Q ^ cross k := by
    have hfermat : (p : ℤ) ∣ (Q ^ e) ^ (p ^ 2) - Q ^ e := by
      have := Fact.mk hp
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [pow_two, pow_mul, ZMod.pow_card, ZMod.pow_card, sub_self]
    have h := dvd_sub_pow_of_dvd_sub hfermat g
    rw [he]
    convert h using 2 <;> ring
  -- the multinomial coefficient
  have hki : k i ≠ 0 := (hpos i).ne'
  have hu : ¬p ∣ k i / p ^ g := Nat.not_dvd_ordCompl hp hki
  have hku : p ^ g * (k i / p ^ g) = k i := Nat.ordProj_mul_ordCompl_eq_self (k i) p
  have hmult : Nat.multinomial univ k = m.choose (k i) * Nat.multinomial (univ.erase i) k := by
    rw [← insert_erase (mem_univ i), Nat.multinomial_insert (notMem_erase i univ),
      add_sum_erase _ _ (mem_univ i), hsum, insert_erase (mem_univ i)]
  have hchoose : k i * m.choose (k i) = m * (m - 1).choose (k i - 1) := by
    have hkm : k i ≤ m := hsum ▸ single_le_sum (fun j _ => Nat.zero_le (k j)) (mem_univ i)
    obtain ⟨M, hM⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, k i = j + 1 := ⟨k i - 1, by omega⟩
    rw [hM, hj, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.add_one_mul_choose_eq]
    ring
  have hm : p ^ s ∣ k i / p ^ g * (p ^ g * m.choose (k i)) := by
    have : k i / p ^ g * (p ^ g * m.choose (k i)) = m * (m - 1).choose (k i - 1) := by
      rw [← hchoose]
      calc k i / p ^ g * (p ^ g * m.choose (k i)) = (p ^ g * (k i / p ^ g)) * m.choose (k i) := by
            ring
        _ = k i * m.choose (k i) := by rw [hku]
    rw [this]
    exact hs.trans (dvd_mul_right _ _)
  have hcop : Nat.Coprime (p ^ s) (k i / p ^ g) :=
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
  have h1 : p ^ s ∣ p ^ g * Nat.multinomial univ k := by
    have := hcop.dvd_of_dvd_mul_left hm
    rw [hmult, ← mul_assoc]
    exact this.trans (dvd_mul_right _ _)
  obtain ⟨D, hD⟩ := hQ
  rw [hD, pow_succ]
  have h1' : (p : ℤ) ^ s ∣ (p : ℤ) ^ g * (Nat.multinomial univ k : ℤ) := by exact_mod_cast h1
  have : (Nat.multinomial univ k : ℤ) * ((p : ℤ) ^ (g + 1) * D) =
      ((p : ℤ) ^ g * (Nat.multinomial univ k : ℤ)) * ((p : ℤ) * D) := by ring
  rw [this]
  exact mul_dvd_mul h1' (dvd_mul_right _ _)

/-- $T_l(m, Q^{p^2}) \equiv T_l(m, Q) \pmod{p^{s+1}}$ when $p^s \mid m$. -/
theorem blockSum_twist (Q : ℤ) {p : ℕ} (hp : p.Prime) (l : ℕ) {s m : ℕ} (hs : p ^ s ∣ m) :
    (p : ℤ) ^ (s + 1) ∣ blockSum (Q ^ (p ^ 2)) l m - blockSum Q l m := by
  rw [blockSum, blockSum, ← sum_sub_distrib]
  refine dvd_sum fun k hk => ?_
  rw [← mul_sub]
  have hsum : ∑ i, k i = m := by simpa using (mem_piAntidiag.mp hk).1
  unfold weight
  split_ifs with hpos
  · exact term_dvd Q hp hsum hpos hs
  · simp

/-! ## Step 4: the Gauss congruences -/

/-- $a_q(pN) \equiv a_q(N) \pmod{p^{v+1}}$ when $p^v \mid N$. -/
theorem a_dvd (q : ℤ) {p : ℕ} (hp : p.Prime) {v N : ℕ} (hv : p ^ v ∣ N) :
    (p : ℤ) ^ (v + 1) ∣ a q (p * N) - a q N := by
  rw [a_eq_sum q (p * N) (p * N + N + 1) (by omega), a_eq_sum q N (p * N + N + 1) (by omega),
    ← sum_sub_distrib]
  have hterm : ∀ l, (p : ℤ) ^ (v + 1) ∣ blockSum q l (p * N) - blockSum q l N := fun l => by
    have := dvd_add (blockSum_frobenius q hp l hv) (blockSum_twist q hp l hv)
    rwa [sub_add_sub_cancel] at this
  set ε : ℤ := (-1) ^ ((p + 1) * N) with hε
  have hsign : ∀ l, ((-1 : ℤ)) ^ (p * N + l) = ε * (-1) ^ (N + l) := fun l => by
    have h2 : (-1 : ℤ) ^ ((p * N + l) + 2 * N) = (-1) ^ (p * N + l) := by
      rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
    rw [hε, ← pow_add, show (p + 1) * N + (N + l) = (p * N + l) + 2 * N by ring, h2]
  have hε1 : (p : ℤ) ^ (v + 1) ∣ ε - 1 := by
    rcases Nat.even_or_odd ((p + 1) * N) with he | ho
    · rw [hε, he.neg_one_pow, sub_self]
      exact dvd_zero _
    · obtain ⟨hp1, hN⟩ := Nat.odd_mul.mp ho
      have hp2 : p = 2 := (hp.even_iff).mp (by simpa [Nat.odd_add_one] using hp1)
      have hv0 : v = 0 := by
        by_contra hv0
        have : 2 ∣ N := (dvd_pow_self 2 hv0).trans (hp2 ▸ hv)
        exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr this)
      rw [hε, ho.neg_one_pow, hv0, hp2]
      norm_num
  refine dvd_sum fun l _ => ?_
  have : (-1 : ℤ) ^ (p * N + l) * blockSum q l (p * N) - (-1) ^ (N + l) * blockSum q l N =
      (-1) ^ (p * N + l) * (blockSum q l (p * N) - blockSum q l N) +
        (ε - 1) * ((-1) ^ (N + l) * blockSum q l N) := by
    rw [hsign]
    ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right (hterm l) _) (dvd_mul_of_dvd_left hε1 _)

/-- **Gauss congruences.** For every integer $q$, every prime $p$ and all $n, r \ge 1$,
$a_q(n p^r) \equiv a_q(n p^{r-1}) \pmod{p^r}$. -/
theorem gauss_congruence (q : ℤ) {p : ℕ} (hp : p.Prime) {n r : ℕ} (_hn : 0 < n) (hr : 0 < r) :
    a q (n * p ^ r) ≡ a q (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ r] := by
  obtain ⟨v, rfl⟩ : ∃ v, r = v + 1 := ⟨r - 1, by omega⟩
  have h := a_dvd q hp (v := v) (N := n * p ^ v) (dvd_mul_left _ _)
  rw [show p * (n * p ^ v) = n * p ^ (v + 1) by ring] at h
  rw [Nat.add_sub_cancel]
  exact (Int.modEq_iff_dvd.mpr h).symm

/-! ## Step 5: Dold's criterion

This section is copied from the package `FCPalomar/OeisA181316` (Apache-2.0, Wentao Li), which
adapts the package `FCPalomar/A158110`. -/

section LogDeriv

/-- Two series with equal constant terms whose logarithmic derivatives agree below degree `N`
agree up to degree `N`. -/
theorem coeff_eq_of_derivative_eq_mul {F G f g : ℚ⟦X⟧} (hF : d⁄dX F = f * F)
    (hG : d⁄dX G = g * G) (h0 : constantCoeff F = constantCoeff G) {N : ℕ}
    (hfg : ∀ i < N, coeff i f = coeff i g) : ∀ i ≤ N, coeff i F = coeff i G := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | j
    · simpa using h0
    · have e1 := congrArg (coeff j) hF
      have e2 := congrArg (coeff j) hG
      rw [coeff_derivative, coeff_mul] at e1 e2
      have hsum : ∑ x ∈ antidiagonal j, coeff x.1 f * coeff x.2 F =
          ∑ x ∈ antidiagonal j, coeff x.1 g * coeff x.2 G := by
        refine sum_congr rfl fun x hx => ?_
        have hx' := mem_antidiagonal.mp hx
        rw [hfg x.1 (by omega), ih x.2 (by omega) (by omega)]
      have hne : (j : ℚ) + 1 ≠ 0 := by positivity
      exact mul_right_cancel₀ hne (e1.trans (hsum.trans e2.symm))

theorem derivative_mul_of {F G f g : ℚ⟦X⟧} (hF : d⁄dX F = f * F)
    (hG : d⁄dX G = g * G) : d⁄dX (F * G) = (f + g) * (F * G) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hF, hG]
  ring

theorem derivative_pow_of {F f : ℚ⟦X⟧} (hF : d⁄dX F = f * F) (n : ℕ) :
    d⁄dX (F ^ n) = (n * f) * F ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, derivative_mul_of ih hF]
    push_cast
    ring

theorem derivative_prod_of {ι : Type*} (s : Finset ι) {F f : ι → ℚ⟦X⟧}
    (hF : ∀ i ∈ s, d⁄dX (F i) = f i * F i) :
    d⁄dX (∏ i ∈ s, F i) = (∑ i ∈ s, f i) * ∏ i ∈ s, F i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact derivative_mul_of (hF a (mem_insert_self a s))
      (ih fun i hi => hF i (mem_insert_of_mem hi))

/-- The chain rule for $\exp \circ L$. -/
theorem derivative_exp_subst {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) :
    d⁄dX (subst L (exp ℚ)) = d⁄dX L * subst L (exp ℚ) := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hL), derivative_exp, mul_comm]

theorem constantCoeff_exp_subst {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) :
    constantCoeff (subst L (exp ℚ)) = 1 := by
  have ha := HasSubst.of_constantCoeff_zero' hL
  have h1 : subst L (exp ℚ) = subst L (exp ℚ - 1) + 1 := by
    rw [← coe_substAlgHom ha, map_sub, map_one, sub_add_cancel]
  have h2 : constantCoeff (subst L (exp ℚ - 1)) = 0 :=
    constantCoeff_subst_eq_zero hL _ (by simp)
  rw [h1, map_add, map_one, h2, zero_add]

end LogDeriv

/-! ## Finite Euler products -/

section EulerProduct

/-- The power series over `ℚ` with integer coefficients. -/
noncomputable abbrev intSeries : Subring ℚ⟦X⟧ := (map (Int.castRingHom ℚ)).range

/-- The series $1 / (1 - x^d) = \sum_{k \ge 0} x^{dk}$. -/
noncomputable def geom (d : ℕ) : ℚ⟦X⟧ := mk fun n => if d ∣ n then 1 else 0

/-- The logarithmic derivative $d x^{d-1} / (1 - x^d)$ of $1 / (1 - x^d)$. -/
noncomputable def geomLogDeriv (d : ℕ) : ℚ⟦X⟧ := (d : ℚ⟦X⟧) * X ^ (d - 1) * geom d

/-- The factor $(1 - x^d)^{-c}$, written with natural exponents. -/
noncomputable def factor (d : ℕ) (c : ℤ) : ℚ⟦X⟧ := geom d ^ c.toNat * (1 - X ^ d) ^ (-c).toNat

/-- The finite product $\prod_{d=1}^{N} (1 - x^d)^{-c(d)}$. -/
noncomputable def eulerProduct (c : ℕ → ℤ) (N : ℕ) : ℚ⟦X⟧ := ∏ d ∈ Icc 1 N, factor d (c d)

theorem geom_mul_one_sub {d : ℕ} (hd : 0 < d) : geom d * (1 - X ^ d) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one, geom, coeff_mk, coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.not_le.mpr hd]
  · rcases le_or_gt d n with h | h
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
      simp [Nat.dvd_add_right (dvd_refl d), hd.ne']
    · have hnd : ¬d ∣ n := fun hdn => absurd (Nat.le_of_dvd hn hdn) (by omega)
      simp [hnd, Nat.not_le.mpr h, hn.ne']

theorem derivative_one_sub_X_pow {d : ℕ} (hd : 0 < d) :
    d⁄dX (1 - X ^ d) = -geomLogDeriv d * (1 - X ^ d) := by
  have h := geom_mul_one_sub hd
  rw [map_sub, derivative_one, derivative_pow, derivative_X, geomLogDeriv]
  linear_combination ((d : ℚ⟦X⟧) * X ^ (d - 1)) * h

theorem derivative_geom {d : ℕ} (hd : 0 < d) :
    d⁄dX (geom d) = geomLogDeriv d * geom d := by
  have h := geom_mul_one_sub hd
  have h' := congrArg (d⁄dX) h
  rw [Derivation.leibniz, derivative_one_sub_X_pow hd, derivative_one, smul_eq_mul,
    smul_eq_mul] at h'
  linear_combination geom d * h' - (d⁄dX (geom d) - geomLogDeriv d * geom d) * h

theorem derivative_factor {d : ℕ} (hd : 0 < d) (c : ℤ) :
    d⁄dX (factor d c) = ((c : ℚ⟦X⟧) * geomLogDeriv d) * factor d c := by
  rw [factor, derivative_mul_of (derivative_pow_of (derivative_geom hd) _)
    (derivative_pow_of (derivative_one_sub_X_pow hd) _)]
  have key : ((c.toNat : ℤ) : ℚ⟦X⟧) - (((-c).toNat : ℤ) : ℚ⟦X⟧) = (c : ℚ⟦X⟧) := by
    rw [← Int.cast_sub, Int.toNat_sub_toNat_neg]
  simp only [Int.cast_natCast] at key
  rw [← key]
  ring

theorem derivative_eulerProduct (c : ℕ → ℤ) (N : ℕ) :
    d⁄dX (eulerProduct c N) =
      (∑ d ∈ Icc 1 N, (c d : ℚ⟦X⟧) * geomLogDeriv d) * eulerProduct c N :=
  derivative_prod_of _ fun d hd => derivative_factor (mem_Icc.mp hd).1 (c d)

theorem constantCoeff_eulerProduct (c : ℕ → ℤ) (N : ℕ) :
    constantCoeff (eulerProduct c N) = 1 := by
  rw [eulerProduct, map_prod]
  refine prod_eq_one fun d hd => ?_
  have hd0 : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
  rw [factor, map_mul, map_pow, map_pow, ← coeff_zero_eq_constantCoeff_apply, geom, coeff_mk]
  simp [hd0]

theorem geom_mem (d : ℕ) : geom d ∈ intSeries :=
  ⟨mk fun n => if d ∣ n then 1 else 0, by
    ext n
    simp only [coeff_map, coeff_mk, geom]
    split_ifs <;> simp⟩

theorem one_sub_X_pow_mem (d : ℕ) : (1 - X ^ d : ℚ⟦X⟧) ∈ intSeries :=
  Subring.sub_mem _ (Subring.one_mem _) (Subring.pow_mem _ (RingHom.mem_range.mpr ⟨X, map_X _⟩) d)

theorem eulerProduct_mem (c : ℕ → ℤ) (N : ℕ) : eulerProduct c N ∈ intSeries :=
  Subring.prod_mem _ fun d _ => Subring.mul_mem _ (Subring.pow_mem _ (geom_mem d) _)
    (Subring.pow_mem _ (one_sub_X_pow_mem d) _)

theorem coeff_geomLogDeriv {d : ℕ} (hd : 0 < d) (j : ℕ) :
    coeff j (geomLogDeriv d) = if d ∣ j + 1 then (d : ℚ) else 0 := by
  rw [geomLogDeriv, mul_assoc, ← map_natCast (C (R := ℚ)) d, coeff_C_mul, coeff_X_pow_mul',
    geom]
  rcases le_or_gt d (j + 1) with h | h
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
    have hj : j - (d - 1) = t := by omega
    rw [ite_eq_left (by omega), coeff_mk, hj, ht]
    by_cases hdt : d ∣ t
    · simp [hdt, Nat.dvd_add_right (dvd_refl d)]
    · simp [hdt, Nat.dvd_add_right (dvd_refl d)]
  · have hnd : ¬d ∣ j + 1 := fun hdj => absurd (Nat.le_of_dvd (by omega) hdj) (by omega)
    rw [ite_eq_right (by omega), ite_eq_right hnd, mul_zero]

theorem coeff_logDeriv_eulerProduct (c : ℕ → ℤ) {N j : ℕ} (hj : j < N) :
    coeff j (∑ d ∈ Icc 1 N, (c d : ℚ⟦X⟧) * geomLogDeriv d) =
      ∑ d ∈ (j + 1).divisors, (d : ℚ) * c d := by
  rw [map_sum]
  have hfilter : (Icc 1 N).filter (· ∣ j + 1) = (j + 1).divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨h, by omega⟩
    · rintro ⟨h, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hj⟩, h⟩
  rw [← hfilter, sum_filter]
  refine sum_congr rfl fun d hd => ?_
  rw [← map_intCast (C (R := ℚ)), coeff_C_mul, coeff_geomLogDeriv (mem_Icc.mp hd).1 j]
  split_ifs <;> ring

end EulerProduct

/-! ## The integrality criterion (from `FCPalomar/A158110`) -/

/-- If $n \mid \sum_{d \mid n} \mu(d) b(n/d)$ for all $n \ge 1$, then
$\exp\left(\sum_{n \ge 1} b(n) x^n / n\right)$ has integer coefficients. -/
theorem exists_coeff_eq_intCast_of_dvd (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * b x.2) (N : ℕ) :
    ∃ z : ℤ, coeff N (subst (mk fun n => if n = 0 then 0 else (b n : ℚ) / n) (exp ℚ)) = z := by
  set L : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else (b n : ℚ) / n with hLdef
  set c : ℕ → ℤ := fun n : ℕ => (∑ x ∈ n.divisorsAntidiagonal, μ x.1 * b x.2) / (n : ℤ)
    with hc
  have hinv : ∀ n : ℕ, 0 < n → ∑ i ∈ n.divisors, (i : ℤ) * c i = b n := by
    refine ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr fun n hn => ?_
    simp only [Int.cast_id, hc]
    exact (Int.mul_ediv_cancel' (hb n hn)).symm
  have hL0 : constantCoeff L = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hLdef, coeff_mk, ite_eq_left rfl]
  have heq := coeff_eq_of_derivative_eq_mul (derivative_exp_subst hL0)
    (derivative_eulerProduct c N)
    (by rw [constantCoeff_exp_subst hL0, constantCoeff_eulerProduct]) (N := N)
    (fun i hi => by
      rw [coeff_derivative, coeff_logDeriv_eulerProduct c hi, hLdef, coeff_mk,
        ite_eq_right (by omega)]
      have h := hinv (i + 1) (by omega)
      have h' : ∑ d ∈ (i + 1).divisors, (d : ℚ) * c d = b (i + 1) := by exact_mod_cast h
      rw [h']
      field_simp
      push_cast
      ring) N le_rfl
  obtain ⟨G, hG⟩ := RingHom.mem_range.mp (eulerProduct_mem c N)
  exact ⟨coeff N G, by rw [heq, ← hG, coeff_map]; simp⟩

theorem sum_divisors_prime_pow_mul {p k N : ℕ} (hp : p.Prime) (hN : ¬p ∣ N) (F : ℕ → ℤ) :
    ∑ d ∈ (p ^ k * N).divisors, F d =
      ∑ i ∈ range (k + 1), ∑ e ∈ N.divisors, F (p ^ i * e) := by
  have hcop : (p ^ k).Coprime N :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hN)
  rw [Nat.divisors_mul, Finset.mul_def, sum_image hcop.mul_injOn_divisors, sum_product]
  simp only [Nat.sum_divisors_prime_pow hp]

/-! ## Gauss sequences

The Möbius pairing is adapted from `prime_pow_dvd_sum_moebius` and `dvd_sum_moebius` in
`FCPalomar/A158110`, with a general Gauss sequence in place of $q^{n^m}$. -/

/-- The Gauss congruences $b(pM) \equiv b(M) \pmod{p^k}$ whenever $p^k \mid pM$. -/
def Gauss (b : ℕ → ℤ) : Prop :=
  ∀ p k M : ℕ, p.Prime → p ^ k ∣ p * M → (p : ℤ) ^ k ∣ b (p * M) - b M

/-- Under the Gauss congruences, $p^k$ divides the Möbius sum at $p^k N$ when $p \nmid N$. -/
theorem prime_pow_dvd_sum_moebius {b : ℕ → ℤ} (hb : Gauss b) {p : ℕ} (hp : p.Prime) {k N : ℕ}
    (hk : 0 < k) (hN : ¬p ∣ N) :
    (p : ℤ) ^ k ∣ ∑ x ∈ (p ^ k * N).divisorsAntidiagonal, μ x.1 * b x.2 := by
  rw [Nat.sum_divisorsAntidiagonal (fun a c => μ a * b c),
    sum_divisors_prime_pow_mul hp hN, sum_comm]
  refine dvd_sum fun e he => ?_
  have hed : e ∣ N := (Nat.mem_divisors.mp he).1
  have hN0 : N ≠ 0 := (Nat.mem_divisors.mp he).2
  have hce : ∀ i, (p ^ i).Coprime e := fun i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hN (h.trans hed))
  have he0 : e ≠ 0 := fun h => hN0 (Nat.eq_zero_of_zero_dvd (h ▸ hed))
  obtain ⟨M, rfl⟩ := hed
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hmu : ∀ i, μ (p ^ i * e) = μ (p ^ i) * μ e := fun i =>
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hce i)
  rw [sum_range_succ', sum_range_succ', sum_eq_zero fun i _ => ?_]
  · have q0 : p ^ (j + 1) * (e * M) / (p ^ 0 * e) = p ^ (j + 1) * M := by
      rw [pow_zero, one_mul, show p ^ (j + 1) * (e * M) = e * (p ^ (j + 1) * M) by ring,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)]
    have q1 : p ^ (j + 1) * (e * M) / (p ^ (0 + 1) * e) = p ^ j * M := by
      rw [zero_add, pow_one,
        show p ^ (j + 1) * (e * M) = (p * e) * (p ^ j * M) by ring,
        Nat.mul_div_cancel_left _ (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero he0))]
    rw [q0, q1, hmu, hmu, pow_zero, ArithmeticFunction.moebius_apply_one, zero_add, pow_one,
      ArithmeticFunction.moebius_apply_prime hp]
    have ht := hb p (j + 1) (p ^ j * M) hp ⟨M, by ring⟩
    rw [show p * (p ^ j * M) = p ^ (j + 1) * M by ring] at ht
    obtain ⟨t, ht⟩ := ht
    exact ⟨μ e * t, by linear_combination (μ e) * ht⟩
  · rw [hmu, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
    simp

/-- Dold's congruence $n \mid \sum_{d \mid n} \mu(d) b(n/d)$ for a Gauss sequence. -/
theorem dvd_sum_moebius {b : ℕ → ℤ} (hb : Gauss b) {n : ℕ} (hn : 0 < n) :
    (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * b x.2 := by
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hv : k ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn.ne').mp hpk
  have hdecomp := Nat.ordProj_mul_ordCompl_eq_self n p
  have hdiv := prime_pow_dvd_sum_moebius hb hp (k := n.factorization p) (by omega)
    (Nat.not_dvd_ordCompl hp hn.ne')
  rw [hdecomp] at hdiv
  rw [← Int.natCast_dvd]
  push_cast
  exact (pow_dvd_pow _ hv).trans hdiv

/-- The series $\sum_{n \ge 1} b(n) x^n / n$ over $\mathbb{Q}$. -/
noncomputable def ofInt (b : ℕ → ℤ) : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else (b n : ℚ) / n

/-- **Dold's criterion, (⇐).** For a Gauss sequence $b$,
$\exp\left(\sum_{n \ge 1} b(n) x^n / n\right)$ has integer coefficients. -/
theorem exists_coeff_eq_intCast_of_gauss {b : ℕ → ℤ} (hb : Gauss b) (N : ℕ) :
    ∃ z : ℤ, coeff N (subst (ofInt b) (exp ℚ)) = z :=
  exists_coeff_eq_intCast_of_dvd b (fun _ hn => dvd_sum_moebius hb hn) N

theorem constantCoeff_ofInt (b : ℕ → ℤ) : constantCoeff (ofInt b) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ofInt, coeff_mk, ite_eq_left rfl]

theorem coeff_derivative_ofInt (b : ℕ → ℤ) (j : ℕ) :
    coeff j (d⁄dX (ofInt b)) = b (j + 1) := by
  rw [coeff_derivative, ofInt, coeff_mk, ite_eq_right (Nat.succ_ne_zero j)]
  field_simp
  push_cast
  ring

/-! ## Corollary 2 -/

/-- $a_q$ is a Gauss sequence. -/
theorem gauss_a (q : ℤ) : Gauss (a q) := by
  intro p k M hp hk
  rcases k with _ | v
  · simp
  have hv : p ^ v ∣ M := by
    rw [pow_succ'] at hk
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos hk
  exact a_dvd q hp hv

theorem logSeries_eq_ofInt (q : ℤ) : logSeries q = ofInt (a q) := rfl

/-- **Integrality for every $q$.** For every integer $q$,
$\exp\left(\sum_{n \ge 1} a_q(n) x^n / n\right)$ has integer coefficients. -/
theorem exp_integral (q : ℤ) (n : ℕ) : ∃ z : ℤ, coeff n (subst (logSeries q) (exp ℚ)) = z := by
  rw [logSeries_eq_ofInt]
  exact exists_coeff_eq_intCast_of_gauss (gauss_a q) n

/-- **Bala's conjecture in A003024** ($q = 2$): the series
$\exp\left(\sum_{n \ge 1} \mathrm{A003024}(n) x^n / n\right) = 1 + x + 2x^2 + 10x^3 + \dots$
has integer coefficients. Its coefficients are the terms of A188490, so every term of A188490
is an integer. -/
theorem a003024_exp_integral (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (logSeries 2) (exp ℚ)) = z := by
  exact exp_integral 2 n

/-- **Bala's conjecture in A188457** ($q = 3$): the series
$\exp\left(\sum_{n \ge 1} \mathrm{A188457}(n) x^n / n\right) = 1 + x + 3x^2 + 39x^3 + \dots$
has integer coefficients. -/
theorem a188457_exp_integral (n : ℕ) :
    ∃ z : ℤ, coeff n (subst (logSeries 3) (exp ℚ)) = z := by
  exact exp_integral 3 n

/-! ## Sanity checks -/

/-- The coefficients $a(n)$ satisfy $(n+1)\,a(n+1) = \sum_{i+j=n} b(i+1)\,a(j)$. -/
theorem coeff_succ_mul (b : ℕ → ℤ) (n : ℕ) :
    coeff (n + 1) (subst (ofInt b) (exp ℚ)) * (n + 1) =
      ∑ x ∈ antidiagonal n, (b (x.1 + 1) : ℚ) * coeff x.2 (subst (ofInt b) (exp ℚ)) := by
  have h := congrArg (coeff n) (derivative_exp_subst (constantCoeff_ofInt b))
  rw [coeff_derivative, coeff_mul] at h
  simpa only [coeff_derivative_ofInt] using h

theorem coeff_zero_exp_subst_ofInt (b : ℕ → ℤ) :
    coeff 0 (subst (ofInt b) (exp ℚ)) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_exp_subst (constantCoeff_ofInt b)]

theorem coeff_one_two_three (b : ℕ → ℤ) :
    coeff 1 (subst (ofInt b) (exp ℚ)) = b 1 ∧
      coeff 2 (subst (ofInt b) (exp ℚ)) * 2 = b 1 * coeff 1 (subst (ofInt b) (exp ℚ)) + b 2 ∧
      coeff 3 (subst (ofInt b) (exp ℚ)) * 3 = b 1 * coeff 2 (subst (ofInt b) (exp ℚ)) +
        b 2 * coeff 1 (subst (ofInt b) (exp ℚ)) + b 3 := by
  have h0 := coeff_zero_exp_subst_ofInt b
  have h1 := coeff_succ_mul b 0
  have h2 := coeff_succ_mul b 1
  have h3 := coeff_succ_mul b 2
  simp only [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, sum_singleton,
    h0] at h1 h2 h3
  push_cast at h1 h2 h3
  exact ⟨by linear_combination h1, by linear_combination h2, by linear_combination h3⟩

/-- The first terms $1, 1, 3, 25, 543$ of A003024. -/
theorem a_two_first_terms :
    a 2 0 = 1 ∧ a 2 1 = 1 ∧ a 2 2 = 3 ∧ a 2 3 = 25 ∧ a 2 4 = 543 := by
  have h1 : a 2 1 = 1 := by rw [a_succ]; simp [a_zero]
  have h2 : a 2 2 = 3 := by rw [a_succ]; simp [sum_Icc_succ_top, a_zero, h1]
  have h3 : a 2 3 = 25 := by rw [a_succ]; simp [sum_Icc_succ_top, a_zero, h1, h2]
  have h4 : a 2 4 = 543 := by
    rw [a_succ]
    simp [sum_Icc_succ_top, a_zero, h1, h2, h3, Nat.choose_two_right]
  exact ⟨a_zero 2, h1, h2, h3, h4⟩

/-- The first terms $1, 1, 5, 109, 9449$ of A188457. -/
theorem a_three_first_terms :
    a 3 0 = 1 ∧ a 3 1 = 1 ∧ a 3 2 = 5 ∧ a 3 3 = 109 ∧ a 3 4 = 9449 := by
  have h1 : a 3 1 = 1 := by rw [a_succ]; simp [a_zero]
  have h2 : a 3 2 = 5 := by rw [a_succ]; simp [sum_Icc_succ_top, a_zero, h1]
  have h3 : a 3 3 = 109 := by rw [a_succ]; simp [sum_Icc_succ_top, a_zero, h1, h2]
  have h4 : a 3 4 = 9449 := by
    rw [a_succ]
    simp [sum_Icc_succ_top, a_zero, h1, h2, h3, Nat.choose_two_right]
  exact ⟨a_zero 3, h1, h2, h3, h4⟩

/-- The first terms $1, 1, 2, 10$ of A188490, Bala's expansion for A003024. -/
theorem a188490_first_terms :
    coeff 1 (subst (logSeries 2) (exp ℚ)) = 1 ∧ coeff 2 (subst (logSeries 2) (exp ℚ)) = 2 ∧
      coeff 3 (subst (logSeries 2) (exp ℚ)) = 10 := by
  obtain ⟨-, h1, h2, h3, -⟩ := a_two_first_terms
  obtain ⟨e1, e2, e3⟩ := coeff_one_two_three (a 2)
  rw [← logSeries_eq_ofInt] at e1 e2 e3
  generalize subst (logSeries 2) (exp ℚ) = G at e1 e2 e3 ⊢
  rw [h1, h2, h3] at *
  norm_num at e1 e2 e3
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The first terms $1, 1, 3, 39$ of Bala's expansion for A188457. -/
theorem a188457_exp_first_terms :
    coeff 1 (subst (logSeries 3) (exp ℚ)) = 1 ∧ coeff 2 (subst (logSeries 3) (exp ℚ)) = 3 ∧
      coeff 3 (subst (logSeries 3) (exp ℚ)) = 39 := by
  obtain ⟨-, h1, h2, h3, -⟩ := a_three_first_terms
  obtain ⟨e1, e2, e3⟩ := coeff_one_two_three (a 3)
  rw [← logSeries_eq_ofInt] at e1 e2 e3
  generalize subst (logSeries 3) (exp ℚ) = G at e1 e2 e3 ⊢
  rw [h1, h2, h3] at *
  norm_num at e1 e2 e3
  exact ⟨by linarith, by linarith, by linarith⟩

end OeisA003024

end
