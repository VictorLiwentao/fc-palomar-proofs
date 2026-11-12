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
# Erdős Problem 1186: positive density of monochromatic progressions

For every $k \ge 2$, every $2$-colouring of $\{1, \dots, n\}$ has at least $c_k n^2$
monochromatic $k$-term arithmetic progressions for large $n$, so $\delta_k > 0$.

The definitions `monoCount`, `minMonoCount` and `δ` are copied verbatim from
`FormalConjectures/ErdosProblems/1186.lean` (Copyright 2026 The Formal Conjectures Authors,
Apache 2.0) at upstream commit `7bdc4a42f24c0316f81c73b26121794b2bed96a3`, in the namespace
`Erdos1186VdW` instead of `Erdos1186`. The theorem `van_der_waerden` is the statement of
`erdos_1186.variants.van_der_waerden` there.

*References:* [erdosproblems.com/1186](https://www.erdosproblems.com/1186);
P. Erdős, "A survey of problems in combinatorial number theory", *Ann. Discrete Math.* (1980),
89--115.

## Proof

* Van der Waerden's theorem with a bound (`exists_ap_bound`): there is `W` such that every
  $2$-colouring of $\{0, \dots, W - 1\}$ has a monochromatic progression
  $s, s + t, \dots, s + (k - 1)t$ with $t \ge 1$. Apply the Hales–Jewett theorem
  (`Combinatorics.Line.exists_mono_in_high_dimension`) to the colouring $v \mapsto c(\sum_i v_i)$
  of $\{0, \dots, k - 1\}^\iota$. A combinatorial line maps to a $k$-term progression whose
  difference is the number of active coordinates.
* Averaging (`mul_le_monoCount`): let $M = \lfloor n / 2W \rfloor$. Each of the $M^2$
  progressions $a + jD$ ($j < W$, $1 \le a, D \le M$) lies in $\{1, \dots, n\}$ and contains a
  monochromatic $k$-term progression. That progression and its position $(s, t)$ determine
  $(a, D)$. Hence $M^2 \le W^2 \cdot \mathrm{monoCount}$, and the quotient
  $\mathrm{minMonoCount}(k, n) / n^2$ is at least $1/(16 W^4)$ for $n \ge 4W$.
-/

@[expose] public section

namespace Erdos1186

open Filter

/--
`monoCount k n c` is the number of monochromatic $k$-term arithmetic progressions in
$\{1,\ldots,n\}$ under the $2$-colouring `c`. The progression $a, a+d, \ldots, a+(k-1)d$ with first
term $a$ and common difference $d \geq 1$ is the pair `(a, d)`, with $a \geq 1$ and
$a + (k-1)d \leq n$. Each progression is counted once.

This is the count of [Er80, p. 93]: there are $\sim n^2/(2(k-1))$ progressions, and the upper bound
in (7) there is their number times the probability $2^{1-k}$ that a random colouring makes one of
them monochromatic. The definition is meant for $k \geq 2$.
-/
def monoCount (k n : ℕ) (c : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ =>
    p.1 + (k - 1) * p.2 ≤ n ∧ ∀ i < k, c (p.1 + i * p.2) = c p.1).card

/--
`minMonoCount k n` is the least number of monochromatic $k$-term arithmetic progressions in a
$2$-colouring of $\{1,\ldots,n\}$. This is $A(n;k)$ in [Er80, p. 93]. The set of values contains
`monoCount k n (fun _ => true)`, so `sInf` is a true minimum.
-/
noncomputable def minMonoCount (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ c : ℕ → Bool, monoCount k n c = m}

/--
`δ k` is the largest constant $\delta_k$ such that every $2$-colouring of $\{1,\ldots,n\}$ has at
least $(\delta_k - o(1))n^2$ monochromatic $k$-term arithmetic progressions, that is,
$\liminf_{n\to\infty} A(n;k)/n^2$.

The quotient `minMonoCount k n / n ^ 2` lies in $[0,1]$, so this `liminf` is not a junk value.
Convergence of the quotient is not assumed. If it converges, `δ k` is its limit.
-/
noncomputable def δ (k : ℕ) : ℝ :=
  atTop.liminf (fun n : ℕ ↦ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2)

/-! ### Van der Waerden's theorem with a bound -/

/-- A coordinate of a combinatorial line, read as a natural number. -/
lemma val_getD {k : ℕ} (o : Option (Fin (k + 1))) (x : Fin (k + 1)) :
    ((o.getD x : Fin (k + 1)) : ℕ) = ((o.getD 0 : Fin (k + 1)) : ℕ) + if o = none then (x : ℕ) else 0 := by
  cases o <;> simp

/-- **Van der Waerden's theorem** for two colours, with a bound `W` on the progression. -/
theorem exists_ap_bound (k : ℕ) : ∃ W : ℕ, ∀ c : ℕ → Bool,
    ∃ s t : ℕ, 0 < t ∧ s + k * t < W ∧ ∀ i ≤ k, c (s + i * t) = c s := by
  obtain ⟨ι, _, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin (k + 1)) Bool
  refine ⟨k * Fintype.card ι + 1, fun c => ?_⟩
  obtain ⟨l, b, hl⟩ := hι fun v => c (∑ i, (v i : ℕ))
  have hl' : ∀ x, c (∑ i, ((l x i : Fin (k + 1)) : ℕ)) = b := hl
  let s := ∑ i, ((l.idxFun i).getD 0 : ℕ)
  let t := (Finset.univ.filter fun i => l.idxFun i = none).card
  have hsum : ∀ x : Fin (k + 1), ∑ i, ((l x i : Fin (k + 1)) : ℕ) = s + x * t := by
    intro x
    simp only [Combinatorics.Line.coe_apply]
    rw [Finset.sum_congr rfl fun i _ => val_getD (l.idxFun i) x, Finset.sum_add_distrib]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]
  have ht : 0 < t := by
    obtain ⟨i, hi⟩ := l.proper
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hbound : s + k * t ≤ k * Fintype.card ι := by
    have h := hsum (Fin.last k)
    rw [Fin.val_last] at h
    rw [← h, mul_comm, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (l (Fin.last k) i).isLt
  refine ⟨s, t, ht, by omega, fun i hi => ?_⟩
  have h1 := hsum ⟨i, Nat.lt_succ_of_le hi⟩
  have h0 := hsum 0
  simp only [Fin.val_zero, zero_mul, add_zero] at h0
  simp only at h1
  rw [← h1, ← h0, hl', hl']

/-! ### Averaging -/

lemma minMonoCount_le (k n : ℕ) (c : ℕ → Bool) : minMonoCount k n ≤ monoCount k n c :=
  Nat.sInf_le ⟨c, rfl⟩

lemma exists_monoCount_eq_minMonoCount (k n : ℕ) :
    ∃ c : ℕ → Bool, monoCount k n c = minMonoCount k n :=
  Nat.sInf_mem (s := {m : ℕ | ∃ c : ℕ → Bool, monoCount k n c = m}) ⟨_, fun _ => true, rfl⟩

lemma minMonoCount_le_mul (k n : ℕ) : minMonoCount k n ≤ n * n :=
  (minMonoCount_le k n fun _ => true).trans <| (Finset.card_filter_le _ _).trans <| by
    simp [Finset.card_product]

/-- Every colouring has at least `M ^ 2 / W ^ 2` monochromatic progressions, `M = n / (2W)`. -/
lemma mul_le_monoCount {k W : ℕ} (hk : 2 ≤ k)
    (hW : ∀ c : ℕ → Bool, ∃ s t : ℕ, 0 < t ∧ s + (k - 1) * t < W ∧
      ∀ i ≤ k - 1, c (s + i * t) = c s) (n : ℕ) (c : ℕ → Bool) :
    n / (2 * W) * (n / (2 * W)) ≤ monoCount k n c * (W * W) := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hW
  set M := n / (2 * W) with hM
  have hWM : M * (2 * W) ≤ n := Nat.div_mul_le_self n (2 * W)
  choose s t hst using fun p : ℕ × ℕ => hW fun j => c (p.1 + j * p.2)
  let g : ℕ × ℕ → (ℕ × ℕ) × (ℕ × ℕ) := fun p =>
    ((p.1 + s p * p.2, t p * p.2), (s p, t p))
  have hmaps : Set.MapsTo g ↑(Finset.Icc 1 M ×ˢ Finset.Icc 1 M)
      ↑(((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ =>
        p.1 + (K + 1 - 1) * p.2 ≤ n ∧ ∀ i < K + 1, c (p.1 + i * p.2) = c p.1) ×ˢ
        (Finset.range W ×ˢ Finset.range W)) := by
    rintro ⟨a, D⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc] at hp
    obtain ⟨⟨ha1, haM⟩, hD1, hDM⟩ := hp
    obtain ⟨ht, hlt, hmono⟩ := hst (a, D)
    simp only at ht hlt hmono
    have hQ : (s (a, D) + K * t (a, D)) * D ≤ (W - 1) * M :=
      Nat.mul_le_mul (by omega) hDM
    have hWM' : (W - 1) * M + M = W * M := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    have hexp : a + s (a, D) * D + K * (t (a, D) * D) = a + (s (a, D) + K * t (a, D)) * D := by
      ring
    have hle : a + s (a, D) * D + K * (t (a, D) * D) ≤ n := by
      rw [hexp]
      have : M * (2 * W) = 2 * (W * M) := by ring
      omega
    have htD : t (a, D) * D ≤ K * (t (a, D) * D) := Nat.le_mul_of_pos_left _ (by omega)
    have htD1 : 1 ≤ t (a, D) * D := Nat.mul_pos ht hD1
    have htW : t (a, D) ≤ K * t (a, D) := Nat.le_mul_of_pos_left _ (by omega)
    simp only [g, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc, Finset.mem_range, Nat.add_sub_cancel]
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, hle, fun i hi => ?_⟩, by omega, by omega⟩
    have := hmono i (by omega)
    rwa [show a + s (a, D) * D + i * (t (a, D) * D) = a + (s (a, D) + i * t (a, D)) * D by ring]
  have hinj : Set.InjOn g ↑(Finset.Icc 1 M ×ˢ Finset.Icc 1 M) := by
    rintro ⟨a, D⟩ hp ⟨a', D'⟩ hp' h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    have ht := (hst (a, D)).1
    rw [h4] at h2
    have hD : D = D' := Nat.eq_of_mul_eq_mul_left (h4 ▸ ht) h2
    subst hD
    rw [h3] at h1
    simp only [Prod.mk.injEq, and_true]
    omega
  have := Finset.card_le_card_of_injOn g hmaps hinj
  simpa [Finset.card_product, Nat.card_Icc, monoCount] using this

/-- **Erdős Problem 1186, van der Waerden bound.** For fixed $k \ge 2$, $\delta_k > 0$. -/
theorem van_der_waerden (k : ℕ) (hk : 2 ≤ k) : 0 < δ k := by
  obtain ⟨W, hW⟩ := exists_ap_bound (k - 1)
  have hW1 : 1 ≤ W := by
    obtain ⟨s, t, -, hst, -⟩ := hW fun _ => true
    omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have h16 : (0 : ℝ) < 16 * (W : ℝ) ^ 4 := mul_pos (by norm_num) (pow_pos hW0 4)
  unfold δ
  refine (one_div_pos.mpr h16).trans_le
    (le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (x := 1) fun n => ?_) ?_)
  · show (minMonoCount k n : ℝ) / (n : ℝ) ^ 2 ≤ 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [div_le_one (pow_pos (by exact_mod_cast hn) 2)]
      exact_mod_cast (minMonoCount_le_mul k n).trans_eq (sq n).symm
  · filter_upwards [eventually_ge_atTop (4 * W)] with n hn
    obtain ⟨c, hc⟩ := exists_monoCount_eq_minMonoCount k n
    have hM := mul_le_monoCount hk hW n c
    rw [hc] at hM
    set M := n / (2 * W) with hMdef
    have h4 : n ≤ 4 * (W * M) := by
      have h1 := Nat.div_add_mod n (2 * W)
      have h2 := Nat.mod_lt n (show 0 < 2 * W by omega)
      have : 2 * W * (n / (2 * W)) = 2 * (W * M) := by rw [hMdef]; ring
      omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h4' : (n : ℝ) ≤ 4 * W * M := by
      have : ((n : ℕ) : ℝ) ≤ ((4 * (W * M) : ℕ) : ℝ) := by exact_mod_cast h4
      push_cast at this
      linarith
    have hM' : (M : ℝ) * M ≤ minMonoCount k n * (W * W) := by exact_mod_cast hM
    rw [div_le_div_iff₀ h16 (pow_pos hn0 2), one_mul]
    have h5 : (n : ℝ) ^ 2 ≤ (4 * W * M) ^ 2 := pow_le_pow_left₀ hn0.le h4' 2
    have h6 : (16 * (W : ℝ) ^ 2) * ((M : ℝ) * M) ≤ (16 * (W : ℝ) ^ 2) * (minMonoCount k n * (W * W)) :=
      mul_le_mul_of_nonneg_left hM' (by positivity)
    nlinarith [h5, h6]

end Erdos1186

/-!
# Erdős Problem 1186: the probabilistic upper bound

For every $k \ge 2$, $\delta_k \le 1 / ((k - 1) 2^k)$: some $2$-colouring of $\{1, \dots, n\}$
has at most $n^2 / ((k - 1) 2^k)$ monochromatic $k$-term arithmetic progressions.

The definitions `monoCount`, `minMonoCount` and `δ` are copied verbatim from
`FormalConjectures/ErdosProblems/1186.lean` (Copyright 2026 The Formal Conjectures Authors,
Apache 2.0) at upstream commit `7bdc4a42f24c0316f81c73b26121794b2bed96a3`, in the namespace
`Erdos1186Prob` instead of `Erdos1186`. The theorem `probabilistic` is the statement of
`erdos_1186.variants.probabilistic` there.

*References:* [erdosproblems.com/1186](https://www.erdosproblems.com/1186);
P. Erdős, "A survey of problems in combinatorial number theory", *Ann. Discrete Math.* (1980),
89--115, p. 93, (7).

## Proof

* Averaging (`sum_monoCount`): colour $x$ by $[x \in A]$ for $A \subseteq \{1, \dots, n\}$. A
  progression $P$ with $k$ terms is monochromatic iff $P \subseteq A$ or $P \cap A = \emptyset$,
  which holds for $2 \cdot 2^{n-k}$ of the $2^n$ sets $A$. So the least count times $2^{k-1}$ is at
  most the number $N$ of progressions.
* Counting (`card_aps_le`): $2 (k - 1) N \le n^2$. With $m = k - 1$, the progression $(a, d)$ and
  $j < m$ give the pair $x < y$ in $\{1, \dots, n\}$ with $x = m (d - 1) + j + 1$, $y = a + m d$.
  This map is injective, and the ordered pairs of distinct elements number $n^2 - n$.
-/

namespace Erdos1186Prob

open Filter (atTop)
open Finset

/--
`monoCount k n c` is the number of monochromatic $k$-term arithmetic progressions in
$\{1,\ldots,n\}$ under the $2$-colouring `c`. The progression $a, a+d, \ldots, a+(k-1)d$ with first
term $a$ and common difference $d \geq 1$ is the pair `(a, d)`, with $a \geq 1$ and
$a + (k-1)d \leq n$. Each progression is counted once.

This is the count of [Er80, p. 93]: there are $\sim n^2/(2(k-1))$ progressions, and the upper bound
in (7) there is their number times the probability $2^{1-k}$ that a random colouring makes one of
them monochromatic. The definition is meant for $k \geq 2$.
-/
def monoCount (k n : ℕ) (c : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ =>
    p.1 + (k - 1) * p.2 ≤ n ∧ ∀ i < k, c (p.1 + i * p.2) = c p.1).card

/--
`minMonoCount k n` is the least number of monochromatic $k$-term arithmetic progressions in a
$2$-colouring of $\{1,\ldots,n\}$. This is $A(n;k)$ in [Er80, p. 93]. The set of values contains
`monoCount k n (fun _ => true)`, so `sInf` is a true minimum.
-/
noncomputable def minMonoCount (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ c : ℕ → Bool, monoCount k n c = m}

/--
`δ k` is the largest constant $\delta_k$ such that every $2$-colouring of $\{1,\ldots,n\}$ has at
least $(\delta_k - o(1))n^2$ monochromatic $k$-term arithmetic progressions, that is,
$\liminf_{n\to\infty} A(n;k)/n^2$.

The quotient `minMonoCount k n / n ^ 2` lies in $[0,1]$, so this `liminf` is not a junk value.
Convergence of the quotient is not assumed. If it converges, `δ k` is its limit.
-/
noncomputable def δ (k : ℕ) : ℝ :=
  atTop.liminf (fun n : ℕ ↦ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2)

/-- Any colouring gives an upper bound for `minMonoCount`. -/
lemma minMonoCount_le (k n : ℕ) (c : ℕ → Bool) : minMonoCount k n ≤ monoCount k n c :=
  Nat.sInf_le ⟨c, rfl⟩

/-- The pairs `(a, d)` that give a `k`-term progression `a, a + d, …` in `{1, …, n}`. -/
def aps (k n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ => p.1 + (k - 1) * p.2 ≤ n

lemma monoCount_eq (k n : ℕ) (c : ℕ → Bool) :
    monoCount k n c = #((aps k n).filter fun p => ∀ i < k, c (p.1 + i * p.2) = c p.1) := by
  rw [monoCount, aps, filter_filter]

/-- Division with remainder by `m` is unique. -/
lemma eq_of_mul_add_eq_mul_add {m q q' j j' : ℕ} (hj : j < m) (hj' : j' < m)
    (h : m * q + j = m * q' + j') : q = q' ∧ j = j' := by
  have hm : 0 < m := by omega
  have h1 : (m * q' + j') / m = q ∧ (m * q' + j') % m = j :=
    (Nat.div_mod_unique hm).mpr ⟨by omega, hj⟩
  have h2 : (m * q' + j') / m = q' ∧ (m * q' + j') % m = j' :=
    (Nat.div_mod_unique hm).mpr ⟨by omega, hj'⟩
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

/-- $2 m$ times the number of pairs `(a, d)` with $a, d \ge 1$ and $a + m d \le n$ is at most
$n^2$. -/
lemma card_aps_le (m n : ℕ) :
    #((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ => p.1 + m * p.2 ≤ n) * m * 2 ≤ n ^ 2 := by
  let g : ((ℕ × ℕ) × ℕ) × Bool → ℕ × ℕ := fun q =>
    bif q.2 then (m * (q.1.1.2 - 1) + q.1.2 + 1, q.1.1.1 + m * q.1.1.2)
    else (q.1.1.1 + m * q.1.1.2, m * (q.1.1.2 - 1) + q.1.2 + 1)
  have hmem : ∀ (a d j : ℕ) (s : Bool), (((a, d), j), s) ∈
      (((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ => p.1 + m * p.2 ≤ n) ×ˢ range m) ×ˢ
        (univ : Finset Bool) →
      1 ≤ a ∧ 1 ≤ d ∧ a + m * d ≤ n ∧ j < m ∧ m * (d - 1) + m = m * d := by
    intro a d j s h
    simp only [mem_product, mem_filter, mem_Icc, mem_range, mem_univ, and_true] at h
    obtain ⟨⟨⟨⟨ha, -⟩, hd, -⟩, had⟩, hj⟩ := h
    refine ⟨ha, hd, had, hj, ?_⟩
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hd]
  have hmaps : Set.MapsTo g
      ↑((((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ => p.1 + m * p.2 ≤ n) ×ˢ range m) ×ˢ
        (univ : Finset Bool)) ↑(Icc 1 n).offDiag := by
    rintro ⟨⟨⟨a, d⟩, j⟩, s⟩ h
    obtain ⟨ha, hd, had, hj, hmd⟩ := hmem a d j s h
    cases s
    · simp only [g, Bool.cond_false, mem_coe, mem_offDiag, mem_Icc]
      omega
    · simp only [g, Bool.cond_true, mem_coe, mem_offDiag, mem_Icc]
      omega
  have hinj : Set.InjOn g
      ↑((((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ => p.1 + m * p.2 ≤ n) ×ˢ range m) ×ˢ
        (univ : Finset Bool)) := by
    rintro ⟨⟨⟨a, d⟩, j⟩, s⟩ h ⟨⟨⟨a', d'⟩, j'⟩, s'⟩ h' heq
    obtain ⟨ha, hd, had, hj, hmd⟩ := hmem a d j s h
    obtain ⟨ha', hd', had', hj', hmd'⟩ := hmem a' d' j' s' h'
    cases s <;> cases s'
    · simp only [g, Bool.cond_false, Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      obtain ⟨hdd, rfl⟩ := eq_of_mul_add_eq_mul_add hj hj'
        (show m * (d - 1) + j = m * (d' - 1) + j' by omega)
      obtain rfl : d = d' := by omega
      obtain rfl : a = a' := by omega
      rfl
    · simp only [g, Bool.cond_false, Bool.cond_true, Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      exfalso
      omega
    · simp only [g, Bool.cond_false, Bool.cond_true, Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      exfalso
      omega
    · simp only [g, Bool.cond_true, Prod.mk.injEq] at heq
      obtain ⟨h2, h1⟩ := heq
      obtain ⟨hdd, rfl⟩ := eq_of_mul_add_eq_mul_add hj hj'
        (show m * (d - 1) + j = m * (d' - 1) + j' by omega)
      obtain rfl : d = d' := by omega
      obtain rfl : a = a' := by omega
      rfl
  have hcard := card_le_card_of_injOn g hmaps hinj
  rw [card_product, card_product, card_range, card_univ, Fintype.card_bool, offDiag_card,
    Nat.card_Icc, Nat.add_sub_cancel] at hcard
  calc _ ≤ n * n - n := hcard
    _ ≤ n ^ 2 := by
      rw [sq]
      exact Nat.sub_le _ _

lemma mem_ap_self (k a d : ℕ) (hk : 1 ≤ k) : a ∈ (range k).image fun i => a + i * d :=
  mem_image.mpr ⟨0, mem_range.mpr (by omega), by simp⟩

/-- The colouring `x ↦ decide (x ∈ A)` makes the progression `(a, d)` monochromatic iff `A`
contains all its terms or none. -/
lemma isMono_iff (k a d : ℕ) (hk : 1 ≤ k) (A : Finset ℕ) :
    (∀ i < k, decide (a + i * d ∈ A) = decide (a ∈ A)) ↔
      (range k).image (fun i => a + i * d) ⊆ A ∨
        Disjoint ((range k).image fun i => a + i * d) A := by
  constructor
  · intro h
    by_cases haA : a ∈ A
    · left
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      simpa [haA] using h i (mem_range.mp hi)
    · right
      rw [disjoint_left]
      intro x hx hxA
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      simpa [haA, hxA] using h i (mem_range.mp hi)
  · rintro (h | h) i hi
    · have h1 : a + i * d ∈ A := h (mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩)
      simp [h1, h (mem_ap_self k a d hk)]
    · have h1 : a + i * d ∉ A :=
        disjoint_left.mp h (mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩)
      simp [h1, disjoint_left.mp h (mem_ap_self k a d hk)]

/-- For nonempty `P ⊆ U`, exactly `2 * 2 ^ (#U - #P)` sets `A ⊆ U` contain `P` or miss it. -/
lemma card_filter_subset_or_disjoint {P U : Finset ℕ} (hPU : P ⊆ U) (hP : P.Nonempty) :
    #(U.powerset.filter fun A => P ⊆ A ∨ Disjoint P A) = 2 * 2 ^ (#U - #P) := by
  obtain ⟨x, hx⟩ := hP
  rw [filter_or, card_union_of_disjoint]
  · have h1 : U.powerset.filter (fun A => P ⊆ A) = Icc P U := by
      ext A
      simp only [mem_filter, mem_powerset, Finset.mem_Icc]
      exact and_comm
    have h2 : U.powerset.filter (fun A => Disjoint P A) = (U \ P).powerset := by
      ext A
      rw [mem_filter, mem_powerset, mem_powerset, subset_sdiff, disjoint_comm]
    rw [h1, h2, card_Icc_finset hPU, card_powerset, card_sdiff_of_subset hPU, two_mul]
  · rw [disjoint_filter]
    intro A _ hsub hdisj
    exact disjoint_left.mp hdisj hx (hsub hx)

/-- A progression is monochromatic under `x ↦ decide (x ∈ A)` for exactly `2 * 2 ^ (n - k)`
sets `A ⊆ {1, …, n}`. -/
lemma card_isMono (k n a d : ℕ) (hk : 1 ≤ k) (hp : (a, d) ∈ aps k n) :
    #((Icc 1 n).powerset.filter fun A : Finset ℕ =>
      ∀ i < k, decide (a + i * d ∈ A) = decide (a ∈ A)) = 2 * 2 ^ (n - k) := by
  simp only [aps, mem_filter, mem_product, mem_Icc] at hp
  obtain ⟨⟨⟨ha, -⟩, hd, -⟩, had⟩ := hp
  have hinj : Function.Injective fun i => a + i * d := fun i j h => by
    have h' : a + i * d = a + j * d := h
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) (by omega)
  have hPU : (range k).image (fun i => a + i * d) ⊆ Icc 1 n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hik : i ≤ k - 1 := by
      have := mem_range.mp hi
      omega
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d hik
    rw [mem_Icc]
    omega
  rw [filter_congr fun A _ => isMono_iff k a d hk A,
    card_filter_subset_or_disjoint hPU ⟨a, mem_ap_self k a d hk⟩, card_image_of_injective _ hinj,
    card_range, Nat.card_Icc, show n + 1 - 1 - k = n - k by omega]

/-- Summing over the $2^n$ colourings $x \mapsto [x \in A]$, $A \subseteq \{1, \dots, n\}$, counts
each progression $2 \cdot 2^{n-k}$ times. -/
lemma sum_monoCount (k n : ℕ) (hk : 1 ≤ k) :
    ∑ A ∈ (Icc 1 n).powerset, monoCount k n (fun x => decide (x ∈ A)) =
      #(aps k n) * (2 * 2 ^ (n - k)) := by
  calc ∑ A ∈ (Icc 1 n).powerset, monoCount k n (fun x => decide (x ∈ A))
      = ∑ p ∈ aps k n, #((Icc 1 n).powerset.filter fun A : Finset ℕ =>
          ∀ i < k, decide (p.1 + i * p.2 ∈ A) = decide (p.1 ∈ A)) := by
        simp_rw [monoCount_eq, card_filter]
        exact sum_comm
    _ = ∑ _p ∈ aps k n, 2 * 2 ^ (n - k) :=
        sum_congr rfl fun p hp => card_isMono k n p.1 p.2 hk hp
    _ = #(aps k n) * (2 * 2 ^ (n - k)) := by rw [sum_const, smul_eq_mul]

/-- $A(n; k) \cdot (k - 1) 2^k \le n^2$ for $2 \le k \le n$. -/
lemma minMonoCount_mul_le (k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    minMonoCount k n * ((k - 1) * 2 ^ k) ≤ n ^ 2 := by
  have hlow : 2 ^ n * minMonoCount k n ≤
      ∑ A ∈ (Icc 1 n).powerset, monoCount k n (fun x => decide (x ∈ A)) := by
    calc 2 ^ n * minMonoCount k n = ∑ _A ∈ (Icc 1 n).powerset, minMonoCount k n := by
          rw [sum_const, card_powerset, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]
      _ ≤ _ := sum_le_sum fun A _ => minMonoCount_le k n _
  have hpow : 2 ^ n = 2 ^ (k - 1) * (2 * 2 ^ (n - k)) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have h1 : 2 ^ (k - 1) * minMonoCount k n ≤ #(aps k n) := by
    refine Nat.le_of_mul_le_mul_right ?_ (by positivity : 0 < 2 * 2 ^ (n - k))
    calc 2 ^ (k - 1) * minMonoCount k n * (2 * 2 ^ (n - k)) = 2 ^ n * minMonoCount k n := by
          rw [hpow]
          ring
      _ ≤ _ := hlow
      _ = _ := sum_monoCount k n (by omega)
  have hcount : #(aps k n) * (k - 1) * 2 ≤ n ^ 2 := card_aps_le (k - 1) n
  have hk2 : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  calc minMonoCount k n * ((k - 1) * 2 ^ k) = 2 ^ (k - 1) * minMonoCount k n * (k - 1) * 2 := by
        rw [hk2]
        ring
    _ ≤ #(aps k n) * (k - 1) * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ ≤ n ^ 2 := hcount

/-- **Erdős Problem 1186, probabilistic bound.** For $k \ge 2$,
$\delta_k \le 1 / ((k - 1) 2^k)$. -/
theorem probabilistic (k : ℕ) (hk : 2 ≤ k) : δ k ≤ 1 / (((k : ℝ) - 1) * 2 ^ k) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hc : (0 : ℝ) < ((k : ℝ) - 1) * 2 ^ k := mul_pos (by linarith) (by positivity)
  unfold δ
  refine Filter.liminf_le_of_frequently_le ?_ ?_
  · refine (Filter.eventually_ge_atTop k).frequently.mono fun n hn => ?_
    show (minMonoCount k n : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (((k : ℝ) - 1) * 2 ^ k)
    have h : ((minMonoCount k n * ((k - 1) * 2 ^ k) : ℕ) : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (minMonoCount_mul_le k n hk hn)
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)] at h
    have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    rw [div_le_div_iff₀ hn0 hc]
    linarith
  · exact Filter.isBoundedUnder_of_eventually_ge (a := 0)
      (Filter.Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

end Erdos1186Prob

namespace Erdos1186

theorem erdos_1186.variants.van_der_waerden (k : ℕ) (hk : 2 ≤ k) : 0 < δ k :=
  _root_.Erdos1186.van_der_waerden k hk

theorem erdos_1186.variants.probabilistic (k : ℕ) (hk : 2 ≤ k) :
    δ k ≤ 1 / (((k : ℝ) - 1) * 2 ^ k) :=
  Erdos1186Prob.probabilistic k hk

end Erdos1186

end
