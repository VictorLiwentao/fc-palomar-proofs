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
# OEIS A326097 and A385907: Hanna's parity pattern

Let $A(x) = \sum_k a(k) x^k / k!$ satisfy $1 = \sum_{n \ge 0} (q(x)^n - A(x))^n / n!$, with the
sum taken coefficientwise, for $q = 1 + x$ (A326097) or $q = 1/(1-x)$ (A385907). The file proves
that $A$ exists and is unique, that every $a(k)$ is an integer, and that $a(k)$ is odd if and only
if $k \in \{0, 1, 3\}$ or $k \equiv 2 \pmod 4$. For A326097 this settles Paul D. Hanna's parity
conjecture.

The proof works with Hurwitz series: sequences $f_n = n!\,[x^n] f$ with the binomial product.
The divided power $g^{[k]}$ is defined by $g^{[0]} = 1$, $D g^{[k+1]} = g^{[k]} D g$ and constant
term $0$, so it exists over every commutative ring. Over $\mathbb{Q}$ it is
$(g - g_0)^k / k!$. Write $Q$ and $B$ for the Hurwitz series of $q$ and $A$.

*Reduction to Hurwitz series.* Here $q(0) = 1$. The constant term of the $n$-th term of the sum
is $(1 - A(0))^n / n!$, so the partial sums stabilize at $x^0$ only if $A(0) = 1$. Then the
$n$-th term is $(Q^n - B)^{[n]}$, which vanishes below index $n$. So the equation says $B_0 = 1$
and $\sum_{n \le m} (Q^n - B)^{[n]}_m = [m = 0]$ for every $m$.

*Existence, uniqueness and integrality.* For $m \ge 1$, the term $n = 1$ contributes
$Q_m - B_m$ at index $m$, and the terms $n \ge 2$ only use $B_0, \dots, B_{m-1}$. So the equation
is a fixed-point equation $T(B) = B$ for an operator $T$ whose coefficient $m$ only uses
coefficients of $B$ below $m$. Over every commutative ring, $T$ has exactly one fixed point, built
one coefficient at a time. The Hurwitz series of $1 + x$ and of $1/(1-x)$ have integer
coefficients ($1 + x$ and $n!$). The image of the integer fixed point is a fixed point over
$\mathbb{Q}$, so by uniqueness it is the Hurwitz series of every rational solution.

*Parity.* Over $\mathbb{F}_2$ both base series reduce to $1 + x$. There $x^2 = 0$, so
$(1 + x)^n$ is $1$ for even $n$ and $1 + x$ for odd $n$. The equation becomes
$\cosh(B) + \sinh(B + x) = 1$, where $\cosh$ and $\sinh$ are the compositions with the even and
odd parts of $e^x$. In characteristic $2$, $D^2$ and $D^4$ are derivations and every square is a
constant. A Jacobson-type chain rule then shows: if $D^2 f = f$, $g_{n+8} = g_{n+4}$ for all $n$,
and $g_4 = 0$, then $f(g)$ also satisfies $f(g)_{n+8} = f(g)_{n+4}$. Let $P_k = 1$ exactly for
$k \in \{0, 1, 3\}$ and $k \equiv 2 \pmod 4$. Both $P$ and $P + x$ satisfy these conditions, so
$\cosh(P) + \sinh(P + x)$ is determined by its first $8$ coefficients. A kernel computation shows
that these agree with $1$. Hence $P$ is the fixed point over $\mathbb{F}_2$, and by uniqueness it is
the reduction of $(a(k))$ modulo $2$.

*References:*
- Paul D. Hanna, [A326097](https://oeis.org/A326097), June 6, 2019.
- Paul D. Hanna, [A385907](https://oeis.org/A385907), July 24, 2025.
-/

@[expose] public section

namespace OeisA326097

open PowerSeries

/-- Hanna's equation $1 = \sum_{n \ge 0} (q(x)^n - A(x))^n / n!$ for a base series $q$.
The infinite sum is taken coefficientwise: for every $m$, the coefficient of $x^m$ in the partial
sums $\sum_{n < N}$ equals that of $1$ for all large $N$. -/
def IsSolution (q A : ℚ⟦X⟧) : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, ∀ N' ≥ N,
    coeff m (∑ n ∈ Finset.range N', (n.factorial : ℚ)⁻¹ • (q ^ n - A) ^ n) = coeff m (1 : ℚ⟦X⟧)

end OeisA326097

namespace OeisA326097

/-! ### Hurwitz series

The Hurwitz-series library below (ring structure, derivative, divided powers, composition and
coefficient maps) is adapted from this repository's A396804 package. -/

/-- A Hurwitz series, stored by its EGF coefficients $f_n = n!\,[x^n] f$. -/
@[ext] structure Hur (R : Type*) where
  /-- The $n$-th EGF coefficient. -/
  coeff : ℕ → R

namespace Hur

section Ring
variable {R : Type*} [CommRing R]

/-- The shift $f_n \mapsto f_{n+1}$. -/
def shift (a : ℕ → R) : ℕ → R := fun n => a (n + 1)

/-- The binomial product $\sum_k \binom{n}{k} a_k b_{n-k}$, defined by the product rule. -/
def prod (a b : ℕ → R) : ℕ → R
  | 0 => a 0 * b 0
  | n + 1 => prod (shift a) b n + prod a (shift b) n

lemma prod_succ (a b : ℕ → R) (n : ℕ) :
    prod a b (n + 1) = prod (shift a) b n + prod a (shift b) n := rfl

lemma prod_comm (a b : ℕ → R) : prod a b = prod b a := by
  funext n
  induction n generalizing a b with
  | zero => simp [prod, mul_comm]
  | succ n ih => rw [prod_succ, prod_succ, ih (shift a) b, ih a (shift b), add_comm]

lemma prod_add_left (a b c : ℕ → R) : prod (a + b) c = prod a c + prod b c := by
  funext n
  induction n generalizing a b c with
  | zero => simp [prod, add_mul]
  | succ n ih =>
    change prod (shift a + shift b) c n + prod (a + b) (shift c) n = _
    rw [ih, ih]
    simp only [Pi.add_apply, prod_succ]
    ring

lemma prod_add_right (a b c : ℕ → R) : prod a (b + c) = prod a b + prod a c := by
  rw [prod_comm, prod_add_left, prod_comm b a, prod_comm c a]

lemma prod_assoc (a b c : ℕ → R) : prod (prod a b) c = prod a (prod b c) := by
  funext n
  induction n generalizing a b c with
  | zero => simp [prod, mul_assoc]
  | succ n ih =>
    have hs : ∀ u v : ℕ → R, shift (prod u v) = prod (shift u) v + prod u (shift v) :=
      fun _ _ => rfl
    simp only [prod_succ, hs, prod_add_left, prod_add_right, Pi.add_apply]
    rw [ih, ih, ih]
    ring

lemma prod_zero_left (b : ℕ → R) : prod 0 b = 0 := by
  funext n
  induction n generalizing b with
  | zero => simp [prod]
  | succ n ih =>
    rw [prod_succ]
    have : shift (0 : ℕ → R) = 0 := rfl
    rw [this, ih, ih]
    simp

lemma prod_zero_right (a : ℕ → R) : prod a 0 = 0 := by
  rw [prod_comm, prod_zero_left]

/-- The unit sequence. -/
def unitSeq : ℕ → R := fun n => if n = 0 then 1 else 0

lemma prod_unit (a : ℕ → R) : prod a unitSeq = a := by
  funext n
  induction n generalizing a with
  | zero => simp [prod, unitSeq]
  | succ n ih =>
    have hs : shift (unitSeq : ℕ → R) = 0 := by
      funext k
      simp [shift, unitSeq]
    rw [prod_succ, hs, prod_zero_right, Pi.zero_apply, add_zero, ih]
    rfl

/-- A coefficient of a product only uses coefficients of the same or lower index. -/
lemma prod_congr (a b c d : ℕ → R) (n : ℕ)
    (ha : ∀ k ≤ n, a k = c k) (hb : ∀ k ≤ n, b k = d k) :
    prod a b n = prod c d n := by
  induction n generalizing a b c d with
  | zero => simp [prod, ha 0 le_rfl, hb 0 le_rfl]
  | succ n ih =>
    rw [prod_succ, prod_succ]
    congr 1
    · apply ih
      · intro k hk; exact ha (k + 1) (Nat.succ_le_succ hk)
      · intro k hk; exact hb k (Nat.le_succ_of_le hk)
    · apply ih
      · intro k hk; exact ha k (Nat.le_succ_of_le hk)
      · intro k hk; exact hb (k + 1) (Nat.succ_le_succ hk)

lemma map_prod {S : Type*} [CommRing S] (φ : R →+* S) (a b : ℕ → R) :
    φ ∘ prod a b = prod (φ ∘ a) (φ ∘ b) := by
  funext n
  change φ (prod a b n) = prod (φ ∘ a) (φ ∘ b) n
  induction n generalizing a b with
  | zero => simp [prod, Function.comp_apply]
  | succ n ih =>
    rw [prod_succ, map_add, ih, ih]
    rfl

instance : Zero (Hur R) := ⟨⟨0⟩⟩
instance : Add (Hur R) := ⟨fun f g => ⟨f.coeff + g.coeff⟩⟩
instance : Neg (Hur R) := ⟨fun f => ⟨-f.coeff⟩⟩
instance : Sub (Hur R) := ⟨fun f g => ⟨f.coeff - g.coeff⟩⟩
instance : SMul ℕ (Hur R) := ⟨fun n f => ⟨n • f.coeff⟩⟩
instance : SMul ℤ (Hur R) := ⟨fun n f => ⟨n • f.coeff⟩⟩
instance : One (Hur R) := ⟨⟨unitSeq⟩⟩
instance : Mul (Hur R) := ⟨fun f g => ⟨prod f.coeff g.coeff⟩⟩

@[simp] lemma coeff_zero' (n : ℕ) : (0 : Hur R).coeff n = 0 := rfl
@[simp] lemma coeff_add (f g : Hur R) (n : ℕ) : (f + g).coeff n = f.coeff n + g.coeff n := rfl
@[simp] lemma coeff_neg (f : Hur R) (n : ℕ) : (-f).coeff n = -f.coeff n := rfl
@[simp] lemma coeff_sub (f g : Hur R) (n : ℕ) : (f - g).coeff n = f.coeff n - g.coeff n := rfl
lemma coeff_mul (f g : Hur R) (n : ℕ) : (f * g).coeff n = prod f.coeff g.coeff n := rfl
@[simp] lemma coeff_mul_zero (f g : Hur R) : (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := rfl
lemma coeff_one (n : ℕ) : (1 : Hur R).coeff n = if n = 0 then 1 else 0 := rfl

instance : AddCommGroup (Hur R) :=
  Function.Injective.addCommGroup Hur.coeff (fun _ _ h => Hur.ext h) rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : CommRing (Hur R) :=
  { (inferInstance : AddCommGroup (Hur R)) with
    mul_assoc := fun a b c => Hur.ext (prod_assoc _ _ _)
    one_mul := fun a => Hur.ext (by
      change prod unitSeq a.coeff = a.coeff
      rw [prod_comm, prod_unit])
    mul_one := fun a => Hur.ext (prod_unit _)
    zero_mul := fun a => Hur.ext (prod_zero_left _)
    mul_zero := fun a => Hur.ext (prod_zero_right _)
    left_distrib := fun a b c => Hur.ext (prod_add_right _ _ _)
    right_distrib := fun a b c => Hur.ext (prod_add_left _ _ _)
    mul_comm := fun a b => Hur.ext (prod_comm _ _)
    natCast := fun n => ⟨fun k => if k = 0 then (n : R) else 0⟩
    natCast_zero := Hur.ext (by funext k; simp)
    natCast_succ := fun n => Hur.ext (by
      funext k
      change (if k = 0 then ((n + 1 : ℕ) : R) else 0) =
        (if k = 0 then (n : R) else 0) + (if k = 0 then 1 else 0)
      split_ifs <;> simp)
    intCast := fun n => ⟨fun k => if k = 0 then (n : R) else 0⟩
    intCast_ofNat := fun n => Hur.ext (by
      funext k
      change (if k = 0 then ((n : ℤ) : R) else 0) = (if k = 0 then (n : R) else 0)
      simp)
    intCast_negSucc := fun n => Hur.ext (by
      funext k
      change (if k = 0 then ((Int.negSucc n : ℤ) : R) else 0) =
        -(if k = 0 then ((n + 1 : ℕ) : R) else 0)
      split_ifs <;> simp [Int.cast_negSucc]) }

lemma coeff_natCast (m n : ℕ) : (m : Hur R).coeff n = if n = 0 then (m : R) else 0 := rfl

/-- The constant coefficient as a ring homomorphism. -/
def coeff0 : Hur R →+* R where
  toFun f := f.coeff 0
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

lemma coeff0_apply (f : Hur R) : coeff0 f = f.coeff 0 := rfl

/-- Constant series. -/
def C (r : R) : Hur R := ⟨fun n => if n = 0 then r else 0⟩

lemma coeff_C (r : R) (n : ℕ) : (C r).coeff n = if n = 0 then r else 0 := rfl

lemma shift_C (r : R) : shift (C r).coeff = 0 := by
  funext n
  simp [shift, coeff_C]

lemma C_mul_coeff (r : R) (f : Hur R) (n : ℕ) : (C r * f).coeff n = r * f.coeff n := by
  induction n generalizing f with
  | zero => simp [coeff_C]
  | succ n ih =>
    rw [coeff_mul, prod_succ, shift_C, prod_zero_left, Pi.zero_apply, zero_add]
    exact ih ⟨shift f.coeff⟩

lemma C_mul (r s : R) : C (r * s) = C r * C s := by
  ext n
  rw [C_mul_coeff]
  simp only [coeff_C]
  split_ifs <;> simp

lemma C_one : C (1 : R) = 1 := rfl

lemma C_pow (r : R) (k : ℕ) : C (r ^ k) = C r ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, C_one]
  | succ k ih => rw [pow_succ, C_mul, ih, pow_succ]

lemma C_zero : C (0 : R) = 0 := by
  ext n
  simp [coeff_C]

/-- Differentiation of Hurwitz series is the shift. -/
def D (f : Hur R) : Hur R := ⟨shift f.coeff⟩

omit [CommRing R] in
@[simp] lemma coeff_D (f : Hur R) (n : ℕ) : (D f).coeff n = f.coeff (n + 1) := rfl

lemma D_add (f g : Hur R) : D (f + g) = D f + D g := rfl
lemma D_sub (f g : Hur R) : D (f - g) = D f - D g := rfl
lemma D_zero : D (0 : Hur R) = 0 := rfl
lemma D_mul (f g : Hur R) : D (f * g) = D f * g + f * D g := rfl

lemma D_C (r : R) : D (C r) = 0 := Hur.ext (shift_C r)

lemma D_one : D (1 : Hur R) = 0 := D_C 1

omit [CommRing R] in
/-- Two series with equal constant terms and equal derivatives are equal. -/
lemma ext_D {f g : Hur R} (h0 : f.coeff 0 = g.coeff 0) (hD : D f = D g) : f = g := by
  ext n
  cases n with
  | zero => exact h0
  | succ n => exact congrArg (fun h => Hur.coeff h n) hD

lemma eq_C_of_D_eq_zero {f : Hur R} (h : D f = 0) : f = C (f.coeff 0) :=
  ext_D (by simp [coeff_C]) (by rw [h, D_C])

lemma D_pow (f : Hur R) (k : ℕ) : D (f ^ (k + 1)) = (k + 1 : ℕ) * f ^ k * D f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, D_mul, ih]
    push_cast
    ring

omit [CommRing R] in
lemma coeff_iterate_D (f : Hur R) (m n : ℕ) : (D^[m] f).coeff n = f.coeff (n + m) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', coeff_D, ih]
    congr 1
    omega

lemma iterate_D_add (f g : Hur R) (m : ℕ) : D^[m] (f + g) = D^[m] f + D^[m] g := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, D_add,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

lemma iterate_D_C (r : R) (m : ℕ) : D^[m + 1] (C r) = 0 := by
  induction m with
  | zero => exact D_C r
  | succ m ih => rw [Function.iterate_succ_apply', ih, D_zero]

/-- The EGF variable $x$. -/
def x : Hur R := ⟨fun n => if n = 1 then 1 else 0⟩

lemma D_x : D (x : Hur R) = 1 := by
  ext n
  cases n <;> simp [x, coeff_one]

end Ring

section Comp
variable {R : Type*} [CommRing R]

/-- The `n`-th coefficient as an additive map. -/
def coeffAdd (n : ℕ) : Hur R →+ R where
  toFun f := f.coeff n
  map_zero' := rfl
  map_add' _ _ := rfl

lemma coeff_sum {ι : Type*} (s : Finset ι) (F : ι → Hur R) (n : ℕ) :
    (∑ i ∈ s, F i).coeff n = ∑ i ∈ s, (F i).coeff n :=
  map_sum (coeffAdd n) F s

/-- Differentiation as an additive map. -/
def DAdd : Hur R →+ Hur R where
  toFun := D
  map_zero' := rfl
  map_add' _ _ := rfl

lemma D_sum {ι : Type*} (s : Finset ι) (F : ι → Hur R) :
    D (∑ i ∈ s, F i) = ∑ i ∈ s, D (F i) :=
  map_sum (DAdd : Hur R →+ Hur R) F s

lemma D_C_mul (r : R) (f : Hur R) : D (C r * f) = C r * D f := by
  rw [D_mul, D_C, zero_mul, zero_add]

lemma coeff_mul_congr (f g f' g' : Hur R) (n : ℕ) (hf : ∀ k ≤ n, f.coeff k = f'.coeff k)
    (hg : ∀ k ≤ n, g.coeff k = g'.coeff k) : (f * g).coeff n = (f' * g').coeff n :=
  prod_congr _ _ _ _ n hf hg

lemma coeff_mul_eq_zero (f g : Hur R) (n : ℕ) (h : ∀ k ≤ n, f.coeff k = 0) :
    (f * g).coeff n = 0 := by
  rw [coeff_mul_congr f g 0 g n h (fun _ _ => rfl), zero_mul]
  rfl

/-- Integration: $(\int h)_0 = 0$ and $(\int h)_{n+1} = h_n$. -/
def integ (h : Hur R) : Hur R := ⟨fun n => match n with
  | 0 => 0
  | n + 1 => h.coeff n⟩

/-- The divided powers $g^{[k]}$ of $g - g_0$, defined by $D g^{[k+1]} = g^{[k]} D g$. -/
def dpow (g : Hur R) : ℕ → Hur R
  | 0 => 1
  | k + 1 => integ (dpow g k * D g)

lemma dpow_zero (g : Hur R) : dpow g 0 = 1 := rfl

lemma D_dpow_succ (g : Hur R) (k : ℕ) : D (dpow g (k + 1)) = dpow g k * D g := rfl

lemma dpow_coeff_lt (g : Hur R) {k n : ℕ} (h : n < k) : (dpow g k).coeff n = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change (dpow g k * D g).coeff n = 0
      apply coeff_mul_eq_zero
      intro j hj
      exact ih (by omega)

/-- A coefficient of $g^{[k]}$ only uses coefficients of $g$ of the same or lower index. -/
lemma dpow_congr (g g' : Hur R) (n : ℕ) (hg : ∀ k ≤ n, g.coeff k = g'.coeff k) (j : ℕ) :
    ∀ m ≤ n, (dpow g j).coeff m = (dpow g' j).coeff m := by
  induction j with
  | zero => intro m _; rfl
  | succ j ih =>
    intro m hm
    cases m with
    | zero => rfl
    | succ m =>
      change (dpow g j * D g).coeff m = (dpow g' j * D g').coeff m
      apply coeff_mul_congr
      · intro k hk; exact ih k (by omega)
      · intro k hk; exact hg (k + 1) (by omega)

/-- Composition $f(g) = \sum_k f_k g^{[k]}$, for $g_0 = 0$. -/
def comp (f g : Hur R) : Hur R :=
  ⟨fun n => ∑ k ∈ Finset.range (n + 1), f.coeff k * (dpow g k).coeff n⟩

/-- A partial sum of the composition series. -/
def compSum (f g : Hur R) (N : ℕ) : Hur R :=
  ∑ k ∈ Finset.range (N + 1), C (f.coeff k) * dpow g k

lemma coeff_compSum (f g : Hur R) {N n : ℕ} (h : n ≤ N) :
    (compSum f g N).coeff n = (comp f g).coeff n := by
  rw [compSum, coeff_sum]
  simp only [C_mul_coeff]
  change _ = ∑ k ∈ Finset.range (n + 1), f.coeff k * (dpow g k).coeff n
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [dpow_coeff_lt g (by omega), mul_zero]

lemma D_compSum (f g : Hur R) (N : ℕ) :
    D (compSum f g (N + 1)) = compSum (D f) g N * D g := by
  rw [compSum, Finset.sum_range_succ', D_add, D_sum]
  simp only [D_C_mul, D_dpow_succ, dpow_zero, D_one, mul_zero, add_zero]
  rw [compSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_D, mul_assoc]

/-- The chain rule $D(f(g)) = (Df)(g) \cdot Dg$. -/
theorem D_comp (f g : Hur R) : D (comp f g) = comp (D f) g * D g := by
  ext n
  rw [coeff_D, ← coeff_compSum f g (le_refl (n + 1)), ← coeff_D, D_compSum]
  apply coeff_mul_congr
  · intro k hk; exact coeff_compSum (D f) g hk
  · intro k _; rfl

end Comp

section Map
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Coefficientwise image under a ring homomorphism. -/
def map (φ : R →+* S) (f : Hur R) : Hur S := ⟨φ ∘ f.coeff⟩

lemma coeff_map (φ : R →+* S) (f : Hur R) (n : ℕ) : (map φ f).coeff n = φ (f.coeff n) := rfl

lemma map_mul' (φ : R →+* S) (f g : Hur R) : map φ (f * g) = map φ f * map φ g :=
  Hur.ext (map_prod φ f.coeff g.coeff)

lemma map_add' (φ : R →+* S) (f g : Hur R) : map φ (f + g) = map φ f + map φ g := by
  ext n
  simp [coeff_map]

lemma map_one' (φ : R →+* S) : map φ (1 : Hur R) = 1 := by
  ext n
  simp only [coeff_map, coeff_one]
  split_ifs <;> simp

lemma map_D (φ : R →+* S) (f : Hur R) : map φ (D f) = D (map φ f) := rfl

lemma map_integ (φ : R →+* S) (h : Hur R) : map φ (integ h) = integ (map φ h) := by
  ext n
  cases n <;> simp [coeff_map, integ]

lemma map_dpow (φ : R →+* S) (g : Hur R) (k : ℕ) : map φ (dpow g k) = dpow (map φ g) k := by
  induction k with
  | zero => exact map_one' φ
  | succ k ih => rw [dpow, dpow, map_integ, map_mul', ih, map_D]

lemma map_x (φ : R →+* S) : map φ (x : Hur R) = x := by
  ext n
  simp only [coeff_map, x]
  split_ifs <;> simp
end Map

section RingHom
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Coefficientwise image under a ring homomorphism, as a ring homomorphism. -/
def mapHom (φ : R →+* S) : Hur R →+* Hur S where
  toFun := map φ
  map_one' := map_one' φ
  map_mul' := map_mul' φ
  map_zero' := by
    ext n
    simp [coeff_map]
  map_add' := map_add' φ

lemma mapHom_apply (φ : R →+* S) (f : Hur R) : mapHom φ f = map φ f := rfl

end RingHom

/-! ### Hanna's equation for Hurwitz series -/

section Hanna
variable {R : Type*} [CommRing R]

/-- A product with an integral only uses coefficients below the index. -/
lemma integ_mul_congr (n : ℕ) : ∀ h h' k k' : Hur R, (∀ i < n, h.coeff i = h'.coeff i) →
    (∀ i < n, k.coeff i = k'.coeff i) → (integ h * k).coeff n = (integ h' * k').coeff n := by
  induction n with
  | zero =>
    intro h h' k k' _ _
    change (0 : R) * k.coeff 0 = 0 * k'.coeff 0
    simp
  | succ n ih =>
    intro h h' k k' hh hk
    change prod h.coeff k.coeff n + (integ h * D k).coeff n =
      prod h'.coeff k'.coeff n + (integ h' * D k').coeff n
    congr 1
    · exact prod_congr _ _ _ _ n (fun i hi => hh i (by omega)) (fun i hi => hk i (by omega))
    · exact ih h h' (D k) (D k') (fun i hi => hh i (by omega)) (fun i hi => hk (i + 1) (by omega))

/-- For $j \ge 2$, coefficient $m$ of $g^{[j]}$ only uses coefficients of $g$ below $m$. -/
lemma dpow_congr_lt (g g' : Hur R) (j m : ℕ) (hg : ∀ i < m, g.coeff i = g'.coeff i) :
    (dpow g (j + 2)).coeff m = (dpow g' (j + 2)).coeff m := by
  cases m with
  | zero => rfl
  | succ m =>
    change (integ (dpow g j * D g) * D g).coeff m = (integ (dpow g' j * D g') * D g').coeff m
    apply integ_mul_congr
    · intro i hi
      apply coeff_mul_congr
      · intro k hk
        exact dpow_congr g g' i (fun l hl => hg l (by omega)) j k hk
      · intro k hk
        exact hg (k + 1) (by omega)
    · intro i hi
      exact hg (i + 1) (by omega)

lemma dpow_one_coeff_succ (g : Hur R) (m : ℕ) : (dpow g 1).coeff (m + 1) = g.coeff (m + 1) := by
  change (dpow g 0 * D g).coeff m = _
  rw [dpow_zero, one_mul, coeff_D]

/-- Hanna's sum $\sum_n (Q^n - B)^{[n]}$, where $f^{[n]}$ is the divided power of $f - f_0$. At
coefficient $m$ the terms with $n > m$ vanish, so the sum is finite there. -/
def Ser (Q B : Hur R) : Hur R :=
  ⟨fun m => ∑ n ∈ Finset.range (m + 1), (dpow (Q ^ n - B) n).coeff m⟩

/-- The Hurwitz form of Hanna's equation: $B_0 = 1$ and $\sum_n (Q^n - B)^{[n]} = 1$. -/
def SolH (Q B : Hur R) : Prop := B.coeff 0 = 1 ∧ Ser Q B = 1

/-- The fixed-point operator of Hanna's equation: its fixed points are the solutions. -/
def T (Q B : Hur R) : Hur R :=
  ⟨fun m => if m = 0 then 1 else B.coeff m + (Ser Q B).coeff m⟩

lemma ser_coeff_zero (Q B : Hur R) : (Ser Q B).coeff 0 = 1 := by
  simp [Ser, dpow_zero, coeff_one]

/-- In $B + \sum_n (Q^n - B)^{[n]}$ the term $B_{m+1}$ cancels against the term $n = 1$. -/
lemma T_coeff_succ (Q B : Hur R) (m : ℕ) :
    (T Q B).coeff (m + 1) = Q.coeff (m + 1) +
      ∑ n ∈ Finset.range m, (dpow (Q ^ (n + 2) - B) (n + 2)).coeff (m + 1) := by
  change (if m + 1 = 0 then 1 else
    B.coeff (m + 1) + ∑ n ∈ Finset.range (m + 1 + 1), (dpow (Q ^ n - B) n).coeff (m + 1)) = _
  rw [ite_eq_right (by omega), Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : (dpow (Q ^ 0 - B) 0).coeff (m + 1) = 0 := by
    rw [dpow_zero, coeff_one, ite_eq_right (by omega)]
  have h1 : (dpow (Q ^ (0 + 1) - B) (0 + 1)).coeff (m + 1) = Q.coeff (m + 1) - B.coeff (m + 1) := by
    rw [zero_add, pow_one, dpow_one_coeff_succ, coeff_sub]
  rw [h0, h1]
  ring

/-- Coefficient $n$ of `T Q B` only uses coefficients of `B` below $n$. -/
theorem T_causal (Q : Hur R) (n : ℕ) (f g : Hur R) (h : ∀ k < n, f.coeff k = g.coeff k) :
    (T Q f).coeff n = (T Q g).coeff n := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [T_coeff_succ, T_coeff_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply dpow_congr_lt
    intro i hi
    simp only [coeff_sub, h i hi]

/-- `T Q` has at most one fixed point. -/
theorem T_fixed_unique (Q : Hur R) {f g : Hur R} (hf : T Q f = f) (hg : T Q g = g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    calc f.coeff n = (T Q f).coeff n := by rw [hf]
      _ = (T Q g).coeff n := T_causal Q n f g ih
      _ = g.coeff n := by rw [hg]

/-- The coefficient recursion for the fixed point of `T Q`. -/
def fixSeq (Q : Hur R) (n : ℕ) : R :=
  (T Q (⟨fun k => if _h : k < n then fixSeq Q k else 0⟩ : Hur R)).coeff n
termination_by n

/-- The fixed point of `T Q`. -/
def fix (Q : Hur R) : Hur R := ⟨fixSeq Q⟩

theorem T_fix (Q : Hur R) : T Q (fix Q) = fix Q := by
  ext n
  change (T Q (fix Q)).coeff n = fixSeq Q n
  rw [fixSeq]
  apply T_causal
  intro k hk
  simp [fix, hk]

/-- The solutions of Hanna's equation are the fixed points of `T Q`. -/
theorem solH_iff (Q B : Hur R) : SolH Q B ↔ T Q B = B := by
  constructor
  · rintro ⟨h0, h1⟩
    ext m
    cases m with
    | zero => exact h0.symm
    | succ m =>
      have h := congrArg (fun F => Hur.coeff F (m + 1)) h1
      simp only [coeff_one, ite_eq_right (Nat.succ_ne_zero m)] at h
      change (if m + 1 = 0 then 1 else B.coeff (m + 1) + (Ser Q B).coeff (m + 1)) = _
      rw [ite_eq_right (by omega), h, add_zero]
  · intro h
    have hc : ∀ m, (T Q B).coeff m = B.coeff m := fun m => by rw [h]
    refine ⟨(hc 0).symm, ?_⟩
    ext m
    cases m with
    | zero => rw [ser_coeff_zero]; rfl
    | succ m =>
      have h' := hc (m + 1)
      change (if m + 1 = 0 then 1 else B.coeff (m + 1) + (Ser Q B).coeff (m + 1)) = _ at h'
      rw [ite_eq_right (by omega)] at h'
      rw [coeff_one, ite_eq_right (by omega)]
      linear_combination h'

end Hanna

section MapHanna
variable {R S : Type*} [CommRing R] [CommRing S]

lemma map_Ser (φ : R →+* S) (Q B : Hur R) : map φ (Ser Q B) = Ser (map φ Q) (map φ B) := by
  ext m
  simp only [Ser, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← coeff_map, map_dpow, ← mapHom_apply, map_sub, map_pow]
  rfl

lemma map_T (φ : R →+* S) (Q B : Hur R) : map φ (T Q B) = T (map φ Q) (map φ B) := by
  ext m
  rw [coeff_map]
  change φ (if m = 0 then 1 else B.coeff m + (Ser Q B).coeff m) =
    (if m = 0 then 1 else (map φ B).coeff m + (Ser (map φ Q) (map φ B)).coeff m)
  split_ifs
  · exact map_one φ
  · rw [map_add, ← map_Ser]
    rfl

lemma map_fix (φ : R →+* S) (Q : Hur R) : map φ (fix Q) = fix (map φ Q) :=
  T_fixed_unique (map φ Q) (by rw [← map_T, T_fix]) (T_fix _)

end MapHanna

/-! ### Characteristic two -/

section Two

/-- Leibniz rule for the second iterate of a derivation in characteristic two. -/
theorem iterate_two_mul {T : Type*} [CommRing T] (h2 : (2 : T) = 0) (δ : T → T)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = δ a * b + a * δ b)
    (a b : T) : δ (δ (a * b)) = δ (δ a) * b + a * δ (δ b) := by
  simp only [hmul, hadd]
  linear_combination (δ a * δ b) * h2

/-- A Jacobson identity in characteristic two: if
$\delta V_m = c_1 V_{m+a} + c_2 V_{m+b} + w V_{m+1}$ with constants $c_1, c_2$, then
$\delta^2 V_0 = c_1^2 V_{2a} + c_2^2 V_{2b} + w^2 V_2 + (\delta w) V_1$. -/
theorem jacobson_two {T : Type*} [CommRing T] (h2 : (2 : T) = 0) (δ : T → T)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = δ a * b + a * δ b)
    (c₁ c₂ w : T) (hc₁ : δ c₁ = 0) (hc₂ : δ c₂ = 0) (V : ℕ → T) (a b : ℕ)
    (hV : ∀ m, δ (V m) = c₁ * V (m + a) + c₂ * V (m + b) + w * V (m + 1)) :
    δ (δ (V 0)) = c₁ ^ 2 * V (a + a) + c₂ ^ 2 * V (b + b) + w ^ 2 * V 2 + δ w * V 1 := by
  have hc : ∀ c v, δ c = 0 → δ (c * v) = c * δ v := fun c v h => by
    rw [hmul, h, zero_mul, zero_add]
  rw [hV 0, hadd, hadd, hc _ _ hc₁, hc _ _ hc₂, hmul, zero_add, zero_add, zero_add, hV a, hV b,
    hV 1, Nat.add_comm b a, Nat.add_comm 1 a, Nat.add_comm 1 b, show (1 + 1 : ℕ) = 2 from rfl]
  linear_combination (c₁ * c₂ * V (a + b) + c₁ * w * V (a + 1) + c₂ * w * V (b + 1)) * h2

local notation "H2" => Hur (ZMod 2)

lemma two_eq_zero : (2 : H2) = 0 := by
  have h : ((2 : ℕ) : H2) = 0 := by
    ext n
    rw [coeff_natCast, coeff_zero']
    split_ifs
    · decide
    · rfl
  exact_mod_cast h

lemma neg_eq_self' (f : H2) : -f = f := by
  linear_combination (-f) * two_eq_zero

lemma zmod_sq (r : ZMod 2) : r ^ 2 = r := by
  revert r
  decide

/-- Every square in characteristic two is a constant. -/
lemma sq_eq_C (f : H2) : f ^ 2 = C (f.coeff 0) := by
  have h1 : D (f ^ 2) = 0 := by
    rw [show f ^ 2 = f ^ (1 + 1) from rfl, D_pow]
    have h : ((1 + 1 : ℕ) : H2) = 0 := by exact_mod_cast two_eq_zero
    rw [h, zero_mul, zero_mul]
  rw [eq_C_of_D_eq_zero h1, ← coeff0_apply, map_pow, coeff0_apply, zmod_sq]

lemma D2_add (f g : H2) : D^[2] (f + g) = D^[2] f + D^[2] g := iterate_D_add f g 2

/-- $D^2$ is a derivation in characteristic two. -/
lemma D2_mul (f g : H2) : D^[2] (f * g) = D^[2] f * g + f * D^[2] g :=
  iterate_two_mul two_eq_zero D D_add D_mul f g

lemma D4_eq (f : H2) : D^[4] f = D^[2] (D^[2] f) := by
  simp only [← Function.iterate_add_apply]

lemma D8_eq (f : H2) : D^[8] f = D^[4] (D^[4] f) := by
  simp only [← Function.iterate_add_apply]

lemma D4_add (f g : H2) : D^[4] (f + g) = D^[4] f + D^[4] g := iterate_D_add f g 4

/-- $D^4$ is a derivation in characteristic two. -/
lemma D4_mul (f g : H2) : D^[4] (f * g) = D^[4] f * g + f * D^[4] g := by
  simp only [D4_eq]
  exact iterate_two_mul two_eq_zero (D^[2]) D2_add D2_mul f g

lemma C_sq (r : ZMod 2) : C r ^ 2 = C r := by
  rw [← C_pow, zmod_sq]

/-- The characteristic-two chain rule for $D^2$. -/
theorem D2_comp (f g : H2) :
    D^[2] (comp f g) = C (g.coeff 1) * comp (D^[2] f) g + D^[2] g * comp (D f) g := by
  have key := jacobson_two two_eq_zero D D_add D_mul 0 0 (D g) D_zero D_zero
    (fun m => comp (D^[m] f) g) 0 0 (fun m => by
      rw [D_comp, ← Function.iterate_succ_apply' D m f]
      ring)
  rw [sq_eq_C (D g)] at key
  change D^[2] (comp f g) = 0 ^ 2 * comp (D^[0 + 0] f) g + 0 ^ 2 * comp (D^[0 + 0] f) g +
    C ((D g).coeff 0) * comp (D^[2] f) g + D^[2] g * comp (D f) g at key
  rw [key, coeff_D]
  ring

/-- The characteristic-two chain rule for $D^4$. -/
theorem D4_comp (f g : H2) :
    D^[4] (comp f g) = C (g.coeff 1) * comp (D^[4] f) g + C (g.coeff 2) * comp (D^[2] f) g +
      D^[4] g * comp (D f) g := by
  have key := jacobson_two two_eq_zero (D^[2]) D2_add D2_mul (C (g.coeff 1)) 0 (D^[2] g)
    (iterate_D_C _ 1) (Function.iterate_fixed D_zero 2) (fun m => comp (D^[m] f) g) 2 0
    (fun m => by
      rw [D2_comp, ← Function.iterate_add_apply, ← Function.iterate_succ_apply' D m f,
        Nat.add_comm 2 m]
      ring)
  rw [C_sq, sq_eq_C (D^[2] g), coeff_iterate_D] at key
  simp only [← D4_eq] at key
  change D^[4] (comp f g) = C (g.coeff 1) * comp (D^[4] f) g + 0 ^ 2 * comp (D^[0] f) g +
    C (g.coeff (0 + 2)) * comp (D^[2] f) g + D^[4] g * comp (D f) g at key
  rw [key, zero_add]
  ring

/-- The characteristic-two chain rule for $D^8$. -/
theorem D8_comp (f g : H2) :
    D^[8] (comp f g) = C (g.coeff 1) * comp (D^[8] f) g + C (g.coeff 2) * comp (D^[4] f) g +
      C (g.coeff 4) * comp (D^[2] f) g + D^[8] g * comp (D f) g := by
  have key := jacobson_two two_eq_zero (D^[4]) D4_add D4_mul (C (g.coeff 1)) (C (g.coeff 2))
    (D^[4] g) (iterate_D_C _ 3) (iterate_D_C _ 3) (fun m => comp (D^[m] f) g) 4 2
    (fun m => by
      rw [D4_comp, ← Function.iterate_add_apply, ← Function.iterate_add_apply,
        ← Function.iterate_succ_apply' D m f, Nat.add_comm 4 m, Nat.add_comm 2 m])
  rw [C_sq, C_sq, sq_eq_C (D^[4] g), coeff_iterate_D] at key
  simp only [← D8_eq] at key
  change D^[8] (comp f g) = C (g.coeff 1) * comp (D^[8] f) g + C (g.coeff 2) * comp (D^[4] f) g +
    C (g.coeff (0 + 4)) * comp (D^[2] f) g + D^[8] g * comp (D f) g at key
  rw [key, zero_add]

/-- The series $f$ over $\mathbb{F}_2$ with $f_{n+8} = f_{n+4}$ for all $n$. -/
def InK (f : H2) : Prop := D^[8] f = D^[4] f

lemma inK_iff (f : H2) : InK f ↔ ∀ n, f.coeff (n + 8) = f.coeff (n + 4) := by
  constructor
  · intro h n
    have := congrArg (fun g => Hur.coeff g n) h
    simpa [coeff_iterate_D] using this
  · intro h
    ext n
    rw [coeff_iterate_D, coeff_iterate_D, h]

lemma inK_add {f g : H2} (hf : InK f) (hg : InK g) : InK (f + g) := by
  unfold InK at *
  rw [iterate_D_add, iterate_D_add, hf, hg]

lemma inK_one : InK (1 : H2) := by
  unfold InK
  rw [← C_one, iterate_D_C, iterate_D_C]

lemma inK_x : InK (x : H2) := by
  have h4 : D^[4] (x : H2) = 0 := by
    change D^[2 + 1] (D x) = 0
    rw [D_x, ← C_one]
    exact iterate_D_C 1 2
  unfold InK
  rw [h4, D8_eq, h4, Function.iterate_fixed D_zero]

/-- Composition with an outer series satisfying $D^2 f = f$ preserves `InK` when $g_4 = 0$. -/
theorem inK_comp {f g : H2} (hf : D^[2] f = f) (hg : InK g) (hg4 : g.coeff 4 = 0) :
    InK (comp f g) := by
  have hf4 : D^[4] f = f := by rw [D4_eq, hf, hf]
  have hf8 : D^[8] f = f := by rw [D8_eq, hf4, hf4]
  unfold InK at *
  rw [D8_comp, D4_comp, hf8, hf4, hf, hg, hg4, C_zero, zero_mul, add_zero]

/-- Two series in `InK` that agree below index $8$ are equal. -/
lemma inK_eq_of_lt {f g : H2} (hf : InK f) (hg : InK g)
    (h : ∀ n < 8, f.coeff n = g.coeff n) : f = g := by
  rw [inK_iff] at hf hg
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 8
    · exact h n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      rw [hf, hg]
      exact ih (m + 4) (by omega)

/-- The even part of $e^x$: coefficient $1$ at even indices. -/
def cosh : H2 := ⟨fun k => if k % 2 = 0 then 1 else 0⟩

/-- The odd part of $e^x$: coefficient $1$ at odd indices. -/
def sinh : H2 := ⟨fun k => if k % 2 = 1 then 1 else 0⟩

lemma D2_cosh : D^[2] cosh = cosh := by
  ext n
  rw [coeff_iterate_D]
  simp only [cosh, Nat.add_mod_right]

lemma D2_sinh : D^[2] sinh = sinh := by
  ext n
  rw [coeff_iterate_D]
  simp only [sinh, Nat.add_mod_right]

lemma x_sq : (x : H2) ^ 2 = 0 := by
  apply ext_D
  · rw [← coeff0_apply, map_pow, coeff0_apply]
    rfl
  · rw [show (x : H2) ^ 2 = x ^ (1 + 1) from rfl, D_pow, D_x, D_zero]
    have h : ((1 + 1 : ℕ) : H2) = 0 := by exact_mod_cast two_eq_zero
    rw [h, zero_mul, zero_mul]

lemma one_add_x_sq : (1 + x : H2) ^ 2 = 1 := by
  linear_combination x * two_eq_zero + x_sq

lemma one_add_x_pow (n : ℕ) : (1 + x : H2) ^ n = if n % 2 = 0 then 1 else 1 + x := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [pow_mul, one_add_x_sq, one_pow, ite_eq_left (by omega)]
  · rw [pow_succ, pow_mul, one_add_x_sq, one_pow, one_mul, ite_eq_right (by omega)]

lemma dpow_eq_of_D_eq {g g' : Hur (ZMod 2)} (h : D g = D g') (k : ℕ) : dpow g k = dpow g' k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dpow, dpow, ih, h]

/-- Over $\mathbb{F}_2$ with $Q = 1 + x$, Hanna's sum is $\cosh(B) + \sinh(B + x)$. -/
theorem ser_two (B : H2) : Ser (1 + x) B = comp cosh B + comp sinh (B + x) := by
  ext m
  simp only [Ser, comp, coeff_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [one_add_x_pow]
  by_cases hn : n % 2 = 0
  · have hD : D (1 - B) = D B := by rw [D_sub, D_one, zero_sub, neg_eq_self']
    rw [ite_eq_left hn, dpow_eq_of_D_eq hD]
    simp [cosh, sinh, hn]
  · have hD : D (1 + x - B) = D (B + x) := by
      rw [D_sub, D_add, D_add, D_one, D_x]
      linear_combination (-D B) * two_eq_zero
    rw [ite_eq_right hn, dpow_eq_of_D_eq hD]
    have hn' : n % 2 = 1 := by omega
    simp [cosh, sinh, hn']

end Two

/-! ### The parity pattern -/

section Pattern

local notation "H2" => Hur (ZMod 2)

/-- The parity pattern: $1$ exactly at $k \in \{0, 1, 3\}$ and at $k \equiv 2 \pmod 4$. -/
def patSeq (k : ℕ) : ZMod 2 := if k = 0 ∨ k = 1 ∨ k = 3 ∨ k % 4 = 2 then 1 else 0

/-- The parity pattern as a Hurwitz series over $\mathbb{F}_2$. -/
def pat : H2 := ⟨patSeq⟩

lemma patSeq_of_ge {m : ℕ} (hm : 4 ≤ m) : patSeq m = if m % 4 = 2 then 1 else 0 := by
  unfold patSeq
  simp only [show (m = 0 ∨ m = 1 ∨ m = 3 ∨ m % 4 = 2) ↔ m % 4 = 2 by omega]

lemma inK_pat : InK pat := by
  rw [inK_iff]
  intro n
  change patSeq (n + 8) = patSeq (n + 4)
  rw [patSeq_of_ge (by omega), patSeq_of_ge (by omega), show (n + 8) % 4 = (n + 4) % 4 by omega]

/-- The finite check: $\cosh(P) + \sinh(P + x)$ agrees with $1$ below index $8$. -/
lemma ser_pat_lt :
    ∀ n < 8, (comp cosh pat + comp sinh (pat + x)).coeff n = (1 : H2).coeff n := by
  decide +kernel

/-- The parity pattern solves Hanna's equation over $\mathbb{F}_2$. -/
theorem ser_pat : Ser (1 + x) pat = 1 := by
  rw [ser_two]
  refine inK_eq_of_lt ?_ inK_one ser_pat_lt
  exact inK_add (inK_comp D2_cosh inK_pat (by decide))
    (inK_comp D2_sinh (inK_add inK_pat inK_x) (by decide))

theorem T_pat : T (1 + x) pat = pat := (solH_iff _ _).1 ⟨by decide, ser_pat⟩

/-- If $Q \equiv 1 + x \pmod 2$, the fixed point of `T Q` over $\mathbb{Z}$ reduces to the
parity pattern. -/
theorem map_fix_two (Q : Hur ℤ) (hQ : map (Int.castRingHom (ZMod 2)) Q = 1 + x) :
    map (Int.castRingHom (ZMod 2)) (fix Q) = pat := by
  rw [map_fix, hQ]
  exact T_fixed_unique _ (T_fix _) T_pat

lemma patSeq_eq_one_iff (k : ℕ) : patSeq k = 1 ↔ (k = 0 ∨ k = 1 ∨ k = 3 ∨ k % 4 = 2) := by
  unfold patSeq
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

end Pattern

lemma coeff_partial {R : Type*} [CommRing R] (Q B : Hur R) {N m : ℕ} (h : m < N) :
    (∑ n ∈ Finset.range N, dpow (Q ^ n - B) n).coeff m = (Ser Q B).coeff m := by
  rw [coeff_sum]
  change _ = ∑ n ∈ Finset.range (m + 1), (dpow (Q ^ n - B) n).coeff m
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    exact dpow_coeff_lt _ (by omega)

lemma fix_coeff_eq_iterate {R : Type*} [CommRing R] (Q : Hur R) (k n : ℕ) (h : n < k) :
    (fix Q).coeff n = ((T Q)^[k] 0).coeff n := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← T_fix]
    apply T_causal
    intro j hj
    exact ih j (by omega)

end Hur

/-! ### Power series -/

section Bridge

open PowerSeries Hur

/-- The Hurwitz series of EGF coefficients $n!\,[x^n] F$ of a rational power series. -/
noncomputable def jetFun (F : ℚ⟦X⟧) : Hur ℚ := ⟨fun n => (n.factorial : ℚ) * coeff n F⟩

lemma jetFun_coeff (F : ℚ⟦X⟧) (n : ℕ) : (jetFun F).coeff n = (n.factorial : ℚ) * coeff n F := rfl

lemma jetFun_derivative (F : ℚ⟦X⟧) : jetFun (derivative (R := ℚ) F) = D (jetFun F) := by
  ext n
  simp only [jetFun_coeff, coeff_D, coeff_derivative, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

lemma jetFun_add (F G : ℚ⟦X⟧) : jetFun (F + G) = jetFun F + jetFun G := by
  ext n
  simp [jetFun_coeff, mul_add]

lemma jetFun_mul (F G : ℚ⟦X⟧) : jetFun (F * G) = jetFun F * jetFun G := by
  suffices h : ∀ n, ∀ F G : ℚ⟦X⟧, (jetFun (F * G)).coeff n = (jetFun F * jetFun G).coeff n from
    Hur.ext (funext fun n => h n F G)
  intro n
  induction n with
  | zero => intro F G; simp [jetFun_coeff]
  | succ n ih =>
    intro F G
    rw [← coeff_D, ← coeff_D, ← jetFun_derivative, (derivative (R := ℚ)).leibniz, smul_eq_mul,
      smul_eq_mul, jetFun_add, coeff_add, ih, ih, D_mul, coeff_add, jetFun_derivative,
      jetFun_derivative, add_comm, mul_comm (jetFun G) (D (jetFun F))]

/-- EGF coefficients as a ring homomorphism $\mathbb{Q}[[x]] \to H(\mathbb{Q})$. -/
noncomputable def jet : ℚ⟦X⟧ →+* Hur ℚ where
  toFun := jetFun
  map_one' := by
    ext n
    rw [jetFun_coeff, PowerSeries.coeff_one, Hur.coeff_one]
    split_ifs with h
    · subst h
      simp
    · simp
  map_mul' := jetFun_mul
  map_zero' := by
    ext n
    simp [jetFun_coeff]
  map_add' := jetFun_add

lemma jet_coeff (F : ℚ⟦X⟧) (n : ℕ) : (jet F).coeff n = (n.factorial : ℚ) * coeff n F := rfl

lemma jet_derivative (F : ℚ⟦X⟧) : jet (derivative (R := ℚ) F) = D (jet F) := jetFun_derivative F

lemma jet_injective : Function.Injective jet := by
  intro F G h
  ext n
  have he := congrArg (fun H => Hur.coeff H n) h
  simp only [jet_coeff] at he
  exact mul_left_cancel₀ (by exact_mod_cast n.factorial_ne_zero) he

lemma jet_X : jet (X : ℚ⟦X⟧) = x := by
  ext n
  rw [jet_coeff, coeff_X]
  simp only [x]
  split_ifs with h
  · subst h
    simp
  · simp

/-- For $g$ without constant term, the Hurwitz series of $g^n / n!$ is the divided power
$g^{[n]}$. -/
theorem jet_dpow (g : ℚ⟦X⟧) (hg : constantCoeff g = 0) (n : ℕ) :
    jet ((n.factorial : ℚ)⁻¹ • g ^ n) = dpow (jet g) n := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, dpow_zero, map_one]
  | succ n ih =>
    apply ext_D
    · rw [jet_coeff, dpow_coeff_lt _ (Nat.succ_pos n), PowerSeries.coeff_smul,
        coeff_zero_eq_constantCoeff_apply, map_pow, hg]
      simp
    · have hd : derivative (R := ℚ) (((n + 1).factorial : ℚ)⁻¹ • g ^ (n + 1)) =
          ((n.factorial : ℚ)⁻¹ • g ^ n) * derivative (R := ℚ) g := by
        rw [Derivation.map_smul, derivative_pow, Nat.add_sub_cancel, mul_assoc, ← nsmul_eq_mul,
          ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_mul_assoc]
        congr 1
        have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
        rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp
      rw [← jet_derivative, hd, map_mul, ih, jet_derivative, D_dpow_succ]

lemma jet_partial (q A : ℚ⟦X⟧) (hq : constantCoeff q = 1) (hA : constantCoeff A = 1) (N : ℕ) :
    jet (∑ n ∈ Finset.range N, (n.factorial : ℚ)⁻¹ • (q ^ n - A) ^ n) =
      ∑ n ∈ Finset.range N, dpow (jet q ^ n - jet A) n := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [jet_dpow _ (by simp [hq, hA]), map_sub, map_pow]

/-- A solution has constant term $1$: otherwise the constant terms of the partial sums never
stabilize. -/
theorem constantCoeff_of_isSolution {q A : ℚ⟦X⟧} (hq : constantCoeff q = 1)
    (h : IsSolution q A) : constantCoeff A = 1 := by
  obtain ⟨N, hN⟩ := h 0
  have h3 : coeff 0 (((N + 1).factorial : ℚ)⁻¹ • (q ^ (N + 1) - A) ^ (N + 1)) = 0 := by
    have h2 := hN (N + 2) (by omega)
    rw [Finset.sum_range_succ, map_add, hN (N + 1) (by omega)] at h2
    linear_combination h2
  rw [PowerSeries.coeff_smul, coeff_zero_eq_constantCoeff_apply, map_pow, map_sub, map_pow, hq,
    one_pow, smul_eq_mul] at h3
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd h4 (inv_ne_zero (by exact_mod_cast (N + 1).factorial_ne_zero))
  · exact (sub_eq_zero.1 (pow_eq_zero_iff (Nat.succ_ne_zero N) |>.1 h4)).symm

theorem solH_of_isSolution {q A : ℚ⟦X⟧} (hq : constantCoeff q = 1) (h : IsSolution q A) :
    SolH (jet q) (jet A) := by
  have hA := constantCoeff_of_isSolution hq h
  refine ⟨by rw [jet_coeff, coeff_zero_eq_constantCoeff_apply, hA]; simp, ?_⟩
  ext m
  obtain ⟨N, hN⟩ := h m
  rw [← coeff_partial _ _ (show m < max N (m + 1) by omega), ← jet_partial q A hq hA, jet_coeff,
    hN _ (le_max_left _ _), ← jet_coeff, map_one]

theorem isSolution_of_solH {q A : ℚ⟦X⟧} (hq : constantCoeff q = 1) (h : SolH (jet q) (jet A)) :
    IsSolution q A := by
  have hA : constantCoeff A = 1 := by
    have h0 := h.1
    rw [jet_coeff, coeff_zero_eq_constantCoeff_apply] at h0
    simpa using h0
  intro m
  refine ⟨m + 1, fun N hN => ?_⟩
  have h1 := congrArg (fun F => Hur.coeff F m) h.2
  rw [← coeff_partial _ _ (show m < N by omega), ← jet_partial q A hq hA, ← map_one jet,
    jet_coeff, jet_coeff] at h1
  exact mul_left_cancel₀ (by exact_mod_cast m.factorial_ne_zero) h1

/-- The exponential generating series of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ) / n.factorial

lemma jet_egf (a : ℕ → ℤ) : jet (egf a) = map (Int.castRingHom ℚ) ⟨a⟩ := by
  ext n
  rw [jet_coeff, egf, coeff_mk, Hur.coeff_map]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp only [eq_intCast]
  field_simp

/-- The general result: if the EGF coefficients of $q$ are integers $Q_n$ with $Q_0 = 1$ and
$Q \equiv 1 + x \pmod 2$, then Hanna's equation has a unique solution, its EGF coefficients are
integers, and they are odd exactly at $k \in \{0, 1, 3\}$ and $k \equiv 2 \pmod 4$. -/
theorem main (q : ℚ⟦X⟧) (Qz : Hur ℤ) (hq0 : constantCoeff q = 1)
    (hq : jet q = map (Int.castRingHom ℚ) Qz) (h2 : map (Int.castRingHom (ZMod 2)) Qz = 1 + x) :
    (∃! A : ℚ⟦X⟧, IsSolution q A) ∧ ∀ A : ℚ⟦X⟧, IsSolution q A → ∀ k : ℕ,
      (k.factorial : ℚ) * coeff k A = (fix Qz).coeff k ∧
      (Odd ((fix Qz).coeff k) ↔ k = 0 ∨ k = 1 ∨ k = 3 ∨ k % 4 = 2) := by
  have hB : T (jet q) (map (Int.castRingHom ℚ) (fix Qz)) = map (Int.castRingHom ℚ) (fix Qz) := by
    rw [hq, ← map_T, T_fix]
  have hjet : ∀ A, IsSolution q A → jet A = map (Int.castRingHom ℚ) (fix Qz) := fun A hA =>
    T_fixed_unique _ ((solH_iff _ _).1 (solH_of_isSolution hq0 hA)) hB
  have hex : IsSolution q (egf (fix Qz).coeff) := by
    apply isSolution_of_solH hq0
    rw [solH_iff, jet_egf]
    exact hB
  refine ⟨⟨_, hex, fun A hA => jet_injective (by rw [hjet A hA, hjet _ hex])⟩, ?_⟩
  intro A hA k
  refine ⟨?_, ?_⟩
  · rw [← jet_coeff, hjet A hA, Hur.coeff_map]
    rfl
  · rw [← ZMod.intCast_eq_one_iff_odd, ← patSeq_eq_one_iff]
    have h := congrArg (fun F => Hur.coeff F k) (map_fix_two Qz h2)
    exact Iff.of_eq (congrArg (· = (1 : ZMod 2)) h)

end Bridge

/-! ### The two OEIS entries -/

section Main

open PowerSeries Hur

lemma jet_one_add_X : jet (1 + X : ℚ⟦X⟧) = Hur.map (Int.castRingHom ℚ) (1 + x) := by
  rw [map_add, map_one, jet_X, ← mapHom_apply, map_add, map_one, mapHom_apply, map_x]

lemma map_two_one_add_x : Hur.map (Int.castRingHom (ZMod 2)) (1 + x : Hur ℤ) = 1 + x := by
  rw [← mapHom_apply, map_add, map_one, mapHom_apply, map_x]

/-- The EGF coefficients $n!$ of $1/(1-x)$. -/
def factSeq : Hur ℤ := ⟨fun n => (n.factorial : ℤ)⟩

lemma coeff_inv_one_sub_X (n : ℕ) : coeff n ((1 - X : ℚ⟦X⟧)⁻¹) = 1 := by
  have h : (1 - X : ℚ⟦X⟧)⁻¹ = PowerSeries.mk 1 :=
    (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).2 (mk_one_mul_one_sub_eq_one ℚ)
  rw [h, coeff_mk]
  rfl

lemma jet_inv_one_sub_X : jet ((1 - X : ℚ⟦X⟧)⁻¹) = Hur.map (Int.castRingHom ℚ) factSeq := by
  ext n
  rw [jet_coeff, coeff_inv_one_sub_X, mul_one, Hur.coeff_map]
  simp [factSeq]

lemma map_two_factSeq : Hur.map (Int.castRingHom (ZMod 2)) factSeq = 1 + x := by
  ext n
  rw [Hur.coeff_map, coeff_add, Hur.coeff_one]
  simp only [factSeq, x, eq_intCast, Int.cast_natCast]
  rcases n with _ | _ | n
  · simp
  · simp
  · have h : 2 ∣ (n + 2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    rw [(ZMod.natCast_eq_zero_iff _ 2).2 h]
    simp

/-- OEIS A326097: exactly one $A(x) \in \mathbb{Q}[[x]]$ satisfies
$1 = \sum_{n \ge 0} ((1+x)^n - A(x))^n / n!$. -/
theorem a326097_existsUnique : ∃! A : ℚ⟦X⟧, IsSolution (1 + X) A :=
  (main (1 + X) (1 + x) (by simp) jet_one_add_X map_two_one_add_x).1

/-- Hanna's parity conjecture for OEIS A326097, in the stronger form: every
$a(k) = k!\,[x^k] A(x)$ is an integer, and $a(k)$ is odd if and only if $k \in \{0, 1, 3\}$ or
$k \equiv 2 \pmod 4$. -/
theorem a326097_parity (A : ℚ⟦X⟧) (hA : IsSolution (1 + X) A) (k : ℕ) :
    ∃ a : ℤ, (k.factorial : ℚ) * coeff k A = a ∧ (Odd a ↔ k = 0 ∨ k = 1 ∨ k = 3 ∨ k % 4 = 2) :=
  ⟨_, (main (1 + X) (1 + x) (by simp) jet_one_add_X map_two_one_add_x).2 A hA k⟩

/-- OEIS A385907: exactly one $A(x) \in \mathbb{Q}[[x]]$ satisfies
$1 = \sum_{n \ge 0} (1/(1-x)^n - A(x))^n / n!$. -/
theorem a385907_existsUnique : ∃! A : ℚ⟦X⟧, IsSolution (1 - X)⁻¹ A :=
  (main (1 - X)⁻¹ factSeq (by simp) jet_inv_one_sub_X map_two_factSeq).1

/-- The parity pattern of OEIS A385907: every $a(k) = k!\,[x^k] A(x)$ is an integer, and $a(k)$
is odd if and only if $k \in \{0, 1, 3\}$ or $k \equiv 2 \pmod 4$. -/
theorem a385907_parity (A : ℚ⟦X⟧) (hA : IsSolution (1 - X)⁻¹ A) (k : ℕ) :
    ∃ a : ℤ, (k.factorial : ℚ) * coeff k A = a ∧ (Odd a ↔ k = 0 ∨ k = 1 ∨ k = 3 ∨ k % 4 = 2) :=
  ⟨_, (main (1 - X)⁻¹ factSeq (by simp) jet_inv_one_sub_X map_two_factSeq).2 A hA k⟩

/-! ### Sanity checks: the first terms agree with the OEIS data -/

lemma values_326097 : ∀ n < 6, ((T (1 + x : Hur ℤ))^[6] 0).coeff n =
    [1, 1, 1, 11, 160, 3634].getD n 0 := by
  decide +kernel

lemma values_385907 : ∀ n < 6, ((T factSeq)^[6] 0).coeff n =
    [1, 1, 3, 23, 352, 8514].getD n 0 := by
  decide +kernel

/-- The first terms of OEIS A326097: $1, 1, 1, 11, 160, 3634$. -/
theorem a326097_first_terms (A : ℚ⟦X⟧) (hA : IsSolution (1 + X) A) :
    ∀ k < 6, (k.factorial : ℚ) * coeff k A = ([1, 1, 1, 11, 160, 3634].getD k 0 : ℤ) := by
  intro k hk
  rw [((main (1 + X) (1 + x) (by simp) jet_one_add_X map_two_one_add_x).2 A hA k).1,
    fix_coeff_eq_iterate _ 6 k hk, values_326097 k hk]

/-- The first terms of OEIS A385907: $1, 1, 3, 23, 352, 8514$. -/
theorem a385907_first_terms (A : ℚ⟦X⟧) (hA : IsSolution (1 - X)⁻¹ A) :
    ∀ k < 6, (k.factorial : ℚ) * coeff k A = ([1, 1, 3, 23, 352, 8514].getD k 0 : ℤ) := by
  intro k hk
  rw [((main (1 - X)⁻¹ factSeq (by simp) jet_inv_one_sub_X map_two_factSeq).2 A hA k).1,
    fix_coeff_eq_iterate _ 6 k hk, values_385907 k hk]

end Main

end OeisA326097

end
