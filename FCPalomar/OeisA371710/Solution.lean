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
# OEIS A371710: Hanna's mod-3 pattern

Let $A(x) = \sum_{n \ge 1} a(n) x^n / n!$ satisfy $\sum_{n \ge 0} (A(x)^n - x)^n / n! = 1$, with
the sum taken coefficientwise. The file proves that $A$ exists and is unique, that every $a(m)$ is
an integer, and that modulo $3$, $a(m) \equiv 2$ for even $m \ge 2$ and $a(m) \equiv 1 - m$ for
odd $m \ge 3$. This settles Paul D. Hanna's conjecture
$a(6n + k) \equiv [2, 0, 2, 1, 2, 2]_k \pmod 3$ for $n > 0$.

The proof works with Hurwitz series: sequences $f_n = n!\,[x^n] f$ with the binomial product, on
which $D$ is the shift. The divided power $g^{[k]}$ is defined by $g^{[0]} = 1$,
$D g^{[k+1]} = g^{[k]} D g$ and constant term $0$, so it exists over every commutative ring.
Over $\mathbb{Q}$ it is $(g - g_0)^k / k!$. Write $B$ for the Hurwitz series of $A$.

*Reduction to Hurwitz series.* For $n \ge 1$ the constant term of the $n$-th term is
$A(0)^{n^2} / n!$, so the partial sums stabilize at $x^0$ only if $A(0) = 0$. Then the $n$-th term
is $(B^n - x)^{[n]}$, which vanishes below index $n$. So the equation says $B_0 = 0$ and
$\sum_{n \le m} (B^n - x)^{[n]}_m = [m = 0]$ for every $m$.

*Existence, uniqueness and integrality.* For $m \ge 1$, the term $n = 1$ contributes $B_m - x_m$
at index $m$, and the terms $n \ge 2$ only use $B_0, \dots, B_{m-1}$. So the equation is a
fixed-point equation $T(B) = B$ for an operator $T$ whose coefficient $m$ only uses coefficients
of $B$ below $m$. Over every commutative ring, $T$ has exactly one fixed point, built one
coefficient at a time. The image of the integer fixed point is a fixed point over $\mathbb{Q}$, so
by uniqueness it is the Hurwitz series of every rational solution.

*Reduction modulo $3$.* Over every commutative ring, $g^n = n!\,g^{[n]}$ and $g^{[1]} = g$ when
$g_0 = 0$. Over $\mathbb{F}_3$ this gives $g^n = 0$ for $n \ge 3$ and $g^{[2]} = -g^2$. So for
$B_0 = 0$ the terms $n \ge 3$ do not depend on $B$, and at $B = 0$ the whole sum is $e^{-x}$.
The equation over $\mathbb{F}_3$ becomes $e^{-x} + B - x B^2 = 1$. This is the classical
divided-power reduction; trureturing issue #24628 applies it to the similar equation of OEIS
A386648.

*The finite check.* In characteristic $3$, $D^3$ and $D^9 = (D^3)^3$ are derivations. So the
series $f$ with $D^9 f = D^3 f$, that is $f_{n+9} = f_{n+3}$ for all $n$, form a subring. It
contains $1$, $x$, $e^{-x}$ and the pattern $P$ with $P_0 = 0$, $P_1 = 1$, and $P_m = 2$ for even
$m \ge 2$ and $P_m = 1 - m$ for odd $m \ge 3$, which has period $6$ from index $2$. Hence
$e^{-x} + P - x P^2 - 1$ lies in the subring, and it is zero because its first $9$ coefficients
are zero; a kernel computation checks these. So $P$ is the fixed point over $\mathbb{F}_3$, and by
uniqueness it is the reduction of $(a(m))$ modulo $3$.

*References:*
- Paul D. Hanna, [A371710](https://oeis.org/A371710), April 10, 2024.
- [trureturing issue #24628](https://github.com/the-omega-institute/trureturing/issues/24628),
  October 31, 2026: the divided-power reduction for OEIS A386648.
-/

@[expose] public section

namespace OeisA371710

open PowerSeries

/-- Hanna's equation $\sum_{n \ge 0} (A(x)^n - x)^n / n! = 1$. The infinite sum is taken
coefficientwise: for every $m$, the coefficient of $x^m$ in the partial sums $\sum_{n < N}$ equals
that of $1$ for all large $N$. -/
def IsSolution (A : ℚ⟦X⟧) : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, ∀ N' ≥ N,
    coeff m (∑ n ∈ Finset.range N', (n.factorial : ℚ)⁻¹ • (A ^ n - X) ^ n) = coeff m (1 : ℚ⟦X⟧)

end OeisA371710

namespace OeisA371710

/-! ### Hurwitz series

The Hurwitz-series library below (ring structure, derivative, divided powers and coefficient
maps), the fixed-point operator and the bridge to power series are adapted from this
repository's A326097 package (Wentao Li, Apache-2.0). -/

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

/-- Differentiation of Hurwitz series is the shift. -/
def D (f : Hur R) : Hur R := ⟨shift f.coeff⟩

omit [CommRing R] in
@[simp] lemma coeff_D (f : Hur R) (n : ℕ) : (D f).coeff n = f.coeff (n + 1) := rfl

lemma D_add (f g : Hur R) : D (f + g) = D f + D g := rfl
lemma D_zero : D (0 : Hur R) = 0 := rfl
lemma D_mul (f g : Hur R) : D (f * g) = D f * g + f * D g := rfl

omit [CommRing R] in
/-- Two series with equal constant terms and equal derivatives are equal. -/
lemma ext_D {f g : Hur R} (h0 : f.coeff 0 = g.coeff 0) (hD : D f = D g) : f = g := by
  ext n
  cases n with
  | zero => exact h0
  | succ n => exact congrArg (fun h => Hur.coeff h n) hD

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

/-- The EGF variable $x$. -/
def x : Hur R := ⟨fun n => if n = 1 then 1 else 0⟩

lemma D_x : D (x : Hur R) = 1 := by
  ext n
  cases n <;> simp [x, coeff_one]

end Ring

section DividedPowers
variable {R : Type*} [CommRing R]

/-- The `n`-th coefficient as an additive map. -/
def coeffAdd (n : ℕ) : Hur R →+ R where
  toFun f := f.coeff n
  map_zero' := rfl
  map_add' _ _ := rfl

lemma coeff_sum {ι : Type*} (s : Finset ι) (F : ι → Hur R) (n : ℕ) :
    (∑ i ∈ s, F i).coeff n = ∑ i ∈ s, (F i).coeff n :=
  map_sum (coeffAdd n) F s

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

end DividedPowers

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

lemma D_neg (f : Hur R) : D (-f) = -D f := rfl

lemma D_natCast (n : ℕ) : D (n : Hur R) = 0 := by
  ext k
  simp [coeff_natCast]

lemma coeff_zero_pow (f : Hur R) (k : ℕ) : (f ^ k).coeff 0 = f.coeff 0 ^ k := by
  rw [← coeff0_apply, map_pow, coeff0_apply]

lemma x_coeff_zero : (x : Hur R).coeff 0 = 0 := rfl

/-- A coefficient of $f^j$ only uses coefficients of $f$ of the same or lower index. -/
lemma pow_coeff_congr (f g : Hur R) (n : ℕ) (h : ∀ k ≤ n, f.coeff k = g.coeff k) (j : ℕ) :
    ∀ k ≤ n, (f ^ j).coeff k = (g ^ j).coeff k := by
  induction j with
  | zero => intro k _; rfl
  | succ j ih =>
    intro k hk
    rw [pow_succ, pow_succ]
    exact coeff_mul_congr _ _ _ _ k (fun i hi => ih i (by omega)) (fun i hi => h i (by omega))

/-- $g^n = n!\,g^{[n]}$ when $g_0 = 0$, over every commutative ring. -/
lemma pow_eq_factorial_mul_dpow (g : Hur R) (hg : g.coeff 0 = 0) (n : ℕ) :
    g ^ n = (n.factorial : Hur R) * dpow g n := by
  induction n with
  | zero => simp [dpow_zero]
  | succ n ih =>
    apply ext_D
    · rw [coeff_zero_pow, hg, zero_pow (Nat.succ_ne_zero n), coeff_mul_zero,
        dpow_coeff_lt g (Nat.succ_pos n), mul_zero]
    · rw [D_pow, D_mul, D_natCast, zero_mul, zero_add, D_dpow_succ, ih, Nat.factorial_succ]
      push_cast
      ring

lemma dpow_one_of (g : Hur R) (hg : g.coeff 0 = 0) : dpow g 1 = g :=
  ext_D (by rw [hg]; rfl) (by rw [D_dpow_succ, dpow_zero, one_mul])

/-- The divided powers of $-x$: $(-x)^{[n]} = (-1)^n x^n / n!$. -/
lemma coeff_dpow_neg_x (n m : ℕ) :
    (dpow (-x : Hur R) n).coeff m = if m = n then (-1) ^ n else 0 := by
  induction n generalizing m with
  | zero => simp [dpow_zero, coeff_one]
  | succ n ih =>
    cases m with
    | zero => rw [dpow_coeff_lt _ (Nat.succ_pos n), ite_eq_right (by omega)]
    | succ m =>
      change (dpow (-x : Hur R) n * D (-x)).coeff m = _
      rw [D_neg, D_x, mul_neg_one, coeff_neg, ih]
      by_cases h : m = n <;> simp [h, pow_succ]

/-- Hanna's sum $\sum_n (B^n - x)^{[n]}$, where $f^{[n]}$ is the divided power of $f - f_0$. At
coefficient $m$ the terms with $n > m$ vanish, so the sum is finite there. -/
def Ser (B : Hur R) : Hur R :=
  ⟨fun m => ∑ n ∈ Finset.range (m + 1), (dpow (B ^ n - x) n).coeff m⟩

/-- The Hurwitz form of Hanna's equation: $B_0 = 0$ and $\sum_n (B^n - x)^{[n]} = 1$. -/
def SolH (B : Hur R) : Prop := B.coeff 0 = 0 ∧ Ser B = 1

/-- The fixed-point operator of Hanna's equation: its fixed points are the solutions. -/
def T (B : Hur R) : Hur R :=
  ⟨fun m => if m = 0 then 0 else B.coeff m - (Ser B).coeff m⟩

lemma ser_coeff_zero (B : Hur R) : (Ser B).coeff 0 = 1 := by
  simp [Ser, dpow_zero, coeff_one]

lemma ser_coeff_eq (B : Hur R) {N m : ℕ} (h : m < N) :
    (Ser B).coeff m = ∑ n ∈ Finset.range N, (dpow (B ^ n - x) n).coeff m := by
  change ∑ n ∈ Finset.range (m + 1), _ = _
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    exact dpow_coeff_lt _ (by omega)

/-- In $B - \sum_n (B^n - x)^{[n]}$ the term $B_{m+1}$ cancels against the term $n = 1$. -/
lemma T_coeff_succ (B : Hur R) (m : ℕ) :
    (T B).coeff (m + 1) = (x : Hur R).coeff (m + 1) -
      ∑ n ∈ Finset.range m, (dpow (B ^ (n + 2) - x) (n + 2)).coeff (m + 1) := by
  change (if m + 1 = 0 then 0 else
    B.coeff (m + 1) - ∑ n ∈ Finset.range (m + 1 + 1), (dpow (B ^ n - x) n).coeff (m + 1)) = _
  rw [ite_eq_right (by omega), Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : (dpow (B ^ 0 - x) 0).coeff (m + 1) = 0 := by
    rw [dpow_zero, coeff_one, ite_eq_right (by omega)]
  have h1 : (dpow (B ^ (0 + 1) - x) (0 + 1)).coeff (m + 1) =
      B.coeff (m + 1) - (x : Hur R).coeff (m + 1) := by
    rw [zero_add, pow_one, dpow_one_coeff_succ, coeff_sub]
  rw [h0, h1]
  ring

/-- Coefficient $n$ of `T B` only uses coefficients of `B` below $n$. -/
theorem T_causal (n : ℕ) (f g : Hur R) (h : ∀ k < n, f.coeff k = g.coeff k) :
    (T f).coeff n = (T g).coeff n := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [T_coeff_succ, T_coeff_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply dpow_congr_lt
    intro i hi
    rw [coeff_sub, coeff_sub,
      pow_coeff_congr f g i (fun k hk => h k (by omega)) (j + 2) i le_rfl]

/-- `T` has at most one fixed point. -/
theorem T_fixed_unique {f g : Hur R} (hf : T f = f) (hg : T g = g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    calc f.coeff n = (T f).coeff n := by rw [hf]
      _ = (T g).coeff n := T_causal n f g ih
      _ = g.coeff n := by rw [hg]

variable (R) in
/-- The coefficient recursion for the fixed point of `T`. -/
def fixSeq (n : ℕ) : R :=
  (T (⟨fun k => if _h : k < n then fixSeq k else 0⟩ : Hur R)).coeff n
termination_by n

variable (R) in
/-- The fixed point of `T`. -/
def fix : Hur R := ⟨fixSeq R⟩

theorem T_fix : T (fix R) = fix R := by
  ext n
  change (T (fix R)).coeff n = fixSeq R n
  rw [fixSeq]
  apply T_causal
  intro k hk
  simp [fix, hk]

/-- The solutions of Hanna's equation are the fixed points of `T`. -/
theorem solH_iff (B : Hur R) : SolH B ↔ T B = B := by
  constructor
  · rintro ⟨h0, h1⟩
    ext m
    cases m with
    | zero => exact h0.symm
    | succ m =>
      have h := congrArg (fun F => Hur.coeff F (m + 1)) h1
      simp only [coeff_one, ite_eq_right (Nat.succ_ne_zero m)] at h
      change (if m + 1 = 0 then 0 else B.coeff (m + 1) - (Ser B).coeff (m + 1)) = _
      rw [ite_eq_right (by omega), h, sub_zero]
  · intro h
    have hc : ∀ m, (T B).coeff m = B.coeff m := fun m => by rw [h]
    refine ⟨(hc 0).symm, ?_⟩
    ext m
    cases m with
    | zero => rw [ser_coeff_zero]; rfl
    | succ m =>
      have h' := hc (m + 1)
      change (if m + 1 = 0 then 0 else B.coeff (m + 1) - (Ser B).coeff (m + 1)) = _ at h'
      rw [ite_eq_right (by omega)] at h'
      rw [coeff_one, ite_eq_right (by omega)]
      linear_combination -h'

/-- If $T$ agrees with a candidate below $N$, so does the fixed point. -/
lemma fix_coeff_of_T (c : Hur R) (N : ℕ) (h : ∀ n < N, (T c).coeff n = c.coeff n) :
    ∀ n < N, (fix R).coeff n = c.coeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [← T_fix, T_causal n (fix R) c (fun k hk => ih k hk (by omega)), h n hn]

/-- Hanna's sum at $B = 0$ is $e^{-x}$. -/
def expNeg : Hur R := ⟨fun m => (-1) ^ m⟩

lemma ser_zero : Ser (0 : Hur R) = expNeg := by
  ext m
  change ∑ n ∈ Finset.range (m + 1), (dpow ((0 : Hur R) ^ n - x) n).coeff m = (-1) ^ m
  rw [Finset.sum_eq_single m]
  · cases m with
    | zero => simp [dpow_zero, coeff_one]
    | succ m => rw [zero_pow (Nat.succ_ne_zero m), zero_sub, coeff_dpow_neg_x, ite_eq_left rfl]
  · intro n _ hn
    cases n with
    | zero => rw [dpow_zero, coeff_one, ite_eq_right (Ne.symm hn)]
    | succ n =>
      rw [zero_pow (Nat.succ_ne_zero n), zero_sub, coeff_dpow_neg_x, ite_eq_right (Ne.symm hn)]
  · intro h
    simp at h

/-- If $B^n = 0$ for $n \ge 3$, only the terms $n = 1, 2$ of Hanna's sum depend on $B$. -/
lemma ser_eq_of_pow (B : Hur R) (hB : ∀ n, B ^ (n + 3) = 0) :
    Ser B = Ser 0 + (dpow (B - x) 1 - dpow (-x) 1) + (dpow (B ^ 2 - x) 2 - dpow (-x) 2) := by
  ext m
  simp only [coeff_add, coeff_sub]
  rw [ser_coeff_eq B (show m < 3 + m by omega), ser_coeff_eq 0 (show m < 3 + m by omega),
    Finset.sum_range_add, Finset.sum_range_add]
  have htail : ∀ k ∈ Finset.range m, (dpow (B ^ (3 + k) - x) (3 + k)).coeff m =
      (dpow ((0 : Hur R) ^ (3 + k) - x) (3 + k)).coeff m := by
    intro k _
    rw [add_comm 3 k, hB k, zero_pow (by omega)]
  rw [Finset.sum_congr rfl htail]
  have h2 : (0 : Hur R) ^ 2 = 0 := zero_pow two_ne_zero
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, h2, zero_sub,
    dpow_zero]
  ring

end Hanna

section MapHanna
variable {R S : Type*} [CommRing R] [CommRing S]

lemma map_Ser (φ : R →+* S) (B : Hur R) : map φ (Ser B) = Ser (map φ B) := by
  ext m
  simp only [Ser, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← coeff_map, map_dpow, ← mapHom_apply, map_sub, map_pow, mapHom_apply, mapHom_apply, map_x]

lemma map_T (φ : R →+* S) (B : Hur R) : map φ (T B) = T (map φ B) := by
  ext m
  rw [coeff_map]
  change φ (if m = 0 then 0 else B.coeff m - (Ser B).coeff m) =
    (if m = 0 then 0 else (map φ B).coeff m - (Ser (map φ B)).coeff m)
  split_ifs
  · exact map_zero φ
  · rw [map_sub, ← map_Ser]
    rfl

lemma map_fix (φ : R →+* S) : map φ (fix R) = fix S :=
  T_fixed_unique (by rw [← map_T, T_fix]) T_fix

end MapHanna

/-! ### Characteristic three -/

section Three

local notation "H3" => Hur (ZMod 3)

/-- Leibniz rule for the third iterate of a derivation in characteristic three. -/
theorem iterate_three_mul {S : Type*} [CommRing S] (h3 : (3 : S) = 0) (δ : S → S)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = δ a * b + a * δ b)
    (a b : S) : δ (δ (δ (a * b))) = δ (δ (δ a)) * b + a * δ (δ (δ b)) := by
  simp only [hmul, hadd]
  linear_combination (δ (δ a) * δ b + δ a * δ (δ b)) * h3

lemma natCast_eq_zero_of_dvd {n : ℕ} (h : 3 ∣ n) : (n : H3) = 0 := by
  ext k
  rw [coeff_natCast, coeff_zero']
  split_ifs
  · exact (ZMod.natCast_eq_zero_iff _ 3).2 h
  · rfl

lemma three_eq_zero : (3 : H3) = 0 := by
  have h : ((3 : ℕ) : H3) = 0 := natCast_eq_zero_of_dvd dvd_rfl
  exact_mod_cast h

/-- In characteristic three, $g^3 = 3!\,g^{[3]} = 0$ when $g_0 = 0$. -/
lemma pow_add_three_eq_zero (g : H3) (hg : g.coeff 0 = 0) (n : ℕ) : g ^ (n + 3) = 0 := by
  rw [pow_add, pow_eq_factorial_mul_dpow g hg 3,
    natCast_eq_zero_of_dvd (Nat.dvd_factorial (by norm_num) le_rfl), zero_mul, mul_zero]

/-- In characteristic three, $g^{[2]} = 2 g^2 = -g^2$ when $g_0 = 0$. -/
lemma dpow_two_eq (g : H3) (hg : g.coeff 0 = 0) : dpow g 2 = -g ^ 2 := by
  have h := pow_eq_factorial_mul_dpow g hg 2
  rw [Nat.factorial_two, Nat.cast_ofNat] at h
  linear_combination h + dpow g 2 * three_eq_zero

/-- Over $\mathbb{F}_3$, Hanna's sum is $e^{-x} + B - x B^2$ when $B_0 = 0$. -/
theorem ser_three (B : H3) (hB : B.coeff 0 = 0) : Ser B = expNeg + B - x * B ^ 2 := by
  have hBx : (B - x).coeff 0 = 0 := by rw [coeff_sub, hB, x_coeff_zero, sub_zero]
  have hB2x : (B ^ 2 - x).coeff 0 = 0 := by
    rw [coeff_sub, coeff_zero_pow, hB, x_coeff_zero]
    ring
  have hx : (-x : H3).coeff 0 = 0 := by rw [coeff_neg, x_coeff_zero, neg_zero]
  rw [ser_eq_of_pow B (pow_add_three_eq_zero B hB), ser_zero, dpow_one_of _ hBx,
    dpow_one_of _ hx, dpow_two_eq _ hB2x, dpow_two_eq _ hx]
  have h4 : B ^ 4 = 0 := pow_add_three_eq_zero B hB 1
  linear_combination (-1 : H3) * h4 + x * B ^ 2 * three_eq_zero

lemma D3_add (f g : H3) : D^[3] (f + g) = D^[3] f + D^[3] g := iterate_D_add f g 3

/-- $D^3$ is a derivation in characteristic three. -/
lemma D3_mul (f g : H3) : D^[3] (f * g) = D^[3] f * g + f * D^[3] g :=
  iterate_three_mul three_eq_zero D D_add D_mul f g

lemma D9_eq (f : H3) : D^[9] f = D^[3] (D^[3] (D^[3] f)) := by
  simp only [← Function.iterate_add_apply]

/-- $D^9$ is a derivation in characteristic three. -/
lemma D9_mul (f g : H3) : D^[9] (f * g) = D^[9] f * g + f * D^[9] g := by
  simp only [D9_eq]
  exact iterate_three_mul three_eq_zero (D^[3]) D3_add D3_mul f g

/-- The series $f$ over $\mathbb{F}_3$ with $D^9 f = D^3 f$, that is, $f_{n+9} = f_{n+3}$. -/
def InK (f : H3) : Prop := D^[9] f = D^[3] f

lemma inK_iff (f : H3) : InK f ↔ ∀ n, f.coeff (n + 9) = f.coeff (n + 3) := by
  constructor
  · intro h n
    have := congrArg (fun g => Hur.coeff g n) h
    simpa [coeff_iterate_D] using this
  · intro h
    ext n
    rw [coeff_iterate_D, coeff_iterate_D, h]

lemma inK_add {f g : H3} (hf : InK f) (hg : InK g) : InK (f + g) := by
  rw [inK_iff] at *
  intro n
  rw [coeff_add, coeff_add, hf, hg]

lemma inK_sub {f g : H3} (hf : InK f) (hg : InK g) : InK (f - g) := by
  rw [inK_iff] at *
  intro n
  rw [coeff_sub, coeff_sub, hf, hg]

/-- `InK` is closed under products, since $D^3$ and $D^9$ are derivations. -/
lemma inK_mul {f g : H3} (hf : InK f) (hg : InK g) : InK (f * g) := by
  unfold InK at *
  rw [D9_mul, D3_mul, hf, hg]

lemma inK_one : InK (1 : H3) := by
  rw [inK_iff]
  intro n
  simp [coeff_one]

lemma inK_x : InK (x : H3) := by
  rw [inK_iff]
  intro n
  simp [x]

lemma inK_expNeg : InK (expNeg : H3) := by
  rw [inK_iff]
  intro n
  change (-1 : ZMod 3) ^ (n + 9) = (-1) ^ (n + 3)
  rw [pow_add, pow_add]
  norm_num

/-- A series in `InK` that vanishes below index $9$ is zero. -/
lemma inK_eq_zero {f : H3} (hf : InK f) (h : ∀ n < 9, f.coeff n = 0) : f = 0 := by
  rw [inK_iff] at hf
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 9
    · exact h n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      rw [hf]
      exact ih (m + 3) (by omega)

/-- The pattern of Theorem 1: $P_0 = 0$, $P_1 = 1$, and for $m \ge 2$, $P_m$ is
$2, 0, 2, 1, 2, 2$ for $m \equiv 0, 1, 2, 3, 4, 5 \pmod 6$. -/
def patSeq (m : ℕ) : ZMod 3 :=
  if m = 0 then 0 else if m = 1 then 1 else [2, 0, 2, 1, 2, 2].getD (m % 6) 0

/-- The pattern as a Hurwitz series over $\mathbb{F}_3$. -/
def pat : H3 := ⟨patSeq⟩

lemma patSeq_of_two_le {m : ℕ} (hm : 2 ≤ m) : patSeq m = [2, 0, 2, 1, 2, 2].getD (m % 6) 0 := by
  unfold patSeq
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma inK_pat : InK pat := by
  rw [inK_iff]
  intro n
  change patSeq (n + 9) = patSeq (n + 3)
  rw [patSeq_of_two_le (by omega), patSeq_of_two_le (by omega),
    show (n + 9) % 6 = (n + 3) % 6 by omega]

/-- The finite check: $e^{-x} + P - x P^2 - 1$ vanishes below index $9$. -/
lemma resid_lt : ∀ n < 9, (expNeg + pat - x * (pat * pat) - 1 : H3).coeff n = 0 := by
  decide +kernel

/-- The pattern solves Hanna's equation over $\mathbb{F}_3$. -/
theorem ser_pat : Ser pat = 1 := by
  rw [ser_three pat rfl, sq]
  have hK : InK (expNeg + pat - x * (pat * pat) - 1) :=
    inK_sub (inK_sub (inK_add inK_expNeg inK_pat) (inK_mul inK_x (inK_mul inK_pat inK_pat)))
      inK_one
  exact sub_eq_zero.1 (inK_eq_zero hK resid_lt)

theorem T_pat : T pat = pat := (solH_iff _).1 ⟨rfl, ser_pat⟩

/-- The integer fixed point reduces modulo $3$ to the pattern. -/
theorem map_fix_three : map (Int.castRingHom (ZMod 3)) (fix ℤ) = pat := by
  rw [map_fix]
  exact T_fixed_unique T_fix T_pat

end Three

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

/-- The Hurwitz series of the $n$-th term $(A^n - x)^n / n!$ of Hanna's sum. -/
lemma jet_term (A : ℚ⟦X⟧) (hA : constantCoeff A = 0) (n : ℕ) :
    jet ((n.factorial : ℚ)⁻¹ • (A ^ n - X) ^ n) = dpow (jet A ^ n - x) n := by
  cases n with
  | zero => simp [dpow_zero]
  | succ n => rw [jet_dpow _ (by simp [hA]), map_sub, map_pow, jet_X]

lemma jet_partial (A : ℚ⟦X⟧) (hA : constantCoeff A = 0) (N : ℕ) :
    jet (∑ n ∈ Finset.range N, (n.factorial : ℚ)⁻¹ • (A ^ n - X) ^ n) =
      ∑ n ∈ Finset.range N, dpow (jet A ^ n - x) n := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => jet_term A hA n

lemma coeff_partial (B : Hur ℚ) {N m : ℕ} (h : m < N) :
    (∑ n ∈ Finset.range N, dpow (B ^ n - x) n).coeff m = (Ser B).coeff m := by
  rw [coeff_sum, ser_coeff_eq B h]

/-- A solution has $A(0) = 0$: otherwise the constant terms of the partial sums never
stabilize. -/
theorem constantCoeff_of_isSolution {A : ℚ⟦X⟧} (h : IsSolution A) : constantCoeff A = 0 := by
  obtain ⟨N, hN⟩ := h 0
  have h3 : PowerSeries.coeff 0 (((N + 1).factorial : ℚ)⁻¹ • (A ^ (N + 1) - X) ^ (N + 1)) = 0 := by
    have h2 := hN (N + 2) (by omega)
    rw [Finset.sum_range_succ, map_add, hN (N + 1) (by omega)] at h2
    linear_combination h2
  rw [PowerSeries.coeff_smul, coeff_zero_eq_constantCoeff_apply, map_pow, map_sub, map_pow,
    constantCoeff_X, sub_zero, smul_eq_mul] at h3
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd h4 (inv_ne_zero (by exact_mod_cast (N + 1).factorial_ne_zero))
  · exact (pow_eq_zero_iff (Nat.succ_ne_zero N)).1 ((pow_eq_zero_iff (Nat.succ_ne_zero N)).1 h4)

theorem solH_of_isSolution {A : ℚ⟦X⟧} (h : IsSolution A) : SolH (jet A) := by
  have hA := constantCoeff_of_isSolution h
  refine ⟨by rw [jet_coeff, coeff_zero_eq_constantCoeff_apply, hA, mul_zero], ?_⟩
  ext m
  obtain ⟨N, hN⟩ := h m
  rw [← coeff_partial _ (show m < max N (m + 1) by omega), ← jet_partial A hA, jet_coeff,
    hN _ (le_max_left _ _), ← jet_coeff, map_one]

theorem isSolution_of_solH {A : ℚ⟦X⟧} (h : SolH (jet A)) : IsSolution A := by
  have hA : constantCoeff A = 0 := by
    have h0 := h.1
    rw [jet_coeff, coeff_zero_eq_constantCoeff_apply] at h0
    simpa using h0
  intro m
  refine ⟨m + 1, fun N hN => ?_⟩
  have h1 := congrArg (fun F => Hur.coeff F m) h.2
  rw [← coeff_partial _ (show m < N by omega), ← jet_partial A hA, ← map_one jet,
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

/-- The general result: Hanna's equation has a unique solution, its EGF coefficients are the
integer fixed point, and they reduce modulo $3$ to the pattern. -/
theorem main : (∃! A : ℚ⟦X⟧, IsSolution A) ∧ ∀ A : ℚ⟦X⟧, IsSolution A → ∀ k : ℕ,
    (k.factorial : ℚ) * coeff k A = (fix ℤ).coeff k ∧
      (((fix ℤ).coeff k : ℤ) : ZMod 3) = patSeq k := by
  have hB : T (map (Int.castRingHom ℚ) (fix ℤ)) = map (Int.castRingHom ℚ) (fix ℤ) := by
    rw [← map_T, T_fix]
  have hjet : ∀ A, IsSolution A → jet A = map (Int.castRingHom ℚ) (fix ℤ) := fun A hA =>
    T_fixed_unique ((solH_iff _).1 (solH_of_isSolution hA)) hB
  have hex : IsSolution (egf (fix ℤ).coeff) := by
    apply isSolution_of_solH
    rw [solH_iff, jet_egf]
    exact hB
  refine ⟨⟨_, hex, fun A hA => jet_injective (by rw [hjet A hA, hjet _ hex])⟩, ?_⟩
  intro A hA k
  refine ⟨?_, ?_⟩
  · rw [← jet_coeff, hjet A hA, Hur.coeff_map]
    rfl
  · exact congrArg (fun F => Hur.coeff F k) map_fix_three

end Bridge

/-! ### The OEIS statements -/

section Main

open PowerSeries Hur

/-- OEIS A371710: exactly one $A(x) \in \mathbb{Q}[[x]]$ satisfies
$\sum_{n \ge 0} (A(x)^n - x)^n / n! = 1$. -/
theorem a371710_existsUnique : ∃! A : ℚ⟦X⟧, IsSolution A :=
  main.1

/-- A solution has $A(0) = 0$, so $A(x) = \sum_{n \ge 1} a(n) x^n / n!$ as in the OEIS entry. -/
theorem a371710_constantCoeff (A : ℚ⟦X⟧) (hA : IsSolution A) : constantCoeff A = 0 :=
  constantCoeff_of_isSolution hA

/-- Every $a(m) = m!\,[x^m] A(x)$ is an integer. -/
theorem a371710_integral (A : ℚ⟦X⟧) (hA : IsSolution A) (m : ℕ) :
    ∃ a : ℤ, (m.factorial : ℚ) * coeff m A = a :=
  ⟨_, (main.2 A hA m).1⟩

/-- Hanna's conjecture for OEIS A371710: for $n > 0$ and $k \in \{0, \dots, 5\}$,
$a(6n + k) \equiv [2, 0, 2, 1, 2, 2]_k \pmod 3$. -/
theorem a371710_mod_three (A : ℚ⟦X⟧) (hA : IsSolution A) (n : ℕ) (hn : 0 < n) (k : Fin 6) :
    ∃ a : ℤ, ((6 * n + (k : ℕ)).factorial : ℚ) * coeff (6 * n + (k : ℕ)) A = a ∧
      a ≡ ![2, 0, 2, 1, 2, 2] k [ZMOD 3] := by
  refine ⟨_, (main.2 A hA _).1, ?_⟩
  have hk := k.isLt
  refine (ZMod.intCast_eq_intCast_iff _ _ 3).1 ?_
  rw [(main.2 A hA _).2, patSeq_of_two_le (by omega),
    show (6 * n + (k : ℕ)) % 6 = k by omega]
  fin_cases k <;> decide

/-- The stronger form: $a(m) \equiv 2 \pmod 3$ for even $m \ge 2$, and
$a(m) \equiv 1 - m \pmod 3$ for odd $m \ge 3$. -/
theorem a371710_mod_three_strong (A : ℚ⟦X⟧) (hA : IsSolution A) (m : ℕ) (hm : 2 ≤ m) :
    ∃ a : ℤ, (m.factorial : ℚ) * coeff m A = a ∧
      (Even m → a ≡ 2 [ZMOD 3]) ∧ (Odd m → a ≡ 1 - m [ZMOD 3]) := by
  refine ⟨_, (main.2 A hA m).1, fun hpar => ?_, fun hpar => ?_⟩ <;>
    refine (ZMod.intCast_eq_intCast_iff _ _ 3).1 ?_ <;>
    rw [(main.2 A hA m).2, patSeq_of_two_le hm]
  · have h : m % 6 = 0 ∨ m % 6 = 2 ∨ m % 6 = 4 := by
      obtain ⟨j, rfl⟩ := hpar
      omega
    rcases h with h | h | h <;> rw [h] <;> decide
  · have hm6 : (m : ZMod 3) = ((m % 6 : ℕ) : ZMod 3) := by
      conv_lhs => rw [← Nat.div_add_mod m 6]
      push_cast
      rw [show (6 : ZMod 3) = 0 by decide, zero_mul, zero_add]
    have h : m % 6 = 1 ∨ m % 6 = 3 ∨ m % 6 = 5 := by
      obtain ⟨j, rfl⟩ := hpar
      omega
    push_cast
    rw [hm6]
    rcases h with h | h | h <;> rw [h] <;> decide

/-! ### Sanity checks: the first terms agree with the OEIS data -/

/-- The first EGF coefficients $a(0), \dots, a(10)$, with $a(0) = 0$. -/
def firstTerms : Hur ℤ :=
  ⟨fun n => [0, 1, -1, 7, -37, 371, -4741, 72885, -1380541, 29678815, -726074821].getD n 0⟩

lemma T_firstTerms : ∀ n < 11, (T firstTerms).coeff n = firstTerms.coeff n := by
  decide +kernel

/-- The first terms of OEIS A371710: $a(1), \dots, a(10)$ are
$1, -1, 7, -37, 371, -4741, 72885, -1380541, 29678815, -726074821$. -/
theorem a371710_first_terms (A : ℚ⟦X⟧) (hA : IsSolution A) :
    ∀ k < 11, (k.factorial : ℚ) * coeff k A =
      ([0, 1, -1, 7, -37, 371, -4741, 72885, -1380541, 29678815, -726074821].getD k 0 : ℤ) := by
  intro k hk
  rw [(main.2 A hA k).1, fix_coeff_of_T firstTerms 11 T_firstTerms k hk]
  rfl

end Main

end OeisA371710

end
