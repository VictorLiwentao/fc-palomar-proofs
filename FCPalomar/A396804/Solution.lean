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
# The exponential generating function $A(x) = x \exp(A^{\circ 4}(x))$

Let $A(x) = \sum_{n \ge 1} a(n) x^n / n!$ be the power series with $A(0) = 0$ and
$A(x) = x \exp(A(A(A(A(x)))))$, where $A^{\circ 4} = A \circ A \circ A \circ A$ is the fourth
compositional iterate.

The file proves existence and uniqueness of $A$ over $\mathbb{Q}$, integrality of $a(n)$, and
that $a(n) \not\equiv 3 \pmod 5$ for every $n \ge 1$.

The proof works with Hurwitz series: sequences $f_n = n!\,[x^n] f$ with the binomial product.
Write $T(B) = x \exp(B^{\circ 4})$ for the operator of the equation on Hurwitz series.

*Existence, uniqueness and integrality.* Over any commutative ring, $T$ is causal: coefficient
$n$ of $T(B)$ depends only on the coefficients of $B$ below $n$. So $T$ has at most one fixed
point, and the fixed point can be built one coefficient at a time. Over $\mathbb{Z}$ this gives
integers $a(n)$. The map $F \mapsto (n!\,[x^n] F)$ turns the equation over $\mathbb{Q}$ into the
fixed-point equation for $T$ over $\mathbb{Q}$. The image of the integer fixed point solves it,
and uniqueness shows that every rational solution is $\sum_n a(n) x^n / n!$.

*Residues modulo 5.* Over $\mathbb{F}_5$, the derivative $D$ satisfies that $D^5$ and $D^{25}$
are derivations and that every fifth power is a constant. A char-5 chain rule shows that $T$
preserves the set of series $f$ with $D^{25} f = D^5 f$ and $f_0 = f_5 = 0$. A series with
$D^{25} f = D^5 f$ is determined by its first $25$ coefficients. The residue pattern $P$ (five
initial values, then period $20$) lies in this set, and a finite computation shows that $T(P)$
and $P$ agree below index $25$. Hence $T(P) = P$. By uniqueness of the fixed point over
$\mathbb{F}_5$, $P$ is the reduction of $(a(n))$ modulo $5$, and no value of $P$ is $3$.

*References:*
- Paul D. Hanna, [A396804](https://oeis.org/A396804), June 9, 2026.
-/

@[expose] public section

namespace OeisA396804

open PowerSeries

/-- The compositional iterate: `iterate A 0 = X` and `iterate A (k + 1) = A ∘ iterate A k`. -/
noncomputable def iterate (A : ℚ⟦X⟧) : ℕ → ℚ⟦X⟧
  | 0 => X
  | k + 1 => A.subst (iterate A k)

/-- The defining equation $A(x) = x \exp(A^{\circ 4}(x))$, normalized by $A(0) = 0$. -/
def IsSolution (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ A = X * (exp ℚ).subst (iterate A 4)

end OeisA396804

namespace OeisA396804

/-! ### Hurwitz series -/

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

lemma D_natCast (m : ℕ) : D (m : Hur R) = 0 := by
  ext n
  simp [coeff_natCast]

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

lemma coeff_x_mul_zero (f : Hur R) : (x * f).coeff 0 = 0 := by
  simp [x]

lemma coeff_x_mul_succ (f : Hur R) (n : ℕ) : (x * f).coeff (n + 1) = (n + 1) * f.coeff n := by
  induction n generalizing f with
  | zero =>
    change prod (shift x.coeff) f.coeff 0 + prod x.coeff (shift f.coeff) 0 = _
    simp [prod, shift, x]
  | succ n ih =>
    change prod (shift x.coeff) f.coeff (n + 1) + prod x.coeff (shift f.coeff) (n + 1) = _
    have hx : shift (x : Hur R).coeff = unitSeq := by
      funext k
      cases k <;> simp [shift, x, unitSeq]
    rw [hx, prod_comm, prod_unit]
    have := ih ⟨shift f.coeff⟩
    change prod x.coeff (shift f.coeff) (n + 1) = _ at this
    rw [this]
    simp only [shift]
    push_cast
    ring

/-- The exponential series $e^x$: every EGF coefficient is one. -/
def e : Hur R := ⟨fun _ => 1⟩

lemma D_e : D (e : Hur R) = e := rfl

lemma iterate_D_e (m : ℕ) : D^[m] (e : Hur R) = e := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, D_e]

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

lemma D_integ (h : Hur R) : D (integ h) = h := rfl

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

lemma comp_coeff_zero (f g : Hur R) : (comp f g).coeff 0 = f.coeff 0 := by
  simp [comp, dpow, coeff_one]

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

/-- A coefficient of $f(g)$ only uses coefficients of $f$ and $g$ of the same or lower index. -/
lemma comp_congr (f g f' g' : Hur R) (n : ℕ) (hf : ∀ k ≤ n, f.coeff k = f'.coeff k)
    (hg : ∀ k ≤ n, g.coeff k = g'.coeff k) : (comp f g).coeff n = (comp f' g').coeff n := by
  change ∑ k ∈ Finset.range (n + 1), f.coeff k * (dpow g k).coeff n =
    ∑ k ∈ Finset.range (n + 1), f'.coeff k * (dpow g' k).coeff n
  apply Finset.sum_congr rfl
  intro k hk
  rw [hf k (by simp only [Finset.mem_range] at hk; omega), dpow_congr g g' n hg k n le_rfl]

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

lemma map_comp (φ : R →+* S) (f g : Hur R) : map φ (comp f g) = comp (map φ f) (map φ g) := by
  ext n
  simp only [coeff_map, comp, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [← coeff_map φ (dpow g k), map_dpow]

lemma map_x (φ : R →+* S) : map φ (x : Hur R) = x := by
  ext n
  simp only [coeff_map, x]
  split_ifs <;> simp

lemma map_e (φ : R →+* S) : map φ (e : Hur R) = e := by
  ext n
  simp [coeff_map, e]

end Map

section Source
variable {R : Type*} [CommRing R]

/-- The source operator $B \mapsto x \exp(B(B(B(B))))$ on Hurwitz series. -/
def T (B : Hur R) : Hur R := x * comp e (comp B (comp B (comp B B)))

lemma T_coeff_zero (B : Hur R) : (T B).coeff 0 = 0 := coeff_x_mul_zero _

lemma map_T {S : Type*} [CommRing S] (φ : R →+* S) (B : Hur R) :
    map φ (T B) = T (map φ B) := by
  simp only [T, map_mul', map_x, map_comp, map_e]

/-- Coefficient $n$ of `T B` only uses coefficients of `B` below $n$. -/
theorem T_causal (n : ℕ) (f g : Hur R) (h : ∀ k < n, f.coeff k = g.coeff k) :
    (T f).coeff n = (T g).coeff n := by
  cases n with
  | zero => rw [T_coeff_zero, T_coeff_zero]
  | succ n =>
    simp only [T, coeff_x_mul_succ]
    congr 1
    have h0 : ∀ k ≤ n, f.coeff k = g.coeff k := fun k hk => h k (by omega)
    have h1 : ∀ k ≤ n, (comp f f).coeff k = (comp g g).coeff k := fun k hk =>
      comp_congr _ _ _ _ k (fun j hj => h0 j (by omega)) (fun j hj => h0 j (by omega))
    have h2 : ∀ k ≤ n, (comp f (comp f f)).coeff k = (comp g (comp g g)).coeff k := fun k hk =>
      comp_congr _ _ _ _ k (fun j hj => h0 j (by omega)) (fun j hj => h1 j (by omega))
    have h3 : ∀ k ≤ n, (comp f (comp f (comp f f))).coeff k =
        (comp g (comp g (comp g g))).coeff k := fun k hk =>
      comp_congr _ _ _ _ k (fun j hj => h0 j (by omega)) (fun j hj => h2 j (by omega))
    exact comp_congr _ _ _ _ n (fun _ _ => rfl) h3

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

end Source

section Five

/-- Leibniz rule for the fifth iterate of a derivation in characteristic five. -/
theorem iterate_five_mul {T : Type*} [CommRing T] (h5 : (5 : T) = 0) (δ : T → T)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = δ a * b + a * δ b)
    (a b : T) :
    δ (δ (δ (δ (δ (a * b))))) = δ (δ (δ (δ (δ a)))) * b + a * δ (δ (δ (δ (δ b)))) := by
  simp only [hmul, hadd]
  linear_combination (δ (δ (δ (δ a))) * δ b + 2 * δ (δ (δ a)) * δ (δ b) +
    2 * δ (δ a) * δ (δ (δ b)) + δ a * δ (δ (δ (δ b)))) * h5

/-- A two-term Jacobson identity in characteristic five: if $\delta V_m = c V_{m+5} + w V_{m+1}$
with $\delta c = 0$, then $\delta^5 V_0 = c^5 V_{25} + w^5 V_5 + (\delta^4 w) V_1$. -/
theorem jacobson_five {T : Type*} [CommRing T] (h5 : (5 : T) = 0) (δ : T → T)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = δ a * b + a * δ b)
    (c w : T) (hc : δ c = 0) (V : ℕ → T)
    (hV : ∀ m, δ (V m) = c * V (m + 5) + w * V (m + 1)) :
    δ (δ (δ (δ (δ (V 0))))) = c ^ 5 * V 25 + w ^ 5 * V 5 + δ (δ (δ (δ w))) * V 1 := by
  simp only [hV, hadd, hmul, hc, zero_mul, zero_add]
  linear_combination (c * c * c * c * (V 21) * w + 2 * c * c * c * (V 16) * δ w +
    2 * c * c * c * (V 17) * w * w + 2 * c * c * (V 11) * δ (δ w) +
    6 * c * c * (V 12) * w * δ w + 2 * c * c * (V 13) * w * w * w + c * (V 6) * δ (δ (δ w)) +
    4 * c * (V 7) * w * δ (δ w) + 3 * c * (V 7) * δ w * δ w + 6 * c * (V 8) * w * w * δ w +
    c * (V 9) * w * w * w * w + (V 2) * w * δ (δ (δ w)) + 2 * (V 2) * δ w * δ (δ w) +
    2 * (V 3) * w * w * δ (δ w) + 3 * (V 3) * w * δ w * δ w +
    2 * (V 4) * w * w * w * δ w) * h5

local notation "H5" => Hur (ZMod 5)

lemma five_eq_zero : (5 : H5) = 0 := by
  have h : ((5 : ℕ) : H5) = 0 := by
    ext n
    rw [coeff_natCast, coeff_zero']
    split_ifs
    · decide
    · rfl
  exact_mod_cast h

lemma zmod_pow_five (r : ZMod 5) : r ^ 5 = r := by
  revert r
  decide

/-- Every fifth power in characteristic five is a constant. -/
lemma pow_five_eq (f : H5) : f ^ 5 = C (f.coeff 0) := by
  have h1 : D (f ^ 5) = 0 := by
    rw [show f ^ 5 = f ^ (4 + 1) from rfl, D_pow]
    have h : ((4 + 1 : ℕ) : H5) = 0 := by exact_mod_cast five_eq_zero
    rw [h, zero_mul, zero_mul]
  rw [eq_C_of_D_eq_zero h1, ← coeff0_apply, map_pow, coeff0_apply, zmod_pow_five]

lemma D5_add (f g : H5) : D^[5] (f + g) = D^[5] f + D^[5] g := iterate_D_add f g 5

/-- $D^5$ is a derivation in characteristic five. -/
lemma D5_mul (f g : H5) : D^[5] (f * g) = D^[5] f * g + f * D^[5] g :=
  iterate_five_mul five_eq_zero D D_add D_mul f g

lemma D25_eq (f : H5) : D^[25] f = D^[5] (D^[5] (D^[5] (D^[5] (D^[5] f)))) := by
  simp only [← Function.iterate_add_apply]

/-- $D^{25}$ is a derivation in characteristic five. -/
lemma D25_mul (f g : H5) : D^[25] (f * g) = D^[25] f * g + f * D^[25] g := by
  simp only [D25_eq]
  exact iterate_five_mul five_eq_zero (D^[5]) D5_add D5_mul f g

/-- The characteristic-five chain rule for $D^5$. -/
theorem D5_comp (f g : H5) :
    D^[5] (comp f g) = C (g.coeff 1) * comp (D^[5] f) g + D^[5] g * comp (D f) g := by
  have key := jacobson_five five_eq_zero D D_add D_mul 0 (D g) D_zero
    (fun m => comp (D^[m] f) g) (fun m => by
      rw [D_comp, ← Function.iterate_succ_apply' D m f]
      ring)
  have hw : D g ^ 5 = C (g.coeff 1) := pow_five_eq (D g)
  rw [hw] at key
  change D^[5] (comp f g) = 0 ^ 5 * comp (D^[25] f) g + C (g.coeff 1) * comp (D^[5] f) g +
    D^[5] g * comp (D f) g at key
  rw [key]
  ring

/-- The characteristic-five chain rule for $D^{25}$. -/
theorem D25_comp (f g : H5) :
    D^[25] (comp f g) = C (g.coeff 1) * comp (D^[25] f) g +
      C (g.coeff 5) * comp (D^[5] f) g + D^[25] g * comp (D f) g := by
  have key := jacobson_five five_eq_zero (D^[5]) D5_add D5_mul (C (g.coeff 1)) (D^[5] g)
    (iterate_D_C _ 4) (fun m => comp (D^[m] f) g) (fun m => by
      rw [D5_comp, ← Function.iterate_add_apply, ← Function.iterate_succ_apply' D m f,
        Nat.add_comm 5 m])
  have hc : C (g.coeff 1) ^ 5 = C (g.coeff 1) := by rw [← C_pow, zmod_pow_five]
  have hw : (D^[5] g) ^ 5 = C (g.coeff 5) := by rw [pow_five_eq, coeff_iterate_D]
  rw [hc, hw] at key
  simp only [← D25_eq] at key
  exact key

/-- The set $S$ of Hurwitz series over $\mathbb{F}_5$ with $D^{25} f = D^5 f$. -/
def InS (f : H5) : Prop := D^[25] f = D^[5] f

lemma inS_iff (f : H5) : InS f ↔ ∀ n, f.coeff (n + 25) = f.coeff (n + 5) := by
  constructor
  · intro h n
    have := congrArg (fun g => Hur.coeff g n) h
    simpa [coeff_iterate_D] using this
  · intro h
    ext n
    rw [coeff_iterate_D, coeff_iterate_D, h]

lemma inS_mul {f g : H5} (hf : InS f) (hg : InS g) : InS (f * g) := by
  unfold InS at *
  rw [D25_mul, D5_mul, hf, hg]

lemma inS_x : InS (x : H5) := by
  have h5 : D^[5] (x : H5) = 0 := by
    change D^[3 + 1] (D x) = 0
    rw [D_x]
    exact iterate_D_C 1 3
  unfold InS
  rw [h5, D25_eq, h5]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, D_zero]

lemma inS_e : InS (e : H5) := by
  unfold InS
  rw [iterate_D_e, iterate_D_e]

/-- Composition preserves $S$ when the inner series has $g_5 = 0$. -/
theorem inS_comp {f g : H5} (hf : InS f) (hg : InS g) (hg5 : g.coeff 5 = 0) :
    InS (comp f g) := by
  unfold InS at *
  rw [D25_comp, D5_comp, hf, hg, hg5, C_zero, zero_mul, add_zero]

lemma coeff_five_comp (f g : H5) :
    (comp f g).coeff 5 = g.coeff 1 * f.coeff 5 + g.coeff 5 * f.coeff 1 := by
  have h := congrArg (fun h => Hur.coeff h 0) (D5_comp f g)
  simp only [coeff_iterate_D, coeff_add, C_mul_coeff, coeff_mul_zero, comp_coeff_zero,
    coeff_D] at h
  simpa using h

/-- Series in $S$ with vanishing coefficients $0$ and $5$. -/
def Good (f : H5) : Prop := InS f ∧ f.coeff 0 = 0 ∧ f.coeff 5 = 0

lemma good_comp {f g : H5} (hf : Good f) (hg : Good g) : Good (comp f g) :=
  ⟨inS_comp hf.1 hg.1 hg.2.2, by rw [comp_coeff_zero, hf.2.1],
    by rw [coeff_five_comp, hf.2.2, hg.2.2, mul_zero, zero_mul, add_zero]⟩

/-- The source operator preserves `Good`. -/
theorem good_T {B : H5} (hB : Good B) : Good (T B) := by
  have h4 := good_comp hB (good_comp hB (good_comp hB hB))
  refine ⟨inS_mul inS_x (inS_comp inS_e h4.1 h4.2.2), T_coeff_zero B, ?_⟩
  change ((x : H5) * comp e (comp B (comp B (comp B B)))).coeff (4 + 1) = 0
  rw [coeff_x_mul_succ]
  have h : ((4 : ℕ) : ZMod 5) + 1 = 0 := by decide
  rw [h, zero_mul]

/-- Two series in $S$ that agree below index $25$ are equal. -/
lemma inS_eq_of_lt {f g : H5} (hf : InS f) (hg : InS g)
    (h : ∀ n < 25, f.coeff n = g.coeff n) : f = g := by
  rw [inS_iff] at hf hg
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 25
    · exact h n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 25 := ⟨n - 25, by omega⟩
      rw [hf, hg]
      exact ih (m + 5) (by omega)

end Five

section Residues

local notation "H5" => Hur (ZMod 5)

/-- The residues of $a(n)$ modulo $5$: five initial values, then period $20$. -/
def patSeq (n : ℕ) : ZMod 5 :=
  if n < 5 then [0, 1, 2, 2, 0].getD n 0
  else [0, 1, 0, 1, 0, 0, 1, 0, 4, 0, 0, 1, 0, 4, 1, 0, 1, 0, 0, 2].getD (n % 20) 0

/-- The residue pattern as a Hurwitz series. -/
def pat : H5 := ⟨patSeq⟩

lemma good_pat : Good pat := by
  refine ⟨(inS_iff pat).2 fun n => ?_, by decide, by decide⟩
  change patSeq (n + 25) = patSeq (n + 5)
  unfold patSeq
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show (n + 25) % 20 = (n + 5) % 20 by omega]

/-- The finite check: `T pat` agrees with `pat` below index $25$. -/
lemma T_pat_lt : ∀ n < 25, (T pat).coeff n = pat.coeff n := by
  decide +kernel

/-- The residue pattern is the fixed point of the source operator over $\mathbb{F}_5$. -/
theorem T_pat : T pat = pat :=
  inS_eq_of_lt (good_T good_pat).1 good_pat.1 T_pat_lt

lemma patSeq_ne_three (n : ℕ) : patSeq n ≠ 3 := by
  have h1 : ∀ m < 5, [0, 1, 2, 2, 0].getD m (0 : ZMod 5) ≠ 3 := by decide
  have h2 : ∀ m < 20,
      [0, 1, 0, 1, 0, 0, 1, 0, 4, 0, 0, 1, 0, 4, 1, 0, 1, 0, 0, 2].getD m (0 : ZMod 5) ≠ 3 := by
    decide
  unfold patSeq
  split_ifs with h
  · exact h1 n h
  · exact h2 _ (Nat.mod_lt _ (by norm_num))

lemma patSeq_add_twenty {n : ℕ} (hn : 5 ≤ n) : patSeq (n + 20) = patSeq n := by
  unfold patSeq
  rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_mod_right]

/-- The reduction modulo $5$ of the integer fixed point is the residue pattern. -/
theorem map_fix_int : map (Int.castRingHom (ZMod 5)) (fix ℤ) = pat :=
  T_fixed_unique (by rw [← map_T, T_fix]) T_pat

lemma fix_int_mod_five (n : ℕ) : (((fix ℤ).coeff n : ℤ) : ZMod 5) = patSeq n :=
  congrArg (fun h => Hur.coeff h n) map_fix_int

end Residues

lemma fix_coeff_eq_iterate {R : Type*} [CommRing R] (k n : ℕ) (h : n < k) :
    (fix R).coeff n = (T^[k] (0 : Hur R)).coeff n := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← T_fix]
    apply T_causal
    intro j hj
    exact ih j (by omega)

end Hur

section Bridge

open PowerSeries Hur

/-- The Hurwitz series of EGF coefficients $n!\,[x^n] F$ of a rational power series. -/
noncomputable def jet (F : ℚ⟦X⟧) : Hur ℚ := ⟨fun n => (n.factorial : ℚ) * coeff n F⟩

lemma jet_coeff (F : ℚ⟦X⟧) (n : ℕ) : (jet F).coeff n = (n.factorial : ℚ) * coeff n F := rfl

lemma jet_derivative (F : ℚ⟦X⟧) : jet (derivative (R := ℚ) F) = D (jet F) := by
  ext n
  simp only [jet_coeff, coeff_D, coeff_derivative, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

lemma jet_add (F G : ℚ⟦X⟧) : jet (F + G) = jet F + jet G := by
  ext n
  simp [jet_coeff, mul_add]

lemma jet_mul (F G : ℚ⟦X⟧) : jet (F * G) = jet F * jet G := by
  suffices h : ∀ n, ∀ F G : ℚ⟦X⟧, (jet (F * G)).coeff n = (jet F * jet G).coeff n from
    Hur.ext (funext fun n => h n F G)
  intro n
  induction n with
  | zero => intro F G; simp [jet_coeff]
  | succ n ih =>
    intro F G
    rw [← coeff_D, ← coeff_D, ← jet_derivative, (derivative (R := ℚ)).leibniz, smul_eq_mul, smul_eq_mul,
      jet_add,
      coeff_add, ih, ih, D_mul, coeff_add, jet_derivative, jet_derivative, add_comm,
      mul_comm (jet G) (D (jet F))]

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

lemma jet_exp : jet (exp ℚ) = e := by
  ext n
  rw [jet_coeff, coeff_exp]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp only [e, Algebra.algebraMap_self, RingHom.id_apply]
  field_simp

lemma constantCoeff_subst_of_zero (F G : ℚ⟦X⟧) (hG : constantCoeff G = 0) :
    constantCoeff (F.subst G) = constantCoeff F := by
  change MvPowerSeries.constantCoeff (F.subst G) = constantCoeff F
  rw [PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero' hG)]
  simp only [map_pow]
  change (∑ᶠ d : ℕ, coeff d F • (constantCoeff G ^ d)) = constantCoeff F
  rw [finsum_eq_single (a := 0)]
  · simp
  · intro d hd
    simp [hG, hd]

/-- Substitution of a series without constant term is Hurwitz composition. -/
theorem jet_subst (G : ℚ⟦X⟧) (hG : constantCoeff G = 0) (F : ℚ⟦X⟧) :
    jet (F.subst G) = comp (jet F) (jet G) := by
  have hs : HasSubst G := HasSubst.of_constantCoeff_zero' hG
  suffices h : ∀ n, ∀ F : ℚ⟦X⟧, ∀ m ≤ n,
      (jet (F.subst G)).coeff m = (comp (jet F) (jet G)).coeff m from
    Hur.ext (funext fun n => h n F n le_rfl)
  have h0 : ∀ F : ℚ⟦X⟧, (jet (F.subst G)).coeff 0 = (comp (jet F) (jet G)).coeff 0 := by
    intro F
    rw [comp_coeff_zero, jet_coeff, jet_coeff, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_subst_of_zero F G hG]
  intro n
  induction n with
  | zero =>
    intro F m hm
    obtain rfl : m = 0 := by omega
    exact h0 F
  | succ n ih =>
    intro F m hm
    cases m with
    | zero => exact h0 F
    | succ m =>
      rw [← coeff_D, ← coeff_D, ← jet_derivative, derivative_subst hs, jet_mul, D_comp,
        ← jet_derivative, ← jet_derivative]
      apply coeff_mul_congr
      · intro k hk
        exact ih (derivative (R := ℚ) F) k (by omega)
      · intro k _
        rfl

/-- The source equation: $A(0) = 0$ and $A(x) = x \exp(A(A(A(A(x)))))$. -/
def Equation (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ A = X * (exp ℚ).subst (A.subst (A.subst (A.subst A)))

/-- The exponential generating series of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ) / n.factorial

lemma jet_egf (a : ℕ → ℤ) : jet (egf a) = map (Int.castRingHom ℚ) ⟨a⟩ := by
  ext n
  rw [jet_coeff, egf, coeff_mk, Hur.coeff_map]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp only [eq_intCast]
  field_simp

lemma jet_source (A : ℚ⟦X⟧) (hA : constantCoeff A = 0) :
    jet (X * (exp ℚ).subst (A.subst (A.subst (A.subst A)))) = T (jet A) := by
  have h2 : constantCoeff (A.subst A) = 0 := by rw [constantCoeff_subst_of_zero _ _ hA, hA]
  have h3 : constantCoeff (A.subst (A.subst A)) = 0 := by
    rw [constantCoeff_subst_of_zero _ _ h2, hA]
  have h4 : constantCoeff (A.subst (A.subst (A.subst A))) = 0 := by
    rw [constantCoeff_subst_of_zero _ _ h3, hA]
  rw [jet_mul, jet_X, jet_subst _ h4, jet_exp, jet_subst _ h3, jet_subst _ h2, jet_subst _ hA]
  rfl

/-- The EGF coefficients $a(n)$ of the source solution, as integers. -/
def a (n : ℕ) : ℤ := (fix ℤ).coeff n

lemma jet_egf_a : jet (egf a) = map (Int.castRingHom ℚ) (fix ℤ) := jet_egf a

lemma constantCoeff_egf_a : constantCoeff (egf a) = 0 := by
  have h := congrArg (fun H => Hur.coeff H 0) jet_egf_a
  simp only [jet_coeff, Nat.factorial_zero, Nat.cast_one, one_mul,
    coeff_zero_eq_constantCoeff_apply, Hur.coeff_map] at h
  rw [h, ← T_fix, T_coeff_zero, map_zero]

/-- The constructed integer EGF solves the source equation. -/
theorem equation_egf_a : Equation (egf a) := by
  refine ⟨constantCoeff_egf_a, jet_injective ?_⟩
  rw [jet_source _ constantCoeff_egf_a, jet_egf_a, ← map_T, T_fix]

/-- Every solution of the source equation is the constructed integer EGF. -/
theorem eq_egf_a {A : ℚ⟦X⟧} (hA : Equation A) : A = egf a := by
  apply jet_injective
  have h1 : T (jet A) = jet A := (jet_source A hA.1).symm.trans (congrArg jet hA.2).symm
  have h2 : T (jet (egf a)) = jet (egf a) := by rw [jet_egf_a, ← map_T, T_fix]
  exact T_fixed_unique h1 h2

/-- Existence and uniqueness of the source solution. -/
theorem existsUnique_equation : ∃! A : ℚ⟦X⟧, Equation A :=
  ⟨egf a, equation_egf_a, fun _ hA => eq_egf_a hA⟩

/-- For every $n$, $a(n) \bmod 5$ is given by the residue pattern. -/
theorem a_mod_five (n : ℕ) : (a n : ZMod 5) = patSeq n := fix_int_mod_five n

/-- For every $n$, $a(n) \not\equiv 3 \pmod 5$. -/
theorem a_emod_five_ne_three (n : ℕ) : a n % 5 ≠ 3 := by
  intro h
  apply patSeq_ne_three n
  have hm : ((a n : ℤ) : ZMod 5) = ((a n % 5 : ℤ) : ZMod 5) := (ZMod.intCast_mod (a n) 5).symm
  rw [← a_mod_five, hm, h]
  rfl

/-- For $n \ge 5$, $a(n + 20) \equiv a(n) \pmod 5$. -/
theorem a_emod_five_periodic {n : ℕ} (hn : 5 ≤ n) : a (n + 20) % 5 = a n % 5 := by
  have h : ((a (n + 20) : ℤ) : ZMod 5) = ((a n : ℤ) : ZMod 5) := by
    rw [a_mod_five, a_mod_five, patSeq_add_twenty hn]
  exact (ZMod.intCast_eq_intCast_iff' _ _ 5).mp h

/-- OEIS A396804: the unique normalized solution of $A(x) = x \exp(A^{\circ 4}(x))$ has integer
EGF coefficients $a(n)$, and $a(n) \bmod 5$ is never $3$ for $n \ge 1$. -/
theorem a396804_mod_five :
    (∃! A : ℚ⟦X⟧, Equation A) ∧
      ∀ A : ℚ⟦X⟧, Equation A → ∃ b : ℕ → ℤ, egf b = A ∧ ∀ n, 1 ≤ n → b n % 5 ≠ 3 :=
  ⟨existsUnique_equation, fun _ hA => ⟨a, (eq_egf_a hA).symm, fun n _ => a_emod_five_ne_three n⟩⟩

/-- Coefficient form: for every solution $A$ and every $n \ge 1$, the number $n!\,[x^n] A$ is an
integer that is not $3$ modulo $5$. -/
theorem a396804_mod_five_coeff (A : ℚ⟦X⟧) (hA : Equation A) (n : ℕ) (_hn : 1 ≤ n) :
    ∃ m : ℤ, (n.factorial : ℚ) * coeff n A = m ∧ m % 5 ≠ 3 := by
  refine ⟨a n, ?_, a_emod_five_ne_three n⟩
  have h := congrArg (fun H => Hur.coeff H n) jet_egf_a
  rw [eq_egf_a hA]
  exact h

end Bridge

end OeisA396804

namespace OeisA396804

open PowerSeries

theorem iterate_four_eq (A : ℚ⟦X⟧) : iterate A 4 = A.subst (A.subst (A.subst A)) := by
  simp only [iterate, X_subst]

theorem isSolution_iff_equation (A : ℚ⟦X⟧) : IsSolution A ↔ Equation A := by
  rw [IsSolution, Equation, iterate_four_eq]

theorem exists_unique_solution : ∃! A : ℚ⟦X⟧, IsSolution A := by
  obtain ⟨A, hA, hu⟩ := a396804_mod_five.1
  exact ⟨A, (isSolution_iff_equation A).2 hA, fun B hB => hu B ((isSolution_iff_equation B).1 hB)⟩

theorem conjecture_mod_five (A : ℚ⟦X⟧) (hA : IsSolution A) (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℤ, (n.factorial : ℚ) * coeff n A = m ∧ m % 5 ≠ 3 :=
  a396804_mod_five_coeff A ((isSolution_iff_equation A).1 hA) n hn

end OeisA396804

end
