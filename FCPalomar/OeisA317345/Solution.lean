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
# OEIS A317345 and A317343: Hanna's residues modulo 10

OEIS A317345 is the e.g.f. $A(x) = \sum_n a(n) x^n / n!$ with
$[x^n]\, \exp(n^3 x) / A(x)^{n^2} = 0$ for $n \ge 1$, and OEIS A317343 is the e.g.f. with
$[x^n]\, \exp(n^2 x) / A(x)^n = 0$ for $n \ge 1$. Both belong to the family $F(a, b)$:
$A(0) = 1$ and $[x^n]\, \exp(n^a x)\, A(x)^{-n^b} = 0$ for every $n \ge 1$. The normalization
$A(0) = 1$ is taken from the data. The file proves:
- for all $a, b$, exactly one $A \in \mathbb{Q}[[x]]$ has the property of $F(a, b)$;
- if $1 \le b$ and `p` is a prime with $b < pa$, then every $a(n)$ lies in $\mathbb{Z}_{(p)}$
  and $a(n) \equiv a(n \bmod p) \pmod p$;
- if $1 \le b < 2a$, then every $a(n)$ is an integer;
- Paul D. Hanna's conjecture $a(5n + k) \equiv [1, 1, 5, 5, 5](k) \pmod{10}$ for A317345, and
  $a(5n + k) \equiv [1, 1, 3, 3, 5](k) \pmod{10}$ for A317343.

The proof works with Hurwitz series over a commutative ring: sequences $f_n = n!\,[x^n] f$ with
the binomial product $(fg)_n = \sum_i \binom{n}{i} f_i g_{n-i}$. Write $H$ for the Hurwitz series
of $A^{-1}$ and $e_c$ for the series of $\exp(cx)$, with coefficients $c^k$. The exponential
$\exp(f)$ of a series with $f_0 = 0$ is the solution of $DE = (Df) E$ with $E_0 = 1$. The
condition says $H_0 = 1$ and $(e_{n^a} H^{n^b})_n = 0$ for $n \ge 1$.

*Existence and uniqueness.* If $F$ and $G$ have constant term $1$ and agree below $n$, then
$(e_c F^m)_n - (e_c G^m)_n = m (F_n - G_n)$. Over $\mathbb{Q}$ the condition is therefore the
fixed-point equation of the causal operator $H_n \mapsto H_n - (e_{n^a} H^{n^b})_n / n^b$, which
has exactly one fixed point. The solution $A$ is the inverse of the power series with Hurwitz
coefficients $H_n$.

*The `p`-adic step.* Fix a prime `p` with $1 \le b < pa$ and map $H$ to $\mathbb{Q}_p$.
- For $n < p$, $n^b$ is a unit of $\mathbb{Z}_p$, so the identity above shows that
  $H_0, \dots, H_{p-1}$ lie in $\mathbb{Z}_p$.
- Let $L = \int (DG) G^{-1}$ be the logarithm of the integral series $G$ with these first
  coefficients, cut $L$ off from index `p` on, and put $S = L + x$. Then $S_0 = S_1 = 0$ (as
  $H_1 = -1$) and $S_k = 0$ for $k \ge p$. The comparison series $\tilde H = \exp(S - x)$ agrees
  with $H$ below `p`.
- Residual estimate: $\varepsilon_n = (e_{n^a} \tilde H^{n^b})_n = (e_{n^a - n^b} \exp(n^b S))_n$
  is divisible by $p^{b v_p(n) + 1}$.
  - If $p \mid n$, write $\exp(mS) = 1 + mS + m^2 W$ with $m = n^b$. Then $p^{b v_p(n) + 1}$
    divides $(n^a - n^b)^n$ because $b < pa$. It divides $m (e_c S)_n$ because $e_c \equiv 1$ and
    $S_n = 0$ modulo `p`, and it divides $m^2$.
  - If $p \nmid n$, reduce modulo `p`. Over $\mathbb{F}_p$, the series that vanish from index `p`
    on are closed under products, because a carry makes the binomial coefficient vanish. The
    exponential of such a series with no linear term is again such a series; this is checked
    monomial by monomial. For such $G$, Lucas' theorem gives
    $(e_c G)_{N + p} = c^p (e_c G)_N$. So $\varepsilon_n \equiv c^{n - n_0} \varepsilon_{n_0}$
    with $n_0 = n \bmod p$, and $\varepsilon_{n_0} = 0$ because $\tilde H$ agrees with $H$ below
    `p`.
- Induction on $n$: let $H'$ lift $H$ below $n$ to $\mathbb{Z}_p$, with $H' \equiv \tilde H$
  modulo `p`. Then $H'^{n^b} \equiv \tilde H^{n^b} \pmod{p^{b v_p(n) + 1}}$
  (`dvd_sub_pow_of_dvd_sub`). The residual estimate and the identity above give
  $n^b (H_n - \tilde H_n) \in p^{b v_p(n) + 1} \mathbb{Z}_p$. So $H_n \in \mathbb{Z}_p$ and
  $H_n \equiv \tilde H_n \pmod p$.
- Hence the integral lift of $A = H^{-1}$ is congruent modulo `p` to
  $\tilde H^{-1} = e_1 \exp(-S)$, and the period lemma with $c = 1$ gives
  $a(n) \equiv a(n \bmod p) \pmod p$.

*Integrality and the residues modulo 10.* If $b < 2a$, then $b < pa$ for every prime `p`, and a
rational number that is `p`-integral for every `p` is an integer. A317345 and A317343 have
$b < 2a$. Modulo `p`, the residues of $a(0), \dots, a(p - 1)$ are determined by the condition for
$n < p$, since $n^b$ is a unit there. Kernel computations check the candidates: the residues
$1, 1$ modulo $2$, and $1, 1, 0, 0, 0$ (A317345) and $1, 1, 3, 3, 0$ (A317343) modulo $5$. The
Chinese remainder theorem gives the residues modulo $10$. A kernel computation also checks the
first terms $1, 1, 5, 445, 196105$ and $1, 1, 3, 43, 1945$.

*References:*
- Paul D. Hanna, [A317345](https://oeis.org/A317345), July 26, 2018.
- Paul D. Hanna, [A317343](https://oeis.org/A317343), July 26, 2018.
-/

@[expose] public section

namespace OeisA317345

open PowerSeries

/-- The family $F(a, b)$: $A(0) = 1$ and $[x^n]\,\exp(n^a x)\,A(x)^{-n^b} = 0$ for every
$n \ge 1$. -/
def IsSolution (a b : ℕ) (A : ℚ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧
    ∀ n : ℕ, 1 ≤ n → coeff n (rescale ((n : ℚ) ^ a) (exp ℚ) * A⁻¹ ^ (n ^ b)) = 0

end OeisA317345

namespace OeisA317345

/-! ### Hurwitz series

The Hurwitz-series basics below (ring structure, derivative, constants, the variable, coefficient
maps and causal fixed points) are adapted from this repository's A326097 package. -/

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

/-- The closed form of the binomial product. -/
lemma prod_eq_sum (a b : ℕ → R) (n : ℕ) :
    prod a b n = ∑ i ∈ Finset.range (n + 1), (n.choose i : R) * (a i * b (n - i)) := by
  induction n generalizing a b with
  | zero => simp [prod]
  | succ n ih =>
    have h := Finset.sum_choose_succ_mul (fun i j => a i * b j) n
    rw [prod_succ, ih, ih, show n + 1 + 1 = n + 2 from rfl, h, add_comm]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_) rfl
    simp only [Finset.mem_range] at hi
    simp only [shift]
    rw [show n - i + 1 = n + 1 - i by omega]

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

/-- The closed form of a product coefficient. -/
lemma coeff_mul_sum (f g : Hur R) (n : ℕ) :
    (f * g).coeff n =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : R) * (f.coeff i * g.coeff (n - i)) :=
  prod_eq_sum _ _ _

/-- If $f$ vanishes below $n$, then $(fg)_n = f_n g_0$. -/
lemma coeff_mul_of_vanish (f g : Hur R) (n : ℕ) (h : ∀ k < n, f.coeff k = 0) :
    (f * g).coeff n = f.coeff n * g.coeff 0 := by
  rw [coeff_mul_sum, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul, Nat.sub_self]
  intro i hi
  rw [h i (Finset.mem_range.1 hi), zero_mul, mul_zero]

/-- If $Z_0 = 0$, then $(ZG)_n$ only uses the coefficients of $G$ below $n$. -/
lemma coeff_mul_congr_of_zero (Z G G' : Hur R) (n : ℕ) (hZ : Z.coeff 0 = 0)
    (h : ∀ k < n, G.coeff k = G'.coeff k) : (Z * G).coeff n = (Z * G').coeff n := by
  rw [coeff_mul_sum, coeff_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [hZ]
  · rw [h (n - i) (by have := Finset.mem_range.1 hi; omega)]

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

lemma natCast_eq_C (m : ℕ) : (m : Hur R) = C (m : R) := rfl

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

lemma C_add (r s : R) : C (r + s) = C r + C s := by
  ext n
  simp only [coeff_add, coeff_C]
  split_ifs <;> simp

lemma C_neg (r : R) : C (-r) = -C r := by
  ext n
  simp only [coeff_neg, coeff_C]
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

lemma D_C_mul (r : R) (f : Hur R) : D (C r * f) = C r * D f := by
  rw [D_mul, D_C, zero_mul, zero_add]

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

/-- The EGF variable $x$. -/
def x : Hur R := ⟨fun n => if n = 1 then 1 else 0⟩

lemma coeff_x (n : ℕ) : (x : Hur R).coeff n = if n = 1 then 1 else 0 := rfl

lemma D_x : D (x : Hur R) = 1 := by
  ext n
  cases n <;> simp [x, coeff_one]

/-- The Hurwitz monomial $x^{[k]} = x^k / k!$. -/
def mono (k : ℕ) : Hur R := ⟨fun n => if n = k then 1 else 0⟩

lemma D_mono (k : ℕ) : D (mono (k + 1) : Hur R) = mono k := by
  ext n
  simp [mono]

lemma coeff_mono_mul (k : ℕ) (f : Hur R) (N : ℕ) :
    (mono k * f).coeff N = if k ≤ N then (N.choose k : R) * f.coeff (N - k) else 0 := by
  rw [coeff_mul_sum]
  simp only [mono, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- The `n`-th coefficient as an additive map. -/
def coeffAdd (n : ℕ) : Hur R →+ R where
  toFun f := f.coeff n
  map_zero' := rfl
  map_add' _ _ := rfl

lemma coeff_sum {ι : Type*} (s : Finset ι) (F : ι → Hur R) (n : ℕ) :
    (∑ i ∈ s, F i).coeff n = ∑ i ∈ s, (F i).coeff n :=
  map_sum (coeffAdd n) F s

/-- A series that vanishes from index $N$ on is a finite sum of monomials. -/
lemma eq_sum_mono (S : Hur R) (N : ℕ) (h : ∀ k, N ≤ k → S.coeff k = 0) :
    S = ∑ k ∈ Finset.range N, C (S.coeff k) * mono k := by
  ext n
  rw [coeff_sum]
  simp only [C_mul_coeff, mono, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · exact h n (by simpa using hn)

lemma coeff_mul_congr (f g f' g' : Hur R) (n : ℕ) (hf : ∀ k ≤ n, f.coeff k = f'.coeff k)
    (hg : ∀ k ≤ n, g.coeff k = g'.coeff k) : (f * g).coeff n = (f' * g').coeff n :=
  prod_congr _ _ _ _ n hf hg

lemma coeff_pow_congr (F G : Hur R) (n : ℕ) (h : ∀ k ≤ n, F.coeff k = G.coeff k) (m : ℕ) :
    ∀ k ≤ n, (F ^ m).coeff k = (G ^ m).coeff k := by
  induction m with
  | zero => intro k _; rfl
  | succ m ih =>
    intro k hk
    rw [pow_succ, pow_succ]
    exact coeff_mul_congr _ _ _ _ k (fun j hj => ih j (by omega)) (fun j hj => h j (by omega))

/-- Integration: $(\int h)_0 = 0$ and $(\int h)_{n+1} = h_n$. -/
def integ (h : Hur R) : Hur R := ⟨fun n => match n with
  | 0 => 0
  | n + 1 => h.coeff n⟩

@[simp] lemma integ_coeff_zero (h : Hur R) : (integ h).coeff 0 = 0 := rfl
@[simp] lemma integ_coeff_succ (h : Hur R) (n : ℕ) : (integ h).coeff (n + 1) = h.coeff n := rfl

lemma D_integ (h : Hur R) : D (integ h) = h := rfl

lemma C_add_integ_D (f : Hur R) : C (f.coeff 0) + integ (D f) = f := by
  ext n
  cases n with
  | zero => simp [coeff_C]
  | succ n => simp [coeff_C]

lemma integ_add (f g : Hur R) : integ (f + g) = integ f + integ g := by
  ext n
  cases n <;> simp

lemma integ_C_mul (r : R) (f : Hur R) : integ (C r * f) = C r * integ f := by
  ext n
  rw [C_mul_coeff]
  cases n with
  | zero => simp
  | succ n => rw [integ_coeff_succ, integ_coeff_succ, C_mul_coeff]

/-- Divisibility by a constant, coefficient by coefficient. -/
lemma C_dvd_of_forall (r : R) (f : Hur R) (h : ∀ k, r ∣ f.coeff k) : C r ∣ f :=
  ⟨⟨fun k => (h k).choose⟩, by ext k; rw [C_mul_coeff]; exact (h k).choose_spec⟩

lemma coeff_dvd_of_C_dvd {r : R} {f : Hur R} (h : C r ∣ f) (k : ℕ) : r ∣ f.coeff k := by
  obtain ⟨g, rfl⟩ := h
  rw [C_mul_coeff]
  exact dvd_mul_right r _

lemma inv_unique' {α : Type*} [CommRing α] {u v w : α} (hv : u * v = 1) (hw : u * w = 1) :
    v = w := by
  calc v = v * (u * w) := by rw [hw, mul_one]
    _ = (u * v) * w := by ring
    _ = w := by rw [hv, one_mul]

end Ring

/-! ### Causal operators and their fixed points -/

section Causal
variable {R : Type*} [CommRing R]

/-- `T` is causal: coefficient `n` of `T f` only uses the coefficients of `f` below `n`. -/
def Causal (T : Hur R → Hur R) : Prop :=
  ∀ n (f g : Hur R), (∀ k < n, f.coeff k = g.coeff k) → (T f).coeff n = (T g).coeff n

omit [CommRing R] in
/-- A causal operator has at most one fixed point. -/
theorem Causal.unique {T : Hur R → Hur R} (hT : Causal T) {f g : Hur R} (hf : T f = f)
    (hg : T g = g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    calc f.coeff n = (T f).coeff n := by rw [hf]
      _ = (T g).coeff n := hT n f g ih
      _ = g.coeff n := by rw [hg]

/-- The coefficient recursion for the fixed point of a causal operator. -/
def fixSeq (T : Hur R → Hur R) (n : ℕ) : R :=
  (T ⟨fun k => if _h : k < n then fixSeq T k else 0⟩).coeff n
termination_by n

/-- The fixed point of a causal operator. -/
def fix (T : Hur R → Hur R) : Hur R := ⟨fixSeq T⟩

theorem Causal.fix_eq {T : Hur R → Hur R} (hT : Causal T) : T (fix T) = fix T := by
  ext n
  change (T (fix T)).coeff n = fixSeq T n
  rw [fixSeq]
  apply hT
  intro k hk
  simp [fix, hk]

end Causal

/-! ### Exponentials, inverses and logarithms -/

section Exp
variable {R : Type*} [CommRing R]

/-- The operator $E \mapsto 1 + \int (Df)\,E$, whose fixed point is $\exp(f - f_0)$. -/
def expOp (f E : Hur R) : Hur R := 1 + integ (D f * E)

lemma expOp_causal (f : Hur R) : Causal (expOp f) := by
  intro n g g' h
  cases n with
  | zero => rfl
  | succ n =>
    change (1 : Hur R).coeff (n + 1) + (D f * g).coeff n =
      (1 : Hur R).coeff (n + 1) + (D f * g').coeff n
    rw [coeff_mul_congr (D f) g (D f) g' n (fun _ _ => rfl) (fun k hk => h k (by omega))]

/-- The exponential $\exp(f - f_0)$, the solution of $DE = (Df) E$ with $E_0 = 1$. -/
def hexp (f : Hur R) : Hur R := fix (expOp f)

lemma hexp_spec (f : Hur R) : 1 + integ (D f * hexp f) = hexp f := (expOp_causal f).fix_eq

lemma hexp_coeff_zero (f : Hur R) : (hexp f).coeff 0 = 1 := by
  rw [← hexp_spec]
  simp [coeff_one]

lemma D_hexp (f : Hur R) : D (hexp f) = D f * hexp f := by
  conv_lhs => rw [← hexp_spec]
  rw [D_add, D_one, zero_add, D_integ]

lemma hexp_unique {f E : Hur R} (h0 : E.coeff 0 = 1) (hD : D E = D f * E) : E = hexp f := by
  apply (expOp_causal f).unique _ (hexp_spec f)
  change 1 + integ (D f * E) = E
  rw [← hD]
  have h := C_add_integ_D E
  rw [h0, C_one] at h
  exact h

lemma hexp_add (f g : Hur R) : hexp (f + g) = hexp f * hexp g := by
  symm
  apply hexp_unique
  · rw [coeff_mul_zero, hexp_coeff_zero, hexp_coeff_zero, one_mul]
  · rw [D_mul, D_hexp, D_hexp, D_add]
    ring

lemma hexp_zero : hexp (0 : Hur R) = 1 :=
  (hexp_unique (by simp [coeff_one]) (by rw [D_one, D_zero, zero_mul])).symm

lemma hexp_natCast_mul (k : ℕ) (f : Hur R) : hexp ((k : Hur R) * f) = hexp f ^ k := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_mul, hexp_zero, pow_zero]
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, hexp_add, ih, pow_succ]

lemma hexp_sum {ι : Type*} (s : Finset ι) (F : ι → Hur R) :
    hexp (∑ i ∈ s, F i) = ∏ i ∈ s, hexp (F i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty, hexp_zero]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi, hexp_add, ih]

/-- A coefficient of $\exp(f)$ only uses coefficients of $f$ of the same or lower index. -/
lemma hexp_congr (f g : Hur R) (n : ℕ) (h : ∀ k ≤ n, f.coeff k = g.coeff k) :
    ∀ j ≤ n, (hexp f).coeff j = (hexp g).coeff j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    cases j with
    | zero => rw [hexp_coeff_zero, hexp_coeff_zero]
    | succ i =>
      rw [← coeff_D, ← coeff_D, D_hexp, D_hexp]
      apply coeff_mul_congr
      · intro k hk
        exact h (k + 1) (by omega)
      · intro k hk
        exact ih k (by omega) (by omega)

/-- The exponential $e^{cx}$, with coefficients $c^k$. -/
def ex (c : R) : Hur R := ⟨fun k => c ^ k⟩

lemma coeff_ex (c : R) (k : ℕ) : (ex c).coeff k = c ^ k := rfl

lemma ex_eq_hexp (c : R) : ex c = hexp (C c * x) := by
  apply hexp_unique
  · exact pow_zero c
  · rw [D_C_mul, D_x, mul_one]
    ext k
    rw [C_mul_coeff, coeff_D, coeff_ex, coeff_ex, pow_succ']

lemma ex_add (c d : R) : ex (c + d) = ex c * ex d := by
  rw [ex_eq_hexp, ex_eq_hexp, ex_eq_hexp, C_add, add_mul, hexp_add]

lemma ex_zero : ex (0 : R) = 1 := by
  ext k
  rw [coeff_ex, coeff_one]
  cases k <;> simp

/-- The key identity: $e^{cx} \exp(S - x)^m = e^{(c - m)x} \exp(m S)$. -/
lemma ex_mul_hexp_pow (c : R) (S : Hur R) (m : ℕ) :
    ex c * hexp (S - x) ^ m = ex (c - m) * hexp (C (m : R) * S) := by
  rw [← hexp_natCast_mul, natCast_eq_C, sub_eq_add_neg c, ex_add, ex_eq_hexp (-(m : R)),
    mul_assoc, ← hexp_add]
  congr 2
  rw [C_neg]
  ring

/-- $\exp(mS) = 1 + mS + m^2 W$ for some $W$, when $S_0 = 0$. -/
lemma hexp_decomp (m : R) (S : Hur R) (hS0 : S.coeff 0 = 0) :
    ∃ W : Hur R, hexp (C m * S) = 1 + C m * S + C m * C m * W := by
  have hE : hexp (C m * S) - 1 = C m * integ (D S * hexp (C m * S)) := by
    have h := C_add_integ_D (hexp (C m * S))
    rw [hexp_coeff_zero, C_one, D_hexp, D_C_mul, mul_assoc, integ_C_mul] at h
    linear_combination (-1 : Hur R) * h
  obtain ⟨g, hg⟩ : C m ∣ hexp (C m * S) - 1 := ⟨_, hE⟩
  refine ⟨integ (D S * g), ?_⟩
  have e3 : integ (D S) = S := by
    have h := C_add_integ_D S
    rwa [hS0, C_zero, zero_add] at h
  have e1 : D S * hexp (C m * S) = D S + C m * (D S * g) := by
    linear_combination (D S) * hg
  calc hexp (C m * S) = 1 + (hexp (C m * S) - 1) := by ring
    _ = 1 + C m * integ (D S + C m * (D S * g)) := by rw [hE, e1]
    _ = 1 + C m * S + C m * C m * integ (D S * g) := by
      rw [integ_add, integ_C_mul, e3]
      ring

/-- The operator $H \mapsto 1 + (1 - B) H$, whose fixed point is $B^{-1}$ when $B_0 = 1$. -/
def invOp (B H : Hur R) : Hur R := 1 + (1 - B) * H

lemma invOp_causal {B : Hur R} (hB : B.coeff 0 = 1) : Causal (invOp B) := by
  intro n g g' h
  change (1 : Hur R).coeff n + ((1 - B) * g).coeff n =
    (1 : Hur R).coeff n + ((1 - B) * g').coeff n
  rw [coeff_mul_congr_of_zero _ g g' n (by rw [coeff_sub, hB]; simp [coeff_one]) h]

/-- The inverse of a series with constant term $1$. -/
def hinv (B : Hur R) : Hur R := fix (invOp B)

lemma mul_hinv {B : Hur R} (hB : B.coeff 0 = 1) : B * hinv B = 1 := by
  have h : 1 + (1 - B) * hinv B = hinv B := (invOp_causal hB).fix_eq
  linear_combination (-1 : Hur R) * h

lemma hinv_coeff_zero {B : Hur R} (hB : B.coeff 0 = 1) : (hinv B).coeff 0 = 1 := by
  have h := congrArg (fun F => Hur.coeff F 0) (mul_hinv hB)
  simp only [coeff_mul_zero, hB, one_mul] at h
  rw [h]
  rfl

/-- The logarithm: if $G_0 = 1$, then $L = \int (DG)\,G^{-1}$ satisfies $\exp(L) = G$. -/
lemma exists_log {G : Hur R} (hG : G.coeff 0 = 1) :
    hexp (integ (D G * hinv G)) = G := by
  symm
  apply hexp_unique hG
  rw [D_integ, mul_assoc, mul_comm (hinv G) G, mul_hinv hG, mul_one]

/-- If $F$ and $G$ have constant term $1$ and agree below $n$, then
$(QF^m)_n - (QG^m)_n = m (F_n - G_n)$ whenever $Q_0 = 1$. -/
lemma coeff_mul_pow_sub (Q F G : Hur R) (hQ : Q.coeff 0 = 1) (hF : F.coeff 0 = 1)
    (hG : G.coeff 0 = 1) (n m : ℕ) (h : ∀ k < n, F.coeff k = G.coeff k) :
    (Q * F ^ m).coeff n - (Q * G ^ m).coeff n = m * (F.coeff n - G.coeff n) := by
  have key : Q * F ^ m - Q * G ^ m =
      (F - G) * (Q * ∑ i ∈ Finset.range m, F ^ i * G ^ (m - 1 - i)) := by
    rw [← mul_sub, ← geom_sum₂_mul]
    ring
  have h0 : (Q * ∑ i ∈ Finset.range m, F ^ i * G ^ (m - 1 - i)).coeff 0 = m := by
    rw [← coeff0_apply, map_mul, map_sum]
    simp only [map_mul, map_pow, coeff0_apply, hQ, hF, hG, one_pow, one_mul,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [← coeff_sub, key,
    coeff_mul_of_vanish _ _ n (fun k hk => by rw [coeff_sub, h k hk, sub_self]), h0, coeff_sub,
    mul_comm]

/-- Two series that solve the defining conditions below `N` agree below `N`, when every
$n^b$ with $1 \le n < N$ is a non-zero-divisor. -/
lemma agree_below (a b : ℕ) {H G : Hur R} (hH0 : H.coeff 0 = 1) (hG0 : G.coeff 0 = 1) (N : ℕ)
    (hH : ∀ n < N, 1 ≤ n → (ex ((n : R) ^ a) * H ^ (n ^ b)).coeff n = 0)
    (hG : ∀ n < N, 1 ≤ n → (ex ((n : R) ^ a) * G ^ (n ^ b)).coeff n = 0)
    (hu : ∀ n < N, 1 ≤ n → ∀ y : R, (n : R) ^ b * y = 0 → y = 0) :
    ∀ n < N, H.coeff n = G.coeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · rw [hH0, hG0]
    · have key := coeff_mul_pow_sub (ex ((n : R) ^ a)) H G (pow_zero _) hH0 hG0 n (n ^ b)
        (fun k hk => ih k hk (by omega))
      rw [hH n hn hn1, hG n hn hn1, sub_self, Nat.cast_pow] at key
      exact sub_eq_zero.1 (hu n hn hn1 _ key.symm)

/-- If $XG$ and $YG$ agree below `N` and $G_0 = 1$, then $X$ and $Y$ agree below `N`. -/
lemma eq_of_mul_eq_below {X Y G : Hur R} (hG : G.coeff 0 = 1) (N : ℕ)
    (h : ∀ k < N, (X * G).coeff k = (Y * G).coeff k) : ∀ k < N, X.coeff k = Y.coeff k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have h1 := coeff_mul_of_vanish (X - Y) G k
      (fun j hj => by rw [coeff_sub, ih j hj (by omega), sub_self])
    rw [sub_mul, coeff_sub, h k hk, sub_self, hG, mul_one, coeff_sub] at h1
    exact sub_eq_zero.1 h1.symm

/-- The Hurwitz form of the defining condition. -/
def Cond (a b : ℕ) (H : Hur R) : Prop :=
  H.coeff 0 = 1 ∧ ∀ n : ℕ, 1 ≤ n → (ex ((n : R) ^ a) * H ^ (n ^ b)).coeff n = 0

lemma Cond.coeff_one {a b : ℕ} {H : Hur R} (hH : Cond a b H) : H.coeff 1 = -1 := by
  have h := hH.2 1 le_rfl
  rw [Nat.cast_one, one_pow, one_pow, pow_one, coeff_mul_sum] at h
  simp [Finset.sum_range_succ, coeff_ex, hH.1] at h
  linear_combination h

end Exp

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

lemma map_x (φ : R →+* S) : map φ (x : Hur R) = x := by
  ext n
  simp only [coeff_map, x]
  split_ifs <;> simp

lemma map_C (φ : R →+* S) (r : R) : map φ (C r) = C (φ r) := by
  ext n
  simp only [coeff_map, coeff_C]
  split_ifs <;> simp

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

lemma map_sub_eq (φ : R →+* S) (f g : Hur R) : map φ (f - g) = map φ f - map φ g := by
  rw [← mapHom_apply, map_sub]
  rfl

lemma map_ex (φ : R →+* S) (c : R) : map φ (ex c) = ex (φ c) := by
  ext k
  simp [coeff_map, coeff_ex]

lemma map_hexp (φ : R →+* S) (f : Hur R) : map φ (hexp f) = hexp (map φ f) := by
  apply hexp_unique
  · rw [coeff_map, hexp_coeff_zero, map_one]
  · rw [← map_D, D_hexp, map_mul', map_D]

lemma map_ex_mul_pow (φ : R →+* S) (c : R) (H : Hur R) (m : ℕ) :
    map φ (ex c * H ^ m) = ex (φ c) * map φ H ^ m := by
  rw [← mapHom_apply, map_mul, map_pow, mapHom_apply, mapHom_apply, map_ex]

lemma Cond.map {a b : ℕ} {H : Hur R} (hH : Cond a b H) (φ : R →+* S) : Cond a b (map φ H) := by
  refine ⟨by rw [coeff_map, hH.1, map_one], fun n hn => ?_⟩
  have h := congrArg φ (hH.2 n hn)
  rwa [← coeff_map, map_ex_mul_pow, map_pow, map_natCast, map_zero] at h

end Map

/-! ### Characteristic `p` -/

section CharP
variable (p : ℕ) [hp : Fact p.Prime]

/-- In characteristic `p`, $f^p = 1$ when $f_0 = 1$. -/
lemma pow_char_eq_one (f : Hur (ZMod p)) (hf : f.coeff 0 = 1) : f ^ p = 1 := by
  have hD : D (f ^ p) = 0 := by
    have e : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_lt.le
    have h := D_pow f (p - 1)
    rw [e, natCast_eq_C, ZMod.natCast_self, C_zero, zero_mul, zero_mul] at h
    exact h
  rw [eq_C_of_D_eq_zero hD, ← coeff0_apply, map_pow, coeff0_apply, hf, one_pow, C_one]

lemma pow_eq_pow_mod (f : Hur (ZMod p)) (hf : f.coeff 0 = 1) (m : ℕ) : f ^ m = f ^ (m % p) := by
  conv_lhs => rw [← Nat.div_add_mod m p, pow_add, pow_mul, pow_char_eq_one p f hf, one_pow,
    one_mul]

/-- A carry in base `p`: $\binom{i+j}{i} \equiv 0 \pmod p$ for $i, j < p \le i + j$. -/
lemma choose_cast_eq_zero {i j : ℕ} (hi : i < p) (hj : j < p) (hij : p ≤ i + j) :
    ((i + j).choose i : ZMod p) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
  rw [Nat.add_sub_cancel_left] at h
  have h1 : p ∣ (i + j).factorial := (Nat.Prime.dvd_factorial hp.out).2 hij
  rw [← h] at h1
  rcases (Nat.Prime.dvd_mul hp.out).1 h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hp.out).1 h2 with h3 | h3
    · exact h3
    · exact absurd ((Nat.Prime.dvd_factorial hp.out).1 h3) (by omega)
  · exact absurd ((Nat.Prime.dvd_factorial hp.out).1 h2) (by omega)

/-- Lucas' theorem for a lower index below `p`. -/
lemma choose_cast_mod {n i : ℕ} (hi : i < p) :
    (n.choose i : ZMod p) = ((n % p).choose i : ZMod p) := by
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n i p _
  rw [Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi, Nat.choose_zero_right, mul_one] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h

/-- The series over $\mathbb{F}_p$ whose coefficients vanish from index `p` on. -/
def InD (f : Hur (ZMod p)) : Prop := ∀ k, p ≤ k → f.coeff k = 0

lemma inD_one : InD p 1 := fun k hk => by
  rw [coeff_one, ite_eq_right (by have := hp.out.pos; omega)]

lemma inD_mul {f g : Hur (ZMod p)} (hf : InD p f) (hg : InD p g) : InD p (f * g) := by
  intro N hN
  rw [coeff_mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.1 hi
  by_cases h1 : p ≤ i
  · rw [hf i h1, zero_mul, mul_zero]
  by_cases h2 : p ≤ N - i
  · rw [hg _ h2, mul_zero, mul_zero]
  have h3 := choose_cast_eq_zero p (i := i) (j := N - i) (by omega) (by omega) (by omega)
  rw [show i + (N - i) = N by omega] at h3
  rw [h3, zero_mul]

lemma inD_prod {ι : Type*} (s : Finset ι) (F : ι → Hur (ZMod p)) (h : ∀ i ∈ s, InD p (F i)) :
    InD p (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact inD_one p
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact inD_mul p (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The exponential of a monomial $s\,x^{[j+1]}$ with $2 \le j + 1 < p$ lies in `InD`. -/
lemma hexp_mono_inD (s : ZMod p) {j : ℕ} (hj : 1 ≤ j) (hjp : j + 1 < p) :
    InD p (hexp (C s * mono (j + 1))) := by
  have hrec : ∀ M, (hexp (C s * mono (j + 1))).coeff (M + 1) =
      s * (if j ≤ M then (M.choose j : ZMod p) * (hexp (C s * mono (j + 1))).coeff (M - j)
        else 0) := by
    intro M
    rw [← coeff_D, D_hexp, D_C_mul, D_mono, mul_assoc, C_mul_coeff, coeff_mono_mul]
  set E := hexp (C s * mono (j + 1))
  have key : ∀ N, (¬ (j + 1) ∣ N → E.coeff N = 0) ∧ (p ≤ N → E.coeff N = 0) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      rcases N with _ | M
      · exact ⟨fun h => absurd (dvd_zero _) h, fun h => absurd h (by have := hp.out.pos; omega)⟩
      · rw [hrec M]
        by_cases hjM : j ≤ M
        · rw [ite_eq_left hjM]
          have hlt : M - j < M + 1 := by omega
          refine ⟨fun hd => ?_, fun hpM => ?_⟩
          · have hnd : ¬ (j + 1) ∣ M - j := fun h' => hd (by
              rw [show M + 1 = (M - j) + (j + 1) by omega]
              exact dvd_add h' dvd_rfl)
            rw [(ih _ hlt).1 hnd, mul_zero, mul_zero]
          · by_cases hpj : p ≤ M - j
            · rw [(ih _ hlt).2 hpj, mul_zero, mul_zero]
            by_cases hd : (j + 1) ∣ M - j
            · rcases Nat.lt_or_ge M p with hMp | hMp
              · exfalso
                have hdp : (j + 1) ∣ p := by
                  rw [show p = (M - j) + (j + 1) by omega]
                  exact dvd_add hd dvd_rfl
                rcases (Nat.dvd_prime hp.out).1 hdp with h1 | h1 <;> omega
              · have h3 := choose_cast_eq_zero p (i := j) (j := M - j) (by omega) (by omega)
                  (by omega)
                rw [show j + (M - j) = M by omega] at h3
                rw [h3, zero_mul, mul_zero]
            · rw [(ih _ hlt).1 hd, mul_zero, mul_zero]
        · rw [ite_eq_right hjM, mul_zero]
          exact ⟨fun _ => rfl, fun _ => rfl⟩
  exact fun N hN => (key N).2 hN

/-- The exponential of a polynomial of degree below `p` without constant or linear term lies in
`InD`. -/
lemma hexp_inD {S : Hur (ZMod p)} (h0 : S.coeff 0 = 0) (h1 : S.coeff 1 = 0) (hS : InD p S) :
    InD p (hexp S) := by
  rw [eq_sum_mono S p hS, hexp_sum]
  apply inD_prod
  intro k hk
  have hk' := Finset.mem_range.1 hk
  match k, hk' with
  | 0, _ => rw [h0, C_zero, zero_mul, hexp_zero]; exact inD_one p
  | 1, _ => rw [h1, C_zero, zero_mul, hexp_zero]; exact inD_one p
  | j + 2, h => exact hexp_mono_inD p _ (by omega) h

lemma coeff_mul_ex_eq_sum {G : Hur (ZMod p)} (hG : InD p G) (c : ZMod p) (N : ℕ) :
    (G * ex c).coeff N =
      ∑ i ∈ Finset.range p, (N.choose i : ZMod p) * (G.coeff i * c ^ (N - i)) := by
  rw [coeff_mul_sum]
  simp only [coeff_ex]
  have hsub1 : Finset.range (N + 1) ⊆ Finset.range (N + 1 + p) :=
    Finset.range_subset_range.2 (by omega)
  have hsub2 : Finset.range p ⊆ Finset.range (N + 1 + p) :=
    Finset.range_subset_range.2 (by omega)
  rw [Finset.sum_subset hsub1, Finset.sum_subset hsub2]
  · intro i _ hi
    rw [hG i (by simpa using hi), zero_mul, mul_zero]
  · intro i _ hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi), Nat.cast_zero, zero_mul]

/-- If $G$ lies in `InD`, then $F = e^{cx} G$ satisfies $F_{N+p} = c^p F_N$. -/
lemma period {G : Hur (ZMod p)} (hG : InD p G) (c : ZMod p) (N : ℕ) :
    (ex c * G).coeff (N + p) = c ^ p * (ex c * G).coeff N := by
  rw [mul_comm, coeff_mul_ex_eq_sum p hG, coeff_mul_ex_eq_sum p hG, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.1 hi
  rw [choose_cast_mod p (n := N + p) hi', choose_cast_mod p (n := N) hi', Nat.add_mod_right]
  by_cases hiN : i ≤ N
  · rw [show N + p - i = (N - i) + p by omega, pow_add]
    ring
  · have hN : N % p = N := Nat.mod_eq_of_lt (by omega)
    rw [hN, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul, mul_zero]

lemma period_iter {G : Hur (ZMod p)} (hG : InD p G) (c : ZMod p) (n0 k : ℕ) :
    (ex c * G).coeff (n0 + p * k) = (c ^ p) ^ k * (ex c * G).coeff n0 := by
  induction k with
  | zero => rw [mul_zero, add_zero, pow_zero, one_mul]
  | succ k ih =>
    rw [Nat.mul_succ, ← add_assoc, period p hG, ih, pow_succ]
    ring

end CharP

end Hur

/-! ### The `p`-adic argument -/

section Padic
open Hur

variable {p : ℕ} [hp : Fact p.Prime]

local notation "ιP" => (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])
local notation "ρP" => (PadicInt.toZMod : ℤ_[p] →+* ZMod p)

lemma toZMod_eq_zero_iff (y : ℤ_[p]) : ρP y = 0 ↔ (p : ℤ_[p]) ∣ y := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

lemma isUnit_natCast {u : ℕ} (hu : ¬ p ∣ u) : IsUnit (u : ℤ_[p]) := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast,
    ZMod.natCast_eq_zero_iff]
  exact hu

lemma coe_injective : Function.Injective ιP := fun _ _ h => PadicInt.ext h

/-- One step of the recursion: if $H'$ lifts $H$ below $n$ and
$(e^{n^a x} H'^{n^b})_n = n^b t$, then $H_n = H'_n - t$. -/
lemma step_lift {O K : Type*} [CommRing O] [Field K] (ι : O →+* K) (a b n : ℕ) (hn : 1 ≤ n)
    (hm : (n : K) ^ b ≠ 0) (H : Hur K) (hH : Cond a b H)
    (H' : Hur O) (hH'0 : H'.coeff 0 = 1) (hag : ∀ k < n, H.coeff k = ι (H'.coeff k))
    (t : O) (ht : (ex ((n : O) ^ a) * H' ^ (n ^ b)).coeff n = (n : O) ^ b * t) :
    H.coeff n = ι (H'.coeff n - t) := by
  have key := coeff_mul_pow_sub (ex ((n : K) ^ a)) H (map ι H') (pow_zero _) hH.1
    (by rw [coeff_map, hH'0, map_one]) n (n ^ b) (fun k hk => by rw [coeff_map, hag k hk])
  have h2 : (ex ((n : K) ^ a) * map ι H' ^ (n ^ b)).coeff n = (n : K) ^ b * ι t := by
    rw [show ((n : K) ^ a) = ι ((n : O) ^ a) by rw [map_pow, map_natCast], ← map_ex_mul_pow,
      coeff_map, ht, map_mul, map_pow, map_natCast]
  rw [hH.2 n hn, h2, coeff_map, Nat.cast_pow] at key
  rw [map_sub]
  have h3 : (n : K) ^ b * (H.coeff n - (ι (H'.coeff n) - ι t)) = 0 := by
    linear_combination (-1 : K) * key
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hm)

/-- Below `p` every coefficient of a solution is `p`-integral. -/
lemma lift_below (a b : ℕ) (H : Hur ℚ_[p]) (hH : Cond a b H) :
    ∀ n < p, ∃ y : ℤ_[p], H.coeff n = ιP y := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · exact ⟨1, by rw [hH.1, map_one]⟩
    · classical
      let H' : Hur ℤ_[p] := ⟨fun k => if h : k < n then (ih k h (by omega)).choose else 0⟩
      have hag : ∀ k < n, H.coeff k = ιP (H'.coeff k) := fun k hk => by
        simp only [H', dite_eq_left hk]
        exact (ih k hk (by omega)).choose_spec
      have hH'0 : H'.coeff 0 = 1 := coe_injective (by rw [← hag 0 hn1, hH.1, map_one])
      have hu : IsUnit ((n : ℤ_[p]) ^ b) :=
        (isUnit_natCast (fun h => by have := Nat.le_of_dvd hn1 h; omega)).pow b
      obtain ⟨t, ht⟩ : (n : ℤ_[p]) ^ b ∣ (ex ((n : ℤ_[p]) ^ a) * H' ^ (n ^ b)).coeff n := hu.dvd
      exact ⟨H'.coeff n - t, step_lift ιP a b n hn1
        (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))) H hH H' hH'0 hag t ht⟩

/-- The comparison series $\exp(S - x)$: it agrees with the solution below `p`, and $S$ is a
polynomial of degree below `p` without constant or linear term. -/
lemma comparison (a b : ℕ) (H : Hur ℚ_[p]) (hH : Cond a b H) :
    ∃ S : Hur ℤ_[p], S.coeff 0 = 0 ∧ S.coeff 1 = 0 ∧ (∀ k, p ≤ k → S.coeff k = 0) ∧
      ∀ k < p, H.coeff k = ιP ((hexp (S - x)).coeff k) := by
  have hp2 := hp.out.two_le
  choose! y hy using lift_below a b H hH
  let G : Hur ℤ_[p] := ⟨fun k => if k = 0 then 1 else y k⟩
  have hG0 : G.coeff 0 = 1 := by simp [G]
  have hGk : ∀ k < p, H.coeff k = ιP (G.coeff k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hG0, hH.1, map_one]
    · simp only [G, ite_eq_right (Nat.pos_iff_ne_zero.1 hk0)]
      exact hy k hk
  obtain ⟨L, hL⟩ : ∃ L, L = integ (D G * hinv G) := ⟨_, rfl⟩
  have hLG : hexp L = G := by rw [hL]; exact exists_log hG0
  have hL0 : L.coeff 0 = 0 := by rw [hL]; rfl
  have hG1 : G.coeff 1 = -1 :=
    coe_injective (by rw [← hGk 1 (by omega), hH.coeff_one, map_neg, map_one])
  have hL1 : L.coeff 1 = -1 := by
    rw [hL]
    change (D G * hinv G).coeff 0 = -1
    rw [coeff_mul_zero, coeff_D, hinv_coeff_zero hG0, mul_one, hG1]
  let L' : Hur ℤ_[p] := ⟨fun k => if k < p then L.coeff k else 0⟩
  refine ⟨L' + x, ?_, ?_, ?_, ?_⟩
  · simp [L', coeff_x, hL0]
  · simp [L', coeff_x, hL1, show 1 < p by omega]
  · intro k hk
    simp [L', coeff_x, show ¬ k < p by omega, show k ≠ 1 by omega]
  · intro k hk
    rw [add_sub_cancel_right, hGk k hk, ← hLG]
    congr 1
    exact hexp_congr L L' k (fun j hj => (ite_eq_left (by omega)).symm) k le_rfl

/-- An integer estimate: if $p \mid n$ and $b < pa$, then $p^{b v_p(n) + 1}$ divides
$(n^a - n^b)^n$. -/
lemma int_pow_dvd (n a b : ℕ) (hn : 1 ≤ n) (hpn : p ∣ n) (hb : 1 ≤ b) (hbp : b < p * a) :
    (p : ℤ) ^ (b * n.factorization p + 1) ∣ ((n : ℤ) ^ a - (n : ℤ) ^ b) ^ n := by
  have hpp := hp.out
  have hv1 : 1 ≤ n.factorization p := (hpp.dvd_iff_one_le_factorization (by omega)).1 hpn
  have hnp : p ≤ n := Nat.le_of_dvd hn hpn
  have hpv : (p : ℤ) ^ n.factorization p ∣ n := by exact_mod_cast Nat.ordProj_dvd n p
  have hk : (p : ℤ) ^ (n.factorization p * min a b) ∣ (n : ℤ) ^ a - (n : ℤ) ^ b := by
    rw [pow_mul]
    apply dvd_sub
    · exact (pow_dvd_pow _ (min_le_left a b)).trans (pow_dvd_pow_of_dvd hpv a)
    · exact (pow_dvd_pow _ (min_le_right a b)).trans (pow_dvd_pow_of_dvd hpv b)
  have hle : b * n.factorization p + 1 ≤ n.factorization p * min a b * n := by
    have hvb : 1 ≤ n.factorization p * b := Nat.mul_le_mul hv1 hb
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab]
      have h1 : a * p ≤ a * n := Nat.mul_le_mul_left a hnp
      nlinarith [Nat.mul_le_mul_left (n.factorization p) h1,
        Nat.mul_le_mul_left (n.factorization p) hbp]
    · rw [min_eq_right hab]
      have h2 : 2 ≤ n := le_trans hpp.two_le hnp
      nlinarith [Nat.mul_le_mul_left (n.factorization p * b) h2]
  calc (p : ℤ) ^ (b * n.factorization p + 1)
      ∣ (p : ℤ) ^ (n.factorization p * min a b * n) := pow_dvd_pow _ hle
    _ = ((p : ℤ) ^ (n.factorization p * min a b)) ^ n := by rw [pow_mul]
    _ ∣ _ := pow_dvd_pow_of_dvd hk n

/-- The residual estimate: $p^{b v_p(n) + 1}$ divides $(e^{n^a x} \exp(S - x)^{n^b})_n$. -/
lemma residual (a b : ℕ) (hb : 1 ≤ b) (hbp : b < p * a) (S : Hur ℤ_[p]) (hS0 : S.coeff 0 = 0)
    (hS1 : S.coeff 1 = 0) (hS : ∀ k, p ≤ k → S.coeff k = 0)
    (hbase : ∀ n, 1 ≤ n → n < p →
      (ex ((n : ℤ_[p]) ^ a) * hexp (S - x) ^ (n ^ b)).coeff n = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    (p : ℤ_[p]) ^ (b * n.factorization p + 1) ∣
      (ex ((n : ℤ_[p]) ^ a) * hexp (S - x) ^ (n ^ b)).coeff n := by
  have hpp := hp.out
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · omega
    · exact h
  by_cases hpn : p ∣ n
  · have hnp : p ≤ n := Nat.le_of_dvd hn hpn
    have hv1 : 1 ≤ n.factorization p := (hpp.dvd_iff_one_le_factorization (by omega)).1 hpn
    rw [ex_mul_hexp_pow]
    set c : ℤ_[p] := (n : ℤ_[p]) ^ a - ((n ^ b : ℕ) : ℤ_[p]) with hc
    set m : ℤ_[p] := ((n ^ b : ℕ) : ℤ_[p]) with hm
    obtain ⟨W, hW⟩ := hexp_decomp m S hS0
    have hexpand : ex c * (1 + C m * S + C m * C m * W) =
        ex c + C m * (ex c * S) + C (m * m) * (ex c * W) := by
      rw [C_mul]
      ring
    rw [hW, hexpand, coeff_add, coeff_add, C_mul_coeff, C_mul_coeff, coeff_ex]
    have hm_dvd : (p : ℤ_[p]) ^ (b * n.factorization p) ∣ m := by
      have h1 : p ^ (b * n.factorization p) ∣ n ^ b := by
        rw [mul_comm, pow_mul]
        exact pow_dvd_pow_of_dvd (Nat.ordProj_dvd n p) b
      have h2 := Nat.cast_dvd_cast (α := ℤ_[p]) h1
      rwa [Nat.cast_pow p] at h2
    have hS_dvd : (p : ℤ_[p]) ∣ (ex c * S).coeff n := by
      rw [← toZMod_eq_zero_iff, ← coeff_map, map_mul', map_ex]
      have hc0 : ρP c = 0 := by
        rw [hc, map_sub, map_pow, map_natCast, map_natCast,
          (ZMod.natCast_eq_zero_iff n p).2 hpn,
          (ZMod.natCast_eq_zero_iff (n ^ b) p).2 (dvd_pow hpn (by omega)),
          zero_pow (by omega), sub_zero]
      rw [hc0, ex_zero, one_mul, coeff_map, hS n hnp, map_zero]
    refine dvd_add (dvd_add ?_ ?_) ?_
    · have h := map_dvd (Int.castRingHom ℤ_[p]) (int_pow_dvd n a b hn hpn hb hbp)
      simp only [map_pow, map_sub, map_natCast] at h
      rw [hc, hm, Nat.cast_pow]
      exact h
    · rw [pow_succ]
      exact mul_dvd_mul hm_dvd hS_dvd
    · apply dvd_mul_of_dvd_left
      calc (p : ℤ_[p]) ^ (b * n.factorization p + 1)
          ∣ (p : ℤ_[p]) ^ (b * n.factorization p) * (p : ℤ_[p]) ^ (b * n.factorization p) := by
            rw [← pow_add]
            exact pow_dvd_pow _ (by nlinarith)
        _ ∣ m * m := mul_dvd_mul hm_dvd hm_dvd
  · have hv0 : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
    rw [hv0, mul_zero, zero_add, pow_one, ← toZMod_eq_zero_iff]
    have hrho : ∀ N : ℕ, ρP ((ex ((N : ℤ_[p]) ^ a) * hexp (S - x) ^ (N ^ b)).coeff N) =
        (ex ((N : ZMod p) ^ a - (N : ZMod p) ^ b) *
          hexp (C ((N : ZMod p) ^ b) * map ρP S)).coeff N := by
      intro N
      rw [← coeff_map, map_ex_mul_pow, map_hexp, map_sub_eq, map_x, ex_mul_hexp_pow, map_pow,
        map_natCast, Nat.cast_pow]
    have hn0p : n % p < p := Nat.mod_lt n hpp.pos
    have hn01 : 1 ≤ n % p := Nat.pos_of_ne_zero (fun h => hpn (Nat.dvd_of_mod_eq_zero h))
    have hcast : (n : ZMod p) = ((n % p : ℕ) : ZMod p) := (ZMod.natCast_mod n p).symm
    have hG : InD p (hexp (C (((n % p : ℕ) : ZMod p) ^ b) * map ρP S)) := by
      apply hexp_inD p
      · rw [C_mul_coeff, coeff_map, hS0, map_zero, mul_zero]
      · rw [C_mul_coeff, coeff_map, hS1, map_zero, mul_zero]
      · intro k hk
        rw [C_mul_coeff, coeff_map, hS k hk, map_zero, mul_zero]
    have hbase' := hrho (n % p)
    rw [hbase (n % p) hn01 hn0p, map_zero] at hbase'
    rw [hrho n, hcast]
    set F := ex (((n % p : ℕ) : ZMod p) ^ a - ((n % p : ℕ) : ZMod p) ^ b) *
      hexp (C (((n % p : ℕ) : ZMod p) ^ b) * map ρP S) with hF
    have e : F.coeff n = F.coeff (n % p + p * (n / p)) := by rw [Nat.mod_add_div]
    rw [e, hF, period_iter p hG, ← hbase', mul_zero]

/-- The main induction: every coefficient of the solution is `p`-integral and congruent modulo
`p` to the coefficient of the comparison series. -/
lemma lift_all (a b : ℕ) (H : Hur ℚ_[p]) (hH : Cond a b H) (Ht : Hur ℤ_[p])
    (hHt0 : Ht.coeff 0 = 1)
    (h4 : ∀ n, 1 ≤ n → (p : ℤ_[p]) ^ (b * n.factorization p + 1) ∣
      (ex ((n : ℤ_[p]) ^ a) * Ht ^ (n ^ b)).coeff n) :
    ∀ n, ∃ y : ℤ_[p], H.coeff n = ιP y ∧ ρP y = ρP (Ht.coeff n) := by
  have hpp := hp.out
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · exact ⟨1, by rw [hH.1, map_one], by rw [hHt0]⟩
    classical
    let H' : Hur ℤ_[p] := ⟨fun k => if h : k < n then (ih k h).choose else Ht.coeff k⟩
    have hH'k : ∀ k (hk : k < n), H'.coeff k = (ih k hk).choose := fun k hk => dite_eq_left hk
    have hag : ∀ k < n, H.coeff k = ιP (H'.coeff k) := fun k hk => by
      rw [hH'k k hk]
      exact (ih k hk).choose_spec.1
    have hH'0 : H'.coeff 0 = 1 := coe_injective (by rw [← hag 0 hn1, hH.1, map_one])
    have hH'n : H'.coeff n = Ht.coeff n := dite_eq_right (lt_irrefl n)
    have hdvd : (p : Hur ℤ_[p]) ∣ H' - Ht := by
      rw [natCast_eq_C]
      apply C_dvd_of_forall
      intro k
      rw [coeff_sub]
      by_cases hk : k < n
      · rw [← toZMod_eq_zero_iff, map_sub, hH'k k hk, (ih k hk).choose_spec.2, sub_self]
      · rw [show H'.coeff k = Ht.coeff k from dite_eq_right hk, sub_self]
        exact dvd_zero _
    have hu : ¬ p ∣ n / p ^ n.factorization p := Nat.not_dvd_ordCompl hpp (by omega)
    have hm : n ^ b = p ^ (b * n.factorization p) * (n / p ^ n.factorization p) ^ b := by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
      rw [mul_pow, ← pow_mul, mul_comm (n.factorization p) b]
    have hlift : (p : Hur ℤ_[p]) ^ (b * n.factorization p + 1) ∣
        H' ^ (n ^ b) - Ht ^ (n ^ b) := by
      rw [hm, pow_mul H', pow_mul Ht]
      exact (dvd_sub_pow_of_dvd_sub hdvd (b * n.factorization p)).trans
        (sub_dvd_pow_sub_pow _ _ _)
    have hr : (p : ℤ_[p]) ^ (b * n.factorization p + 1) ∣
        (ex ((n : ℤ_[p]) ^ a) * H' ^ (n ^ b)).coeff n -
          (ex ((n : ℤ_[p]) ^ a) * Ht ^ (n ^ b)).coeff n := by
      rw [← coeff_sub, ← mul_sub]
      apply coeff_dvd_of_C_dvd
      rw [C_pow, ← natCast_eq_C]
      exact dvd_mul_of_dvd_right hlift _
    have hr' : (p : ℤ_[p]) ^ (b * n.factorization p + 1) ∣
        (ex ((n : ℤ_[p]) ^ a) * H' ^ (n ^ b)).coeff n := by
      have h := dvd_add hr (h4 n hn1)
      rwa [sub_add_cancel] at h
    obtain ⟨r', hr'⟩ := hr'
    obtain ⟨w', hw'⟩ : ∃ w', ((n / p ^ n.factorization p : ℕ) : ℤ_[p]) ^ b * w' = 1 := by
      have hw := (isUnit_natCast hu).pow b
      exact ⟨((hw.unit⁻¹ : (ℤ_[p])ˣ) : ℤ_[p]), hw.mul_val_inv⟩
    have hnb : (n : ℤ_[p]) ^ b = (p : ℤ_[p]) ^ (b * n.factorization p) *
        ((n / p ^ n.factorization p : ℕ) : ℤ_[p]) ^ b := by
      rw [← Nat.cast_pow, hm]
      push_cast
      ring
    refine ⟨Ht.coeff n - p * r' * w', ?_, ?_⟩
    · rw [← hH'n]
      apply step_lift ιP a b n hn1 (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))) H hH H' hH'0
        hag
      rw [hr', hnb]
      linear_combination (-(p : ℤ_[p]) ^ (b * n.factorization p + 1) * r') * hw'
    · rw [map_sub, map_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul, zero_mul,
        sub_zero]

/-- The `p`-adic theorem for Hurwitz series: if $B H = 1$ and $H$ satisfies the defining
condition over $\mathbb{Q}_p$ with $1 \le b < pa$, then $B$ has an integral lift $A'$ whose
reduction modulo `p` has period `p`. -/
theorem master (a b : ℕ) (hb : 1 ≤ b) (hbp : b < p * a) (H B : Hur ℚ_[p]) (hH : Cond a b H)
    (hBH : B * H = 1) :
    ∃ A' H' : Hur ℤ_[p], map ιP A' = B ∧ A' * H' = 1 ∧ Cond a b H' ∧
      ∀ n, ρP (A'.coeff n) = ρP (A'.coeff (n % p)) := by
  obtain ⟨S, hS0, hS1, hS, hagr⟩ := comparison a b H hH
  have hbase : ∀ n, 1 ≤ n → n < p →
      (ex ((n : ℤ_[p]) ^ a) * hexp (S - x) ^ (n ^ b)).coeff n = 0 := by
    intro n hn hnp
    apply coe_injective
    rw [← coeff_map, map_ex_mul_pow, map_pow, map_natCast, map_zero]
    refine Eq.trans ?_ (hH.2 n hn)
    apply coeff_mul_congr _ _ _ _ n (fun _ _ => rfl)
    exact coeff_pow_congr _ _ n (fun k hk => by rw [coeff_map, ← hagr k (by omega)]) _
  have h4 := residual a b hb hbp S hS0 hS1 hS hbase
  choose y hy using lift_all a b H hH (hexp (S - x)) (hexp_coeff_zero _) h4
  have hmapH : map ιP ⟨y⟩ = H := by
    ext n
    exact (hy n).1.symm
  have hH'0 : (⟨y⟩ : Hur ℤ_[p]).coeff 0 = 1 :=
    coe_injective (by rw [← coeff_map, hmapH, hH.1, map_one])
  have hcond : Cond a b (⟨y⟩ : Hur ℤ_[p]) := by
    refine ⟨hH'0, fun n hn => coe_injective ?_⟩
    rw [← coeff_map, map_ex_mul_pow, map_pow, map_natCast, hmapH, hH.2 n hn, map_zero]
  refine ⟨hinv ⟨y⟩, ⟨y⟩, ?_, by rw [mul_comm, mul_hinv hH'0], hcond, ?_⟩
  · have h1 : H * map ιP (hinv ⟨y⟩) = 1 := by
      rw [← hmapH, ← map_mul', mul_hinv hH'0, map_one']
    exact inv_unique' h1 (by rw [mul_comm]; exact hBH)
  · intro n
    have hAt : hexp (x - S) * hexp (S - x) = 1 := by
      rw [← hexp_add, sub_add_sub_cancel, sub_self, hexp_zero]
    have hmod : map ρP (hinv ⟨y⟩) = map ρP (hexp (x - S)) := by
      have e1 : map ρP ⟨y⟩ = map ρP (hexp (S - x)) := by
        ext k
        rw [coeff_map, coeff_map]
        exact (hy k).2
      have h1 : map ρP ⟨y⟩ * map ρP (hinv ⟨y⟩) = 1 := by
        rw [← map_mul', mul_hinv hH'0, map_one']
      have h2 : map ρP ⟨y⟩ * map ρP (hexp (x - S)) = 1 := by
        rw [e1, ← map_mul', mul_comm, hAt, map_one']
      exact inv_unique' h1 h2
    have hG : InD p (hexp (C (-1) * map ρP S)) := by
      apply hexp_inD p
      · rw [C_mul_coeff, coeff_map, hS0, map_zero, mul_zero]
      · rw [C_mul_coeff, coeff_map, hS1, map_zero, mul_zero]
      · intro k hk
        rw [C_mul_coeff, coeff_map, hS k hk, map_zero, mul_zero]
    have hform : map ρP (hexp (x - S)) = ex 1 * hexp (C (-1) * map ρP S) := by
      rw [map_hexp, map_sub_eq, map_x, ex_eq_hexp, ← hexp_add, C_neg, C_one]
      congr 1
      ring
    have key : ∀ k, ρP ((hinv ⟨y⟩).coeff k) = (ex 1 * hexp (C (-1) * map ρP S)).coeff k :=
      fun k => by rw [← coeff_map, hmod, hform]
    rw [key, key]
    calc (ex 1 * hexp (C (-1) * map ρP S)).coeff n
        = (ex 1 * hexp (C (-1) * map ρP S)).coeff (n % p + p * (n / p)) := by
          rw [Nat.mod_add_div]
      _ = _ := by rw [period_iter p hG, one_pow, one_pow, one_mul]

end Padic

/-! ### Rational solutions -/

section Rat
open Hur

/-- The series with constant term replaced by $1$. -/
def norm1 (H : Hur ℚ) : Hur ℚ := ⟨fun k => if k = 0 then 1 else H.coeff k⟩

lemma norm1_eq {H : Hur ℚ} (h : H.coeff 0 = 1) : norm1 H = H := by
  ext k
  change (if k = 0 then 1 else H.coeff k) = H.coeff k
  split_ifs with hk
  · rw [hk, h]
  · rfl

/-- The recursion $H_n \mapsto H_n - (e^{n^a x} H^{n^b})_n / n^b$, whose fixed points over
$\mathbb{Q}$ are the solutions. -/
def solOp (a b : ℕ) (H : Hur ℚ) : Hur ℚ :=
  ⟨fun n => if n = 0 then 1 else
    H.coeff n - (ex ((n : ℚ) ^ a) * norm1 H ^ (n ^ b)).coeff n / (n : ℚ) ^ b⟩

lemma solOp_causal (a b : ℕ) : Causal (solOp a b) := by
  intro n f g h
  change (if n = 0 then (1 : ℚ) else
      f.coeff n - (ex ((n : ℚ) ^ a) * norm1 f ^ (n ^ b)).coeff n / (n : ℚ) ^ b) =
    (if n = 0 then (1 : ℚ) else
      g.coeff n - (ex ((n : ℚ) ^ a) * norm1 g ^ (n ^ b)).coeff n / (n : ℚ) ^ b)
  split_ifs with hn
  · rfl
  · have key := coeff_mul_pow_sub (ex ((n : ℚ) ^ a)) (norm1 f) (norm1 g) (pow_zero _)
      (by simp [norm1]) (by simp [norm1]) n (n ^ b) (fun k hk => by
        change (if k = 0 then 1 else f.coeff k) = (if k = 0 then 1 else g.coeff k)
        rw [h k hk])
    have hfn : (norm1 f).coeff n = f.coeff n := ite_eq_right hn
    have hgn : (norm1 g).coeff n = g.coeff n := ite_eq_right hn
    rw [hfn, hgn, Nat.cast_pow] at key
    have hm : (n : ℚ) ^ b ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hn)
    rw [sub_eq_sub_iff_sub_eq_sub, ← sub_div, key, mul_div_cancel_left₀ _ hm]

lemma solOp_fixed_iff (a b : ℕ) (H : Hur ℚ) : solOp a b H = H ↔ Cond a b H := by
  have hcoeff : ∀ n, (solOp a b H).coeff n = if n = 0 then 1 else
      H.coeff n - (ex ((n : ℚ) ^ a) * norm1 H ^ (n ^ b)).coeff n / (n : ℚ) ^ b := fun n => rfl
  constructor
  · intro h
    have h0 : H.coeff 0 = 1 := by
      have h1 := hcoeff 0
      rw [h, ite_eq_left rfl] at h1
      exact h1
    refine ⟨h0, fun n hn => ?_⟩
    have h1 := hcoeff n
    rw [h, ite_eq_right (by omega), norm1_eq h0] at h1
    have hm : (n : ℚ) ^ b ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
    have h2 : (ex ((n : ℚ) ^ a) * H ^ (n ^ b)).coeff n / (n : ℚ) ^ b = 0 := by linarith
    exact (div_eq_zero_iff.1 h2).resolve_right hm
  · intro hH
    ext n
    rw [hcoeff]
    split_ifs with hn
    · rw [hn, hH.1]
    · rw [norm1_eq hH.1, hH.2 n (by omega), zero_div, sub_zero]

theorem existsUnique_cond (a b : ℕ) : ∃! H : Hur ℚ, Cond a b H :=
  ⟨fix (solOp a b), (solOp_fixed_iff a b _).1 (solOp_causal a b).fix_eq,
    fun G hG => (solOp_causal a b).unique ((solOp_fixed_iff a b G).2 hG)
      (solOp_causal a b).fix_eq⟩

/-- The residues below `p` from a candidate pair $(A_c, H_c)$ over $\mathbb{F}_p$. -/
lemma first_values (p : ℕ) [Fact p.Prime] (a b : ℕ) {Abar Hbar : Hur (ZMod p)}
    (Ac Hc : Hur (ZMod p)) (hAH : Abar * Hbar = 1) (hH : Cond a b Hbar) (hHc0 : Hc.coeff 0 = 1)
    (hHc : ∀ n < p, 1 ≤ n → (ex ((n : ZMod p) ^ a) * Hc ^ (n ^ b % p)).coeff n = 0)
    (hAc : ∀ k < p, (Ac * Hc).coeff k = (1 : Hur (ZMod p)).coeff k) :
    ∀ k < p, Abar.coeff k = Ac.coeff k := by
  have hagree := agree_below a b hH.1 hHc0 p (fun n _ hn => hH.2 n hn)
    (fun n hn hn1 => by rw [pow_eq_pow_mod p Hc hHc0]; exact hHc n hn hn1)
    (fun n hn hn1 y hy => (mul_eq_zero.1 hy).resolve_left (pow_ne_zero _ (by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => by have := Nat.le_of_dvd hn1 h; omega)))
  apply eq_of_mul_eq_below hHc0 p
  intro k hk
  rw [hAc k hk, ← hAH]
  exact coeff_mul_congr _ _ _ _ k (fun _ _ => rfl) (fun j hj => (hagree j (by omega)).symm)

end Rat

/-! ### Power series

The map `jet` to Hurwitz series is adapted from this repository's A326097 package. -/

section Bridge
open PowerSeries

/-- The Hurwitz series of EGF coefficients $n!\,[x^n] F$ of a rational power series. -/
noncomputable def jetFun (F : ℚ⟦X⟧) : Hur ℚ := ⟨fun n => (n.factorial : ℚ) * coeff n F⟩

lemma jetFun_coeff (F : ℚ⟦X⟧) (n : ℕ) : (jetFun F).coeff n = (n.factorial : ℚ) * coeff n F := rfl

lemma jetFun_derivative (F : ℚ⟦X⟧) : jetFun (derivative (R := ℚ) F) = Hur.D (jetFun F) := by
  ext n
  simp only [jetFun_coeff, Hur.coeff_D, coeff_derivative, Nat.factorial_succ, Nat.cast_mul]
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
    rw [← Hur.coeff_D, ← Hur.coeff_D, ← jetFun_derivative, (derivative (R := ℚ)).leibniz,
      smul_eq_mul, smul_eq_mul, jetFun_add, Hur.coeff_add, ih, ih, Hur.D_mul, Hur.coeff_add,
      jetFun_derivative, jetFun_derivative, add_comm, mul_comm (jetFun G) (Hur.D (jetFun F))]

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

lemma jet_injective : Function.Injective jet := by
  intro F G h
  ext n
  have he := congrArg (fun H => Hur.coeff H n) h
  simp only [jet_coeff] at he
  exact mul_left_cancel₀ (by exact_mod_cast n.factorial_ne_zero) he

lemma jet_rescale_exp (c : ℚ) : jet (rescale c (exp ℚ)) = Hur.ex c := by
  ext n
  rw [jet_coeff, coeff_rescale, coeff_exp, Hur.coeff_ex]
  have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  field_simp

lemma inv_inv_of {F : ℚ⟦X⟧} (hF : constantCoeff F ≠ 0) : F⁻¹⁻¹ = F := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one
    (by rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero hF)]
  exact PowerSeries.mul_inv_cancel F hF

lemma isSolution_iff (a b : ℕ) (A : ℚ⟦X⟧) :
    IsSolution a b A ↔ constantCoeff A = 1 ∧ Hur.Cond a b (jet A⁻¹) := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_, fun n hn => ?_⟩
    · rw [jet_coeff, coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv, h0]
      simp
    · rw [← jet_rescale_exp, ← map_pow, ← map_mul, jet_coeff, h n hn, mul_zero]
  · rintro ⟨h0, hc⟩
    refine ⟨h0, fun n hn => ?_⟩
    have h1 := hc.2 n hn
    rw [← jet_rescale_exp, ← map_pow, ← map_mul, jet_coeff] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast n.factorial_ne_zero)

/-- The power series with EGF coefficients $H_n$. -/
noncomputable def egfOf (H : Hur ℚ) : ℚ⟦X⟧ := PowerSeries.mk fun n => H.coeff n / n.factorial

lemma jet_egfOf (H : Hur ℚ) : jet (egfOf H) = H := by
  ext n
  rw [jet_coeff, egfOf, coeff_mk]
  have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- For all $a$ and $b$, exactly one power series has the property of $F(a, b)$. -/
theorem exists_unique_solution (a b : ℕ) : ∃! A : ℚ⟦X⟧, IsSolution a b A := by
  obtain ⟨H, hH, huniq⟩ := existsUnique_cond a b
  have hF0 : constantCoeff (egfOf H) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, egfOf, coeff_mk, hH.1]
    simp
  refine ⟨(egfOf H)⁻¹, ?_, fun A hA => ?_⟩
  · show IsSolution a b (egfOf H)⁻¹
    rw [isSolution_iff, inv_inv_of (by rw [hF0]; exact one_ne_zero), jet_egfOf,
      PowerSeries.constantCoeff_inv, hF0, inv_one]
    exact ⟨rfl, hH⟩
  · have hA : IsSolution a b A := hA
    rw [isSolution_iff] at hA
    have h2 : A⁻¹ = egfOf H := jet_injective (by rw [huniq _ hA.2, jet_egfOf])
    rw [← h2, inv_inv_of (by rw [hA.1]; exact one_ne_zero)]

/-- The `p`-adic theorem for a rational solution. -/
theorem master_rat (a b p : ℕ) [Fact p.Prime] (hb : 1 ≤ b) (hbp : b < p * a) (A : ℚ⟦X⟧)
    (hA : IsSolution a b A) :
    ∃ A' H' : Hur ℤ_[p],
      (∀ n, (((n.factorial : ℚ) * coeff n A : ℚ) : ℚ_[p]) = (A'.coeff n : ℚ_[p])) ∧
      A' * H' = 1 ∧ Hur.Cond a b H' ∧
      ∀ n, PadicInt.toZMod (A'.coeff n) = PadicInt.toZMod (A'.coeff (n % p)) := by
  rw [isSolution_iff] at hA
  have hBH : Hur.map (Rat.castHom ℚ_[p]) (jet A) * Hur.map (Rat.castHom ℚ_[p]) (jet A⁻¹) = 1 := by
    rw [← Hur.map_mul', ← map_mul, PowerSeries.mul_inv_cancel A (by rw [hA.1]; exact one_ne_zero),
      map_one, Hur.map_one']
  obtain ⟨A', H', hA', hAH, hc, hcong⟩ :=
    master a b hb hbp _ _ (hA.2.map (Rat.castHom ℚ_[p])) hBH
  refine ⟨A', H', fun n => ?_, hAH, hc, hcong⟩
  have h := congrArg (fun F => Hur.coeff F n) hA'
  simp only [Hur.coeff_map, jet_coeff, eq_ratCast] at h
  exact h.symm

/-- Let $1 \le b$ and let `p` be a prime with $b < pa$. Then every $a(n) = n!\,[x^n] A(x)$ lies in
$\mathbb{Z}_{(p)}$, and $a(n) \equiv a(n \bmod p) \pmod p$. -/
theorem padic_congruence (a b p : ℕ) (hp : p.Prime) (hb : 1 ≤ b) (hbp : b < p * a) (A : ℚ⟦X⟧)
    (hA : IsSolution a b A) (n : ℕ) :
    padicNorm p ((n.factorial : ℚ) * coeff n A) ≤ 1 ∧
      padicNorm p ((n.factorial : ℚ) * coeff n A -
        ((n % p).factorial : ℚ) * coeff (n % p) A) < 1 := by
  have := Fact.mk hp
  obtain ⟨A', -, hA', -, -, hcong⟩ := master_rat a b p hb hbp A hA
  constructor
  · have h := Padic.eq_padicNorm (p := p) ((n.factorial : ℚ) * coeff n A)
    rw [hA' n, ← PadicInt.norm_def] at h
    have h3 := PadicInt.norm_le_one (A'.coeff n)
    rw [h] at h3
    exact_mod_cast h3
  · have h := Padic.eq_padicNorm (p := p)
      ((n.factorial : ℚ) * coeff n A - ((n % p).factorial : ℚ) * coeff (n % p) A)
    rw [Rat.cast_sub, hA' n, hA' (n % p), ← PadicInt.coe_sub, ← PadicInt.norm_def] at h
    have h2 : ‖A'.coeff n - A'.coeff (n % p)‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd, ← toZMod_eq_zero_iff, map_sub, hcong n, sub_self]
    rw [h] at h2
    exact_mod_cast h2

/-- A rational number that is `p`-integral for every prime `p` is an integer. -/
lemma rat_eq_int_of_padicNorm (q : ℚ) (h : ∀ p : ℕ, p.Prime → padicNorm p q ≤ 1) :
    ∃ z : ℤ, q = z := by
  refine ⟨q.num, ?_⟩
  have hden : q.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have := Fact.mk hp
    have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hpn
      have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.1 hpn
      have h2 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 hpd
      rw [q.reduced.gcd_eq_one] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
    have e : padicNorm p (q * q.den) = padicNorm p q * padicNorm p q.den := padicNorm.mul _ _
    rw [Rat.mul_den_eq_num, (padicNorm.int_eq_one_iff q.num).2 hnum] at e
    have h3 : padicNorm p (q.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff q.den).2 hpd
    have h4 : padicNorm p q * padicNorm p q.den ≤ padicNorm p q.den :=
      mul_le_of_le_one_left (padicNorm.nonneg _) (h p hp)
    linarith
  exact (Rat.coe_int_num_of_den_eq_one hden).symm

/-- If $1 \le b < 2a$, then every $a(n) = n!\,[x^n] A(x)$ is an integer. -/
theorem integer_coefficients (a b : ℕ) (hb : 1 ≤ b) (hab : b < 2 * a) (A : ℚ⟦X⟧)
    (hA : IsSolution a b A) (n : ℕ) : ∃ z : ℤ, (n.factorial : ℚ) * coeff n A = z :=
  rat_eq_int_of_padicNorm _ fun p hp =>
    (padic_congruence a b p hp hb (lt_of_lt_of_le hab (Nat.mul_le_mul_right a hp.two_le)) A hA n).1

/-- The residue of $a(N)$ modulo `p` from a candidate pair. -/
lemma residue (a b p : ℕ) [Fact p.Prime] (hb : 1 ≤ b) (hbp : b < p * a) (A : ℚ⟦X⟧)
    (hA : IsSolution a b A) (Ac Hc : Hur (ZMod p)) (hHc0 : Hc.coeff 0 = 1)
    (hHc : ∀ n < p, 1 ≤ n → (Hur.ex ((n : ZMod p) ^ a) * Hc ^ (n ^ b % p)).coeff n = 0)
    (hAc : ∀ k < p, (Ac * Hc).coeff k = (1 : Hur (ZMod p)).coeff k)
    (N : ℕ) (z : ℤ) (hz : (N.factorial : ℚ) * coeff N A = z) :
    (z : ZMod p) = Ac.coeff (N % p) := by
  obtain ⟨A', H', hA', hAH, hc, hcong⟩ := master_rat a b p hb hbp A hA
  have h1 : A'.coeff N = (z : ℤ_[p]) := by
    apply PadicInt.ext
    rw [← hA' N, hz, PadicInt.coe_intCast, Rat.cast_intCast]
  have hfv := first_values p a b (Abar := Hur.map PadicInt.toZMod A')
    (Hbar := Hur.map PadicInt.toZMod H') Ac Hc (by rw [← Hur.map_mul', hAH, Hur.map_one'])
    (hc.map PadicInt.toZMod) hHc0 hHc hAc
  rw [← map_intCast PadicInt.toZMod z, ← h1, hcong N, ← Hur.coeff_map]
  exact hfv _ (Nat.mod_lt _ (Fact.out : p.Prime).pos)

/-! ### The two OEIS entries -/

/-- The residues $1, 1$ modulo $2$ of $a(0), a(1)$, and of $h(0), h(1)$ for $H = A^{-1}$. -/
def res2 : Hur (ZMod 2) := ⟨fun k => (([1, 1].getD k 0 : ℤ) : ZMod 2)⟩

/-- The residues of $a(0), \dots, a(4)$ modulo $5$ for A317345. -/
def acA317345 : Hur (ZMod 5) := ⟨fun k => (([1, 1, 0, 0, 0].getD k 0 : ℤ) : ZMod 5)⟩

/-- The residues modulo $5$ of the first coefficients of $A^{-1}$ for A317345. -/
def hcA317345 : Hur (ZMod 5) := ⟨fun k => (([1, 4, 2, 4, 4].getD k 0 : ℤ) : ZMod 5)⟩

/-- The residues of $a(0), \dots, a(4)$ modulo $5$ for A317343. -/
def acA317343 : Hur (ZMod 5) := ⟨fun k => (([1, 1, 3, 3, 0].getD k 0 : ℤ) : ZMod 5)⟩

/-- The residues modulo $5$ of the first coefficients of $A^{-1}$ for A317343. -/
def hcA317343 : Hur (ZMod 5) := ⟨fun k => (([1, 4, 4, 4, 4].getD k 0 : ℤ) : ZMod 5)⟩

lemma res2_eq_one : ∀ j < 2, res2.coeff j = ((1 : ℤ) : ZMod 2) := by decide

lemma res2_zero : res2.coeff 0 = 1 := by decide

lemma hcA317345_zero : hcA317345.coeff 0 = 1 := by decide

lemma hcA317343_zero : hcA317343.coeff 0 = 1 := by decide

lemma cond2_A317345 : ∀ n : ℕ, n < 2 → 1 ≤ n →
    (Hur.ex ((n : ZMod 2) ^ 3) * res2 ^ (n ^ 2 % 2)).coeff n = 0 := by decide +kernel

lemma cond2_A317343 : ∀ n : ℕ, n < 2 → 1 ≤ n →
    (Hur.ex ((n : ZMod 2) ^ 2) * res2 ^ (n ^ 1 % 2)).coeff n = 0 := by decide +kernel

lemma inv2 : ∀ k < 2, (res2 * res2).coeff k = (1 : Hur (ZMod 2)).coeff k := by decide +kernel

lemma cond5_A317345 : ∀ n : ℕ, n < 5 → 1 ≤ n →
    (Hur.ex ((n : ZMod 5) ^ 3) * hcA317345 ^ (n ^ 2 % 5)).coeff n = 0 := by decide +kernel

lemma inv5_A317345 : ∀ k < 5, (acA317345 * hcA317345).coeff k = (1 : Hur (ZMod 5)).coeff k := by
  decide +kernel

lemma cond5_A317343 : ∀ n : ℕ, n < 5 → 1 ≤ n →
    (Hur.ex ((n : ZMod 5) ^ 2) * hcA317343 ^ (n ^ 1 % 5)).coeff n = 0 := by decide +kernel

lemma inv5_A317343 : ∀ k < 5, (acA317343 * hcA317343).coeff k = (1 : Hur (ZMod 5)).coeff k := by
  decide +kernel

/-- Hanna's conjecture for OEIS A317345: every $a(n)$ is an integer and
$a(5n + k) \equiv [1, 1, 5, 5, 5](k) \pmod{10}$ for $n \ge 0$ and $0 \le k \le 4$. -/
theorem a317345_mod_ten (A : ℚ⟦X⟧) (hA : IsSolution 3 2 A) (n k : ℕ) (hk : k < 5) :
    ∃ z : ℤ, ((5 * n + k).factorial : ℚ) * coeff (5 * n + k) A = z ∧
      z ≡ [1, 1, 5, 5, 5].getD k 0 [ZMOD 10] := by
  obtain ⟨z, hz⟩ := integer_coefficients 3 2 (by norm_num) (by norm_num) A hA (5 * n + k)
  refine ⟨z, hz, ?_⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h2 := residue 3 2 2 (by norm_num) (by norm_num) A hA res2 res2 res2_zero
    cond2_A317345 inv2 _ z hz
  have h5 := residue 3 2 5 (by norm_num) (by norm_num) A hA acA317345 hcA317345 hcA317345_zero
    cond5_A317345 inv5_A317345 _ z hz
  rw [show (5 * n + k) % 5 = k by omega] at h5
  have h5' : (z : ZMod 5) = (([1, 1, 0, 0, 0].getD k 0 : ℤ) : ZMod 5) := h5
  have h2' : (z : ZMod 2) = ((1 : ℤ) : ZMod 2) := by
    rw [h2]
    exact res2_eq_one _ (Nat.mod_lt _ (by norm_num))
  have e2 := (ZMod.intCast_eq_intCast_iff z 1 2).1 h2'
  have e5 := (ZMod.intCast_eq_intCast_iff z _ 5).1 h5'
  unfold Int.ModEq at e2 e5 ⊢
  interval_cases k <;> simp at e5 ⊢ <;> omega

/-- The analogue for OEIS A317343: every $a(n)$ is an integer and
$a(5n + k) \equiv [1, 1, 3, 3, 5](k) \pmod{10}$ for $n \ge 0$ and $0 \le k \le 4$. -/
theorem a317343_mod_ten (A : ℚ⟦X⟧) (hA : IsSolution 2 1 A) (n k : ℕ) (hk : k < 5) :
    ∃ z : ℤ, ((5 * n + k).factorial : ℚ) * coeff (5 * n + k) A = z ∧
      z ≡ [1, 1, 3, 3, 5].getD k 0 [ZMOD 10] := by
  obtain ⟨z, hz⟩ := integer_coefficients 2 1 (by norm_num) (by norm_num) A hA (5 * n + k)
  refine ⟨z, hz, ?_⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h2 := residue 2 1 2 (by norm_num) (by norm_num) A hA res2 res2 res2_zero
    cond2_A317343 inv2 _ z hz
  have h5 := residue 2 1 5 (by norm_num) (by norm_num) A hA acA317343 hcA317343 hcA317343_zero
    cond5_A317343 inv5_A317343 _ z hz
  rw [show (5 * n + k) % 5 = k by omega] at h5
  have h5' : (z : ZMod 5) = (([1, 1, 3, 3, 0].getD k 0 : ℤ) : ZMod 5) := h5
  have h2' : (z : ZMod 2) = ((1 : ℤ) : ZMod 2) := by
    rw [h2]
    exact res2_eq_one _ (Nat.mod_lt _ (by norm_num))
  have e2 := (ZMod.intCast_eq_intCast_iff z 1 2).1 h2'
  have e5 := (ZMod.intCast_eq_intCast_iff z _ 5).1 h5'
  unfold Int.ModEq at e2 e5 ⊢
  interval_cases k <;> simp at e5 ⊢ <;> omega

/-! ### Sanity checks: the first terms agree with the OEIS data -/

/-- The first terms from integer candidates $A_c$ and $H_c$ with $A_c H_c \equiv 1$ that satisfy
the condition below `N`. -/
lemma first_terms_of (a b : ℕ) (A : ℚ⟦X⟧) (hA : IsSolution a b A) (N : ℕ) (Ac Hc : Hur ℤ)
    (hHc0 : Hc.coeff 0 = 1)
    (hHc : ∀ n : ℕ, n < N → 1 ≤ n → (Hur.ex ((n : ℤ) ^ a) * Hc ^ (n ^ b)).coeff n = 0)
    (hAc : ∀ k < N, (Ac * Hc).coeff k = (1 : Hur ℤ).coeff k) :
    ∀ k < N, (k.factorial : ℚ) * coeff k A = Ac.coeff k := by
  rw [isSolution_iff] at hA
  set φ := Int.castRingHom ℚ
  have hq0 : (Hur.map φ Hc).coeff 0 = 1 := by rw [Hur.coeff_map, hHc0, map_one]
  have hagree := Hur.agree_below a b hA.2.1 hq0 N (fun n _ hn => hA.2.2 n hn)
    (fun n hn hn1 => by
      rw [show ((n : ℚ) ^ a) = φ ((n : ℤ) ^ a) by simp [φ], ← Hur.map_ex_mul_pow,
        Hur.coeff_map, hHc n hn hn1, map_zero])
    (fun n _ hn1 y hy => (mul_eq_zero.1 hy).resolve_left
      (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))))
  have hBH : jet A * jet A⁻¹ = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel A (by rw [hA.1]; exact one_ne_zero), map_one]
  intro k hk
  have h := Hur.eq_of_mul_eq_below hq0 N (X := jet A) (Y := Hur.map φ Ac) (fun j hj => by
    rw [← Hur.map_mul', Hur.coeff_map, hAc j hj, ← Hur.coeff_map, Hur.map_one', ← hBH]
    exact Hur.coeff_mul_congr _ _ _ _ j (fun _ _ => rfl) (fun i hi => (hagree i (by omega)).symm))
    k hk
  rw [← jet_coeff, h, Hur.coeff_map]
  rfl

/-- The first coefficients $1, -1, -3, -421, -192551$ of $A^{-1}$ for A317345. -/
def hcZA317345 : Hur ℤ := ⟨fun k => [1, -1, -3, -421, -192551].getD k 0⟩

/-- The first terms $1, 1, 5, 445, 196105$ of A317345. -/
def acZA317345 : Hur ℤ := ⟨fun k => [1, 1, 5, 445, 196105].getD k 0⟩

/-- The first coefficients $1, -1, -1, -31, -1631$ of $A^{-1}$ for A317343. -/
def hcZA317343 : Hur ℤ := ⟨fun k => [1, -1, -1, -31, -1631].getD k 0⟩

/-- The first terms $1, 1, 3, 43, 1945$ of A317343. -/
def acZA317343 : Hur ℤ := ⟨fun k => [1, 1, 3, 43, 1945].getD k 0⟩

lemma condZ_A317345 : ∀ n : ℕ, n < 5 → 1 ≤ n →
    (Hur.ex ((n : ℤ) ^ 3) * hcZA317345 ^ (n ^ 2)).coeff n = 0 := by decide +kernel

lemma invZ_A317345 : ∀ k < 5, (acZA317345 * hcZA317345).coeff k = (1 : Hur ℤ).coeff k := by
  decide +kernel

lemma condZ_A317343 : ∀ n : ℕ, n < 5 → 1 ≤ n →
    (Hur.ex ((n : ℤ) ^ 2) * hcZA317343 ^ (n ^ 1)).coeff n = 0 := by decide +kernel

lemma invZ_A317343 : ∀ k < 5, (acZA317343 * hcZA317343).coeff k = (1 : Hur ℤ).coeff k := by
  decide +kernel

/-- The first terms of OEIS A317345: $1, 1, 5, 445, 196105$. -/
theorem a317345_first_terms (A : ℚ⟦X⟧) (hA : IsSolution 3 2 A) :
    ∀ k < 5, (k.factorial : ℚ) * coeff k A = ([1, 1, 5, 445, 196105].getD k 0 : ℤ) :=
  first_terms_of 3 2 A hA 5 acZA317345 hcZA317345 rfl condZ_A317345 invZ_A317345

/-- The first terms of OEIS A317343: $1, 1, 3, 43, 1945$. -/
theorem a317343_first_terms (A : ℚ⟦X⟧) (hA : IsSolution 2 1 A) :
    ∀ k < 5, (k.factorial : ℚ) * coeff k A = ([1, 1, 3, 43, 1945].getD k 0 : ℤ) :=
  first_terms_of 2 1 A hA 5 acZA317343 hcZA317343 rfl condZ_A317343 invZ_A317343

end Bridge

end OeisA317345

end
