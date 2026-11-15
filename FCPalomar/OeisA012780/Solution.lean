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
# OEIS A012780: Bala's periodicity conjecture for $\arcsin(\tan x)$

Let $a(n) = (2n+1)!\,[x^{2n+1}] \arcsin(\tan x)$ (OEIS A012780, offset 0). The file proves that
every $a(n)$ is an integer and that:
- $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for $e \ge 1$ and every $n$;
- $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ for odd primes $p$, $e \ge 1$ and $2n \ge e$;
- $a(n + \varphi(k)) \equiv a(n) \pmod k$ for $k \ge 1$ whenever $2n$ is at least the exponent of
  every odd prime in $k$. With the pre-period $N = k$ this is Peter Bala's conjecture.
- $a(n) \equiv 2n + 1 \pmod 8$, so $a(n + 2) \not\equiv a(n) \pmod 8$: the shift
  $2 = \lambda(8)$ is not an eventual period.

The proof works with Hurwitz series over a commutative ring: sequences $f_n = n!\,[x^n] f$ with
the binomial product. The series $\cos x$, $\sin x$, $\cosh x$, $\sinh x$ have explicit
coefficients, $\sec x$ and $\operatorname{sech} x$ are the inverses of $\cos x$ and $\cosh x$, and
$S = (\cos 2x)^{-1/2}$ and $\tilde S = (\cosh 2x)^{-1/2}$ are the solutions of
$DS = \tan(2x)\,S$ and $D\tilde S = -\tanh(2x)\,\tilde S$ with constant term $1$. All of them
have integer coefficients.

*Integrality.* Let $g = \sec x \cdot S$ and $P = \arcsin' \circ \tan$ in $\mathbb{Q}[[x]]$.
- The series $B = \sum_k \binom{2k}{k} z^k / 4^k$ satisfies $2(1 - z) B' = B$, so
  $B^2 (1 - z) = 1$. As $\arcsin'(x) = B(x^2)$, this gives $\arcsin'^2 (1 - x^2) = 1$, and
  substitution gives $P^2 (1 - \tan^2 x) = 1$.
- The chain rule gives $(\arcsin \circ \tan)' = P \tan'$, and $\tan' = \sec^2$.
- By the double angle formula $\cos 2x = \cos^2 x - \sin^2 x$, the series $P \sec x$ satisfies
  $(P \sec x)^2 \cos 2x = 1$ and has constant term $1$. So does $S$. Such a series is unique,
  since $2$ is not a zero divisor. Hence $P \sec x = S$ and $(\arcsin \circ \tan)' = g$.
So $a(n) = g_{2n}$, an integer.

*The hyperbolic form.* Over $\mathbb{C}$, the rescaling $x \mapsto ix$ maps $\cos, \sin, \sec,
\tan, S$ to $\cosh, i \sinh, \operatorname{sech}, i \tanh, \tilde S$. So
$G = \operatorname{sech} x \cdot \tilde S$ satisfies $g_{2n} = (-1)^n G_{2n}$.

*The prime 2.* Write $G = c\,e^x$ with $c = \tilde S\,d$ and
$d = e^{-x} \operatorname{sech} x = 2/(1 + e^{2x})$. Then $G_M = \sum_l \binom{M}{l} c_l$.
- From $D\tilde S = -\tanh(2x)\tilde S$, induction gives $2^{\lceil m/2 \rceil} \mid \tilde S_m$.
- A truncated geometric series for $1/(1 + y/2)$, with $y = e^{2x} - 1$, gives
  $d_l = \sum_{j \le l} (-1)^j 2^{l-j} j!\,(e^x - 1)^{[j]}_l$. The divided powers $f^{[j]}$ have
  integer coefficients, and $2^{\lfloor j/2 \rfloor} \mid j!$. So
  $2^{\lfloor l/2 \rfloor} \mid d_l$,
  and then $2^{\lfloor l/2 \rfloor} \mid c_l$.
- By Vandermonde, $\binom{M + 2^e}{l} - \binom{M}{l} = \sum_{r \ge 1} \binom{2^e}{r}
  \binom{M}{l - r}$, and $2^e \mid r \binom{2^e}{r}$. Write $r = 2^v u$ with $u$ odd. Then
  $2v \le 2^v \le l$, so $2^v \mid c_l$ and $2^e \mid \binom{2^e}{r} c_l$.
So $2^e \mid G_{M + 2^e} - G_M$ for every $M$. The signs $(-1)^n$ give the first congruence.

*Odd primes.* Fix an odd prime power $p^e$ and work over $R = \mathbb{Z}/p^e$, where $2$ is a
unit. Let $K$ be the set of series that agree, up to every index, with a polynomial in
$u = e^x - 1$.
- $K$ is a subring that contains $e^x$. It contains $H$ whenever $HF = 1$, $F \in K$ and
  $F_0 = 1$, by a truncated geometric series. It contains $\sum_k b_k w^k$ for every sequence
  $b$ and every $w \in K$ with $w_0 = 0$.
- So $\cosh x = (e^x + e^{-x})/2$, $\operatorname{sech} x$ and $\cosh 2x$ lie in $K$.
- Let $b_k = (-1)^k \binom{2k}{k} / 4^k$ and $Y = \sum_k b_k (\cosh 2x - 1)^k$. The identity
  $\sum_{i + j = m} \binom{2i}{i} \binom{2j}{j} = 4^m$ (from $B^2 = 1/(1 - z)$) gives
  $Y^2 \cosh 2x = 1$. By uniqueness, $Y = \tilde S$, so $G \in K$.
- A polynomial in $e^x$ has coefficients $\sum_i c_i\, i^M$. For $M \ge e$,
  $i^{M + \varphi(p^e)} = i^M$ in $R$: by Euler's theorem if $p \nmid i$, and since $p^e \mid i^M$
  otherwise.
So $G_{M + \varphi(p^e)} \equiv G_M \pmod{p^e}$ for $M \ge e$. As $\varphi(p^e)$ is even,
applying this twice from $M = 2n$ gives the second congruence.

*Every modulus.* For each prime power $q^f$ that exactly divides $k$, $\varphi(q^f) \mid
\varphi(k)$, so the prime-power congruences, iterated, hold modulo $q^f$ with shift
$\varphi(k)$. These prime powers are pairwise coprime, so $k$ divides the difference.

The Hurwitz-series library is adapted from this repository's A396804, OeisA317345 and
OeisA371710 packages. The 2-adic step is a form of Y. Nishibuchi's criterion on the coefficients
of $e^{-x} G$, and the odd-prime step is the $p$-local form of the method of A. Kallat and
R. Blanco Gómez.

*References:*
- Patrick Demichel, [A012780](https://oeis.org/A012780); the conjecture is Peter Bala's comment
  of February 15, 2026.
- Y. Nishibuchi, "A Unified Framework for $p$-adic Congruences and $p$-adic Interpolations of
  Sequences", arXiv:2610.11648 (2026).
- A. Kallat, arXiv:2609.07238 (2026); R. Blanco Gómez, Zenodo 23150466 and 23291157 (2026).
-/

@[expose] public section

namespace OeisA012780

open PowerSeries

/-- The Maclaurin series $\arcsin u = \sum_{k \ge 0} \binom{2k}{k} \frac{u^{2k+1}}{4^k (2k+1)}$. -/
noncomputable def arcsin : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n % 2 = 1 then ((n / 2).centralBinom : ℚ) / (4 ^ (n / 2) * n) else 0

/-- The Maclaurin series $\tan x = \sin x / \cos x$. -/
noncomputable def tan : ℚ⟦X⟧ := sin ℚ * (cos ℚ)⁻¹

/-- OEIS A012780: $a(n) = (2n+1)!\,[x^{2n+1}] \arcsin(\tan x)$. -/
noncomputable def a (n : ℕ) : ℚ := (2 * n + 1).factorial * coeff (2 * n + 1) (arcsin.subst tan)

end OeisA012780

namespace OeisA012780

/-! ### Hurwitz series

The Hurwitz-series basics below (ring structure, derivative, constants, coefficient maps, causal
fixed points, exponentials and inverses) are adapted from this repository's OeisA317345 package,
and the divided powers from the A396804 and OeisA371710 packages. -/

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

end Map



section Extra
variable {R : Type*} [CommRing R]

/-- The constant series as a ring homomorphism. -/
def CHom : R →+* Hur R where
  toFun := C
  map_one' := C_one
  map_mul' := C_mul
  map_zero' := C_zero
  map_add' := C_add

lemma CHom_apply (r : R) : CHom r = C r := rfl

lemma D_neg (f : Hur R) : D (-f) = -D f := rfl

lemma D_natCast (m : ℕ) : D (m : Hur R) = 0 := by
  rw [natCast_eq_C, D_C]

lemma coeff_zero_pow (f : Hur R) (k : ℕ) : (f ^ k).coeff 0 = f.coeff 0 ^ k := by
  rw [← coeff0_apply, map_pow, coeff0_apply]

lemma natCast_mul_coeff (m : ℕ) (f : Hur R) (n : ℕ) :
    ((m : Hur R) * f).coeff n = m * f.coeff n := by
  rw [natCast_eq_C, C_mul_coeff]

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
      rw [coeff_mul_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [ih (by simp only [Finset.mem_range] at hj; omega), zero_mul, mul_zero]

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

/-- If $g_0 = 0$, then $g^k$ vanishes below $k$. -/
lemma pow_coeff_lt (g : Hur R) (hg : g.coeff 0 = 0) {k n : ℕ} (h : n < k) :
    (g ^ k).coeff n = 0 := by
  rw [pow_eq_factorial_mul_dpow g hg, natCast_mul_coeff, dpow_coeff_lt g h, mul_zero]

/-- If $y^2 c = z^2 c = 1$, $y_0 = z_0 = 1$ and $2$ is not a zero divisor, then $y = z$. -/
lemma sq_unique (h2 : ∀ r : R, 2 * r = 0 → r = 0) {y z c : Hur R} (hy : y ^ 2 * c = 1)
    (hz : z ^ 2 * c = 1) (hy0 : y.coeff 0 = 1) (hz0 : z.coeff 0 = 1) : y = z := by
  have hsq : (y - z) * (y + z) = 0 := by linear_combination (z ^ 2) * hy - (y ^ 2) * hz
  have key : ∀ n, (y - z).coeff n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have h1 := coeff_mul_of_vanish (y - z) (y + z) n ih
      rw [hsq, coeff_add, hy0, hz0] at h1
      apply h2
      rw [coeff_zero'] at h1
      linear_combination -h1
  ext n
  exact sub_eq_zero.1 (key n)

/-- The rescaling $f(x) \mapsto f(cx)$, with coefficients $c^n f_n$. -/
def scale (c : R) (f : Hur R) : Hur R := ⟨fun n => c ^ n * f.coeff n⟩

lemma coeff_scale (c : R) (f : Hur R) (n : ℕ) : (scale c f).coeff n = c ^ n * f.coeff n := rfl

lemma scale_mul (c : R) (f g : Hur R) : scale c (f * g) = scale c f * scale c g := by
  ext n
  rw [coeff_scale, coeff_mul_sum, coeff_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : c ^ n = c ^ i * c ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
  rw [coeff_scale, coeff_scale, hc]
  ring

/-- Rescaling as a ring homomorphism. -/
def scaleHom (c : R) : Hur R →+* Hur R where
  toFun := scale c
  map_one' := by
    ext n
    rw [coeff_scale, coeff_one]
    split_ifs with h <;> simp [h]
  map_mul' := scale_mul c
  map_zero' := by
    ext n
    simp [coeff_scale]
  map_add' f g := by
    ext n
    simp [coeff_scale, mul_add]

lemma scaleHom_apply (c : R) (f : Hur R) : scaleHom c f = scale c f := rfl

lemma scale_C (c r : R) : scale c (C r) = C r := by
  ext n
  rw [coeff_scale, coeff_C]
  split_ifs with h <;> simp [h]

lemma D_scale (c : R) (f : Hur R) : D (scale c f) = C c * scale c (D f) := by
  ext n
  rw [coeff_D, C_mul_coeff, coeff_scale, coeff_scale, coeff_D, pow_succ]
  ring

lemma scale_scale (a b : R) (f : Hur R) : scale a (scale b f) = scale (a * b) f := by
  ext n
  simp only [coeff_scale, mul_pow]
  ring

lemma scale_ex (c d : R) : scale c (ex d) = ex (c * d) := by
  ext n
  simp [coeff_scale, coeff_ex, mul_pow]

lemma scale_integ (c : R) (h : Hur R) : D (scale c (integ h)) = C c * scale c h := by
  rw [D_scale, D_integ]

lemma scale_hexp (c : R) (f : Hur R) : scale c (hexp f) = hexp (scale c f) := by
  apply hexp_unique
  · rw [coeff_scale, hexp_coeff_zero, pow_zero, one_mul]
  · rw [D_scale, D_hexp, scale_mul, D_scale]
    ring

lemma hexp_eq_of_D_eq {f g : Hur R} (h : D f = D g) : hexp f = hexp g :=
  hexp_unique (hexp_coeff_zero f) (by rw [D_hexp, h])

lemma ex_natCast (i : ℕ) : ex (1 : R) ^ i = ex (i : R) := by
  induction i with
  | zero => rw [pow_zero, Nat.cast_zero, ex_zero]
  | succ i ih => rw [pow_succ, ih, ← ex_add, Nat.cast_succ]

lemma ex_mul_ex_neg (c : R) : ex c * ex (-c) = 1 := by
  rw [← ex_add, add_neg_cancel, ex_zero]

lemma map_scale {S : Type*} [CommRing S] (φ : R →+* S) (c : R) (f : Hur R) :
    map φ (scale c f) = scale (φ c) (map φ f) := by
  ext n
  simp [coeff_map, coeff_scale]

end Extra

end Hur

end OeisA012780

namespace OeisA012780

namespace Hur

section Trig
variable (R : Type*) [CommRing R]

/-- The series of $\cos x$. -/
def cosH : Hur R := ⟨fun n => if n % 2 = 0 then (-1) ^ (n / 2) else 0⟩

/-- The series of $\sin x$. -/
def sinH : Hur R := ⟨fun n => if n % 2 = 1 then (-1) ^ (n / 2) else 0⟩

/-- The series of $\cosh x$. -/
def coshH : Hur R := ⟨fun n => if n % 2 = 0 then 1 else 0⟩

/-- The series of $\sinh x$. -/
def sinhH : Hur R := ⟨fun n => if n % 2 = 1 then 1 else 0⟩

/-- The series of $\sec x$. -/
def secH : Hur R := hinv (cosH R)

/-- The series of $\tan x$. -/
def tanH : Hur R := sinH R * secH R

/-- The series of $\operatorname{sech} x$. -/
def sechH : Hur R := hinv (coshH R)

/-- The series of $\tanh x$. -/
def tanhH : Hur R := sinhH R * sechH R

/-- The series of $(\cos 2x)^{-1/2}$: the solution of $DS = \tan(2x)\,S$ with $S_0 = 1$. -/
def sqH : Hur R := hexp (integ (scale 2 (tanH R)))

/-- The series of $(\cosh 2x)^{-1/2}$: the solution of $DS = -\tanh(2x)\,S$ with $S_0 = 1$. -/
def sqhH : Hur R := hexp (integ (-scale 2 (tanhH R)))

/-- The series $g = \sec x\,(\cos 2x)^{-1/2}$. -/
def gH : Hur R := secH R * sqH R

/-- The series $G = \operatorname{sech} x\,(\cosh 2x)^{-1/2}$. -/
def GH : Hur R := sechH R * sqhH R

variable {R}

lemma C_two : C (2 : R) = 2 := map_ofNat CHom 2

lemma cosH_coeff_zero : (cosH R).coeff 0 = 1 := by simp [cosH]

lemma coshH_coeff_zero : (coshH R).coeff 0 = 1 := by simp [coshH]

lemma D_cosH : D (cosH R) = -sinH R := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k) % 2 = 0 := by omega
    simp [cosH, sinH, h1, h2]
  · have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    have h3 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h4 : (2 * k + 1) / 2 = k := by omega
    simp [cosH, sinH, h1, h2, h3, h4, pow_succ]

lemma D_sinH : D (sinH R) = cosH R := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k) % 2 = 0 := by omega
    have h3 : (2 * k + 1) / 2 = k := by omega
    have h4 : (2 * k) / 2 = k := by omega
    simp [cosH, sinH, h1, h2, h3, h4]
  · have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [cosH, sinH, h1, h2]

lemma D_coshH : D (coshH R) = sinhH R := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k) % 2 = 0 := by omega
    simp [coshH, sinhH, h1, h2]
  · have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [coshH, sinhH, h1, h2]

lemma D_sinhH : D (sinhH R) = coshH R := by
  ext n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k) % 2 = 0 := by omega
    simp [coshH, sinhH, h1, h2]
  · have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [coshH, sinhH, h1, h2]

lemma cosH_mul_secH : cosH R * secH R = 1 := mul_hinv cosH_coeff_zero

lemma coshH_mul_sechH : coshH R * sechH R = 1 := mul_hinv coshH_coeff_zero

lemma secH_coeff_zero : (secH R).coeff 0 = 1 := hinv_coeff_zero cosH_coeff_zero

lemma sechH_coeff_zero : (sechH R).coeff 0 = 1 := hinv_coeff_zero coshH_coeff_zero

lemma tanH_coeff_zero : (tanH R).coeff 0 = 0 := by
  simp [tanH, sinH]

lemma tanhH_coeff_zero : (tanhH R).coeff 0 = 0 := by
  simp [tanhH, sinhH]

lemma sinH_sq_add_cosH_sq : sinH R * sinH R + cosH R * cosH R = 1 := by
  have hD : D (sinH R * sinH R + cosH R * cosH R) = 0 := by
    rw [D_add, D_mul, D_mul, D_sinH, D_cosH]
    ring
  rw [eq_C_of_D_eq_zero hD]
  simp [cosH, sinH, ← C_one]

lemma D_secH : D (secH R) = sinH R * (secH R * secH R) := by
  have h1 := cosH_mul_secH (R := R)
  have h2 : D (cosH R * secH R) = 0 := by rw [h1, D_one]
  rw [D_mul, D_cosH] at h2
  linear_combination (-D (secH R)) * h1 + secH R * h2

lemma D_sechH : D (sechH R) = -(sinhH R * (sechH R * sechH R)) := by
  have h1 := coshH_mul_sechH (R := R)
  have h2 : D (coshH R * sechH R) = 0 := by rw [h1, D_one]
  rw [D_mul, D_coshH] at h2
  linear_combination (-D (sechH R)) * h1 + sechH R * h2

lemma tanH_mul_cosH : tanH R * cosH R = sinH R := by
  rw [tanH, mul_assoc, mul_comm (secH R), cosH_mul_secH, mul_one]

lemma tanhH_mul_coshH : tanhH R * coshH R = sinhH R := by
  rw [tanhH, mul_assoc, mul_comm (sechH R), coshH_mul_sechH, mul_one]

lemma D_tanH : D (tanH R) = secH R * secH R := by
  have h1 := cosH_mul_secH (R := R)
  have h2 := sinH_sq_add_cosH_sq (R := R)
  rw [tanH, D_mul, D_sinH, D_secH]
  linear_combination (secH R * secH R) * h2 - (cosH R * secH R) * h1

lemma two_coshH : 2 * coshH R = ex 1 + ex (-1) := by
  ext n
  rw [← C_two, C_mul_coeff, coeff_add, coeff_ex, coeff_ex, one_pow]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h2 : (2 * k) % 2 = 0 := by omega
    simp [coshH, h2, pow_mul]
    norm_num
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [coshH, h2, pow_succ, pow_mul]

/-- The double angle formulas, proved together by induction on the coefficients. -/
lemma double_angle :
    scale 2 (cosH R) = cosH R * cosH R - sinH R * sinH R ∧
      scale 2 (sinH R) = 2 * (sinH R * cosH R) := by
  set A := cosH R * cosH R - sinH R * sinH R - scale 2 (cosH R)
  set B := 2 * (sinH R * cosH R) - scale 2 (sinH R)
  have hA : D A = -(2 * B) := by
    simp only [A, B, D_sub, D_mul, D_scale, D_cosH, D_sinH, C_two]
    have : scale 2 (-sinH R) = -scale 2 (sinH R) := map_neg (scaleHom 2) _
    rw [this]
    ring
  have hB : D B = 2 * A := by
    have h2 : D (2 : Hur R) = 0 := by rw [← C_two, D_C]
    simp only [A, B, D_sub, D_mul, D_scale, D_cosH, D_sinH, C_two, h2]
    ring
  have key : ∀ n, A.coeff n = 0 ∧ B.coeff n = 0 := by
    intro n
    induction n with
    | zero => simp [A, B, cosH, sinH, coeff_scale, ← C_two, C_mul_coeff]
    | succ n ih =>
      constructor
      · rw [← coeff_D, hA, coeff_neg, ← C_two, C_mul_coeff, ih.2, mul_zero, neg_zero]
      · rw [← coeff_D, hB, ← C_two, C_mul_coeff, ih.1, mul_zero]
  constructor
  · have : A = 0 := Hur.ext (funext fun n => (key n).1)
    linear_combination -this
  · have : B = 0 := Hur.ext (funext fun n => (key n).2)
    linear_combination -this

lemma D_sqH : D (sqH R) = scale 2 (tanH R) * sqH R := by
  rw [sqH, D_hexp, D_integ]

lemma D_sqhH : D (sqhH R) = -scale 2 (tanhH R) * sqhH R := by
  rw [sqhH, D_hexp, D_integ]

lemma sqH_coeff_zero : (sqH R).coeff 0 = 1 := hexp_coeff_zero _

lemma sqhH_coeff_zero : (sqhH R).coeff 0 = 1 := hexp_coeff_zero _

/-- $S^2 \cos 2x = 1$ for $S = (\cos 2x)^{-1/2}$. -/
lemma sqH_sq_mul : sqH R ^ 2 * scale 2 (cosH R) = 1 := by
  have ht : scale 2 (tanH R) * scale 2 (cosH R) = scale 2 (sinH R) := by
    rw [← scale_mul, tanH_mul_cosH]
  have hD : D (sqH R ^ 2 * scale 2 (cosH R)) = 0 := by
    have hn : scale 2 (-sinH R) = -scale 2 (sinH R) := map_neg (scaleHom 2) _
    rw [sq, D_mul, D_mul, D_sqH, D_scale, D_cosH, hn, C_two]
    linear_combination (2 * sqH R * sqH R) * ht
  rw [eq_C_of_D_eq_zero hD, coeff_mul_zero, coeff_scale, ← C_one]
  congr 1
  rw [coeff_zero_pow, sqH_coeff_zero, cosH_coeff_zero]
  simp

/-- $	ilde S^2 \cosh 2x = 1$ for $	ilde S = (\cosh 2x)^{-1/2}$. -/
lemma sqhH_sq_mul : sqhH R ^ 2 * scale 2 (coshH R) = 1 := by
  have ht : scale 2 (tanhH R) * scale 2 (coshH R) = scale 2 (sinhH R) := by
    rw [← scale_mul, tanhH_mul_coshH]
  have hD : D (sqhH R ^ 2 * scale 2 (coshH R)) = 0 := by
    rw [sq, D_mul, D_mul, D_sqhH, D_scale, D_coshH, C_two]
    linear_combination (-2 * sqhH R * sqhH R) * ht
  rw [eq_C_of_D_eq_zero hD, coeff_mul_zero, coeff_scale, ← C_one]
  congr 1
  rw [coeff_zero_pow, sqhH_coeff_zero, coshH_coeff_zero]
  simp

end Trig

end Hur

end OeisA012780

namespace OeisA012780

namespace Hur

section MapTrig
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

lemma map_neg' (f : Hur R) : map φ (-f) = -map φ f := by
  rw [← mapHom_apply, map_neg]
  rfl

lemma map_integ (h : Hur R) : map φ (integ h) = integ (map φ h) := by
  ext n
  cases n <;> simp [coeff_map]

lemma map_hinv {B : Hur R} (hB : B.coeff 0 = 1) : map φ (hinv B) = hinv (map φ B) := by
  have h0 : (map φ B).coeff 0 = 1 := by rw [coeff_map, hB, map_one]
  refine inv_unique' (u := map φ B) ?_ (mul_hinv h0)
  rw [← map_mul', mul_hinv hB, map_one']

lemma map_cosH : map φ (cosH R) = cosH S := by
  ext n
  simp only [coeff_map, cosH]
  split_ifs <;> simp

lemma map_sinH : map φ (sinH R) = sinH S := by
  ext n
  simp only [coeff_map, sinH]
  split_ifs <;> simp

lemma map_coshH : map φ (coshH R) = coshH S := by
  ext n
  simp only [coeff_map, coshH]
  split_ifs <;> simp

lemma map_sinhH : map φ (sinhH R) = sinhH S := by
  ext n
  simp only [coeff_map, sinhH]
  split_ifs <;> simp

lemma map_secH : map φ (secH R) = secH S := by
  rw [secH, map_hinv φ cosH_coeff_zero, map_cosH, secH]

lemma map_sechH : map φ (sechH R) = sechH S := by
  rw [sechH, map_hinv φ coshH_coeff_zero, map_coshH, sechH]

lemma map_tanH : map φ (tanH R) = tanH S := by
  rw [tanH, map_mul', map_sinH, map_secH, tanH]

lemma map_tanhH : map φ (tanhH R) = tanhH S := by
  rw [tanhH, map_mul', map_sinhH, map_sechH, tanhH]

lemma map_sqH : map φ (sqH R) = sqH S := by
  rw [sqH, map_hexp, map_integ, map_scale, map_ofNat, map_tanH, sqH]

lemma map_sqhH : map φ (sqhH R) = sqhH S := by
  rw [sqhH, map_hexp, map_integ, map_neg', map_scale, map_ofNat, map_tanhH, sqhH]

lemma map_gH : map φ (gH R) = gH S := by
  rw [gH, map_mul', map_secH, map_sqH, gH]

lemma map_GH : map φ (GH R) = GH S := by
  rw [GH, map_mul', map_sechH, map_sqhH, GH]

end MapTrig

section Twist
open Complex

lemma I_pow_two_mul (k : ℕ) : I ^ (2 * k) = (-1 : ℂ) ^ k := by
  rw [pow_mul, I_sq]

lemma scale_I_cosH : scale I (cosH ℂ) = coshH ℂ := by
  ext n
  rw [coeff_scale]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h2 : (2 * k) % 2 = 0 := by omega
    have h3 : (2 * k) / 2 = k := by omega
    simp only [cosH, coshH, h2, h3, ite_true, I_pow_two_mul, ← mul_pow]
    norm_num
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [cosH, coshH, h2]

lemma scale_I_sinH : scale I (sinH ℂ) = C I * sinhH ℂ := by
  ext n
  rw [coeff_scale, C_mul_coeff]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h2 : (2 * k) % 2 = 0 := by omega
    simp [sinH, sinhH, h2]
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    have h3 : (2 * k + 1) / 2 = k := by omega
    simp only [sinH, sinhH, h2, h3, ite_true, pow_succ, I_pow_two_mul]
    rw [mul_assoc, mul_comm I, ← mul_assoc, ← mul_pow]
    norm_num

lemma scale_I_secH : scale I (secH ℂ) = sechH ℂ := by
  refine inv_unique' (u := coshH ℂ) ?_ coshH_mul_sechH
  rw [← scale_I_cosH, ← scale_mul, cosH_mul_secH, ← scaleHom_apply, map_one]

lemma scale_I_tanH : scale I (tanH ℂ) = C I * tanhH ℂ := by
  rw [tanH, scale_mul, scale_I_sinH, scale_I_secH, tanhH, mul_assoc]

lemma scale_I_sqH : scale I (sqH ℂ) = sqhH ℂ := by
  rw [sqH, scale_hexp, sqhH]
  apply hexp_eq_of_D_eq
  have hs : scale I (scale 2 (tanH ℂ)) = scale 2 (scale I (tanH ℂ)) := by
    rw [scale_scale, scale_scale, mul_comm]
  rw [scale_integ, D_integ, hs, scale_I_tanH, scale_mul, scale_C, ← mul_assoc, ← C_mul,
    I_mul_I, C_neg, C_one]
  ring

lemma scale_I_gH : scale I (gH ℂ) = GH ℂ := by
  rw [gH, scale_mul, scale_I_secH, scale_I_sqH, GH]

/-- The even coefficients of $g$ and $G(x) = g(ix)$ differ by the sign $(-1)^n$. -/
theorem gH_coeff_even (n : ℕ) : (gH ℤ).coeff (2 * n) = (-1) ^ n * (GH ℤ).coeff (2 * n) := by
  have h := congrArg (fun F => Hur.coeff F (2 * n)) scale_I_gH
  simp only [coeff_scale, I_pow_two_mul] at h
  rw [← map_gH (Int.castRingHom ℂ), ← map_GH (Int.castRingHom ℂ), coeff_map, coeff_map] at h
  apply Int.cast_injective (α := ℂ)
  push_cast
  simp only [eq_intCast] at h
  have h1 : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  linear_combination (-1 : ℂ) ^ n * h - ((gH ℤ).coeff (2 * n) : ℂ) * h1

end Twist

end Hur

end OeisA012780

namespace OeisA012780

open PowerSeries

section Bridge
open Hur

/-- The Hurwitz series of EGF coefficients $n!\,[x^n] F$ of a rational power series. -/
noncomputable def jetFun (F : ℚ⟦X⟧) : Hur ℚ :=
  ⟨fun n => (n.factorial : ℚ) * coeff n F⟩

lemma jetFun_coeff (F : ℚ⟦X⟧) (n : ℕ) :
    (jetFun F).coeff n = (n.factorial : ℚ) * coeff n F := rfl

lemma jetFun_derivative (F : ℚ⟦X⟧) : jetFun (derivative (R := ℚ) F) = Hur.D (jetFun F) := by
  ext n
  simp only [jetFun_coeff, Hur.coeff_D, coeff_derivative, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

lemma jetFun_add (F G : ℚ⟦X⟧) : jetFun (F + G) = jetFun F + jetFun G := by
  ext n
  simp [jetFun_coeff, mul_add]

lemma jetFun_mul (F G : ℚ⟦X⟧) : jetFun (F * G) = jetFun F * jetFun G := by
  suffices h : ∀ n, ∀ F G : ℚ⟦X⟧,
      (jetFun (F * G)).coeff n = (jetFun F * jetFun G).coeff n from
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

lemma jet_coeff (F : ℚ⟦X⟧) (n : ℕ) :
    (jet F).coeff n = (n.factorial : ℚ) * coeff n F := rfl

lemma jet_derivative (F : ℚ⟦X⟧) : jet (d⁄dX F) = D (jet F) := jetFun_derivative F

lemma jet_injective : Function.Injective jet := by
  intro F G h
  ext n
  have he := congrArg (fun H => Hur.coeff H n) h
  simp only [jet_coeff] at he
  exact mul_left_cancel₀ (by exact_mod_cast n.factorial_ne_zero) he

lemma constantCoeff_eq_jet (F : ℚ⟦X⟧) : constantCoeff F = (jet F).coeff 0 := by
  rw [jet_coeff, ← coeff_zero_eq_constantCoeff_apply]
  simp

lemma jet_X : jet (X : ℚ⟦X⟧) = x := by
  ext n
  rw [jet_coeff, coeff_X]
  simp only [Hur.coeff_x]
  split_ifs with h
  · subst h
    simp
  · simp

lemma jet_C (r : ℚ) : jet (PowerSeries.C r) = Hur.C r := by
  ext n
  rw [jet_coeff, PowerSeries.coeff_C, Hur.coeff_C]
  split_ifs with h
  · subst h
    simp
  · simp

lemma jet_sin : jet (sin ℚ) = sinH ℚ := by
  ext n
  rw [jet_coeff, PowerSeries.sin, coeff_mk]
  simp only [sinH, Nat.even_iff, Algebra.algebraMap_self, RingHom.id_apply]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  by_cases h : n % 2 = 0
  · simp [h]
  · have h1 : n % 2 = 1 := by omega
    rw [ite_eq_right h, ite_eq_left h1]
    field_simp

lemma jet_cos : jet (cos ℚ) = cosH ℚ := by
  ext n
  rw [jet_coeff, PowerSeries.cos, coeff_mk]
  simp only [cosH, Nat.even_iff, Algebra.algebraMap_self, RingHom.id_apply]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  by_cases h : n % 2 = 0
  · rw [ite_eq_left h, ite_eq_left h]
    field_simp
  · simp [h]

lemma jet_inv_cos : jet (cos ℚ)⁻¹ = secH ℚ := by
  have h0 : constantCoeff (cos ℚ) ≠ 0 := by
    rw [constantCoeff_eq_jet, jet_cos, cosH_coeff_zero]
    exact one_ne_zero
  refine inv_unique' (u := cosH ℚ) ?_ cosH_mul_secH
  rw [← jet_cos, ← map_mul, PowerSeries.mul_inv_cancel _ h0, map_one]

lemma jet_tan : jet tan = tanH ℚ := by
  rw [tan, map_mul, jet_sin, jet_inv_cos, tanH]

lemma constantCoeff_tan : constantCoeff tan = 0 := by
  rw [constantCoeff_eq_jet, jet_tan, tanH_coeff_zero]

lemma hasSubst_tan : HasSubst tan := HasSubst.of_constantCoeff_zero' constantCoeff_tan

/-- The series $\sum_k \binom{2k}{k} x^k / 4^k = (1 - x)^{-1/2}$. -/
noncomputable def cbSeries : ℚ⟦X⟧ := PowerSeries.mk fun k => (k.centralBinom : ℚ) / 4 ^ k

lemma cbSeries_ode : (1 - X) * d⁄dX cbSeries = PowerSeries.C (1 / 2 : ℚ) * cbSeries := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_C_mul, coeff_derivative]
  cases n with
  | zero =>
    rw [coeff_zero_X_mul]
    simp [cbSeries, Nat.centralBinom]
    norm_num
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative]
    simp only [cbSeries, coeff_mk]
    have h := Nat.succ_mul_centralBinom_succ (n + 1)
    have hn : (n + 2) * (n + 2).centralBinom = 2 * (2 * n + 3) * (n + 1).centralBinom := by
      rw [h]
      ring
    have hq : ((n : ℚ) + 2) * ((n + 2).centralBinom : ℚ) =
        2 * (2 * n + 3) * (n + 1).centralBinom := by
      exact_mod_cast hn
    rw [show n + 1 + 1 = n + 2 by ring, pow_succ (4 : ℚ) (n + 1)]
    have hq' : ((n + 2).centralBinom : ℚ) = 2 * (2 * n + 3) * (n + 1).centralBinom / (n + 2) := by
      rw [← hq]
      field_simp
    rw [hq']
    push_cast
    field_simp
    ring

lemma cbSeries_sq : cbSeries ^ 2 * (1 - X) = 1 := by
  apply jet_injective
  have hode : (1 - x) * D (jet cbSeries) = Hur.C (1 / 2) * jet cbSeries := by
    rw [← jet_derivative, ← jet_X, ← map_one jet, ← map_sub, ← map_mul, cbSeries_ode,
      map_mul, jet_C]
  have hc : Hur.C (1 / 2 : ℚ) * 2 = 1 := by
    rw [← C_two, ← Hur.C_mul]
    norm_num
    rfl
  have hD : D (jet (cbSeries ^ 2 * (1 - X))) = 0 := by
    rw [map_mul, map_pow, map_sub, map_one, jet_X, sq, D_mul, D_mul, D_sub, D_one, D_x]
    linear_combination (2 * jet cbSeries) * hode + (jet cbSeries) ^ 2 * hc
  rw [eq_C_of_D_eq_zero hD, map_one, ← C_one]
  congr 1
  rw [← constantCoeff_eq_jet, map_mul, map_pow, map_sub, map_one, constantCoeff_X]
  simp [cbSeries, ← coeff_zero_eq_constantCoeff_apply]

/-- $\sum_{i + j = m} \binom{2i}{i} \binom{2j}{j} = 4^m$. -/
theorem centralBinom_conv (m : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, p.1.centralBinom * p.2.centralBinom =
      4 ^ m := by
  have hc : ∀ m, coeff m (cbSeries ^ 2) = 1 := by
    intro m
    induction m with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, map_pow]
      simp [cbSeries, ← coeff_zero_eq_constantCoeff_apply]
    | succ m ih =>
      have h := congrArg (PowerSeries.coeff (m + 1)) cbSeries_sq
      rw [mul_sub, mul_one, map_sub, mul_comm, coeff_succ_X_mul, ih, PowerSeries.coeff_one] at h
      simp only [Nat.add_one_ne_zero, ite_false] at h
      linear_combination h
  have h := hc m
  rw [sq, PowerSeries.coeff_mul] at h
  have h2 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      coeff p.1 cbSeries * coeff p.2 cbSeries =
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
        (p.1.centralBinom * p.2.centralBinom : ℚ)) / 4 ^ m := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [cbSeries, coeff_mk]
    rw [← hp, pow_add]
    field_simp
  rw [h2, div_eq_one_iff_eq (by positivity)] at h
  exact_mod_cast h

lemma derivative_arcsin : d⁄dX arcsin = expand 2 two_ne_zero cbSeries := by
  ext n
  rw [coeff_derivative, coeff_expand]
  simp only [arcsin, cbSeries, coeff_mk]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    rw [ite_eq_left h1, ite_eq_left (dvd_mul_right 2 k), h2,
      Nat.mul_div_cancel_left k two_pos]
    push_cast
    field_simp
  · have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
    have h2 : ¬ 2 ∣ 2 * k + 1 := by omega
    rw [ite_eq_right (by omega), ite_eq_right h2, zero_mul]

lemma derivative_arcsin_sq : (d⁄dX arcsin) ^ 2 * (1 - X ^ 2) = 1 := by
  rw [derivative_arcsin, ← expand_X 2 two_ne_zero, ← map_pow,
    ← map_one (expand 2 two_ne_zero),
    ← map_sub, ← map_mul, cbSeries_sq, map_one]

lemma constantCoeff_derivative_arcsin : constantCoeff (d⁄dX arcsin) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
  simp [arcsin]

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

/-- The derivative of $\arcsin(\tan x)$ is $\sec x\,(\cos 2x)^{-1/2}$. -/
theorem jet_derivative_arcsin_tan : jet (d⁄dX (arcsin.subst tan)) = gH ℚ := by
  set P := (d⁄dX arcsin).subst tan with hPdef
  have hP : P ^ 2 * (1 - tan ^ 2) = 1 := by
    have h := congrArg (substAlgHom (R := ℚ) hasSubst_tan) derivative_arcsin_sq
    rw [map_mul, map_pow, map_sub, map_one, map_pow, coe_substAlgHom, subst_X hasSubst_tan] at h
    exact h
  have hP0 : (jet P).coeff 0 = 1 := by
    rw [← constantCoeff_eq_jet, hPdef, constantCoeff_subst_of_zero _ _ constantCoeff_tan,
      constantCoeff_derivative_arcsin]
  have hJ : jet P ^ 2 * (1 - tanH ℚ ^ 2) = 1 := by
    have h := congrArg jet hP
    rwa [map_mul, map_pow, map_sub, map_one, map_pow, jet_tan] at h
  rw [derivative_subst hasSubst_tan, map_mul, jet_derivative, jet_tan, D_tanH, ← hPdef]
  have hQ : jet P * secH ℚ = sqH ℚ := by
    refine sq_unique (c := scale 2 (cosH ℚ)) (fun r hr => by linarith) ?_ sqH_sq_mul ?_
      sqH_coeff_zero
    · rw [double_angle.1]
      have hcs := cosH_mul_secH (R := ℚ)
      rw [tanH] at hJ
      linear_combination hJ + (jet P) ^ 2 * (cosH ℚ * secH ℚ + 1) * hcs
    · rw [coeff_mul_zero, hP0, secH_coeff_zero, one_mul]
  rw [gH, ← hQ]
  ring

/-- The integer sequence $A(n) = g_{2n}$, the even Hurwitz coefficients of
$g = \sec x\,(\cos 2x)^{-1/2}$. -/
def A (n : ℕ) : ℤ := (gH ℤ).coeff (2 * n)

/-- $a(n) = A(n)$: the OEIS terms are the integers $g_{2n}$. -/
theorem a_eq (n : ℕ) : a n = A n := by
  have h := congrArg (fun F => Hur.coeff F (2 * n)) jet_derivative_arcsin_tan
  simp only [jet_derivative, coeff_D, jet_coeff] at h
  rw [a, h, A, ← map_gH (Int.castRingHom ℚ), Hur.coeff_map]
  rfl

end Bridge

end OeisA012780

namespace OeisA012780

open Hur

section TwoAdic

lemma two_pow_dvd_mul_choose (e i : ℕ) : 2 ^ e ∣ (2 ^ e).choose (i + 1) * (i + 1) := by
  have h := Nat.add_one_mul_choose_eq (2 ^ e - 1) i
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h
  exact ⟨_, h.symm⟩

lemma two_mul_le_two_pow (v : ℕ) : 2 * v ≤ 2 ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · simp
    · have : 2 ≤ 2 ^ v := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
      rw [pow_succ]
      omega

/-- If $2^v \mid c$ whenever $2^v \le l$, then $2^e \mid (\binom{N+2^e}{l} - \binom{N}{l})\,c$. -/
lemma two_pow_dvd_choose_shift (N e l : ℕ) (c : ℤ)
    (hc : ∀ v, 2 ^ v ≤ l → (2 : ℤ) ^ v ∣ c) :
    (2 : ℤ) ^ e ∣ (((N + 2 ^ e).choose l : ℤ) - (N.choose l : ℤ)) * c := by
  have hV : ((N + 2 ^ e).choose l : ℤ) - N.choose l =
      ∑ i ∈ Finset.range l,
        (((2 ^ e).choose (i + 1) * N.choose (l - (i + 1)) : ℕ) : ℤ) := by
    rw [add_comm N, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero]
    push_cast
    ring
  rw [hV, Finset.sum_mul]
  refine Finset.dvd_sum fun i hi => ?_
  have hil : i + 1 ≤ l := Finset.mem_range.1 hi
  obtain ⟨v, u, hu, hiu⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.succ_ne_zero i)
  have hvi : 2 ^ v ≤ i + 1 := by
    rw [show i + 1 = 2 ^ v * u from hiu]
    exact Nat.le_mul_of_pos_right _ hu.pos
  obtain ⟨c', rfl⟩ := hc v (le_trans hvi hil)
  have h1 : 2 ^ e ∣ ((2 ^ e).choose (i + 1) * 2 ^ v) * u := by
    rw [mul_assoc, ← hiu]
    exact two_pow_dvd_mul_choose e i
  have h2 : 2 ^ e ∣ (2 ^ e).choose (i + 1) * 2 ^ v :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hu)) h1
  have h3 : (2 : ℤ) ^ e ∣ ((2 ^ e).choose (i + 1) : ℤ) * 2 ^ v := by exact_mod_cast h2
  have h4 : ((((2 ^ e).choose (i + 1) * N.choose (l - (i + 1)) : ℕ) : ℤ)) * (2 ^ v * c') =
      (((2 ^ e).choose (i + 1) : ℤ) * 2 ^ v) * (N.choose (l - (i + 1)) * c') := by
    push_cast
    ring
  rw [h4]
  exact Dvd.dvd.mul_right h3 _

/-- If $2^{\lfloor l/2 \rfloor} \mid c_l$ for every $l$, then $F = c \cdot e^x$ satisfies
$2^e \mid F_{M + 2^e} - F_M$. -/
lemma mahler (c : Hur ℤ) (hc : ∀ l, (2 : ℤ) ^ (l / 2) ∣ c.coeff l) (M e : ℕ) :
    (2 : ℤ) ^ e ∣ (c * ex 1).coeff (M + 2 ^ e) - (c * ex 1).coeff M := by
  have hext : ∀ N K, N ≤ K → (c * ex 1).coeff N =
      ∑ l ∈ Finset.range (K + 1), (N.choose l : ℤ) * c.coeff l := by
    intro N K hNK
    rw [coeff_mul_sum]
    simp only [coeff_ex, one_pow, mul_one]
    apply Finset.sum_subset
    · intro l hl
      simp only [Finset.mem_range] at hl ⊢
      omega
    · intro l _ hl
      simp only [Finset.mem_range, not_lt] at hl
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  rw [hext (M + 2 ^ e) (M + 2 ^ e) le_rfl, hext M (M + 2 ^ e) (Nat.le_add_right M _),
    ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun l _ => ?_
  rw [← sub_mul]
  apply two_pow_dvd_choose_shift
  intro v hv
  exact (pow_dvd_pow 2 (by have := two_mul_le_two_pow v; omega)).trans (hc l)

lemma two_pow_half_dvd_factorial (j : ℕ) : 2 ^ (j / 2) ∣ j.factorial := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j, ih with
    | 0, _ => simp
    | 1, _ => simp
    | j + 2, ih =>
      have h := ih j (by omega)
      have h2 : 2 ∣ (j + 2) * (j + 1) := by
        rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact Dvd.dvd.mul_right ⟨k + 1, by omega⟩ _
        · exact Dvd.dvd.mul_left ⟨k + 1, by omega⟩ _
      have hf : (j + 2).factorial = ((j + 2) * (j + 1)) * j.factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ, mul_assoc]
      rw [hf, show (j + 2) / 2 = j / 2 + 1 by omega, pow_succ, mul_comm (2 ^ (j / 2)) 2]
      exact Nat.mul_dvd_mul h2 h

/-- Lemma 3: $2^{\lceil m/2 \rceil}$ divides the coefficient $\tilde S_m$ of
$(\cosh 2x)^{-1/2}$. -/
lemma two_pow_dvd_sqhH (m : ℕ) : (2 : ℤ) ^ ((m + 1) / 2) ∣ (sqhH ℤ).coeff m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [← coeff_D, D_sqhH, coeff_mul_sum]
      refine Finset.dvd_sum fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp [coeff_scale, tanhH_coeff_zero]
      · have h1 := ih (m - i) (by omega)
        rw [coeff_neg, coeff_scale]
        have h2 : (2 : ℤ) ^ ((m + 1 + 1) / 2) ∣ 2 ^ i * 2 ^ ((m - i + 1) / 2) := by
          rw [← pow_add]
          exact pow_dvd_pow 2 (by omega)
        have h3 : (m.choose i : ℤ) * (-(2 ^ i * (tanhH ℤ).coeff i) * (sqhH ℤ).coeff (m - i)) =
            (2 ^ i * (sqhH ℤ).coeff (m - i)) * (-((m.choose i : ℤ) * (tanhH ℤ).coeff i)) := by
          ring
        rw [h3]
        exact Dvd.dvd.mul_right (h2.trans (mul_dvd_mul (dvd_refl _) h1)) _

/-- $d = e^{-x} \operatorname{sech} x = 2/(1 + e^{2x})$. -/
def dH : Hur ℤ := ex (-1) * sechH ℤ

lemma dH_mul : dH * (C 2 + (ex 2 - 1)) = C 2 := by
  have h1 := two_coshH (R := ℤ)
  have h2 := coshH_mul_sechH (R := ℤ)
  have h3 : ex (-1 : ℤ) * ex 2 = ex 1 := by rw [← ex_add]; norm_num
  rw [C_two]
  unfold dH
  linear_combination (sechH ℤ) * h3 - (sechH ℤ) * h1 + 2 * h2

lemma coeff_neg_y_pow (j l : ℕ) : ((-(ex (2 : ℤ) - 1)) ^ j).coeff l =
    (-1) ^ j * 2 ^ l * (j.factorial * (dpow (ex (1 : ℤ) - 1) j).coeff l) := by
  have hy : ex (2 : ℤ) - 1 = scale 2 (ex 1 - 1) := by
    rw [← scaleHom_apply, map_sub, map_one, scaleHom_apply, scale_ex, mul_one]
  have h0 : (ex (1 : ℤ) - 1).coeff 0 = 0 := by simp [coeff_ex, coeff_one]
  have hm : ((-1 : Hur ℤ)) ^ j = C ((-1) ^ j) := by rw [C_pow, C_neg, C_one]
  rw [neg_pow, hy, ← scaleHom_apply, ← map_pow, scaleHom_apply, pow_eq_factorial_mul_dpow _ h0,
    hm,
    C_mul_coeff, coeff_scale, natCast_mul_coeff]
  ring

/-- $2^{\lfloor l/2 \rfloor}$ divides $d_l$. -/
lemma two_pow_dvd_dH (l : ℕ) : (2 : ℤ) ^ (l / 2) ∣ dH.coeff l := by
  set y : Hur ℤ := ex 2 - 1
  have hy0 : (-y).coeff 0 = 0 := by simp [y, coeff_ex, coeff_one]
  let Gs : ℕ → Hur ℤ := fun N => ∑ j ∈ Finset.range N, (-y) ^ j * C 2 ^ (N - 1 - j)
  have hG : ∀ N, Gs N * (C 2 + y) = C 2 ^ N - (-y) ^ N := by
    intro N
    have h := geom_sum₂_mul (-y) (C (2 : ℤ)) N
    linear_combination -h
  have key : ∀ N, l < N → 2 * (Gs N).coeff l = 2 ^ N * dH.coeff l := by
    intro N hN
    have hdy : dH * (C 2 + y) = C 2 := dH_mul
    have h : Gs N * C 2 = dH * (C 2 ^ N - (-y) ^ N) := by
      calc Gs N * C 2 = Gs N * (dH * (C 2 + y)) := by rw [hdy]
        _ = dH * (Gs N * (C 2 + y)) := by ring
        _ = dH * (C 2 ^ N - (-y) ^ N) := by rw [hG]
    have h' := congrArg (fun F => Hur.coeff F l) h
    rw [mul_comm, C_mul_coeff, mul_sub, coeff_sub, ← C_pow, mul_comm dH, C_mul_coeff,
      mul_comm dH, coeff_mul_of_vanish _ _ l (fun k hk => pow_coeff_lt _ hy0 (by omega)),
      pow_coeff_lt _ hy0 hN, zero_mul, sub_zero] at h'
    exact h'
  have hsum : (Gs (l + 1)).coeff l = 2 ^ l *
      ∑ j ∈ Finset.range (l + 1),
        (2 : ℤ) ^ (l - j) * ((-1) ^ j * (j.factorial * (dpow (ex (1 : ℤ) - 1) j).coeff l)) := by
    simp only [Gs, coeff_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show l + 1 - 1 - j = l - j by omega, mul_comm, ← C_pow, C_mul_coeff, coeff_neg_y_pow]
    ring
  have hd : dH.coeff l = ∑ j ∈ Finset.range (l + 1),
      (2 : ℤ) ^ (l - j) * ((-1) ^ j * (j.factorial * (dpow (ex (1 : ℤ) - 1) j).coeff l)) := by
    have h := key (l + 1) (by omega)
    rw [hsum, pow_succ] at h
    have h2 : (2 : ℤ) ^ l * 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ h2
    linear_combination -h
  rw [hd]
  refine Finset.dvd_sum fun j hj => ?_
  have hjl : j ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hf : (2 : ℤ) ^ (j / 2) ∣ j.factorial := by exact_mod_cast two_pow_half_dvd_factorial j
  have h1 : (2 : ℤ) ^ (l / 2) ∣ 2 ^ (l - j) * 2 ^ (j / 2) := by
    rw [← pow_add]
    exact pow_dvd_pow 2 (by omega)
  have h2 : (2 : ℤ) ^ (l - j) * ((-1) ^ j * (j.factorial * (dpow (ex (1 : ℤ) - 1) j).coeff l)) =
      (2 ^ (l - j) * j.factorial) * ((-1) ^ j * (dpow (ex (1 : ℤ) - 1) j).coeff l) := by ring
  rw [h2]
  exact Dvd.dvd.mul_right (h1.trans (mul_dvd_mul (dvd_refl _) hf)) _

lemma GH_eq : GH ℤ = (sqhH ℤ * dH) * ex 1 := by
  have h := ex_mul_ex_neg (1 : ℤ)
  unfold GH dH
  linear_combination -(sechH ℤ * sqhH ℤ) * h

lemma two_pow_dvd_sqhH_mul_dH (l : ℕ) : (2 : ℤ) ^ (l / 2) ∣ (sqhH ℤ * dH).coeff l := by
  rw [coeff_mul_sum]
  refine Finset.dvd_sum fun j hj => ?_
  have hjl : j ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have h1 : (2 : ℤ) ^ (l / 2) ∣ 2 ^ ((j + 1) / 2) * 2 ^ ((l - j) / 2) := by
    rw [← pow_add]
    exact pow_dvd_pow 2 (by omega)
  exact Dvd.dvd.mul_left (h1.trans (mul_dvd_mul (two_pow_dvd_sqhH j) (two_pow_dvd_dH (l - j)))) _

/-- $2^e \mid G_{M + 2^e} - G_M$ for every $M$ and $e$. -/
theorem GH_two_adic (M e : ℕ) :
    (2 : ℤ) ^ e ∣ (GH ℤ).coeff (M + 2 ^ e) - (GH ℤ).coeff M := by
  rw [GH_eq]
  exact mahler _ two_pow_dvd_sqhH_mul_dH M e

/-- Theorem 1: $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for $e \ge 1$ and every $n$. -/
theorem A_two_adic (e n : ℕ) (he : 1 ≤ e) : A (n + 2 ^ (e - 1)) ≡ A n [ZMOD 2 ^ e] := by
  rw [Int.modEq_iff_dvd]
  unfold A
  rw [gH_coeff_even, gH_coeff_even]
  have hT : 2 * (n + 2 ^ (e - 1)) = 2 * n + 2 ^ e := by
    rw [mul_add, ← pow_succ', Nat.sub_add_cancel he]
  rw [hT]
  have hG := GH_two_adic (2 * n) e
  have hs : (2 : ℤ) ^ e ∣ (-1) ^ (2 ^ (e - 1)) - 1 := by
    rcases Nat.lt_or_ge 1 e with h | h
    · have h2 : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2, pow_mul]
      norm_num
    · obtain rfl : e = 1 := by omega
      norm_num
  rw [pow_add]
  have h3 : (-1 : ℤ) ^ n * (GH ℤ).coeff (2 * n) -
      (-1) ^ n * (-1) ^ 2 ^ (e - 1) * (GH ℤ).coeff (2 * n + 2 ^ e) =
      -((-1) ^ n * ((-1) ^ 2 ^ (e - 1) * ((GH ℤ).coeff (2 * n + 2 ^ e) - (GH ℤ).coeff (2 * n)) +
        ((-1) ^ 2 ^ (e - 1) - 1) * (GH ℤ).coeff (2 * n))) := by ring
  rw [h3, dvd_neg]
  exact Dvd.dvd.mul_left (dvd_add (Dvd.dvd.mul_left hG _) (Dvd.dvd.mul_right hs _)) _

end TwoAdic

end OeisA012780

namespace OeisA012780

open Hur

section Kallat
variable {R : Type*} [CommRing R]

/-- `F` and `G` agree up to index `N`. -/
def Agree (N : ℕ) (F G : Hur R) : Prop := ∀ M ≤ N, F.coeff M = G.coeff M

namespace Agree
variable {N : ℕ} {F G H F' G' : Hur R}

omit [CommRing R] in
lemma refl' (F : Hur R) : Agree N F F := fun _ _ => rfl

omit [CommRing R] in
lemma symm (h : Agree N F G) : Agree N G F := fun M hM => (h M hM).symm

omit [CommRing R] in
lemma trans (h1 : Agree N F G) (h2 : Agree N G H) : Agree N F H :=
  fun M hM => (h1 M hM).trans (h2 M hM)

lemma mul (h1 : Agree N F F') (h2 : Agree N G G') : Agree N (F * G) (F' * G') := fun M hM =>
  coeff_mul_congr _ _ _ _ M (fun k hk => h1 k (by omega)) (fun k hk => h2 k (by omega))

lemma add (h1 : Agree N F F') (h2 : Agree N G G') : Agree N (F + G) (F' + G') := fun M hM => by
  rw [coeff_add, coeff_add, h1 M hM, h2 M hM]

lemma pow (h : Agree N F G) (k : ℕ) : Agree N (F ^ k) (G ^ k) := fun M hM =>
  coeff_pow_congr F G N h k M hM

lemma sum {ι : Type*} (s : Finset ι) {f g : ι → Hur R} (h : ∀ i ∈ s, Agree N (f i) (g i)) :
    Agree N (∑ i ∈ s, f i) (∑ i ∈ s, g i) := fun M hM => by
  rw [coeff_sum, coeff_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi M hM

end Agree

lemma agree_pow_succ_mul {N : ℕ} {w : Hur R} (hw : w.coeff 0 = 0) (G : Hur R) :
    Agree N (w ^ (N + 1) * G) 0 := fun M hM => by
  rw [coeff_mul_of_vanish _ _ M (fun k hk => pow_coeff_lt w hw (by omega)),
    pow_coeff_lt w hw (by omega), zero_mul]
  rfl

/-- Evaluation of a polynomial at a series. -/
noncomputable def ev (w : Hur R) : Polynomial R →+* Hur R := Polynomial.eval₂RingHom CHom w

lemma ev_C (w : Hur R) (r : R) : ev w (Polynomial.C r) = C r := Polynomial.eval₂_C _ _

lemma ev_X (w : Hur R) : ev w Polynomial.X = w := Polynomial.eval₂_X _ _

lemma ev_coeff_zero (w : Hur R) (hw : w.coeff 0 = 0) (P : Polynomial R) :
    (ev w P).coeff 0 = P.coeff 0 := by
  have h := Polynomial.hom_eval₂ P CHom (coeff0 : Hur R →+* R) w
  have hc : (coeff0 : Hur R →+* R).comp CHom = RingHom.id R := by
    ext r
    simp [CHom_apply, coeff0_apply, coeff_C]
  simp only [hc, coeff0_apply] at h
  rw [hw] at h
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact h

/-- The variable $u = e^x - 1$. -/
def uH : Hur R := ex 1 - 1

lemma uH_coeff_zero : (uH : Hur R).coeff 0 = 0 := by simp [uH, coeff_ex, coeff_one]

/-- `F` agrees, up to every index, with a polynomial in $u = e^x - 1$. -/
def InK (F : Hur R) : Prop := ∀ N, ∃ P : Polynomial R, Agree N F (ev uH P)

variable {F G H w : Hur R}

lemma InK.mul (hF : InK F) (hG : InK G) : InK (F * G) := fun N => by
  obtain ⟨P, hP⟩ := hF N
  obtain ⟨Q, hQ⟩ := hG N
  exact ⟨P * Q, by rw [map_mul]; exact hP.mul hQ⟩

lemma InK.add (hF : InK F) (hG : InK G) : InK (F + G) := fun N => by
  obtain ⟨P, hP⟩ := hF N
  obtain ⟨Q, hQ⟩ := hG N
  exact ⟨P + Q, by rw [map_add]; exact hP.add hQ⟩

lemma InK.pow (hF : InK F) (k : ℕ) : InK (F ^ k) := fun N => by
  obtain ⟨P, hP⟩ := hF N
  exact ⟨P ^ k, by rw [map_pow]; exact hP.pow k⟩

lemma inK_C (r : R) : InK (C r) := fun _ => ⟨Polynomial.C r, by rw [ev_C]; exact Agree.refl' _⟩

lemma inK_ex_one : InK (ex (1 : R)) := fun _ =>
  ⟨Polynomial.X + 1, by rw [map_add, map_one, ev_X, uH, sub_add_cancel]; exact Agree.refl' _⟩

/-- `K` is closed under inverses of series with constant term $1$. -/
lemma InK.inv (hF : InK F) (h0 : F.coeff 0 = 1) (hH : H * F = 1) : InK H := by
  intro N
  obtain ⟨P, hP⟩ := hF N
  have hP0 : P.coeff 0 = 1 := by
    rw [← ev_coeff_zero uH uH_coeff_zero, ← hP 0 (Nat.zero_le _), h0]
  set q : Polynomial R := -(Polynomial.X * P.divX) with hq
  have hPq : P = 1 - q := by
    have h := Polynomial.X_mul_divX_add P
    rw [hP0, map_one] at h
    rw [hq]
    linear_combination -h
  refine ⟨∑ m ∈ Finset.range (N + 1), q ^ m, ?_⟩
  have hq0 : (ev uH q).coeff 0 = 0 := by
    rw [ev_coeff_zero _ uH_coeff_zero, hq]
    simp
  have hQP : ev uH (∑ m ∈ Finset.range (N + 1), q ^ m) * ev uH P = 1 - ev uH q ^ (N + 1) := by
    rw [← map_mul, hPq, mul_comm, mul_neg_geom_sum, map_sub, map_one, map_pow]
  have h1 : Agree N (ev uH (∑ m ∈ Finset.range (N + 1), q ^ m) * F) 1 := by
    refine ((Agree.refl' _).mul hP).trans ?_
    rw [hQP]
    intro M hM
    have h := agree_pow_succ_mul (N := N) hq0 1 M hM
    rw [mul_one] at h
    rw [coeff_sub, h, coeff_zero', sub_zero]
  have h2 := h1.mul (Agree.refl' H)
  rw [mul_assoc, mul_comm F H, hH, mul_one, one_mul] at h2
  exact h2.symm

/-- The composition $\sum_k b_k w^k$ of an ordinary power series with a series $w$, $w_0 = 0$. -/
def compose (b : ℕ → R) (w : Hur R) : Hur R :=
  ⟨fun M => ∑ k ∈ Finset.range (M + 1), b k * (w ^ k).coeff M⟩

/-- The truncation $\sum_{k \le N} b_k X^k$. -/
noncomputable def bpoly (b : ℕ → R) (N : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (b k) * Polynomial.X ^ k

lemma ev_bpoly (b : ℕ → R) (w : Hur R) (N : ℕ) :
    ev w (bpoly b N) = ∑ k ∈ Finset.range (N + 1), C (b k) * w ^ k := by
  simp [bpoly, map_sum, ev_C, ev_X]

lemma agree_compose (b : ℕ → R) (hw : w.coeff 0 = 0) (N : ℕ) :
    Agree N (compose b w) (ev w (bpoly b N)) := by
  intro M hM
  rw [ev_bpoly, coeff_sum]
  simp only [C_mul_coeff, compose]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [pow_coeff_lt w hw (by omega), mul_zero]

lemma compose_coeff_zero (b : ℕ → R) (w : Hur R) : (compose b w).coeff 0 = b 0 := by
  simp [compose, coeff_one]

lemma InK.compose (b : ℕ → R) (hw : InK w) (hw0 : w.coeff 0 = 0) : InK (compose b w) := by
  intro N
  obtain ⟨P, hP⟩ := hw N
  refine ⟨∑ k ∈ Finset.range (N + 1), Polynomial.C (b k) * P ^ k, ?_⟩
  refine (agree_compose b hw0 N).trans ?_
  rw [ev_bpoly, map_sum]
  refine Agree.sum _ fun k _ => ?_
  rw [map_mul, map_pow, ev_C]
  exact (Agree.refl' _).mul (hP.pow k)

lemma bpoly_coeff (b : ℕ → R) (N i : ℕ) :
    (bpoly b N).coeff i = if i ≤ N then b i else 0 := by
  simp only [bpoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

/-- The coefficients $\binom{-1/2}{k} = (-1)^k \binom{2k}{k} / 4^k$, with $t = 1/2$. -/
def bR (t : R) (k : ℕ) : R := (-1) ^ k * (k.centralBinom : R) * (t ^ 2) ^ k

lemma bR_conv (t : R) (ht : 2 * t = 1) (d : ℕ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal d, bR t x.1 * bR t x.2 = (-1) ^ d := by
  have h : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal d, bR t x.1 * bR t x.2 =
      (-1) ^ d * (t ^ 2) ^ d * ((x.1.centralBinom * x.2.centralBinom : ℕ) : R) := by
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    simp only [bR]
    rw [← hx, pow_add, pow_add]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← Nat.cast_sum, centralBinom_conv]
  have h4 : (t ^ 2) ^ d * ((4 ^ d : ℕ) : R) = 1 := by
    have h5 : t ^ 2 * 4 = 1 := by linear_combination (2 * t + 1) * ht
    push_cast
    rw [← mul_pow, h5, one_pow]
  linear_combination (-1) ^ d * h4

lemma bpoly_sq (t : R) (ht : 2 * t = 1) (N : ℕ) :
    ∃ T : Polynomial R,
      bpoly (bR t) N ^ 2 * (1 + Polynomial.X) = 1 + Polynomial.X ^ (N + 1) * T := by
  have hc : ∀ m ≤ N, (bpoly (bR t) N ^ 2).coeff m = (-1) ^ m := by
    intro m hm
    rw [sq, Polynomial.coeff_mul, ← bR_conv t ht m]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [bpoly_coeff, bpoly_coeff, ite_eq_left (by omega), ite_eq_left (by omega)]
  have hdvd : Polynomial.X ^ (N + 1) ∣ bpoly (bR t) N ^ 2 * (1 + Polynomial.X) - 1 := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_one]
    cases d with
    | zero =>
      rw [Polynomial.coeff_mul_X_zero, hc 0 (Nat.zero_le _)]
      simp
    | succ d =>
      rw [Polynomial.coeff_mul_X, hc (d + 1) (by omega), hc d (by omega)]
      simp [pow_succ]
  obtain ⟨T, hT⟩ := hdvd
  exact ⟨T, by linear_combination hT⟩

lemma compose_bR_sq (t : R) (ht : 2 * t = 1) (hw : w.coeff 0 = 0) :
    compose (bR t) w ^ 2 * (1 + w) = 1 := by
  ext M
  obtain ⟨T, hT⟩ := bpoly_sq t ht M
  have h1 : Agree M (compose (bR t) w ^ 2 * (1 + w))
      (ev w (bpoly (bR t) M ^ 2 * (1 + Polynomial.X))) := by
    rw [map_mul, map_pow, map_add, map_one, ev_X]
    exact ((agree_compose (bR t) hw M).pow 2).mul (Agree.refl' _)
  rw [h1 M le_rfl, hT, map_add, map_one, map_mul, map_pow, ev_X, coeff_add,
    agree_pow_succ_mul (N := M) hw _ M le_rfl]
  simp

lemma coeff_ev_ex (Q : Polynomial R) (M : ℕ) :
    (ev (ex 1) Q).coeff M = ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * (i : R) ^ M := by
  rw [ev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range, coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CHom_apply, C_mul_coeff, ex_natCast, coeff_ex]

lemma ev_uH (P : Polynomial R) : ev uH P = ev (ex 1) (P.comp (Polynomial.X - 1)) := by
  rw [ev, ev, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_comp]
  congr 1
  simp [uH]

/-- A member of `K` is periodic wherever every power $i^M$ is. -/
lemma InK.periodic {L e : ℕ}
    (hR : ∀ i : ℕ, ∀ M, e ≤ M → (i : R) ^ (M + L) = (i : R) ^ M)
    (hF : InK F) {M : ℕ} (hM : e ≤ M) : F.coeff (M + L) = F.coeff M := by
  obtain ⟨P, hP⟩ := hF (M + L)
  rw [hP (M + L) le_rfl, hP M (by omega), ev_uH, coeff_ev_ex, coeff_ev_ex]
  exact Finset.sum_congr rfl fun i _ => by rw [hR i M hM]

lemma inK_ex_neg_one : InK (ex (-1 : R)) :=
  InK.inv inK_ex_one (by simp [coeff_ex]) (by rw [mul_comm]; exact ex_mul_ex_neg 1)

section Half
variable (t : R) (ht : 2 * t = 1)
include ht

lemma inK_coshH : InK (coshH R) := by
  have h : coshH R = C t * (ex 1 + ex (-1)) := by
    rw [← two_coshH, ← C_two, ← mul_assoc, ← C_mul, mul_comm t, ht, C_one, one_mul]
  rw [h]
  exact (inK_C t).mul (inK_ex_one.add (inK_ex_neg_one))

lemma inK_sechH : InK (sechH R) :=
  InK.inv (inK_coshH t ht) coshH_coeff_zero (by rw [mul_comm]; exact coshH_mul_sechH)

lemma inK_cosh2 : InK (scale 2 (coshH R)) := by
  have h1 : C (2 : R) * scale 2 (coshH R) = ex 1 ^ 2 + ex (-1) ^ 2 := by
    rw [← scale_C 2 2, ← scale_mul, C_two, two_coshH, ← scaleHom_apply, map_add,
      scaleHom_apply,
      scaleHom_apply, scale_ex, scale_ex, sq, sq, ← ex_add, ← ex_add]
    ring_nf
  have h : scale 2 (coshH R) = C t * (ex 1 ^ 2 + ex (-1) ^ 2) := by
    rw [← h1, ← mul_assoc, ← C_mul, mul_comm t, ht, C_one, one_mul]
  rw [h]
  exact (inK_C t).mul ((inK_ex_one.pow 2).add ((inK_ex_neg_one).pow 2))

lemma sqhH_eq_compose :
    sqhH R = compose (bR t) (scale 2 (coshH R) - 1) := by
  have hw0 : (scale 2 (coshH R) - 1).coeff 0 = 0 := by
    simp [coeff_scale, coshH_coeff_zero, coeff_one]
  refine (sq_unique (c := scale 2 (coshH R)) (fun r hr => ?_) sqhH_sq_mul ?_ sqhH_coeff_zero ?_)
  · linear_combination t * hr - r * ht
  · have h := compose_bR_sq t ht hw0
    rwa [add_sub_cancel] at h
  · rw [compose_coeff_zero]
    simp [bR]

lemma inK_sqhH : InK (sqhH R) := by
  have h : scale 2 (coshH R) - 1 = scale 2 (coshH R) + C (-1) := by
    rw [C_neg, C_one, sub_eq_add_neg]
  rw [sqhH_eq_compose t ht, h]
  refine InK.compose _ ((inK_cosh2 t ht).add (inK_C (-1))) ?_
  simp [coeff_scale, coshH_coeff_zero, coeff_C]

lemma inK_GH : InK (GH R) := (inK_sechH t ht).mul (inK_sqhH t ht)

end Half

end Kallat

section OddPrime

lemma zmod_pow_periodic {p e : ℕ} (hp : p.Prime) (i M : ℕ) (hM : e ≤ M) :
    (i : ZMod (p ^ e)) ^ (M + (p ^ e).totient) = (i : ZMod (p ^ e)) ^ M := by
  by_cases h : p ∣ i
  · obtain ⟨s, rfl⟩ := h
    have h0 : ((p : ZMod (p ^ e))) ^ M = 0 := by
      rw [show M = e + (M - e) by omega, pow_add, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
    rw [Nat.cast_mul, mul_pow, mul_pow, pow_add (p : ZMod (p ^ e)), h0, zero_mul, zero_mul,
      zero_mul]
  · have hcop : Nat.Coprime i (p ^ e) :=
      Nat.Coprime.pow_right e (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
    have hu := ZMod.pow_totient (ZMod.unitOfCoprime i hcop)
    have h1 : (i : ZMod (p ^ e)) ^ (p ^ e).totient = 1 := by
      have := congrArg Units.val hu
      rwa [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at this
    rw [pow_add, h1, mul_one]

/-- $G_{M + \varphi(p^e)} \equiv G_M \pmod{p^e}$ for odd primes $p$ and $M \ge e$. -/
theorem GH_odd_prime {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : ℕ} (hM : e ≤ M) :
    (GH ℤ).coeff (M + (p ^ e).totient) ≡ (GH ℤ).coeff M [ZMOD p ^ e] := by
  have hcop : Nat.Coprime 2 (p ^ e) :=
    Nat.Coprime.pow_right e ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h2 : IsUnit (2 : ZMod (p ^ e)) := by
    have := (ZMod.unitOfCoprime 2 hcop).isUnit
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  obtain ⟨t, ht⟩ : ∃ t : ZMod (p ^ e), 2 * t = 1 := ⟨h2.unit⁻¹.val, h2.mul_val_inv⟩
  have h := (inK_GH t ht).periodic (zmod_pow_periodic hp) hM
  rw [← map_GH (Int.castRingHom (ZMod (p ^ e))), coeff_map, coeff_map] at h
  have h' := (ZMod.intCast_eq_intCast_iff _ _ _).1 h
  exact_mod_cast h'

/-- Theorem 2: $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ for odd primes $p$, $e \ge 1$
and $2n \ge e$. -/
theorem A_odd_prime {p e n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hn : e ≤ 2 * n) :
    A (n + (p ^ e).totient) ≡ A n [ZMOD p ^ e] := by
  set L := (p ^ e).totient
  have hL : Even L := by
    apply Nat.totient_even
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    calc 2 < 3 := by norm_num
      _ ≤ p := h3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  unfold A
  rw [gH_coeff_even, gH_coeff_even, pow_add, hL.neg_one_pow, mul_one,
    show 2 * (n + L) = (2 * n + L) + L by ring]
  have h1 := GH_odd_prime (e := e) hp hp2 (M := 2 * n + L) (by omega)
  have h2 := GH_odd_prime (e := e) hp hp2 (M := 2 * n) hn
  exact (h1.trans h2).mul_left _

end OddPrime

end OeisA012780

namespace OeisA012780

/-- A period that holds from `N0` on also holds for its multiples. -/
lemma period_mul {x : ℕ → ℤ} {m : ℤ} {L N0 : ℕ}
    (h : ∀ n, N0 ≤ n → x (n + L) ≡ x n [ZMOD m]) (c : ℕ) :
    ∀ n, N0 ≤ n → x (n + c * L) ≡ x n [ZMOD m] := by
  induction c with
  | zero => intro n _; simp
  | succ c ih =>
    intro n hn
    rw [show n + (c + 1) * L = (n + c * L) + L by ring]
    exact (h _ (by omega)).trans (ih n hn)

/-- If every prime-power part of `k` divides `z`, then `k` divides `z`. -/
lemma dvd_of_prime_pow_dvd {k : ℕ} (hk : k ≠ 0) {z : ℤ}
    (h : ∀ q ∈ k.primeFactors, ((q ^ k.factorization q : ℕ) : ℤ) ∣ z) :
    (k : ℤ) ∣ z := by
  have hk' : (∏ q ∈ k.primeFactors, q ^ k.factorization q) = k := by
    have := Nat.prod_factorization_pow_eq_self hk
    rwa [Finsupp.prod, Nat.support_factorization] at this
  rw [← hk', Nat.cast_prod]
  apply Finset.prod_dvd_of_coprime
  · intro q hq q' hq' hne
    simp only [Function.onFun]
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hq)
      (Nat.prime_of_mem_primeFactors hq')).2 hne)
  · exact h

/-- The prime-power step of Corollary 3: the congruence modulo $q^f$, $q^f \| k$. -/
lemma A_prime_pow_part {k q n : ℕ} (hq : q ∈ k.primeFactors)
    (hn : q ≠ 2 → k.factorization q ≤ 2 * n) :
    A (n + k.totient) ≡ A n [ZMOD ((q ^ k.factorization q : ℕ) : ℤ)] := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  set f := k.factorization q
  have hf : 1 ≤ f := (hqp.dvd_iff_one_le_factorization (Nat.mem_primeFactors.1 hq).2.2).1
    (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨c, hc⟩ := Nat.totient_dvd_of_dvd (Nat.ordProj_dvd k q)
  rw [hc, mul_comm]
  push_cast
  by_cases h2 : q = 2
  · subst h2
    have hL : (2 ^ f).totient = 2 ^ (f - 1) := by
      rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp
    rw [hL]
    exact period_mul (N0 := 0) (fun m _ => A_two_adic f m hf) c n (Nat.zero_le n)
  · exact period_mul (N0 := n) (fun m hm => A_odd_prime hqp h2 hf (by have := hn h2; omega))
      c n le_rfl

/-- Corollary 3: $a(n + \varphi(k)) \equiv a(n) \pmod k$ whenever $2n$ is at least the exponent
of every odd prime in `k`. -/
theorem A_corollary3 {k : ℕ} (hk : 1 ≤ k) (n : ℕ)
    (hn : ∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n) :
    A (n + k.totient) ≡ A n [ZMOD k] := by
  rw [Int.modEq_iff_dvd]
  apply dvd_of_prime_pow_dvd (by omega)
  intro q hq
  exact Int.modEq_iff_dvd.1
    (A_prime_pow_part hq fun h2 => hn q (Nat.prime_of_mem_primeFactors hq) h2)

/-- The exponent of a prime in `k` is less than `k`. -/
lemma factorization_lt {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) : k.factorization p < k := by
  calc k.factorization p < p ^ k.factorization p := Nat.lt_pow_self hp.one_lt
    _ ≤ k := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd k p)

/-- Bala's conjecture with the explicit threshold $N = k$. -/
theorem A_bala {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : k ≤ n) :
    A (n + k.totient) ≡ A n [ZMOD k] :=
  A_corollary3 hk n fun p hp _ => by have := factorization_lt hk hp; omega

/-- $A(n) \equiv 2n + 1 \pmod 8$, from the period $4$ modulo $8$ and the first four terms. -/
theorem A_mod_eight (n : ℕ) : A n ≡ 2 * n + 1 [ZMOD 8] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n
      · have h : A 0 = 1 := by decide +kernel
        rw [h, Int.ModEq]; norm_num
      · have h : A 1 = 3 := by decide +kernel
        rw [h, Int.ModEq]; norm_num
      · have h : A 2 = 45 := by decide +kernel
        rw [h, Int.ModEq]; norm_num
      · have h : A 3 = 1743 := by decide +kernel
        rw [h, Int.ModEq]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h := A_two_adic 3 m (by norm_num)
      norm_num at h
      have hm := ih m (by omega)
      rw [Int.ModEq] at h hm ⊢
      push_cast
      omega

end OeisA012780

namespace OeisA012780

/-! ### The statements -/

/-- The first terms agree with the OEIS data. -/
theorem a_first_terms : a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 45 ∧ a 3 = 1743 ∧ a 4 = 133305 := by
  have h0 : A 0 = 1 := by decide +kernel
  have h1 : A 1 = 3 := by decide +kernel
  have h2 : A 2 = 45 := by decide +kernel
  have h3 : A 3 = 1743 := by decide +kernel
  have h4 : A 4 = 133305 := by decide +kernel
  simp only [a_eq, h0, h1, h2, h3, h4]
  norm_num

/-- Bala's conjecture for OEIS A012780: every $a(n)$ is an integer, and for every $k \ge 1$ the
sequence $a(n) \bmod k$ is eventually periodic with period dividing $\varphi(k)$. -/
theorem bala_conjecture :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N, b (n + k.totient) ≡ b n [ZMOD k] :=
  ⟨A, fun n => (a_eq n).symm, fun _ hk => ⟨_, fun _ hn => A_bala hk hn⟩⟩

/-- The conjecture with an explicit pre-period: $a(n + \varphi(k)) \equiv a(n) \pmod k$ for every
$k \ge 1$ and every $n$ such that $2n$ is at least the exponent of each odd prime in $k$. -/
theorem bala_explicit :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k n : ℕ, 1 ≤ k →
        (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n) →
        b (n + k.totient) ≡ b n [ZMOD k] :=
  ⟨A, fun n => (a_eq n).symm, fun _ n hk hn => A_corollary3 hk n hn⟩

/-- The prime $2$: $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for every $e \ge 1$ and every $n$. -/
theorem period_two_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 1 ≤ e → b (n + 2 ^ (e - 1)) ≡ b n [ZMOD 2 ^ e] :=
  ⟨A, fun n => (a_eq n).symm, fun e n he => A_two_adic e n he⟩

/-- Odd primes: $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ for every odd prime $p$, every
$e \ge 1$ and every $n \ge e/2$. -/
theorem period_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n →
        b (n + (p ^ e).totient) ≡ b n [ZMOD p ^ e] :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ _ hp hp2 he hn => A_odd_prime hp hp2 he hn⟩

/-- Modulo $8$, the shift $2 = \lambda(8)$ is not an eventual period:
$a(n + 2) \not\equiv a(n) \pmod 8$ for every $n$. -/
theorem not_period_two_mod_eight :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ ∀ n, ¬ b (n + 2) ≡ b n [ZMOD 8] := by
  refine ⟨A, fun n => (a_eq n).symm, fun n h => ?_⟩
  have h1 := A_mod_eight (n + 2)
  have h2 := A_mod_eight n
  rw [Int.ModEq] at h h1 h2
  push_cast at h1
  omega

end OeisA012780

end
