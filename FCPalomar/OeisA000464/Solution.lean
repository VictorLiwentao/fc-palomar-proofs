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
# OEIS A000464: Bala's conjectures for $\sin x / \cos 2x$

Let $a(n) = (2n+1)!\,[x^{2n+1}]\, \sin x / \cos 2x$ (OEIS A000464, offset 0). The file proves
that every $a(n)$ is an integer and that:
- Bala's conjecture 1) is false as stated: modulo every multiple of $81$, $(a(n))_{n \ge 1}$ is
  not purely periodic with any period, because $a(55) \equiv 65 \not\equiv 11 = a(1)
  \pmod{81}$;
- $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for $e \ge 1$ and every $n$ (Theorem 1), and
  $a(n + 2^{e-2}) \equiv a(n) \pmod{2^e}$ for $e \ge 3$;
- $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n) \pmod{p^e}$ for odd primes $p$,
  $e \ge 1$ and $2n + 1 \ge e$, hence $a(n + \varphi(p^e)) \equiv a(n)$ (Theorem 2);
- $a(n + \varphi(k)) \equiv a(n) \pmod k$ whenever $2n + 1$ is at least the exponent of every odd
  prime in $k$ (Corollary 3, conjecture 1) corrected). So 1) holds eventually for every $k$, and
  from $n = 1$ when every odd prime exponent of $k$ is at most $3$;
- the same with the Carmichael function $\lambda(k)$ in place of $\varphi(k)$. At $k = 8$ the
  period $\lambda(8) = 2$ cannot be replaced by $1$, as $a(1) = 11 \not\equiv 1 = a(0)
  \pmod 8$;
- the Gauss congruences $a(n p^k + i) \equiv a(n p^{k-1} + i) \pmod{p^k}$ (conjecture 2), and
  so $\exp\left(\sum_{n \ge 1} a(n + i) x^n / n\right)$ has integer coefficients;
- $a(mn) \equiv a(m)^n \pmod{2^{2 v_2(m) + 4}}$ (conjecture 3), and $a(2mn) \equiv a(n)^{2m}$,
  $a((2m+1)n) \equiv a(n)^{2m+1} \pmod{2^{v_2(m) + 4}}$ (conjecture 4), for $m, n \ge 1$.

The proof works with Hurwitz series over a commutative ring: sequences $f_n = n!\,[x^n] f$ with
the binomial product. The series $\cos x$, $\sin x$, $\cosh x$, $\sinh x$ have explicit
coefficients, $\sec x$ and $\operatorname{sech} x$ are the inverses of $\cos x$ and $\cosh x$,
and $f(x) \mapsto f(cx)$ is the rescaling $f_n \mapsto c^n f_n$.

*Integrality.* The Hurwitz coefficients of $\sin x / \cos 2x$ over $\mathbb{Q}$ are those of
$g = \sin x \cdot \sec 2x$, which has integer coefficients. So $a(n) = A(n) := g_{2n+1}$.

*The hyperbolic form.* Over $\mathbb{C}$, the rescaling $x \mapsto ix$ maps $\sin x$,
$\sec 2x$ to $i \sinh x$, $\operatorname{sech} 2x$. So $G = \sinh x \cdot \operatorname{sech} 2x$
satisfies $g_{2n+1} = (-1)^n G_{2n+1}$.

*The prime 2.* With $w = e^x$, $G = c\,w$ for $c = \frac{w^2 - 1}{2} \cdot
\frac{2}{1 + w^4}$. The first factor has coefficients $2^{l-1}$ ($l \ge 1$), and the second is
$d(2x)$ with $d = 2/(1 + e^{2x}) = e^{-x} \operatorname{sech} x$ integral, so its coefficients are
divisible by $2^l$. Hence $2^{\lfloor l/2 \rfloor} \mid c_l$, and the Vandermonde argument for
$G_M = \sum_l \binom{M}{l} c_l$ gives $2^e \mid G_{M + 2^e} - G_M$ for every $M$. The signs
$(-1)^n$ give Theorem 1.

*The prime 2, sharper.* In fact $2^{l-1} \mid c_l$, and $c_0 = 0$, $c_1 = 1$, $c_2 = -2$. In
$G_{M + 2^k} - G_M = \sum_l \left(\binom{M + 2^k}{l} - \binom{M}{l}\right) c_l$, Vandermonde
writes the bracket as $\sum_{1 \le i \le l} \binom{2^k}{i} \binom{M}{l-i}$, and
$2^{k - v} \mid \binom{2^k}{i}$ for $v = v_2(i)$. For $l \ge 3$, $2^v \le l$ gives
$v + 1 \le l - 1$, so these terms are divisible by $2^{k+1}$. The terms $l = 1, 2$ sum to
$2^k (2 - 2M - 2^k)$, by $2 \binom{n}{2} = n(n-1)$. So $2^{k+1} \mid G_{M + 2^k} - G_M$ for
$k \ge 1$. Take $M = 2n + 1$ and $k = e - 1$; the sign $(-1)^{2^{e-2}}$ is $1$ for $e \ge 3$.

*Odd primes.* Fix an odd prime power $p^e$ and work over $\mathbb{Z}/p^e$, where $2$ is a unit.
The set $K$ of series that agree, up to every index, with a polynomial in $u = e^x - 1$ is a
subring that contains $e^{\pm x}$ and is closed under inverses of series with constant term $1$.
So $\sinh x$, $\cosh 2x$, $\operatorname{sech} 2x$ and $G$ lie in $K$. A polynomial in $e^x$ has
coefficients $\sum_i c_i\, i^M$, and $i^{M + \varphi(p^e)} = i^M$ in $\mathbb{Z}/p^e$ for
$M \ge e$. So $G_{M + \varphi(p^e)} \equiv G_M \pmod{p^e}$ for $M \ge e$. With $M = 2n + 1$ and
$\varphi(p^e) = 2 \cdot \frac{p-1}{2} p^{e-1}$, the sign $(-1)^{\frac{p-1}{2} p^{e-1}} =
(-1)^{(p-1)/2}$ gives Theorem 2. Applying it twice gives the period $\varphi(p^e)$.

*Every modulus.* For each prime power $q^f$ that exactly divides $k$, $\varphi(q^f) \mid
\varphi(k)$, so the prime-power congruences, iterated, hold modulo $q^f$ with shift
$\varphi(k)$. These prime powers are pairwise coprime, so $k$ divides the difference. The same
argument works with $\lambda(q^f) \mid \lambda(k)$ (Mathlib's `carmichael_dvd`), where
$\lambda(2^f) = 2^{f-1}$ for $f \le 2$, $\lambda(2^f) = 2^{f-2}$ for $f \ge 3$, and
$\lambda(q^f) = \varphi(q^f)$ for odd $q$. For the Gauss congruences take $k = p^k$: the index
$n p^{k-1} + i$ is at least $p^{k-1} \ge k$, and $n p^k - n p^{k-1} = n\,\varphi(p^k)$.

*The value $a(55) \bmod 81$.* The identity $\cos 2x \cdot g = \sin x$ gives the recurrence
$\sum_{k=0}^{n} \binom{2n+1}{2k} (-4)^k a(n-k) = (-1)^n$. The function `listA` evaluates it with
exact integers; `listA_getD` proves that it returns $A$, and `decide +kernel` evaluates
$a(55) \bmod 81 = 65$ and the first terms $1, 11, 361, 24611$.

*Conjecture 1) is false.* By Theorem 2 at $p^e = 3^4$, the sequence has period $54$ modulo $81$
from $n = 2$. A pure period $T$ modulo a multiple of $81$ would give
$a(1) \equiv a(1 + 54T) = a(55 + 54(T - 1)) \equiv a(55) \pmod{81}$, a contradiction.

*The power congruences (conjectures 3 and 4).* Work in $\mathbb{Z}_2$ with
$b(n) = a(n) / 11^n$ and Newton coefficients $\Delta^k b(0)$.
- $2G = \Psi(2x)\,e^x$ with $\Psi = (e^x - 1)\,e^{-x} \operatorname{sech} x$ integral. So
  $2 G_M = L((1 + 2y)^M)$ for the $\mathbb{Z}$-linear map $L(y^j) = \Psi_j$ on
  $\mathbb{Z}[y]$. As $(1 + 2y)(-(1 + 2y)^2 - 11)^k = (-4)^k (1 + 2y)(y^2 + y + 3)^k$, the
  integers $f_k = \sum_i \binom{k}{i} (-11)^{k-i} a(i) = 11^k \Delta^k b(0)$ satisfy
  $2^{2k} \mid 2 f_k$. With $f_2 = 240$ this gives $2^{k+2} \mid \Delta^k b(0)$ for $k \ge 2$;
  also $\Delta b(0) = 0$.
- Let $E = b - 1$. The Leibniz rule $\Delta^l(fg)(0) = \sum_a \binom{l}{a} \Delta^a f(0)\,
  \Delta^{l-a} g(a)$ and Newton's formula give $2^{l + 2r} \mid \Delta^l(E^r)(0)$. Since
  $2^{N+2} \mid \binom{2^N}{r} 4^r$ for $r \ge 1$, the binomial expansion of
  $B = b^{2^N} = (1 + E)^{2^N}$ gives $2^{N + l + 2} \mid \Delta^l B(0)$ for $l \ge 1$.
- Newton's formula for $B$ gives $B(xy) - y B(x) = (1 - y) + \sum_{l \ge 1}
  \left(\binom{xy}{l} - y \binom{x}{l}\right) \Delta^l B(0)$. A telescoping product shows that
  $x^2 y (y - 1)$ divides $l!\left(\binom{xy}{l} - y \binom{x}{l}\right)$, and
  $v_2(l!) \le l - 1$. So if $2^K \mid x^2 y (y - 1)$ and $N = K$, every term is divisible by
  $2^{2K+3}$. Also $B(x)^y \equiv 1 + y (B(x) - 1) \pmod{2^{2K+4}}$, as $2^{K+2} \mid B(x) - 1$.
- Hence $2^{2K+3} \mid b(xy)^{2^K} - (b(x)^y)^{2^K}$. Here $b \equiv 1 \pmod 4$ by Theorem 1
  at $e = 2$, so $\beta + \gamma = 2 \cdot$ unit for $\beta, \gamma \equiv 1 \pmod 4$, and each
  square root step loses exactly one factor $2$. So $2^{K+3} \mid b(xy) - b(x)^y$, that is,
  $a(xy) \equiv a(x)^y \pmod{2^{K+3}}$.
- Conjecture 3) is $(x, y) = (m, n)$ with $K = 2 v_2(m) + 1$. Conjecture 4) is
  $(x, y) = (n, 2m)$ and $(n, 2m + 1)$ with $K = v_2(m) + 1$.

The informal proof uses the 2-adic logarithm and a finite computation of its Newton
coefficients for $l \le 7$. The Lean proof replaces the logarithm by the power map
$z \mapsto z^{2^N}$, and the bound $2^{k+2} \mid \Delta^k b(0)$, which uses $f_2 = 240$, makes
the finite computation unnecessary.

*Dold's criterion.* For a Gauss sequence $b$, Möbius inversion writes $b(n) = \sum_{d \mid n}
d\,c(d)$ with integers $c(d)$, and $\exp\left(\sum b(n) x^n / n\right)$ agrees up to each degree
with a finite product $\prod_d (1 - x^d)^{-c(d)}$.

The Hurwitz-series library, the twist, the 2-adic Vandermonde step (`mahler`) and the class $K$
are adapted from this repository's OeisA012780 package. Dold's criterion is copied from the
OeisA181316 package, which took it from the A158110 package. The power congruences and the
sharper 2-adic step are written for this package.

*References:*
- N. J. A. Sloane, [A000464](https://oeis.org/A000464); the conjectures are Peter Bala's
  comments of December 22, 2021.
- J. W. L. Glaisher, On the coefficients in the expansions of $\cos x / \cos 2x$ and
  $\sin x / \cos 2x$, Quart. J. Pure Appl. Math. 45 (1914), 187–222.
- R. Blanco Gómez, Zenodo 23404924 and 23407292 (2026), Theorem 1 (the odd-prime congruences).
- A. Dold, *Fixed point indices of iterated maps*, Invent. Math. 74 (1983), 419–435.
-/

@[expose] public section

namespace OeisA000464

open PowerSeries

/-- OEIS A000464: $a(n) = (2n+1)!\,[x^{2n+1}]\, \sin x / \cos 2x$. -/
noncomputable def a (n : ℕ) : ℚ :=
  (2 * n + 1).factorial * coeff (2 * n + 1) (sin ℚ * (rescale (2 : ℚ) (cos ℚ))⁻¹)

end OeisA000464

namespace OeisA000464

/-! ### Hurwitz series

The Hurwitz-series library (ring structure, derivative, constants, causal fixed points,
exponentials, inverses, coefficient maps, divided powers and rescaling) is copied from this
repository's OeisA012780 package, which adapted it from the OeisA317345, A396804 and
OeisA371710 packages. -/


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

/-- The series of $\operatorname{sech} x$. -/
def sechH : Hur R := hinv (coshH R)

/-- The series $g = \sin x \cdot \sec 2x$. -/
def gH : Hur R := sinH R * scale 2 (secH R)

/-- The series $G = \sinh x \cdot \operatorname{sech} 2x$. -/
def GH : Hur R := sinhH R * scale 2 (sechH R)

variable {R}

lemma C_two : C (2 : R) = 2 := map_ofNat CHom 2

lemma cosH_coeff_zero : (cosH R).coeff 0 = 1 := by simp [cosH]

lemma coshH_coeff_zero : (coshH R).coeff 0 = 1 := by simp [coshH]

lemma cosH_mul_secH : cosH R * secH R = 1 := mul_hinv cosH_coeff_zero

lemma coshH_mul_sechH : coshH R * sechH R = 1 := mul_hinv coshH_coeff_zero

lemma scale_one (c : R) : scale c (1 : Hur R) = 1 := map_one (scaleHom c)

/-- $\cos 2x \cdot \sec 2x = 1$. -/
lemma cos2_mul_sec2 : scale 2 (cosH R) * scale 2 (secH R) = 1 := by
  rw [← scale_mul, cosH_mul_secH, scale_one]

/-- $\cosh 2x \cdot \operatorname{sech} 2x = 1$. -/
lemma cosh2_mul_sech2 : scale 2 (coshH R) * scale 2 (sechH R) = 1 := by
  rw [← scale_mul, coshH_mul_sechH, scale_one]

/-- $\cos 2x \cdot g = \sin x$. -/
lemma cos2_mul_gH : scale 2 (cosH R) * gH R = sinH R := by
  rw [gH, mul_left_comm, cos2_mul_sec2, mul_one]

lemma two_coshH : 2 * coshH R = ex 1 + ex (-1) := by
  ext n
  rw [← C_two, C_mul_coeff, coeff_add, coeff_ex, coeff_ex, one_pow]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h2 : (2 * k) % 2 = 0 := by omega
    simp [coshH, h2, pow_mul]
    norm_num
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [coshH, h2, pow_succ, pow_mul]

lemma two_sinhH : 2 * sinhH R = ex 1 - ex (-1) := by
  ext n
  rw [← C_two, C_mul_coeff, coeff_sub, coeff_ex, coeff_ex, one_pow]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h2 : (2 * k) % 2 = 0 := by omega
    simp [sinhH, h2, pow_mul]
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [sinhH, h2, pow_succ, pow_mul]
    norm_num

end Trig

section MapTrig
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

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


lemma map_gH : map φ (gH R) = gH S := by
  rw [gH, map_mul', map_sinH, map_scale, map_ofNat, map_secH, gH]

lemma map_GH : map φ (GH R) = GH S := by
  rw [GH, map_mul', map_sinhH, map_scale, map_ofNat, map_sechH, GH]

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


lemma scale_I_gH : scale I (gH ℂ) = C I * GH ℂ := by
  have h : scale I (scale 2 (secH ℂ)) = scale 2 (sechH ℂ) := by
    rw [scale_scale, mul_comm, ← scale_scale, scale_I_secH]
  rw [gH, scale_mul, scale_I_sinH, h, GH, mul_assoc]

/-- The odd coefficients of $g$ and of $G(x) = -i\,g(ix)$ differ by the sign $(-1)^n$. -/
theorem gH_coeff_odd (n : ℕ) :
    (gH ℤ).coeff (2 * n + 1) = (-1) ^ n * (GH ℤ).coeff (2 * n + 1) := by
  have h := congrArg (fun F => Hur.coeff F (2 * n + 1)) scale_I_gH
  simp only [coeff_scale, C_mul_coeff, pow_succ, I_pow_two_mul] at h
  rw [← map_gH (Int.castRingHom ℂ), ← map_GH (Int.castRingHom ℂ), coeff_map, coeff_map] at h
  apply Int.cast_injective (α := ℂ)
  push_cast
  simp only [eq_intCast] at h
  have h1 : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h2 : (-1 : ℂ) ^ n * ((gH ℤ).coeff (2 * n + 1) : ℂ) = (GH ℤ).coeff (2 * n + 1) := by
    apply mul_left_cancel₀ I_ne_zero
    linear_combination h
  linear_combination (-1 : ℂ) ^ n * h2 - ((gH ℤ).coeff (2 * n + 1) : ℂ) * h1

end Twist

end Hur

section Bridge
open PowerSeries Hur

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


lemma jet_rescale (c : ℚ) (F : ℚ⟦X⟧) : jet (rescale c F) = scale c (jet F) := by
  ext n
  rw [jet_coeff, coeff_rescale, coeff_scale, jet_coeff]
  ring

lemma jet_inv_cos2 : jet (rescale (2 : ℚ) (cos ℚ))⁻¹ = scale 2 (secH ℚ) := by
  have h0 : constantCoeff (rescale (2 : ℚ) (cos ℚ)) ≠ 0 := by
    rw [constantCoeff_eq_jet, jet_rescale, jet_cos, coeff_scale, cosH_coeff_zero]
    norm_num
  refine inv_unique' (u := scale 2 (cosH ℚ)) ?_ cos2_mul_sec2
  rw [← jet_cos, ← jet_rescale, ← map_mul, PowerSeries.mul_inv_cancel _ h0, map_one]

/-- The Hurwitz series of $\sin x / \cos 2x$ is $g$. -/
lemma jet_eq_gH : jet (sin ℚ * (rescale (2 : ℚ) (cos ℚ))⁻¹) = gH ℚ := by
  rw [map_mul, jet_sin, jet_inv_cos2, gH]

/-- The integer sequence $A(n) = g_{2n+1}$, the odd Hurwitz coefficients of
$g = \sin x \cdot \sec 2x$. -/
def A (n : ℕ) : ℤ := (gH ℤ).coeff (2 * n + 1)

/-- $a(n) = A(n)$: the OEIS terms are the integers $g_{2n+1}$. -/
theorem a_eq (n : ℕ) : a n = A n := by
  have h := congrArg (fun F => Hur.coeff F (2 * n + 1)) jet_eq_gH
  simp only [jet_coeff] at h
  rw [a, h, A, ← map_gH (Int.castRingHom ℚ), Hur.coeff_map]
  rfl

end Bridge

section TwoAdic
open Hur

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

/-- $(c\,e^x)_N = \sum_{l \le K} \binom{N}{l} c_l$ for $N \le K$. -/
lemma coeff_mul_ex_one (c : Hur ℤ) {N K : ℕ} (hNK : N ≤ K) :
    (c * ex 1).coeff N = ∑ l ∈ Finset.range (K + 1), (N.choose l : ℤ) * c.coeff l := by
  rw [coeff_mul_sum]
  simp only [coeff_ex, one_pow, mul_one]
  apply Finset.sum_subset
  · intro l hl
    simp only [Finset.mem_range] at hl ⊢
    omega
  · intro l _ hl
    simp only [Finset.mem_range, not_lt] at hl
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

/-- If $2^{\lfloor l/2 \rfloor} \mid c_l$ for every $l$, then $F = c \cdot e^x$ satisfies
$2^e \mid F_{M + 2^e} - F_M$. -/
lemma mahler (c : Hur ℤ) (hc : ∀ l, (2 : ℤ) ^ (l / 2) ∣ c.coeff l) (M e : ℕ) :
    (2 : ℤ) ^ e ∣ (c * ex 1).coeff (M + 2 ^ e) - (c * ex 1).coeff M := by
  rw [coeff_mul_ex_one c le_rfl, coeff_mul_ex_one c (Nat.le_add_right M (2 ^ e)),
    ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun l _ => ?_
  rw [← sub_mul]
  apply two_pow_dvd_choose_shift
  intro v hv
  exact (pow_dvd_pow 2 (by have := two_mul_le_two_pow v; omega)).trans (hc l)


/-- The series $(e^{2x} - 1)/2$, with coefficients $2^{l-1}$ for $l \ge 1$. -/
def hY : Hur ℤ := ⟨fun l => if l = 0 then 0 else 2 ^ (l - 1)⟩

lemma C_two_mul_hY : C 2 * hY = ex 2 - 1 := by
  ext l
  rw [C_mul_coeff, coeff_sub, coeff_ex, coeff_one]
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp [hY]
  · simp only [hY, hl.ne', ↓reduceIte, sub_zero]
    rw [← pow_succ', Nat.sub_add_cancel hl]

/-- The series $c = \frac{e^{2x} - 1}{2} \cdot \frac{2}{1 + e^{4x}}$, so that $G = c\,e^x$. -/
def cH : Hur ℤ := hY * scale 2 (ex (-1) * sechH ℤ)

lemma C_two_cancel {F F' : Hur ℤ} (h : C 2 * F = C 2 * F') : F = F' := by
  ext n
  have h' := congrArg (fun H => Hur.coeff H n) h
  simp only [C_mul_coeff] at h'
  exact mul_left_cancel₀ two_ne_zero h'

/-- $G = c\,e^x$. -/
lemma GH_eq : GH ℤ = cH * ex 1 := by
  apply C_two_cancel
  have h1 : scale 2 (ex (-1 : ℤ) * sechH ℤ) = ex (-2) * scale 2 (sechH ℤ) := by
    rw [scale_mul, scale_ex]
    norm_num
  have h2 : ex (2 : ℤ) * ex (-2) = 1 := ex_mul_ex_neg 2
  have h3 : ex (-2 : ℤ) * ex 1 = ex (-1) := by rw [← ex_add]; norm_num
  have h4 := two_sinhH (R := ℤ)
  have hY2 : 2 * hY = ex 2 - 1 := by rw [← C_two, C_two_mul_hY]
  rw [GH, cH, h1, C_two]
  linear_combination (scale 2 (sechH ℤ)) * h4 - (ex (-2) * ex 1 * scale 2 (sechH ℤ)) * hY2 -
    (ex 1 * scale 2 (sechH ℤ)) * h2 + (scale 2 (sechH ℤ)) * h3

/-- $2^{\lfloor l/2 \rfloor}$ divides $c_l$; in fact $2^{l-1}$ does for $l \ge 1$. -/
lemma two_pow_dvd_cH (l : ℕ) : (2 : ℤ) ^ (l / 2) ∣ cH.coeff l := by
  rw [cH, coeff_mul_sum]
  refine Finset.dvd_sum fun i hi => ?_
  have hil : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [hY]
  · have h1 : hY.coeff i = 2 ^ (i - 1) := by simp [hY, hi0.ne']
    rw [h1, coeff_scale]
    have h2 : (2 : ℤ) ^ (l / 2) ∣ 2 ^ (i - 1) * 2 ^ (l - i) := by
      rw [← pow_add]
      exact pow_dvd_pow 2 (by omega)
    have h3 : (l.choose i : ℤ) * (2 ^ (i - 1) * (2 ^ (l - i) *
        (ex (-1) * sechH ℤ).coeff (l - i))) =
        (2 ^ (i - 1) * 2 ^ (l - i)) * ((l.choose i : ℤ) * (ex (-1) * sechH ℤ).coeff (l - i)) := by
      ring
    rw [h3]
    exact Dvd.dvd.mul_right h2 _

/-- $2^e \mid G_{M + 2^e} - G_M$ for every $M$ and $e$. -/
theorem GH_two_adic (M e : ℕ) :
    (2 : ℤ) ^ e ∣ (GH ℤ).coeff (M + 2 ^ e) - (GH ℤ).coeff M := by
  rw [GH_eq]
  exact mahler _ two_pow_dvd_cH M e

/-- Theorem 1: $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for $e \ge 1$ and every $n$. -/
theorem A_two_adic (e n : ℕ) (he : 1 ≤ e) : A (n + 2 ^ (e - 1)) ≡ A n [ZMOD 2 ^ e] := by
  rw [Int.modEq_iff_dvd]
  unfold A
  rw [gH_coeff_odd, gH_coeff_odd]
  have hT : 2 * (n + 2 ^ (e - 1)) + 1 = (2 * n + 1) + 2 ^ e := by
    rw [mul_add, ← pow_succ', Nat.sub_add_cancel he]
    ring
  rw [hT]
  have hG := GH_two_adic (2 * n + 1) e
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
  have h3 : (-1 : ℤ) ^ n * (GH ℤ).coeff (2 * n + 1) -
      (-1) ^ n * (-1) ^ 2 ^ (e - 1) * (GH ℤ).coeff (2 * n + 1 + 2 ^ e) =
      -((-1) ^ n * ((-1) ^ 2 ^ (e - 1) * ((GH ℤ).coeff (2 * n + 1 + 2 ^ e) -
        (GH ℤ).coeff (2 * n + 1)) + ((-1) ^ 2 ^ (e - 1) - 1) * (GH ℤ).coeff (2 * n + 1))) := by
    ring
  rw [h3, dvd_neg]
  exact Dvd.dvd.mul_left (dvd_add (Dvd.dvd.mul_left hG _) (Dvd.dvd.mul_right hs _)) _

/-! #### The sharper 2-adic congruence -/

/-- $2^{l-1}$ divides $c_l$. -/
lemma two_pow_pred_dvd_cH (l : ℕ) : (2 : ℤ) ^ (l - 1) ∣ cH.coeff l := by
  rw [cH, coeff_mul_sum]
  refine Finset.dvd_sum fun i hi => ?_
  have hil : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [hY]
  · have h1 : hY.coeff i = 2 ^ (i - 1) := by simp [hY, hi0.ne']
    rw [h1, coeff_scale]
    have h2 : (2 : ℤ) ^ (l - 1) ∣ 2 ^ (i - 1) * 2 ^ (l - i) := by
      rw [← pow_add]
      exact pow_dvd_pow 2 (by omega)
    have h3 : (l.choose i : ℤ) * (2 ^ (i - 1) * (2 ^ (l - i) *
        (ex (-1) * sechH ℤ).coeff (l - i))) =
        (2 ^ (i - 1) * 2 ^ (l - i)) * ((l.choose i : ℤ) * (ex (-1) * sechH ℤ).coeff (l - i)) := by
      ring
    rw [h3]
    exact Dvd.dvd.mul_right h2 _

lemma sechH_coeff_zero : (sechH ℤ).coeff 0 = 1 := hinv_coeff_zero coshH_coeff_zero

lemma sechH_coeff_one : (sechH ℤ).coeff 1 = 0 := by
  have h := congrArg (fun F => Hur.coeff F 1) (coshH_mul_sechH (R := ℤ))
  simp only [coeff_mul_sum, Finset.sum_range_succ, Finset.sum_range_zero, coeff_one] at h
  simpa [coshH, sechH_coeff_zero] using h

lemma cH_coeff_zero : cH.coeff 0 = 0 := by simp [cH, hY]

lemma cH_coeff_one : cH.coeff 1 = 1 := by
  simp [cH, hY, coeff_mul_sum, Finset.sum_range_succ, coeff_scale, coeff_ex, sechH_coeff_zero]

lemma cH_coeff_two : cH.coeff 2 = -2 := by
  simp [cH, hY, coeff_mul_sum, Finset.sum_range_succ, coeff_scale, coeff_ex, sechH_coeff_zero,
    sechH_coeff_one]

/-- $2 \binom{n}{2} = n (n - 1)$. -/
lemma two_mul_choose_two (n : ℕ) : 2 * (n.choose 2 : ℤ) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination ih

/-- If $2^{v+1} \mid c$ whenever $2^v \le l$, then
$2^{e+1} \mid (\binom{N+2^e}{l} - \binom{N}{l})\,c$. -/
lemma two_pow_succ_dvd_choose_shift (N e l : ℕ) (c : ℤ)
    (hc : ∀ v, 2 ^ v ≤ l → (2 : ℤ) ^ (v + 1) ∣ c) :
    (2 : ℤ) ^ (e + 1) ∣ (((N + 2 ^ e).choose l : ℤ) - (N.choose l : ℤ)) * c := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  obtain ⟨c', rfl⟩ := hc 0 (by rw [pow_zero]; omega)
  have h := two_pow_dvd_choose_shift N e l c' fun v hv => by
    have h' := hc v hv
    rw [pow_succ, zero_add, pow_one, mul_comm] at h'
    exact (mul_dvd_mul_iff_left two_ne_zero).1 h'
  rw [zero_add, pow_one, mul_left_comm, pow_succ, mul_comm _ (2 : ℤ)]
  exact mul_dvd_mul_left 2 h

/-- $2^{k+1} \mid G_{M + 2^k} - G_M$ for every $M$ and every $k \ge 1$. -/
theorem GH_two_adic_sharp (M k : ℕ) (hk : 1 ≤ k) :
    (2 : ℤ) ^ (k + 1) ∣ (GH ℤ).coeff (M + 2 ^ k) - (GH ℤ).coeff M := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [GH_eq, coeff_mul_ex_one cH le_rfl, coeff_mul_ex_one cH (Nat.le_add_right M (2 ^ k)),
    ← Finset.sum_sub_distrib, ← Finset.sum_range_add_sum_Ico _ (show 3 ≤ M + 2 ^ k + 1 by omega)]
  refine dvd_add ?_ (Finset.dvd_sum fun l hl => ?_)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
      Nat.choose_one_right, cH_coeff_zero, cH_coeff_one, cH_coeff_two]
    have h1 := two_mul_choose_two (M + 2 ^ (j + 1))
    have h2 := two_mul_choose_two M
    push_cast at h1 h2 ⊢
    exact ⟨1 - M - 2 ^ j, by linear_combination (-1 : ℤ) * h1 + h2⟩
  · have hl3 : 3 ≤ l := (Finset.mem_Ico.1 hl).1
    rw [← sub_mul]
    apply two_pow_succ_dvd_choose_shift
    intro v hv
    have := two_mul_le_two_pow v
    exact (pow_dvd_pow 2 (by omega)).trans (two_pow_pred_dvd_cH l)

/-- $a(n + 2^{e-2}) \equiv a(n) \pmod{2^e}$ for $e \ge 3$ and every $n$. -/
theorem A_two_adic_sharp (e n : ℕ) (he : 3 ≤ e) : A (n + 2 ^ (e - 2)) ≡ A n [ZMOD 2 ^ e] := by
  have hT : 2 * (n + 2 ^ (e - 2)) + 1 = (2 * n + 1) + 2 ^ (e - 1) := by
    rw [mul_add, ← pow_succ', show e - 2 + 1 = e - 1 by omega]
    ring
  have hG := GH_two_adic_sharp (2 * n + 1) (e - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hG
  have hs : (-1 : ℤ) ^ (2 ^ (e - 2)) = 1 := by
    rw [show e - 2 = (e - 3) + 1 by omega, pow_succ, pow_mul', neg_one_sq, one_pow]
  unfold A
  rw [gH_coeff_odd, gH_coeff_odd, hT, pow_add, hs, mul_one]
  exact (Int.modEq_iff_dvd.2 hG).symm.mul_left _

end TwoAdic

section HurSections
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


lemma inK_sinhH : InK (sinhH R) := by
  have h : sinhH R = C t * ex 1 + C (-t) * ex (-1) := by
    have h2 := two_sinhH (R := R)
    have h1 : C t * 2 = (1 : Hur R) := by rw [← C_two, ← C_mul, mul_comm, ht, C_one]
    rw [C_neg]
    linear_combination (C t) * h2 - (sinhH R) * h1
  rw [h]
  exact ((inK_C t).mul inK_ex_one).add ((inK_C (-t)).mul inK_ex_neg_one)

lemma inK_sech2 : InK (scale 2 (sechH R)) :=
  InK.inv (inK_cosh2 t ht) (by simp [coeff_scale, coshH_coeff_zero])
    (by rw [mul_comm]; exact cosh2_mul_sech2)

lemma inK_GH : InK (GH R) := (inK_sinhH t ht).mul (inK_sech2 t ht)

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


/-- $2 \cdot \frac{p-1}{2} p^{e-1} = \varphi(p^e)$ for an odd prime $p$ and $e \ge 1$. -/
lemma two_mul_half_totient {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    2 * ((p - 1) / 2 * p ^ (e - 1)) = (p ^ e).totient := by
  rw [Nat.totient_prime_pow hp (by omega)]
  obtain ⟨k, rfl⟩ := hp.odd_of_ne_two hp2
  rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left k two_pos]
  ring

/-- $(-1)^{hq} = (-1)^h$ for odd $q$. -/
lemma neg_one_pow_mul_odd (h q : ℕ) (hq : Odd q) : (-1 : ℤ) ^ (h * q) = (-1) ^ h := by
  rw [pow_mul', hq.neg_one_pow]

/-- Theorem 2: $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n) \pmod{p^e}$ for odd
primes $p$, $e \ge 1$ and $2n + 1 \ge e$. -/
theorem A_antiperiod {p e n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hn : e ≤ 2 * n + 1) :
    A (n + (p - 1) / 2 * p ^ (e - 1)) ≡ (-1) ^ ((p - 1) / 2) * A n [ZMOD p ^ e] := by
  have hL := two_mul_half_totient hp hp2 he
  unfold A
  rw [gH_coeff_odd, gH_coeff_odd, show 2 * (n + (p - 1) / 2 * p ^ (e - 1)) + 1 =
    (2 * n + 1) + (p ^ e).totient by rw [← hL]; ring]
  have hG := GH_odd_prime (e := e) hp hp2 (M := 2 * n + 1) hn
  have hs : (-1 : ℤ) ^ (n + (p - 1) / 2 * p ^ (e - 1)) = (-1) ^ ((p - 1) / 2) * (-1) ^ n := by
    rw [pow_add, neg_one_pow_mul_odd _ _ ((hp.odd_of_ne_two hp2).pow), mul_comm]
  rw [hs]
  calc (-1) ^ ((p - 1) / 2) * (-1) ^ n * (GH ℤ).coeff (2 * n + 1 + (p ^ e).totient)
      ≡ (-1) ^ ((p - 1) / 2) * (-1) ^ n * (GH ℤ).coeff (2 * n + 1) [ZMOD p ^ e] :=
        hG.mul_left _
    _ = (-1) ^ ((p - 1) / 2) * ((-1) ^ n * (GH ℤ).coeff (2 * n + 1)) := by ring

/-- $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ for odd primes $p$, $e \ge 1$ and
$2n + 1 \ge e$. -/
theorem A_odd_period {p e n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hn : e ≤ 2 * n + 1) : A (n + (p ^ e).totient) ≡ A n [ZMOD p ^ e] := by
  have hL := two_mul_half_totient hp hp2 he
  set q := (p - 1) / 2 * p ^ (e - 1)
  have h1 := A_antiperiod hp hp2 he (n := n + q) (by omega)
  have h2 := A_antiperiod hp hp2 he hn
  have hsq : ((-1 : ℤ) ^ ((p - 1) / 2)) * (-1) ^ ((p - 1) / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [← hL, two_mul, ← add_assoc]
  calc A (n + q + q) ≡ (-1) ^ ((p - 1) / 2) * A (n + q) [ZMOD p ^ e] := h1
    _ ≡ (-1) ^ ((p - 1) / 2) * ((-1) ^ ((p - 1) / 2) * A n) [ZMOD p ^ e] := h2.mul_left _
    _ = A n := by rw [← mul_assoc, hsq, one_mul]

end OddPrime

/-! ### Every modulus -/

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

/-- The exponent of a prime in `k` is less than `k`. -/
lemma factorization_lt {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) : k.factorization p < k := by
  calc k.factorization p < p ^ k.factorization p := Nat.lt_pow_self hp.one_lt
    _ ≤ k := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd k p)


/-- The prime-power step of Corollary 3: the congruence modulo $q^f$, $q^f \| k$. -/
lemma A_prime_pow_part {k q n : ℕ} (hq : q ∈ k.primeFactors)
    (hn : q ≠ 2 → k.factorization q ≤ 2 * n + 1) :
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
  · exact period_mul (N0 := n)
      (fun m hm => A_odd_period hqp h2 hf (by have := hn h2; omega)) c n le_rfl

/-- Corollary 3: $a(n + \varphi(k)) \equiv a(n) \pmod k$ whenever $2n + 1$ is at least the
exponent of every odd prime in `k`. -/
theorem A_corollary3 {k : ℕ} (hk : 1 ≤ k) (n : ℕ)
    (hn : ∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n + 1) :
    A (n + k.totient) ≡ A n [ZMOD k] := by
  rw [Int.modEq_iff_dvd]
  apply dvd_of_prime_pow_dvd (by omega)
  intro q hq
  exact Int.modEq_iff_dvd.1
    (A_prime_pow_part hq fun h2 => hn q (Nat.prime_of_mem_primeFactors hq) h2)


/-- The exponent of a prime $q$ in $p^k$ is at most $k$. -/
lemma factorization_prime_pow_le {p q : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).factorization q ≤ k := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, hp.factorization, Finsupp.single_apply]
  split_ifs <;> simp

/-- Corollary 5 (conjecture 2): $a(n p^k + i) \equiv a(n p^{k-1} + i) \pmod{p^k}$. -/
theorem A_gauss (i : ℕ) {p n k : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    A (n * p ^ k + i) ≡ A (n * p ^ (k - 1) + i) [ZMOD p ^ k] := by
  set u := n * p ^ (k - 1) + i with hu
  have hku : k ≤ u := by
    have h1 : k - 1 < p ^ (k - 1) := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ (k - 1) ≤ n * p ^ (k - 1) := Nat.le_mul_of_pos_left _ hn
    omega
  have hidx : n * p ^ k + i = u + n * (p ^ k).totient := by
    rw [Nat.totient_prime_pow hp hk, hu]
    have h1 : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [h1]
    have hp1 : 1 ≤ p := hp.one_lt.le
    zify [hp1]
    ring
  rw [hidx]
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  have h := period_mul (N0 := u) (x := A) (m := ((p ^ k : ℕ) : ℤ))
    (fun m hm => A_corollary3 hpk m fun q _ _ => by
      have := factorization_prime_pow_le (q := q) hp k
      omega) n u le_rfl
  push_cast at h
  exact h

/-- Bala's pure form of conjecture 1) when every odd prime exponent of $k$ is at most $3$. -/
theorem A_pure {k : ℕ} (hk : 1 ≤ k) (hE : ∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 3)
    {n : ℕ} (hn : 1 ≤ n) : A (n + k.totient) ≡ A n [ZMOD k] :=
  A_corollary3 hk n fun p hp hp2 => by have := hE p hp hp2; omega

/-- $a(n + \lambda(2^f)) \equiv a(n) \pmod{2^f}$ for $f \ge 1$ and every $n$. -/
lemma A_two_pow_carmichael {f : ℕ} (hf : 1 ≤ f) (n : ℕ) :
    A (n + ArithmeticFunction.carmichael (2 ^ f)) ≡ A n [ZMOD 2 ^ f] := by
  rcases Nat.lt_or_ge f 3 with h | h
  · rw [ArithmeticFunction.carmichael_two_pow_of_le_two (by omega)]
    exact A_two_adic f n hf
  · rw [ArithmeticFunction.carmichael_two_pow_of_ne_two (by omega)]
    exact A_two_adic_sharp f n h

/-- The prime-power step with $\lambda$: the congruence modulo $q^f$, $q^f \| k$. -/
lemma A_prime_pow_part_carmichael {k q n : ℕ} (hq : q ∈ k.primeFactors)
    (hn : q ≠ 2 → k.factorization q ≤ 2 * n + 1) :
    A (n + ArithmeticFunction.carmichael k) ≡ A n [ZMOD ((q ^ k.factorization q : ℕ) : ℤ)] := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  set f := k.factorization q
  have hf : 1 ≤ f := (hqp.dvd_iff_one_le_factorization (Nat.mem_primeFactors.1 hq).2.2).1
    (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨c, hc⟩ := ArithmeticFunction.carmichael_dvd (Nat.ordProj_dvd k q)
  rw [hc, mul_comm]
  push_cast
  by_cases h2 : q = 2
  · subst h2
    exact period_mul (N0 := 0) (fun m _ => A_two_pow_carmichael hf m) c n (Nat.zero_le n)
  · rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two f hqp h2]
    exact period_mul (N0 := n)
      (fun m hm => A_odd_period hqp h2 hf (by have := hn h2; omega)) c n le_rfl

/-- $a(n + \lambda(k)) \equiv a(n) \pmod k$ whenever $2n + 1$ is at least the exponent of every
odd prime in `k`. -/
theorem A_carmichael {k : ℕ} (hk : 1 ≤ k) (n : ℕ)
    (hn : ∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n + 1) :
    A (n + ArithmeticFunction.carmichael k) ≡ A n [ZMOD k] := by
  rw [Int.modEq_iff_dvd]
  apply dvd_of_prime_pow_dvd (by omega)
  intro q hq
  exact Int.modEq_iff_dvd.1
    (A_prime_pow_part_carmichael hq fun h2 => hn q (Nat.prime_of_mem_primeFactors hq) h2)

/-! ### The recurrence and a verified evaluator -/

section Eval

/-- Split a sum over `range (2 * m)` into even and odd indices. -/
lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), f i = ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

lemma coeff_cos2_odd (k : ℕ) : (scale 2 (cosH ℤ)).coeff (2 * k + 1) = 0 := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  simp [coeff_scale, cosH, h1]

lemma coeff_cos2_even (k : ℕ) : (scale 2 (cosH ℤ)).coeff (2 * k) = (-4) ^ k := by
  have h1 : (2 * k) % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  simp only [coeff_scale, cosH, h1, h2, ↓reduceIte]
  rw [pow_mul, ← mul_pow]
  norm_num

lemma coeff_sinH_odd (n : ℕ) : (sinH ℤ).coeff (2 * n + 1) = (-1) ^ n := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp [sinH, h1, h2]

/-- The recurrence $\sum_{k \le n} \binom{2n+1}{2k} (-4)^k a(n-k) = (-1)^n$, from
$\cos 2x \cdot g = \sin x$. -/
lemma A_rec (n : ℕ) :
    A n + ∑ j ∈ Finset.range n,
      ((2 * n + 1).choose (2 * (j + 1)) : ℤ) * (-4) ^ (j + 1) * A (n - 1 - j) = (-1) ^ n := by
  have h := congrArg (fun F => Hur.coeff F (2 * n + 1)) (cos2_mul_gH (R := ℤ))
  simp only [coeff_mul_sum, coeff_sinH_odd] at h
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, sum_range_two_mul, Finset.sum_range_succ'] at h
  rw [← h, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.1 hj
    rw [coeff_cos2_odd, coeff_cos2_even, zero_mul, mul_zero, add_zero, A,
      show 2 * n + 1 - 2 * (j + 1) = 2 * (n - 1 - j) + 1 by omega]
    ring
  · rw [coeff_cos2_odd, coeff_cos2_even]
    simp [A]

/-- One step of the recurrence: from `l = [A (n-1), ..., A 0]`, the value `A n`. The binomial
coefficients are written with factorials, which the kernel evaluates quickly. -/
def stepA (n : ℕ) (l : List ℤ) : ℤ :=
  (-1) ^ n - ((List.range n).map fun j =>
    (((2 * n + 1).factorial / ((2 * (j + 1)).factorial * (2 * n + 1 - 2 * (j + 1)).factorial) :
      ℕ) : ℤ) * (-4) ^ (j + 1) * l.getD j 0).sum

/-- The list `[A (n-1), ..., A 0]`, computed by the recurrence. -/
def listA : ℕ → List ℤ
  | 0 => []
  | n + 1 => stepA n (listA n) :: listA n

lemma listA_getD (n : ℕ) : ∀ j < n, (listA n).getD j 0 = A (n - 1 - j) := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rcases j with _ | j
    · have hL : ((List.range n).map fun j =>
          (((2 * n + 1).factorial / ((2 * (j + 1)).factorial *
            (2 * n + 1 - 2 * (j + 1)).factorial) : ℕ) : ℤ) * (-4) ^ (j + 1) *
            (listA n).getD j 0).sum =
          ∑ j ∈ Finset.range n,
            ((2 * n + 1).choose (2 * (j + 1)) : ℤ) * (-4) ^ (j + 1) * A (n - 1 - j) := by
        rw [show ∀ f : ℕ → ℤ, ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j from
          fun f => rfl]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' := Finset.mem_range.1 hj
        rw [ih j hj', ← Nat.choose_eq_factorial_div_factorial (by omega)]
      show stepA n (listA n) = A (n + 1 - 1 - 0)
      rw [stepA, hL, show n + 1 - 1 - 0 = n by omega]
      linear_combination (-1 : ℤ) * A_rec n
    · show (listA n).getD j 0 = A (n + 1 - 1 - (j + 1))
      rw [ih j (by omega), show n + 1 - 1 - (j + 1) = n - 1 - j by omega]

lemma A_eq_listA (n : ℕ) : A n = (listA (n + 1)).getD 0 0 := by
  rw [listA_getD (n + 1) 0 (by omega), show n + 1 - 1 - 0 = n by omega]

lemma listA_four : listA 4 = [24611, 361, 11, 1] := by decide +kernel

lemma A_small : A 0 = 1 ∧ A 1 = 11 ∧ A 2 = 361 ∧ A 3 = 24611 := by
  have h := listA_getD 4
  rw [listA_four] at h
  exact ⟨(h 3 (by norm_num)).symm, (h 2 (by norm_num)).symm, (h 1 (by norm_num)).symm,
    (h 0 (by norm_num)).symm⟩

/-- The counterexample value, by kernel evaluation of the recurrence: $a(55) \equiv 65
\pmod{81}$. -/
lemma A_fifty_five : A 55 ≡ 65 [ZMOD 81] := by
  rw [A_eq_listA]
  show (listA 56).getD 0 0 % 81 = 65 % 81
  decide +kernel

end Eval

/-! ### Conjecture 1) is false -/

/-- Modulo $81$, the sequence has period $54 = \varphi(81)$ from $n = 2$ on. -/
lemma A_period_81 (m : ℕ) (hm : 2 ≤ m) : A (m + 54) ≡ A m [ZMOD 81] := by
  have h := A_odd_period (p := 3) (e := 4) (n := m) Nat.prime_three (by norm_num) (by norm_num)
    (by omega)
  have ht : (3 ^ 4 : ℕ).totient = 54 := by
    rw [Nat.totient_prime_pow Nat.prime_three (by norm_num)]
    norm_num
  rw [ht] at h
  norm_num at h
  exact h

/-- For every multiple $k$ of $81$, $(a(n))_{n \ge 1}$ modulo $k$ has no pure period: a pure
period $T$ would give $a(1) \equiv a(1 + 54T) \equiv a(55) \pmod{81}$. -/
theorem A_not_periodic {k T : ℕ} (hk : 81 ∣ k) (hT : 0 < T) :
    ¬ ∀ n : ℕ, 1 ≤ n → A (n + T) ≡ A n [ZMOD k] := by
  intro h
  have h81 : ∀ n : ℕ, 1 ≤ n → A (n + T) ≡ A n [ZMOD 81] := fun n hn =>
    Int.ModEq.of_dvd (by exact_mod_cast hk) (h n hn)
  have h1 : A (1 + 54 * T) ≡ A 1 [ZMOD 81] := period_mul h81 54 1 le_rfl
  have h2 : A (55 + (T - 1) * 54) ≡ A 55 [ZMOD 81] :=
    period_mul (N0 := 2) (fun m hm => A_period_81 m hm) (T - 1) 55 (by norm_num)
  rw [show 1 + 54 * T = 55 + (T - 1) * 54 by omega] at h1
  have h3 := (h2.symm.trans h1).symm.trans A_fifty_five
  rw [A_small.2.1, Int.ModEq] at h3
  norm_num at h3

section Power
open fwdDiff

/-! ### The power congruences (conjectures 3 and 4) -/

/-- The series $\Psi = (e^x - 1)\,e^{-x} \operatorname{sech} x$, so that $2G = \Psi(2x)\,e^x$. -/
def PsiH : Hur ℤ := (ex 1 - 1) * (ex (-1) * sechH ℤ)

lemma two_GH : C 2 * GH ℤ = scale 2 PsiH * ex 1 := by
  have h : scale 2 (ex (1 : ℤ) - 1) = ex 2 - 1 := by
    rw [← scaleHom_apply, map_sub, map_one, scaleHom_apply, scale_ex, mul_one]
  rw [GH_eq, ← mul_assoc, cH, ← mul_assoc, C_two_mul_hY, PsiH, scale_mul (2 : ℤ) (ex 1 - 1), h]

lemma two_GH_coeff (M : ℕ) :
    2 * (GH ℤ).coeff M =
      ∑ j ∈ Finset.range (M + 1), (M.choose j : ℤ) * (2 ^ j * PsiH.coeff j) := by
  have h := congrArg (fun F => Hur.coeff F M) two_GH
  rw [C_mul_coeff, coeff_mul_sum] at h
  simp only [coeff_ex, one_pow, mul_one, coeff_scale] at h
  exact h

/-- The linear functional $L(y^j) = \Psi_j$ on $\mathbb{Z}[y]$. -/
noncomputable def Lf : Polynomial ℤ →ₗ[ℤ] ℤ :=
  Polynomial.lsum fun j => LinearMap.mulRight ℤ (PsiH.coeff j)

lemma Lf_monomial (j : ℕ) (c : ℤ) : Lf (Polynomial.monomial j c) = c * PsiH.coeff j := by
  simp [Lf, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

/-- $L((1 + 2y)^M) = 2 G_M$. -/
lemma Lf_pow (M : ℕ) : Lf ((2 * Polynomial.X + 1) ^ M) = 2 * (GH ℤ).coeff M := by
  rw [two_GH_coeff, add_pow, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (2 * Polynomial.X : Polynomial ℤ) ^ j * 1 ^ (M - j) * (M.choose j : Polynomial ℤ) =
      Polynomial.monomial j ((M.choose j : ℤ) * 2 ^ j) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, one_pow, mul_one, mul_pow]
    simp only [map_mul, map_pow, map_natCast, Polynomial.C_ofNat]
    ring
  rw [h, Lf_monomial]
  ring

/-- $f_k = \sum_i \binom{k}{i} (-11)^{k-i} a(i)$, so $f_k / 11^k$ is the $k$-th Newton
coefficient of $a(n)/11^n$. -/
def fk (k : ℕ) : ℤ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℤ) * (-11) ^ (k - i) * A i

lemma two_fk (k : ℕ) :
    2 * fk k =
      (-4) ^ k * Lf ((2 * Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 3) ^ k) := by
  have hpoly : (2 * Polynomial.X + 1 : Polynomial ℤ) *
      (-(2 * Polynomial.X + 1) ^ 2 + (-11 : Polynomial ℤ)) ^ k =
      (((-4) ^ k : ℤ) : Polynomial ℤ) *
        ((2 * Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 3) ^ k) := by
    rw [show -(2 * Polynomial.X + 1) ^ 2 + (-11 : Polynomial ℤ) =
      -4 * (Polynomial.X ^ 2 + Polynomial.X + 3) by ring, mul_pow]
    push_cast
    ring
  have hL : ∀ (c : ℤ) (P : Polynomial ℤ), c * Lf P = Lf ((c : Polynomial ℤ) * P) := by
    intro c P
    rw [← zsmul_eq_mul, map_zsmul, smul_eq_mul]
  rw [hL, ← hpoly, add_pow, Finset.mul_sum, map_sum, fk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (2 * Polynomial.X + 1 : Polynomial ℤ) *
      ((-(2 * Polynomial.X + 1) ^ 2) ^ i * (-11) ^ (k - i) * (k.choose i : Polynomial ℤ)) =
      (((k.choose i : ℤ) * (-11) ^ (k - i) * (-1) ^ i : ℤ) : Polynomial ℤ) *
        (2 * Polynomial.X + 1) ^ (2 * i + 1) := by
    rw [neg_pow, ← pow_mul]
    push_cast
    ring
  rw [h, ← zsmul_eq_mul, map_zsmul, Lf_pow, smul_eq_mul, A, gH_coeff_odd]
  ring

lemma two_pow_dvd_two_fk (k : ℕ) : (2 : ℤ) ^ (2 * k) ∣ 2 * fk k := by
  rw [two_fk, pow_mul]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (by norm_num) k) _

lemma fk_two : fk 2 = 240 := by
  obtain ⟨h0, h1, h2, -⟩ := A_small
  simp [fk, Finset.sum_range_succ, h0, h1, h2]

/-- $2^{k+2} \mid f_k$ for $k \ge 2$. -/
lemma two_pow_dvd_fk {k : ℕ} (hk : 2 ≤ k) : (2 : ℤ) ^ (k + 2) ∣ fk k := by
  rcases Nat.lt_or_ge k 3 with h | h
  · obtain rfl : k = 2 := by omega
    rw [fk_two]
    norm_num
  · have h1 := two_pow_dvd_two_fk k
    have h2 : (2 : ℤ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2] at h1
    exact (pow_dvd_pow 2 (by omega)).trans ((mul_dvd_mul_iff_left two_ne_zero).1 h1)


/-! #### The 2-adic integers -/

lemma isUnit_of_not_two_dvd {x : ℤ_[2]} (h : ¬ (2 : ℤ_[2]) ∣ x) : IsUnit x := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one x) (not_lt.1 fun hlt => h ?_)
  have h1 := (PadicInt.norm_lt_one_iff_dvd x).1 hlt
  exact_mod_cast h1

lemma not_two_dvd_one_add (t : ℤ_[2]) : ¬ (2 : ℤ_[2]) ∣ 1 + 2 * t := by
  intro h
  have h1 : (2 : ℤ_[2]) ∣ 1 := by
    have := dvd_sub h (dvd_mul_right (2 : ℤ_[2]) t)
    rwa [add_sub_cancel_right] at this
  have h2 := PadicInt.p_nonunit (p := 2)
  rw [mem_nonunits_iff] at h2
  exact h2 (by exact_mod_cast isUnit_of_dvd_one h1)

lemma isUnit_intCast_of_odd {z : ℤ} (hz : ¬ (2 : ℤ) ∣ z) : IsUnit (z : ℤ_[2]) := by
  apply isUnit_of_not_two_dvd
  intro h
  have := (PadicInt.pow_p_dvd_int_iff (p := 2) 1 z).1 (by simpa using h)
  exact hz (by simpa using this)

lemma int_dvd_of_padic {K : ℕ} {z : ℤ} (h : (2 : ℤ_[2]) ^ K ∣ (z : ℤ_[2])) : (2 : ℤ) ^ K ∣ z := by
  have := (PadicInt.pow_p_dvd_int_iff (p := 2) K z).1 (by exact_mod_cast h)
  exact_mod_cast this

lemma sq_sub_one_dvd {β : ℤ_[2]} {s : ℕ} (hs : 1 ≤ s) (h : (2 : ℤ_[2]) ^ s ∣ β - 1) :
    (2 : ℤ_[2]) ^ (s + 1) ∣ β ^ 2 - 1 := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t + 2 ^ (s - 1) * t ^ 2, ?_⟩
  have hb : β = 1 + 2 ^ s * t := by linear_combination ht
  have h2 : (2 : ℤ_[2]) ^ s = 2 * 2 ^ (s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hb, show (2 : ℤ_[2]) ^ (s + 1) = 2 * 2 ^ s from pow_succ' 2 s, h2]
  ring

lemma pow_two_pow_sub_one_dvd {β : ℤ_[2]} {s : ℕ} (hs : 1 ≤ s) (h : (2 : ℤ_[2]) ^ s ∣ β - 1)
    (N : ℕ) : (2 : ℤ_[2]) ^ (s + N) ∣ β ^ (2 ^ N) - 1 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    rw [show s + (N + 1) = s + N + 1 by ring, pow_succ 2 N, pow_mul]
    exact sq_sub_one_dvd (by omega) ih

lemma dvd_sub_of_sq_dvd {β γ : ℤ_[2]} {s : ℕ} (hβ : (4 : ℤ_[2]) ∣ β - 1)
    (hγ : (4 : ℤ_[2]) ∣ γ - 1) (h : (2 : ℤ_[2]) ^ (s + 1) ∣ β ^ 2 - γ ^ 2) :
    (2 : ℤ_[2]) ^ s ∣ β - γ := by
  obtain ⟨t1, h1⟩ := hβ
  obtain ⟨t2, h2⟩ := hγ
  have hu := isUnit_of_not_two_dvd (not_two_dvd_one_add (t1 + t2))
  have he : β ^ 2 - γ ^ 2 = (β - γ) * 2 * (1 + 2 * (t1 + t2)) := by
    linear_combination (β - γ) * (h1 + h2)
  rw [he, hu.dvd_mul_right, pow_succ] at h
  exact (mul_dvd_mul_iff_right two_ne_zero).1 h

lemma dvd_sub_of_pow_dvd (N : ℕ) : ∀ {β γ : ℤ_[2]} (s : ℕ), (4 : ℤ_[2]) ∣ β - 1 →
    (4 : ℤ_[2]) ∣ γ - 1 → (2 : ℤ_[2]) ^ (s + N) ∣ β ^ (2 ^ N) - γ ^ (2 ^ N) →
    (2 : ℤ_[2]) ^ s ∣ β - γ := by
  induction N with
  | zero => intro β γ s _ _ h; simpa using h
  | succ N ih =>
    intro β γ s hβ hγ h
    have hβ2 : (4 : ℤ_[2]) ∣ β ^ 2 - 1 := hβ.trans ⟨β + 1, by ring⟩
    have hγ2 : (4 : ℤ_[2]) ∣ γ ^ 2 - 1 := hγ.trans ⟨γ + 1, by ring⟩
    have h' : (2 : ℤ_[2]) ^ ((s + 1) + N) ∣ (β ^ 2) ^ (2 ^ N) - (γ ^ 2) ^ (2 ^ N) := by
      rw [← pow_mul, ← pow_mul, ← pow_succ', show s + 1 + N = s + (N + 1) by ring]
      exact h
    exact dvd_sub_of_sq_dvd hβ hγ (ih (s + 1) hβ2 hγ2 h')

/-! #### $b(n) = a(n) / 11^n$ -/

lemma isUnit_eleven : IsUnit (11 : ℤ_[2]) := by
  have := isUnit_intCast_of_odd (z := 11) (by norm_num)
  simpa using this

/-- The inverse of $11$ in $\mathbb{Z}_2$. -/
noncomputable def uInv : ℤ_[2] := ↑(isUnit_eleven.unit⁻¹)

lemma eleven_mul_uInv : (11 : ℤ_[2]) * uInv = 1 := isUnit_eleven.mul_val_inv

/-- $b(n) = a(n) / 11^n$ in $\mathbb{Z}_2$. -/
noncomputable def bZ (n : ℕ) : ℤ_[2] := (A n : ℤ_[2]) * uInv ^ n

lemma A_eq_bZ (n : ℕ) : (A n : ℤ_[2]) = 11 ^ n * bZ n := by
  have h : (11 : ℤ_[2]) ^ n * uInv ^ n = 1 := by rw [← mul_pow, eleven_mul_uInv, one_pow]
  rw [bZ]
  linear_combination (-(A n : ℤ_[2])) * h

lemma A_mod_four (n : ℕ) : (4 : ℤ) ∣ A n - 11 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [A_small.1]
    · simp [A_small.2.1]
    · have h1 := Int.ModEq.dvd (A_two_adic 2 n (by norm_num))
      have h2 := ih n (by omega)
      norm_num at h1
      have h3 : A (n + 1 + 1) - 11 ^ (n + 1 + 1) =
          -(A n - A (n + 2)) + (A n - 11 ^ n) - 4 * (30 * 11 ^ n) := by ring
      rw [h3]
      exact dvd_sub (dvd_add (dvd_neg.2 h1) h2) (dvd_mul_right 4 _)

lemma four_dvd_bZ_sub_one (n : ℕ) : (4 : ℤ_[2]) ∣ bZ n - 1 := by
  have h' : (11 : ℤ_[2]) ^ n * uInv ^ n = 1 := by rw [← mul_pow, eleven_mul_uInv, one_pow]
  have h : bZ n - 1 = uInv ^ n * ((A n - 11 ^ n : ℤ) : ℤ_[2]) := by
    rw [bZ]
    push_cast
    linear_combination h'
  rw [h]
  have := map_dvd (Int.castRingHom ℤ_[2]) (A_mod_four n)
  simp only [eq_intCast] at this
  exact Dvd.dvd.mul_left (by exact_mod_cast this) _

/-- The Newton coefficients of $b$: $\Delta^k b(0) = f_k / 11^k$. -/
lemma iter_bZ (k : ℕ) : (fwdDiff 1)^[k] bZ 0 = uInv ^ k * (fk k : ℤ_[2]) := by
  rw [fwdDiff_iter_eq_sum_shift, fk]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : uInv ^ k = uInv ^ (k - i) * uInv ^ i := by rw [← pow_add, Nat.sub_add_cancel hik]
  have h2 : (11 : ℤ_[2]) ^ (k - i) * uInv ^ (k - i) = 1 := by
    rw [← mul_pow, eleven_mul_uInv, one_pow]
  rw [zsmul_eq_mul, zero_add, smul_eq_mul, mul_one, bZ, h1]
  push_cast
  rw [neg_pow (11 : ℤ_[2])]
  linear_combination (-((k.choose i : ℤ_[2]) * A i * uInv ^ i * (-1) ^ (k - i))) * h2

/-- $E(n) = b(n) - 1$. -/
noncomputable def EZ (n : ℕ) : ℤ_[2] := bZ n - 1

lemma iter_const (c : ℤ_[2]) {l : ℕ} (hl : 1 ≤ l) :
    (fwdDiff 1)^[l] (fun _ : ℕ => c) = fun _ => 0 := by
  obtain ⟨l, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Function.iterate_succ_apply, fwdDiff_const]
  exact Function.iterate_fixed (fwdDiff_const 1 (0 : ℤ_[2])) l

/-- $2^{j+2}$ divides the Newton coefficients of $E$: they vanish for $j \le 1$, and
$2^{j+2} \mid f_j$ for $j \ge 2$. -/
lemma iter_EZ (j : ℕ) : (2 : ℤ_[2]) ^ (j + 2) ∣ (fwdDiff 1)^[j] EZ 0 := by
  rcases j with _ | _ | j
  · simp [EZ, bZ, A_small.1]
  · simp [EZ, bZ, fwdDiff, A_small.1, A_small.2.1, eleven_mul_uInv]
  · have hE : EZ = bZ + fun _ => -1 := by
      funext n
      simp [EZ, sub_eq_add_neg]
    rw [hE, fwdDiff_iter_add, Pi.add_apply, iter_bZ, iter_const _ (by omega), add_zero]
    have := map_dvd (Int.castRingHom ℤ_[2]) (two_pow_dvd_fk (k := j + 1 + 1) (by omega))
    simp only [eq_intCast] at this
    exact Dvd.dvd.mul_left (by exact_mod_cast this) _

lemma iter_succ_apply (F : ℕ → ℤ_[2]) (k n : ℕ) :
    (fwdDiff 1)^[k + 1] F n = (fwdDiff 1)^[k] F (n + 1) - (fwdDiff 1)^[k] F n := by
  rw [Function.iterate_succ_apply']
  rfl

/-- The Leibniz rule $\Delta^l (fg)(n) = \sum_a \binom{l}{a} \Delta^a f(n)\,
\Delta^{l-a} g(n + a)$. -/
lemma fwdDiff_iter_mul (f g : ℕ → ℤ_[2]) (l : ℕ) : ∀ n, (fwdDiff 1)^[l] (f * g) n =
    ∑ a ∈ Finset.range (l + 1),
      (l.choose a : ℤ_[2]) * ((fwdDiff 1)^[a] f n * (fwdDiff 1)^[l - a] g (n + a)) := by
  induction l with
  | zero => intro n; simp
  | succ l ih =>
    intro n
    rw [iter_succ_apply, ih, ih, show l + 1 + 1 = l + 2 from rfl,
      Finset.sum_choose_succ_mul (fun i j => (fwdDiff 1)^[i] f n * (fwdDiff 1)^[j] g (n + i)) l,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hal : a ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    rw [show l + 1 - a = (l - a) + 1 by omega, iter_succ_apply g (l - a), iter_succ_apply f a,
      show n + 1 + a = n + a + 1 by ring, show n + (a + 1) = n + a + 1 by ring]
    ring

/-- $2^{l + 2r}$ divides the $l$-th Newton coefficient of $E^r$. -/
lemma two_pow_dvd_iter_EZ_pow (r : ℕ) :
    ∀ l, (2 : ℤ_[2]) ^ (l + 2 * r) ∣ (fwdDiff 1)^[l] (fun n => EZ n ^ r) 0 := by
  induction r with
  | zero =>
    intro l
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    · simp only [pow_zero]
      rw [iter_const 1 hl]
      simp
  | succ r ih =>
    intro l
    have hfun : (fun n => EZ n ^ (r + 1)) = (fun n => EZ n ^ r) * EZ := by
      funext n
      simp [pow_succ]
    rw [hfun, fwdDiff_iter_mul]
    refine Finset.dvd_sum fun a ha => ?_
    have hal : a ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have hN := shift_eq_sum_fwdDiff_iter 1 ((fwdDiff 1)^[l - a] EZ) a 0
    simp only [zero_add, smul_eq_mul, mul_one] at hN
    rw [zero_add, hN]
    apply Dvd.dvd.mul_left
    rw [Finset.mul_sum]
    refine Finset.dvd_sum fun c _ => ?_
    rw [← Function.iterate_add_apply, nsmul_eq_mul]
    have h1 := ih a
    have h2 := iter_EZ (c + (l - a))
    have h3 : (2 : ℤ_[2]) ^ (l + 2 * (r + 1)) ∣ 2 ^ (a + 2 * r) * 2 ^ (c + (l - a) + 2) := by
      rw [← pow_add]
      exact pow_dvd_pow 2 (by omega)
    exact h3.trans (mul_dvd_mul h1 (Dvd.dvd.mul_left h2 _))

/-- $2^{N+2} \mid \binom{2^N}{r} 4^r$ for $r \ge 1$. -/
lemma two_pow_dvd_choose_mul_four_pow (N r : ℕ) (hr : 1 ≤ r) :
    2 ^ (N + 2) ∣ (2 ^ N).choose r * 4 ^ r := by
  obtain ⟨v, o, ho, hro⟩ := Nat.exists_eq_two_pow_mul_odd (n := r) (by omega)
  have h1 : 2 ^ N ∣ (2 ^ N).choose r * r := by
    have := two_pow_dvd_mul_choose N (r - 1)
    rwa [Nat.sub_add_cancel hr] at this
  have e : (2 ^ N).choose r * r = (2 ^ N).choose r * 2 ^ v * o := by rw [mul_assoc, ← hro]
  rw [e] at h1
  have h2 : 2 ^ N ∣ (2 ^ N).choose r * 2 ^ v :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left N (Nat.coprime_two_left.2 ho)) h1
  have hv : 2 ^ v ≤ r := by rw [hro]; exact Nat.le_mul_of_pos_right _ ho.pos
  have hv1 : v < 2 ^ v := Nat.lt_pow_self (by norm_num)
  have h4 : 4 ^ r = 2 ^ v * 2 ^ (2 * r - v) := by
    rw [← pow_add, show v + (2 * r - v) = 2 * r by omega, pow_mul]
    norm_num
  rw [h4, ← mul_assoc, pow_add]
  exact Nat.mul_dvd_mul h2 (pow_dvd_pow 2 (by omega))

/-- $2^{N + l + 2}$ divides the $l$-th Newton coefficient of $b^{2^N}$ for $l \ge 1$. -/
lemma two_pow_dvd_iter_bZ_pow (N l : ℕ) (hl : 1 ≤ l) :
    (2 : ℤ_[2]) ^ (N + l + 2) ∣ (fwdDiff 1)^[l] (fun n => bZ n ^ (2 ^ N)) 0 := by
  have hfun : (fun n => bZ n ^ (2 ^ N)) =
      ∑ r ∈ Finset.range (2 ^ N + 1), ((2 ^ N).choose r) • (fun n => EZ n ^ r) := by
    funext n
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    rw [show bZ n = EZ n + 1 by simp [EZ], add_pow]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [one_pow, mul_one, nsmul_eq_mul, mul_comm]
  rw [hfun, fwdDiff_iter_finsetSum, Finset.sum_apply]
  refine Finset.dvd_sum fun r _ => ?_
  rw [fwdDiff_iter_const_smul, Pi.smul_apply, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp only [pow_zero]
    rw [iter_const 1 hl]
    simp
  · obtain ⟨t, ht⟩ := two_pow_dvd_iter_EZ_pow r l
    obtain ⟨s, hs⟩ := two_pow_dvd_choose_mul_four_pow N r hr0
    have hs' : ((2 ^ N).choose r : ℤ_[2]) * 4 ^ r = 2 ^ (N + 2) * s := by exact_mod_cast hs
    have h4 : (2 : ℤ_[2]) ^ (2 * r) = 4 ^ r := by rw [pow_mul]; norm_num
    rw [ht]
    refine ⟨s * t, ?_⟩
    rw [pow_add (2 : ℤ_[2]) l, h4]
    linear_combination (2 ^ l * t) * hs'

/-! #### The polynomial divisibility -/

lemma prod_sub_prod_dvd {ι : Type*} (s : Finset ι) (f g : ι → ℤ) (d : ℤ)
    (h : ∀ i ∈ s, d ∣ f i - g i) : d ∣ ∏ i ∈ s, f i - ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [e]
    exact dvd_add (Dvd.dvd.mul_right h1 _) (Dvd.dvd.mul_left h2 _)

lemma descFactorial_intCast (n k : ℕ) :
    (n.descFactorial k : ℤ) = ∏ i ∈ Finset.range k, ((n : ℤ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, Nat.cast_mul, ih]
    rcases le_or_gt k n with h | h
    · rw [Nat.cast_sub h]
      ring
    · have h0 : ∏ i ∈ Finset.range k, ((n : ℤ) - i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 h) (by simp)
      rw [h0]
      simp

/-- $l!\,\left(\binom{xy}{l} - y \binom{x}{l}\right)$ is divisible by $x^2 y (y - 1)$ for
$l \ge 1$. -/
lemma dvd_factorial_mul_choose_sub (x y l : ℕ) (hl : 1 ≤ l) :
    ((x : ℤ) ^ 2 * y * (y - 1)) ∣
      (l.factorial : ℤ) * (((x * y).choose l : ℤ) - y * (x.choose l : ℤ)) := by
  have e1 : (l.factorial : ℤ) * ((x * y).choose l : ℤ) = ((x * y).descFactorial l : ℤ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have e2 : (l.factorial : ℤ) * (x.choose l : ℤ) = (x.descFactorial l : ℤ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have h3 : ∀ n : ℕ, ((n.descFactorial (m + 1) : ℕ) : ℤ) =
      n * ∏ i ∈ Finset.range m, ((n : ℤ) - (i + 1)) := by
    intro n
    rw [descFactorial_intCast, Finset.prod_range_succ']
    push_cast
    ring
  have key : ((m + 1).factorial : ℤ) * (((x * y).choose (m + 1) : ℤ) - y * (x.choose (m + 1) : ℤ))
      = ((x * y : ℕ) : ℤ) * ∏ i ∈ Finset.range m, (((x * y : ℕ) : ℤ) - (i + 1)) -
        y * ((x : ℤ) * ∏ i ∈ Finset.range m, ((x : ℤ) - (i + 1))) := by
    rw [mul_sub, e1, mul_left_comm, e2, h3, h3]
  rw [key]
  obtain ⟨t, ht⟩ := prod_sub_prod_dvd (Finset.range m)
    (fun i => ((x * y : ℕ) : ℤ) - (i + 1)) (fun i => (x : ℤ) - (i + 1)) ((x : ℤ) * (y - 1))
    (fun i _ => ⟨1, by push_cast; ring⟩)
  refine ⟨t, ?_⟩
  push_cast at ht ⊢
  linear_combination ((x : ℤ) * y) * ht

/-- One term of the Newton expansion: if $2^K \mid l!\,P$ and $2^{K + l + 2} \mid \beta$
($l \ge 1$), then $2^{2K+3} \mid P \beta$, because $v_2(l!) \le l - 1$. -/
lemma two_pow_dvd_term (K l : ℕ) (P : ℤ) (β : ℤ_[2])
    (hP : (2 : ℤ) ^ K ∣ ((l + 1).factorial : ℤ) * P)
    (hβ : (2 : ℤ_[2]) ^ (K + (l + 1) + 2) ∣ β) : (2 : ℤ_[2]) ^ (K + K + 3) ∣ (P : ℤ_[2]) * β := by
  obtain ⟨w, o, ho, hwo⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.factorial_ne_zero (l + 1))
  have hw : w ≤ l := by
    have h1 : 2 ^ w ∣ (l + 1).factorial := ⟨o, hwo⟩
    have h2 : padicValNat 2 (l + 1).factorial < l + 1 :=
      padicValNat_factorial_lt_of_ne_zero 2 (Nat.succ_ne_zero l)
    have h3 : w ≤ padicValNat 2 (l + 1).factorial :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).1 h1
    omega
  have hcop : IsCoprime ((2 : ℤ) ^ K) (o : ℤ) := by
    apply IsCoprime.pow_left
    rw [Int.prime_two.coprime_iff_not_dvd]
    obtain ⟨c, rfl⟩ := ho
    intro h
    omega
  have h2P : (2 : ℤ) ^ K ∣ 2 ^ w * P := by
    rw [hwo] at hP
    push_cast at hP
    have e : (2 : ℤ) ^ w * (o : ℤ) * P = 2 ^ w * P * o := by ring
    rw [e] at hP
    exact hcop.dvd_of_dvd_mul_right hP
  obtain ⟨c, hc⟩ := h2P
  obtain ⟨t, ht⟩ := hβ
  have hc' : (2 : ℤ_[2]) ^ w * P = 2 ^ K * c := by exact_mod_cast hc
  refine ⟨c * 2 ^ (l - w) * t, ?_⟩
  have e : (2 : ℤ_[2]) ^ (K + (l + 1) + 2) = 2 ^ w * 2 ^ (K + 3) * 2 ^ (l - w) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [ht, e]
  linear_combination (2 ^ (K + 3) * 2 ^ (l - w) * t) * hc'

lemma one_add_pow_sub_dvd (z : ℤ_[2]) (y : ℕ) : z ^ 2 ∣ (1 + z) ^ y - 1 - y * z := by
  induction y with
  | zero => simp
  | succ y ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(1 + z) * c + y, ?_⟩
    push_cast
    linear_combination (1 + z) * hc

/-- The core congruence: if $2^K \mid x^2 y (y - 1)$, then
$a(xy) \equiv a(x)^y \pmod{2^{K+3}}$. -/
theorem A_pow_core (x y K : ℕ) (hK : 2 ^ K ∣ x ^ 2 * y * (y - 1)) :
    (2 : ℤ) ^ (K + 3) ∣ A (x * y) - A x ^ y := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [A_small.1]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [A_small.1]
  apply int_dvd_of_padic
  set B : ℕ → ℤ_[2] := fun m => bZ m ^ (2 ^ K) with hB
  have hNewt : ∀ n, B n = ∑ l ∈ Finset.range (n + 1),
      (n.choose l : ℤ_[2]) * (fwdDiff 1)^[l] B 0 := by
    intro n
    have h := shift_eq_sum_fwdDiff_iter 1 B n 0
    simp only [zero_add, smul_eq_mul, mul_one] at h
    rw [h]
    simp only [nsmul_eq_mul]
  have hB0 : (fwdDiff 1)^[0] B 0 = 1 := by simp [hB, bZ, A_small.1]
  have hxy : x ≤ x * y := Nat.le_mul_of_pos_right x hy
  -- the Newton expansion of `B (x y) - y B x`
  have hsum : B (x * y) - y * B x = ∑ l ∈ Finset.range (x * y),
      ((((x * y).choose (l + 1) : ℤ) - y * (x.choose (l + 1) : ℤ) : ℤ) : ℤ_[2]) *
        (fwdDiff 1)^[l + 1] B 0 + (1 - y) := by
    have hBx : B x =
        ∑ l ∈ Finset.range (x * y + 1), (x.choose l : ℤ_[2]) * (fwdDiff 1)^[l] B 0 := by
      rw [hNewt x]
      apply Finset.sum_subset
      · intro l hl
        simp only [Finset.mem_range] at hl ⊢
        omega
      · intro l _ hl
        simp only [Finset.mem_range, not_lt] at hl
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    rw [hNewt (x * y), hBx, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_range_succ',
      hB0]
    congr 1
    · refine Finset.sum_congr rfl fun l _ => ?_
      push_cast
      ring
    · simp
  have hterm : (2 : ℤ_[2]) ^ (K + K + 3) ∣ B (x * y) - y * B x - (1 - y) := by
    rw [hsum, add_sub_cancel_right]
    refine Finset.dvd_sum fun l _ => ?_
    apply two_pow_dvd_term K l
    · have h1 := dvd_factorial_mul_choose_sub x y (l + 1) (by omega)
      have h2 : (2 : ℤ) ^ K ∣ (x : ℤ) ^ 2 * y * (y - 1) := by
        have := Int.natCast_dvd_natCast.2 hK
        push_cast [Nat.cast_sub hy] at this
        exact this
      exact h2.trans h1
    · exact two_pow_dvd_iter_bZ_pow K (l + 1) (by omega)
  -- `B x ^ y` is close to `1 + y (B x - 1)`
  have hz : (2 : ℤ_[2]) ^ (2 + K) ∣ B x - 1 :=
    pow_two_pow_sub_one_dvd (s := 2) (by norm_num)
      (by rw [show (2 : ℤ_[2]) ^ 2 = 4 by norm_num]; exact four_dvd_bZ_sub_one x) K
  have hpow : (2 : ℤ_[2]) ^ (K + K + 3) ∣ B x ^ y - 1 - y * (B x - 1) := by
    have h1 := one_add_pow_sub_dvd (B x - 1) y
    rw [add_sub_cancel] at h1
    have h2 : (2 : ℤ_[2]) ^ (K + K + 3) ∣ (B x - 1) ^ 2 := by
      have := pow_dvd_pow_of_dvd hz 2
      rw [← pow_mul] at this
      exact (pow_dvd_pow 2 (by omega)).trans this
    exact h2.trans h1
  have hmain : (2 : ℤ_[2]) ^ ((K + 3) + K) ∣
      bZ (x * y) ^ (2 ^ K) - (bZ x ^ y) ^ (2 ^ K) := by
    have e : bZ (x * y) ^ (2 ^ K) - (bZ x ^ y) ^ (2 ^ K) =
        (B (x * y) - y * B x - (1 - y)) - (B x ^ y - 1 - y * (B x - 1)) := by
      simp only [hB]
      rw [← pow_mul, ← pow_mul, mul_comm y]
      ring
    rw [e, show K + 3 + K = K + K + 3 by ring]
    exact dvd_sub hterm hpow
  have hγ : (4 : ℤ_[2]) ∣ bZ x ^ y - 1 := by
    have := sub_dvd_pow_sub_pow (bZ x) 1 y
    rw [one_pow] at this
    exact (four_dvd_bZ_sub_one x).trans this
  have hroot := dvd_sub_of_pow_dvd K (K + 3) (four_dvd_bZ_sub_one (x * y)) hγ hmain
  have e : ((A (x * y) - A x ^ y : ℤ) : ℤ_[2]) = 11 ^ (x * y) * (bZ (x * y) - bZ x ^ y) := by
    push_cast
    rw [A_eq_bZ, A_eq_bZ, mul_pow, ← pow_mul]
    ring
  rw [e]
  exact Dvd.dvd.mul_left hroot _

/-- Conjecture 3): $a(mn) \equiv a(m)^n \pmod{2^{2 v_2(m) + 4}}$. -/
theorem A_conj3 {m n : ℕ} : A (m * n) ≡ A m ^ n [ZMOD 2 ^ (2 * m.factorization 2 + 4)] := by
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  have hm : 2 ^ m.factorization 2 ∣ m := Nat.ordProj_dvd m 2
  have hn : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  have hK : 2 ^ (2 * m.factorization 2 + 1) ∣ m ^ 2 * n * (n - 1) := by
    rw [pow_succ, pow_mul', mul_assoc]
    exact Nat.mul_dvd_mul (pow_dvd_pow_of_dvd hm 2) hn
  exact A_pow_core m n _ hK

/-- Conjecture 4): $a(2mn) \equiv a(n)^{2m}$ and $a((2m+1)n) \equiv a(n)^{2m+1}$ modulo
$2^{v_2(m) + 4}$. -/
theorem A_conj4 {m n : ℕ} :
    A (2 * m * n) ≡ A n ^ (2 * m) [ZMOD 2 ^ (m.factorization 2 + 4)] ∧
      A ((2 * m + 1) * n) ≡ A n ^ (2 * m + 1) [ZMOD 2 ^ (m.factorization 2 + 4)] := by
  have hm : 2 ^ (m.factorization 2 + 1) ∣ 2 * m := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 2 (Nat.ordProj_dvd m 2)
  constructor
  · apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, mul_comm (2 * m)]
    refine A_pow_core n (2 * m) _ ?_
    exact hm.trans ⟨n ^ 2 * (2 * m - 1), by ring⟩
  · apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, mul_comm (2 * m + 1)]
    refine A_pow_core n (2 * m + 1) _ ?_
    exact hm.trans ⟨n ^ 2 * (2 * m + 1), by rw [Nat.add_sub_cancel]; ring⟩

end Power


end HurSections

/-! ### Dold's criterion

This section is copied from the package `FCPalomar/OeisA181316`, which copied the logarithmic
derivatives, the finite Euler products and the integrality criterion from `FCPalomar/A158110`
(Apache-2.0, Wentao Li). -/

section Dold

open PowerSeries Finset
open scoped ArithmeticFunction.Moebius Pointwise

/-! #### Logarithmic derivatives -/

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

/-! #### Finite Euler products -/

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

/-! #### The integrality criterion -/

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

/-! #### Gauss sequences

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

end Dold

open PowerSeries

/-- The shifted sequence $n \mapsto a(n + i)$ is a Gauss sequence. -/
lemma gauss_shift (i : ℕ) : Gauss (fun n => A (n + i)) := by
  intro p k M hp hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have hpM : p ^ (k - 1) ∣ M := by
    have h1 : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk0]
    rw [h1] at hk
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos hk
  obtain ⟨n, rfl⟩ := hpM
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := A_gauss i hp hn hk0
  have e1 : p * (p ^ (k - 1) * n) = n * p ^ k := by
    rw [mul_comm n, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk0]
  show (p : ℤ) ^ k ∣ A (p * (p ^ (k - 1) * n) + i) - A (p ^ (k - 1) * n + i)
  rw [e1, mul_comm (p ^ (k - 1))]
  exact h.symm.dvd

/-! ### The statements -/

/-- The first terms agree with the OEIS data. -/
theorem a_first_terms : a 0 = 1 ∧ a 1 = 11 ∧ a 2 = 361 ∧ a 3 = 24611 := by
  obtain ⟨h0, h1, h2, h3⟩ := A_small
  simp only [a_eq, h0, h1, h2, h3]
  norm_num

/-- Bala's conjecture 1) is false as stated: it is not true that for every $k \ge 1$ the
sequence $(a(n))_{n \ge 1}$ modulo $k$ is purely periodic with a period dividing
$\varphi(k)$. -/
theorem not_conjecture1 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ¬ ∀ k : ℕ, 1 ≤ k → ∃ T : ℕ, 0 < T ∧ T ∣ k.totient ∧
        ∀ n : ℕ, 1 ≤ n → b (n + T) ≡ b n [ZMOD k] := by
  refine ⟨A, fun n => (a_eq n).symm, fun h => ?_⟩
  obtain ⟨T, hT, -, hper⟩ := h 81 (by norm_num)
  exact A_not_periodic (dvd_refl 81) hT (by exact_mod_cast hper)

/-- For every multiple $k$ of $81$, the sequence $(a(n))_{n \ge 1}$ modulo $k$ is not purely
periodic with any period $T \ge 1$. -/
theorem not_periodic_of_eighty_one_dvd :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k T : ℕ, 81 ∣ k → 0 < T → ¬ ∀ n : ℕ, 1 ≤ n → b (n + T) ≡ b n [ZMOD k] :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ hk hT => A_not_periodic hk hT⟩

/-- The counterexample: $a(1) = 11$ and $a(55) \equiv 65 \pmod{81}$. -/
theorem a_fifty_five :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ b 1 = 11 ∧ b 55 ≡ 65 [ZMOD 81] :=
  ⟨A, fun n => (a_eq n).symm, A_small.2.1, A_fifty_five⟩

/-- The prime $2$: $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for every $e \ge 1$ and every
$n \ge 0$. -/
theorem period_two_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 1 ≤ e → b (n + 2 ^ (e - 1)) ≡ b n [ZMOD 2 ^ e] :=
  ⟨A, fun n => (a_eq n).symm, fun e n he => A_two_adic e n he⟩

/-- The prime $2$, sharper: $a(n + 2^{e-2}) \equiv a(n) \pmod{2^e}$ for every $e \ge 3$ and
every $n \ge 0$. -/
theorem period_two_pow_of_three_le :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 3 ≤ e → b (n + 2 ^ (e - 2)) ≡ b n [ZMOD 2 ^ e] :=
  ⟨A, fun n => (a_eq n).symm, fun e n he => A_two_adic_sharp e n he⟩

/-- Odd primes: $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n) \pmod{p^e}$ for every
odd prime $p$, every $e \ge 1$ and every $n$ with $2n + 1 \ge e$. -/
theorem antiperiod_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n + 1 →
        b (n + (p - 1) / 2 * p ^ (e - 1)) ≡ (-1) ^ ((p - 1) / 2) * b n [ZMOD p ^ e] :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ _ hp hp2 he hn => A_antiperiod hp hp2 he hn⟩

/-- Odd primes: $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ for every odd prime $p$, every
$e \ge 1$ and every $n$ with $2n + 1 \ge e$. -/
theorem period_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n + 1 →
        b (n + (p ^ e).totient) ≡ b n [ZMOD p ^ e] :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ _ hp hp2 he hn => A_odd_period hp hp2 he hn⟩

/-- Conjecture 1), corrected: $a(n + \varphi(k)) \equiv a(n) \pmod k$ for every $k \ge 1$ and
every $n$ such that $2n + 1$ is at least the exponent of each odd prime in $k$. -/
theorem period_totient :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k n : ℕ, 1 ≤ k →
        (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n + 1) →
        b (n + k.totient) ≡ b n [ZMOD k] :=
  ⟨A, fun n => (a_eq n).symm, fun _ n hk hn => A_corollary3 hk n hn⟩

/-- Conjecture 1) in its eventual form: for every $k \ge 1$, the sequence $a(n)$ modulo $k$ is
eventually periodic with period dividing $\varphi(k)$. -/
theorem conjecture1_eventual :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N, b (n + k.totient) ≡ b n [ZMOD k] :=
  ⟨A, fun n => (a_eq n).symm, fun k hk => ⟨k, fun n hn => A_corollary3 hk n fun p hp _ => by
    have := factorization_lt hk hp; omega⟩⟩

/-- Conjecture 1) in its pure form when every odd prime exponent of $k$ is at most $3$:
then $a(n + \varphi(k)) \equiv a(n) \pmod k$ for all $n \ge 1$. -/
theorem conjecture1_of_exponent_le_three :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 3) →
        ∀ n : ℕ, 1 ≤ n → b (n + k.totient) ≡ b n [ZMOD k] :=
  ⟨A, fun n => (a_eq n).symm, fun _ hk hE _ hn => A_pure hk hE hn⟩

/-- Conjecture 1), corrected, with the Carmichael function: $a(n + \lambda(k)) \equiv a(n)
\pmod k$ for every $k \ge 1$ and every $n$ such that $2n + 1$ is at least the exponent of each
odd prime in $k$. -/
theorem period_carmichael :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k n : ℕ, 1 ≤ k →
        (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n + 1) →
        b (n + ArithmeticFunction.carmichael k) ≡ b n [ZMOD k] :=
  ⟨A, fun n => (a_eq n).symm, fun _ n hk hn => A_carmichael hk n hn⟩

/-- Conjecture 1) in its eventual form with the Carmichael function: for every $k \ge 1$, the
sequence $a(n)$ modulo $k$ is eventually periodic with period dividing $\lambda(k)$. -/
theorem conjecture1_carmichael_eventual :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N,
        b (n + ArithmeticFunction.carmichael k) ≡ b n [ZMOD k] :=
  ⟨A, fun n => (a_eq n).symm, fun k hk => ⟨k, fun n hn => A_carmichael hk n fun p hp _ => by
    have := factorization_lt hk hp; omega⟩⟩

/-- The period $\lambda(8) = 2$ modulo $8$ cannot be replaced by $1$: $a(1) \not\equiv a(0)
\pmod 8$. -/
theorem carmichael_eight_sharp :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ArithmeticFunction.carmichael 8 = 2 ∧ ¬ b 1 ≡ b 0 [ZMOD 8] := by
  refine ⟨A, fun n => (a_eq n).symm, ?_, ?_⟩
  · rw [show 8 = 2 ^ 3 by norm_num, ArithmeticFunction.carmichael_two_pow_of_ne_two (by norm_num)]
    norm_num
  · rw [A_small.1, A_small.2.1]
    decide

/-- Bala's conjecture 2): for every shift $i \ge 0$, every prime $p$ and all $n, k \ge 1$,
$a(n p^k + i) \equiv a(n p^{k-1} + i) \pmod{p^k}$. -/
theorem conjecture2 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ i p n k : ℕ, p.Prime → 1 ≤ n → 1 ≤ k →
        b (n * p ^ k + i) ≡ b (n * p ^ (k - 1) + i) [ZMOD p ^ k] :=
  ⟨A, fun n => (a_eq n).symm, fun i _ _ _ hp hn hk => A_gauss i hp hn hk⟩

/-- The consequence stated with conjecture 2): for every shift $i \ge 0$,
$\exp\left(\sum_{n \ge 1} a(n + i) x^n / n\right)$ has integer coefficients. -/
theorem conjecture2_exp_integral (i N : ℕ) :
    ∃ z : ℤ, coeff N (subst (mk fun n : ℕ => if n = 0 then (0 : ℚ) else a (n + i) / n)
      (exp ℚ)) = z := by
  have h : (mk fun n : ℕ => if n = 0 then (0 : ℚ) else a (n + i) / n) =
      ofInt (fun n => A (n + i)) := by
    ext n
    simp only [ofInt, coeff_mk, a_eq]
  rw [h]
  exact exists_coeff_eq_intCast_of_gauss (gauss_shift i) N


/-- Bala's conjecture 3): $a(mn) \equiv a(m)^n \pmod{2^{2 v_2(m) + 4}}$ for all $m, n \ge 1$. -/
theorem conjecture3 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (m * n) ≡ b m ^ n [ZMOD 2 ^ (2 * m.factorization 2 + 4)] :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ _ _ => A_conj3⟩

/-- Bala's conjecture 4): for all $m, n \ge 1$, $a(2mn) \equiv a(n)^{2m}$ and
$a((2m+1)n) \equiv a(n)^{2m+1}$ modulo $2^{v_2(m) + 4}$. -/
theorem conjecture4 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (2 * m * n) ≡ b n ^ (2 * m) [ZMOD 2 ^ (m.factorization 2 + 4)] ∧
          b ((2 * m + 1) * n) ≡ b n ^ (2 * m + 1) [ZMOD 2 ^ (m.factorization 2 + 4)] :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ _ _ => A_conj4⟩

end OeisA000464

end
