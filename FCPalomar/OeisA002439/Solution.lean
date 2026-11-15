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
# OEIS A002439: Bala's conjectures for $\sin 2x / (2 \cos 3x)$

Let $a(n) = (2n+1)!\,[x^{2n+1}]\, \sin 2x / (2 \cos 3x)$ (OEIS A002439, Glaisher's $T$
numbers, offset 0). The file proves that every $a(n)$ is an integer and that:
- Bala's conjectures 3), 4) and 5) hold: for $m, n \ge 1$, $a(mn) \equiv a(m)^n$ modulo
  $2^{2 v_2(m) + 7}$ and modulo $3^{2 v_3(m) + 2}$; $a(2mn) \equiv a(n)^{2m}$ and
  $a((2m+1)n) \equiv a(n)^{2m+1} \pmod{2^{v_2(m) + 7}}$; $a(3mn) \equiv a(n)^{3m}$ and
  $a((3m+1)n) \equiv a(n)^{3m+1} \pmod{3^{v_3(m) + 2}}$; and
  $a((3m+2)n) \equiv a(n)^{3m+2} \pmod 9$ for $m \ge 0$ (Theorem 1); 5)(i), (ii) even hold
  modulo $3^{v_3(m) + 3}$;
- $a(n) \equiv 23^n \pmod{1152}$ for every $n$ (Bala's formula);
- conjecture 6) is false: $a(6252) \equiv (1 + 5^5)\,a(2) \pmod{5^6}$, so
  $v_5(a(6252) - a(2)^{3126}) = 5$, while 6) at $p = 5$, $n = 1$, $m = 3126$ asks for $6$
  (Theorem 2);
- $a(n + h p^{e-1}) \equiv (-1)^h a(n) \pmod{p^e}$ for odd primes $p$, $h = (p-1)/2$, $e \ge 1$
  and $2n + 1 \ge e$ (Lemma 10), and conjecture 6) holds when $v_p(m-1) \le (p-1)n$
  (Theorem 3);
- more precisely, for primes $p \ge 5$, every $e \ge 1$ and every $n$,
  $a(n + h p^{e-1}) \equiv (-1)^h \big(1 - \chi_{12}(p)\, p^{2n+1}\big)\, a(n) \pmod{p^e}$,
  and conjecture 6) holds exactly when $v_p(m-1) \le (p-1)n$;
- $a(n + 3^{e-1}) \equiv -a(n) \pmod{3^e}$ for every $e \ge 1$ and every $n$.

The proof works with Hurwitz series over a commutative ring: sequences $f_n = n!\,[x^n] f$ with
the binomial product.

*Integrality.* The Hurwitz coefficients of $\sin 2x / (2 \cos 3x)$ over $\mathbb{Q}$ are those
of $g = \frac12 \sin 2x \cdot \sec 3x$, which has integer coefficients ($\frac12 \sin 2x$ has
coefficients $(-4)^k$ at $2k + 1$). So $a(n) = A(n) := g_{2n+1}$. The identity
$\cos 3x \cdot g = \frac12 \sin 2x$ gives the recurrence
$\sum_{k \le n} \binom{2n+1}{2k} (-9)^k a(n-k) = (-4)^n$; the function `listA` evaluates it, and
`decide +kernel` checks the first terms $1, 23, 1681, 257543$.

*The hyperbolic form.* Over $\mathbb{C}$, $x \mapsto ix$ shows $g_{2n+1} = (-1)^n G_{2n+1}$ for
$G = \frac12 \sinh 2x \cdot \operatorname{sech} 3x$. Since $\cosh 3x = \cosh x\,(2 \cosh 2x - 1)$,
$G = \sinh x / (2 \cosh 2x - 1)$. With $w = e^x$ this gives $2 G\,(w^6 + 1) = w^5 - w$ and
$2 G = \Psi(2x)\, e^x$ for $\Psi = (e^x - 1)/(e^{2x} - e^x + 1)$, which has integer
coefficients.

*Odd moduli.* Let $P$ be odd. In $H(\mathbb{Z}/P)$ the series $s = e^{6x}$ has coefficients
$6^k$, and $s^P = e^{6Px} = 1$. So $(1 + s) \sum_{x < P} (-s)^x = 1 + s^P = 2$, and
$4 G = (w^5 - w) \sum_{x < P} (-s)^x$. Hence
$4 G_M \equiv \sum_{x < P} (-1)^x \big((5 + 6x)^M - (1 + 6x)^M\big) \pmod P$ for every $M$.

*Lemma 10.* Take $P = p^e$. Every base $u$ satisfies $u^{M + \varphi(p^e)} \equiv u^M$ for
$M \ge e$ (Euler's theorem, or $p^e \mid u^M$), and $4$ is a unit, so
$G_{M + \varphi(p^e)} \equiv G_M$. With $M = 2n + 1$ and $\varphi(p^e) = 2 h p^{e-1}$ the signs
give the antiperiod. For $p \ge 5$ this congruence is a case of R. Blanco Gómez (2026),
Theorem 1, applied to $6^r E_r(1/6)$; that theorem needs $p \nmid 6$, so it does not cover $p = 3$.

*Theorem 3.* Write $m - 1 = p^r t$ with $r = v_p(m-1)$. Lemma 10 at $e = r + 1$, applied $nt$
times from the index $hn$ (allowed as $2hn + 1 = (p-1)n + 1 \ge r + 1$), gives
$a(hnm) \equiv \varepsilon^t a(hn) \pmod{p^{r+1}}$ with $\varepsilon = (-1)^{hn}$. Lemma 10 at
$e = 1$ gives $a(hn) \equiv \varepsilon \pmod p$, so $a(hn)^{p^r} \equiv \varepsilon
\pmod{p^{r+1}}$ and $a(hn)^m = a(hn)\,(a(hn)^{p^r})^t \equiv \varepsilon^t a(hn)$.

*Theorem 2.* Take $P = 5^6$, $M = 5$ and $L = \varphi(5^6) = 12500$. In the difference of the
alternating sums for $M + L$ and $M$, every base prime to $5$ cancels. The bases divisible by
$5$ are $5 + 6x = 5(1 + 6y)$ for $x = 5y$ and $1 + 6x = 5(5 + 6y)$ for $x = 5y + 4$; each
contributes $-u^5$. So $4(G_{12505} - G_5) \equiv 5^5 \sum_{y < 5^5} (-1)^y
\big((5 + 6y)^5 - (1 + 6y)^5\big) \equiv 5^5 \cdot 4 G_5 \pmod{5^6}$, by the formula for
$P = 5^5$. Hence $a(6252) \equiv (1 + 5^5)\,a(2) \pmod{5^6}$. As $a(2) = 1681 \equiv 1
\pmod 5$, $a(2)^{3126} \equiv a(2) \pmod{5^6}$, and the difference is $5^5 \cdot 1681$ modulo
$5^6$. There is no large computation.

*The Euler factor.* Let $p \ge 5$ be prime, and take $P = p^e$ and $L = \varphi(p^e)$ in the
odd-modulus formula, for any $M \ge 1$. In the difference of the sums for $M + L$ and $M$, the
bases prime to $p$ cancel, and a base divisible by $p$ contributes $-u^M$, as $M + L \ge e$.
These bases are $5 + 6x = p(c_1 + 6y)$ for $x = x_0 + py$ and $1 + 6x = p(c_2 + 6y)$ for
$x = x_1 + py$, with $\{c_1, c_2\} = \{1, 5\}$ and $(-1)^{x_0} = (-1)^{x_1}$. A check of the
four classes of $p \bmod 12$ shows that together they give $-\chi_{12}(p)\, p^M$ times the sum
for $P = p^{e-1}$, which is $p^M \cdot 4 G_M$ modulo $p^{e-1+M}$. So
$G_{M+L} \equiv (1 - \chi_{12}(p)\, p^M)\, G_M \pmod{p^e}$. The factor
$1 - \chi_{12}(p)\, p^{2n+1}$ is the Euler factor of the Kummer congruences for
$L(-2n-1, \chi_{12})$, and Theorem 2 is its case $p = 5$, $n = 2$, $e = 6$. At $p = 3$ no base is
divisible by $3$, so $a(n + 3^{e-1}) \equiv -a(n) \pmod{3^e}$ for every $n$.

*Conjecture 6), exactly.* Let $r = v_p(m-1)$, $m - 1 = p^r t$ and $N = hn$. One step of the
Euler-factor congruence at $e = r + 1$ from $N$, then $nt - 1$ steps of Lemma 10, give
$a(hnm) \equiv \varepsilon^t (1 - \chi_{12}(p)\, p^{2N+1})\, a(N) \pmod{p^{r+1}}$, while
$a(N)^m \equiv \varepsilon^t a(N)$ as in Theorem 3. If the two agree, then
$p^{r+1} \mid p^{2N+1} a(N)$; as $p \nmid a(N)$, this gives $r \le 2N = (p-1)n$. The converse is
Theorem 3.

*Theorem 1, Newton coefficients.* Let $f_k = \sum_i \binom{k}{i} (-23)^{k-i} a(i)$, so that
$f_k / 23^k = \Delta^k b(0)$ for $b(n) = a(n) / 23^n$. If $c\,G_M \equiv \sum_x \mu_x
(u_x^M - v_x^M) \pmod Q$ for odd $M$, then $c f_k \equiv \sum_x \mu_x (R_k(u_x) - R_k(v_x))$
with $R_k(u) = u\,(-u^2 - 23)^k$.
- At $2$: $\Psi$ lies in the class $K$ of series that agree up to every index with a
  polynomial in $e^x$ (it is closed under inverses), so $2 G_M = \sum_i Q_i (2i + 1)^M$
  exactly. As $8 \mid (2i + 1)^2 + 23$, $2^{3k} \mid 2 f_k$.
- At $3$: the odd-modulus formula with $P = 3^k$; both $(5 + 6x)^2 + 23$ and $(1 + 6x)^2 + 23$
  are multiples of $12$, so $3^k \mid f_k$.

With $f_0 = 1$, $f_1 = 0$ and $f_2 = 1152 = 2^7 \cdot 3^2$, the Newton coefficients of
$E = b - 1$ in $\mathbb{Z}_2$ are divisible by $2^{j+5}$, and those in $\mathbb{Z}_3$ by $3^j$
and by $9$. So $b \equiv 1$ modulo $2^7$ and modulo $9$, which is Bala's formula.

*Theorem 1, power congruences.* The informal proof uses $p$-adic logarithms. The Lean proof
uses the power map $z \mapsto z^{p^N}$ in $\mathbb{Z}_p$ for $p = 2, 3$.
- The Leibniz rule for $\Delta$ gives $2^{l + 5r} \mid \Delta^l(E^r)(0)$ and
  $3^{\max(l, 2r)} \mid \Delta^l(E^r)(0)$. With $p^N \mid \binom{p^N}{r} p^{v_p(r)}$, the
  binomial expansion of $B = b^{p^N}$ gives $2^{N + l + 5} \mid \Delta^l B(0)$ and
  $3^{N + 2 + \lfloor (l-1)/2 \rfloor} \mid \Delta^l B(0)$ for $l \ge 1$.
- Newton's formula writes $B(xy) - y B(x) - (1 - y)$ as
  $\sum_{l \ge 1} \left(\binom{xy}{l} - y \binom{x}{l}\right) \Delta^l B(0)$. Here
  $x^2 y (y - 1)$ divides $l!\left(\binom{xy}{l} - y \binom{x}{l}\right)$, and
  $(p - 1)\, v_p(l!) \le l - 1$. Also $B(x)^y \equiv 1 + y (B(x) - 1)$ modulo
  $(B(x) - 1)^2$. So if $p^K \mid x^2 y (y - 1)$ and $N = K$, then $2^{2K + 6}$, respectively
  $3^{2K + 2}$, divides $b(xy)^{p^K} - (b(x)^y)^{p^K}$.
- Each square root step loses one factor $2$ (as $b \equiv 1 \pmod 4$), and each cube root
  step loses one factor $3$ (as $b \equiv 1 \pmod 3$: $\beta^3 - \gamma^3 = (\beta - \gamma)
  \cdot 3 \cdot \text{unit}$). So $a(xy) \equiv a(x)^y$ modulo $2^{K+6}$, respectively
  $3^{K+2}$.
- 3)(i) is $(x, y) = (m, n)$ with $K = 2 v_2(m) + 1$, and 3)(ii) has $K = 2 v_3(m)$. 4) is
  $(x, y) = (n, 2m), (n, 2m + 1)$ with $K = v_2(m) + 1$. 5)(i), (ii) are
  $(n, 3m), (n, 3m + 1)$ with $K = v_3(m) + 1$; they hold modulo $3^{v_3(m) + 3}$. 5)(iii) is
  $(n, 3m + 2)$ with $K = 0$.

The Hurwitz-series library, the twist $x \mapsto ix$, the class $K$, the evaluator pattern
`listA`/`listA_getD`, the Leibniz rule, the polynomial divisibility and the $2$-adic square root
steps are adapted from this repository's OeisA000464 package, which took the Hurwitz library
from the OeisA012780 package. The odd-modulus formula, the counterexample, the Euler factor,
the $3$-adic part and the general $p$-adic core are written for this package.

*References:*
- N. J. A. Sloane, [A002439](https://oeis.org/A002439); the conjectures are Peter Bala's
  comments of December 18, 2021, and the formula $a(n) \equiv 23^n \pmod{1152}$ is his
  comment of December 25, 2021.
- J. W. L. Glaisher, On a set of coefficients analogous to the Eulerian numbers, Proc. London
  Math. Soc. 31 (1899), 216–235.
- R. Blanco Gómez, Zenodo 23404924 (2026), Theorem 1 (the odd-prime congruence for $p \ge 5$).
-/

@[expose] public section

namespace OeisA002439

open PowerSeries

/-- OEIS A002439: $a(n) = (2n+1)!\,[x^{2n+1}]\, \sin 2x / (2 \cos 3x)$. -/
noncomputable def a (n : ℕ) : ℚ :=
  (2 * n + 1).factorial *
    coeff (2 * n + 1) (rescale (2 : ℚ) (sin ℚ) * (2 * rescale (3 : ℚ) (cos ℚ))⁻¹)

/-- The Dirichlet character $\chi_{12}$ at an integer $p$ prime to $6$: $\chi_{12}(p) = 1$ if
$p \equiv \pm 1 \pmod{12}$ and $\chi_{12}(p) = -1$ if $p \equiv \pm 5 \pmod{12}$. -/
def chi12 (p : ℕ) : ℤ := if p % 12 = 1 ∨ p % 12 = 11 then 1 else -1

end OeisA002439

namespace OeisA002439

/-! ### Hurwitz series

The Hurwitz-series library (ring structure, derivative, constants, causal fixed points,
exponentials, inverses, coefficient maps, divided powers and rescaling) is copied from this
repository's OeisA000464 package. That package took it from the OeisA012780 package, which
adapted it from the OeisA317345, A396804 and OeisA371710 packages. -/

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

/-- The series of $\cosh x$. -/
def coshH : Hur R := ⟨fun n => if n % 2 = 0 then 1 else 0⟩

/-- The series of $\sinh x$. -/
def sinhH : Hur R := ⟨fun n => if n % 2 = 1 then 1 else 0⟩

/-- The series of $\sin x$. -/
def sinH : Hur R := ⟨fun n => if n % 2 = 1 then (-1) ^ (n / 2) else 0⟩

/-- The series of $\frac12 \sin 2x$, with coefficients $(-4)^k$ at $2k + 1$. -/
def hsin2 : Hur R := ⟨fun n => if n % 2 = 1 then (-4) ^ (n / 2) else 0⟩

/-- The series of $\frac12 \sinh 2x$, with coefficients $4^k$ at $2k + 1$. -/
def hsinh2 : Hur R := ⟨fun n => if n % 2 = 1 then 4 ^ (n / 2) else 0⟩

/-- The series of $\sec x$. -/
def secH : Hur R := hinv (cosH R)

/-- The series of $\operatorname{sech} x$. -/
def sechH : Hur R := hinv (coshH R)

/-- The series $g = \frac12 \sin 2x \cdot \sec 3x$. -/
def gH : Hur R := hsin2 R * scale 3 (secH R)

/-- The series $G = \frac12 \sinh 2x \cdot \operatorname{sech} 3x$. -/
def GH : Hur R := hsinh2 R * scale 3 (sechH R)

variable {R}

lemma C_two : C (2 : R) = 2 := map_ofNat CHom 2

lemma cosH_coeff_zero : (cosH R).coeff 0 = 1 := by simp [cosH]

lemma coshH_coeff_zero : (coshH R).coeff 0 = 1 := by simp [coshH]

lemma cosH_mul_secH : cosH R * secH R = 1 := mul_hinv cosH_coeff_zero

lemma coshH_mul_sechH : coshH R * sechH R = 1 := mul_hinv coshH_coeff_zero

lemma scale_one (c : R) : scale c (1 : Hur R) = 1 := map_one (scaleHom c)

/-- $\cos 3x \cdot \sec 3x = 1$. -/
lemma cos3_mul_sec3 : scale 3 (cosH R) * scale 3 (secH R) = 1 := by
  rw [← scale_mul, cosH_mul_secH, scale_one]

/-- $\cosh 3x \cdot \operatorname{sech} 3x = 1$. -/
lemma cosh3_mul_sech3 : scale 3 (coshH R) * scale 3 (sechH R) = 1 := by
  rw [← scale_mul, coshH_mul_sechH, scale_one]

/-- $\cos 3x \cdot g = \frac12 \sin 2x$. -/
lemma cos3_mul_gH : scale 3 (cosH R) * gH R = hsin2 R := by
  rw [gH, mul_left_comm, cos3_mul_sec3, mul_one]

/-- $2 \cdot \frac12 \sin 2x = \sin 2x$. -/
lemma two_hsin2 : C 2 * hsin2 R = scale 2 (sinH R) := by
  ext n
  rw [C_mul_coeff, coeff_scale]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h2 : (2 * k) % 2 = 0 := by omega
    simp [hsin2, sinH, h2]
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    have h3 : (2 * k + 1) / 2 = k := by omega
    simp only [hsin2, sinH, h2, h3, ite_true, pow_succ, pow_mul]
    rw [show (-4 : R) = 2 ^ 2 * (-1) by ring, mul_pow]
    ring

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

/-- $4 \cdot \frac12 \sinh 2x = e^{2x} - e^{-2x}$. -/
lemma four_hsinh2 : C 4 * hsinh2 R = ex 2 - ex (-2) := by
  ext n
  rw [C_mul_coeff, coeff_sub, coeff_ex, coeff_ex]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h2 : (2 * k) % 2 = 0 := by omega
    simp [hsinh2, h2, pow_mul]
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    have h3 : (2 * k + 1) / 2 = k := by omega
    simp only [hsinh2, h2, h3, ite_true, pow_succ, pow_mul]
    ring

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

lemma map_coshH : map φ (coshH R) = coshH S := by
  ext n
  simp only [coeff_map, coshH]
  split_ifs <;> simp

lemma map_hsin2 : map φ (hsin2 R) = hsin2 S := by
  ext n
  simp only [coeff_map, hsin2]
  split_ifs
  · rw [map_pow, map_neg, show φ 4 = 4 from map_ofNat φ 4]
  · exact map_zero φ

lemma map_hsinh2 : map φ (hsinh2 R) = hsinh2 S := by
  ext n
  simp only [coeff_map, hsinh2]
  split_ifs
  · rw [map_pow, show φ 4 = 4 from map_ofNat φ 4]
  · exact map_zero φ

lemma map_secH : map φ (secH R) = secH S := by
  rw [secH, map_hinv φ cosH_coeff_zero, map_cosH, secH]

lemma map_sechH : map φ (sechH R) = sechH S := by
  rw [sechH, map_hinv φ coshH_coeff_zero, map_coshH, sechH]

lemma map_gH : map φ (gH R) = gH S := by
  rw [gH, map_mul', map_hsin2, map_scale, map_ofNat, map_secH, gH]

lemma map_GH : map φ (GH R) = GH S := by
  rw [GH, map_mul', map_hsinh2, map_scale, map_ofNat, map_sechH, GH]

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

lemma scale_I_hsin2 : scale I (hsin2 ℂ) = C I * hsinh2 ℂ := by
  ext n
  rw [coeff_scale, C_mul_coeff]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h2 : (2 * k) % 2 = 0 := by omega
    simp [hsin2, hsinh2, h2]
  · have h2 : (2 * k + 1) % 2 = 1 := by omega
    have h3 : (2 * k + 1) / 2 = k := by omega
    simp only [hsin2, hsinh2, h2, h3, ite_true, pow_succ, I_pow_two_mul]
    rw [mul_assoc, mul_comm I, ← mul_assoc, ← mul_pow]
    norm_num
    ring

lemma scale_I_secH : scale I (secH ℂ) = sechH ℂ := by
  refine inv_unique' (u := coshH ℂ) ?_ coshH_mul_sechH
  rw [← scale_I_cosH, ← scale_mul, cosH_mul_secH, ← scaleHom_apply, map_one]

lemma scale_I_gH : scale I (gH ℂ) = C I * GH ℂ := by
  have h : scale I (scale 3 (secH ℂ)) = scale 3 (sechH ℂ) := by
    rw [scale_scale, mul_comm, ← scale_scale, scale_I_secH]
  rw [gH, scale_mul, scale_I_hsin2, h, GH, mul_assoc]

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

lemma jet_inv_cos3 :
    jet (2 * rescale (3 : ℚ) (cos ℚ))⁻¹ = Hur.C (1 / 2) * scale 3 (secH ℚ) := by
  have h2 : jet (2 : ℚ⟦X⟧) = Hur.C 2 := by rw [map_ofNat, C_two]
  have h0 : constantCoeff (2 * rescale (3 : ℚ) (cos ℚ)) ≠ 0 := by
    rw [constantCoeff_eq_jet, map_mul, h2, jet_rescale, jet_cos, C_mul_coeff, coeff_scale,
      cosH_coeff_zero]
    norm_num
  refine inv_unique' (u := Hur.C 2 * scale 3 (cosH ℚ)) ?_ ?_
  · rw [← jet_cos, ← jet_rescale, ← h2, ← map_mul, ← map_mul, PowerSeries.mul_inv_cancel _ h0,
      map_one]
  · rw [show Hur.C (2 : ℚ) * scale 3 (cosH ℚ) * (Hur.C (1 / 2) * scale 3 (secH ℚ)) =
      Hur.C (2 * (1 / 2)) * (scale 3 (cosH ℚ) * scale 3 (secH ℚ)) by rw [C_mul]; ring,
      cos3_mul_sec3]
    norm_num [C_one]

/-- The Hurwitz series of $\sin 2x / (2 \cos 3x)$ is $g$. -/
lemma jet_eq_gH :
    jet (rescale (2 : ℚ) (sin ℚ) * (2 * rescale (3 : ℚ) (cos ℚ))⁻¹) = gH ℚ := by
  rw [map_mul, jet_rescale, jet_sin, jet_inv_cos3, ← two_hsin2, gH]
  rw [show Hur.C (2 : ℚ) * hsin2 ℚ * (Hur.C (1 / 2) * scale 3 (secH ℚ)) =
    Hur.C (2 * (1 / 2)) * (hsin2 ℚ * scale 3 (secH ℚ)) by rw [C_mul]; ring]
  norm_num [C_one]

/-- The integer sequence $A(n) = g_{2n+1}$, the odd Hurwitz coefficients of
$g = \frac12 \sin 2x \cdot \sec 3x$. -/
def A (n : ℕ) : ℤ := (gH ℤ).coeff (2 * n + 1)

/-- $a(n) = A(n)$: the OEIS terms are the integers $g_{2n+1}$. -/
theorem a_eq (n : ℕ) : a n = A n := by
  have h := congrArg (fun F => Hur.coeff F (2 * n + 1)) jet_eq_gH
  simp only [jet_coeff] at h
  rw [a, h, A, ← map_gH (Int.castRingHom ℚ), Hur.coeff_map]
  rfl

/-- $a(n) = (-1)^n G_{2n+1}$. -/
lemma A_eq_GH (n : ℕ) : A n = (-1) ^ n * (GH ℤ).coeff (2 * n + 1) := gH_coeff_odd n

end Bridge

/-! ### Exponential identities for $G$ -/

section Identities
open Hur

lemma ex_pow {R : Type*} [CommRing R] (c : R) (k : ℕ) : ex c ^ k = ex (k * c) := by
  induction k with
  | zero => simp [ex_zero]
  | succ k ih =>
    rw [pow_succ, ih, ← ex_add]
    congr 1
    push_cast
    ring

lemma ex_mul_ex' {R : Type*} [CommRing R] (c d : R) : ex c * ex d = ex (c + d) :=
  (ex_add c d).symm

/-- Cancel a nonzero integer factor in $H(\mathbb{Z})$. -/
lemma C_cancel {k : ℤ} (hk : k ≠ 0) {F F' : Hur ℤ} (h : C k * F = C k * F') : F = F' := by
  ext n
  have h' := congrArg (fun H => Hur.coeff H n) h
  simp only [C_mul_coeff] at h'
  exact mul_left_cancel₀ hk h'

/-- The series $D = e^{2x} + e^{-2x} - 1 = 2 \cosh 2x - 1$. -/
def DtH : Hur ℤ := ex 2 + ex (-2) - 1

lemma DtH_coeff_zero : DtH.coeff 0 = 1 := by
  simp [DtH, coeff_ex, coeff_one]

lemma ex_two_eq : ex (2 : ℤ) = ex 1 ^ 2 := by rw [ex_pow]; norm_num
lemma ex_three_eq : ex (3 : ℤ) = ex 1 ^ 3 := by rw [ex_pow]; norm_num
lemma ex_four_eq : ex (4 : ℤ) = ex 1 ^ 4 := by rw [ex_pow]; norm_num
lemma ex_neg_two_eq : ex (-2 : ℤ) = ex (-1) ^ 2 := by rw [ex_pow]; norm_num
lemma ex_neg_three_eq : ex (-3 : ℤ) = ex (-1) ^ 3 := by rw [ex_pow]; norm_num

lemma scale3_coshH : 2 * scale 3 (coshH ℤ) = ex 1 ^ 3 + ex (-1) ^ 3 := by
  have h := congrArg (scaleHom (3 : ℤ)) (two_coshH (R := ℤ))
  rw [map_mul, map_add, map_ofNat, scaleHom_apply, scaleHom_apply, scaleHom_apply, scale_ex,
    scale_ex] at h
  rw [h, ← ex_three_eq, ← ex_neg_three_eq]
  norm_num

lemma DtH_eq : DtH = ex 1 ^ 2 + ex (-1) ^ 2 - 1 := by rw [DtH, ex_two_eq, ex_neg_two_eq]

lemma DtH_mul_hinv : (ex (1 : ℤ) ^ 2 + ex (-1) ^ 2 - 1) * hinv DtH = 1 := by
  rw [← DtH_eq]
  exact mul_hinv DtH_coeff_zero

/-- $G = \sinh x / (2 \cosh 2x - 1)$, since $\cosh 3x = \cosh x\,(2 \cosh 2x - 1)$ and
$\frac12 \sinh 2x = \sinh x \cosh x$. -/
lemma GH_eq : GH ℤ = sinhH ℤ * hinv DtH := by
  have hw : ex (1 : ℤ) * ex (-1) = 1 := ex_mul_ex_neg 1
  have hU := DtH_mul_hinv
  have hS : scale 3 (coshH ℤ) * scale 3 (sechH ℤ) = 1 := cosh3_mul_sech3
  have h4 : 4 * hsinh2 ℤ = ex 1 ^ 2 - ex (-1) ^ 2 := by
    rw [← ex_two_eq, ← ex_neg_two_eq, ← four_hsinh2, show (4 : Hur ℤ) = C 4 from
      (map_ofNat CHom 4).symm]
  have h2s : 2 * sinhH ℤ = ex 1 - ex (-1) := two_sinhH
  have h2c := scale3_coshH
  apply C_cancel (k := 4) four_ne_zero
  rw [show C (4 : ℤ) = 4 from map_ofNat CHom 4, GH]
  set w := ex (1 : ℤ)
  set w' := ex (-1 : ℤ)
  set U := hinv DtH
  set S3 := scale 3 (sechH ℤ)
  set C3 := scale 3 (coshH ℤ)
  linear_combination S3 * h4 - 2 * U * h2s - (w ^ 2 - w' ^ 2) * S3 * hU +
    2 * (w - w') * U * hS + (w ^ 2 - w' ^ 2) * U * S3 * hw - (w - w') * U * S3 * h2c

/-- $2 G \cdot (e^{6x} + 1) = e^{5x} - e^x$. -/
lemma two_GH_mul : 2 * GH ℤ * (ex 1 ^ 6 + 1) = ex 1 ^ 5 - ex 1 := by
  have hw : ex (1 : ℤ) * ex (-1) = 1 := ex_mul_ex_neg 1
  have hU := DtH_mul_hinv
  have h2s : 2 * sinhH ℤ = ex 1 - ex (-1) := two_sinhH
  rw [GH_eq]
  set w := ex (1 : ℤ)
  set w' := ex (-1 : ℤ)
  set U := hinv DtH
  linear_combination U * (w ^ 6 + 1) * h2s + (w - w') * (w ^ 2 + 1) * w ^ 2 * hU +
    (-(w * (w ^ 2 + 1)) - (w - w') * (w ^ 2 + 1) * (w * w' + 1) * U) * hw

/-- The series $\Psi = (e^x - 1) / (e^{2x} - e^x + 1)$, with integer coefficients. -/
def PsiH : Hur ℤ := (ex 1 - 1) * hinv (ex 2 - ex 1 + 1)

lemma Bq_coeff_zero : (ex (2 : ℤ) - ex 1 + 1).coeff 0 = 1 := by
  simp [coeff_ex, coeff_one]

lemma scale2_Bq : scale 2 (ex (2 : ℤ) - ex 1 + 1) = ex 1 ^ 4 - ex 1 ^ 2 + 1 := by
  rw [← scaleHom_apply, map_add, map_sub, map_one, scaleHom_apply, scaleHom_apply, scale_ex,
    scale_ex, ← ex_four_eq, ← ex_two_eq]
  norm_num

lemma scale2_ex_sub_one : scale 2 (ex (1 : ℤ) - 1) = ex 1 ^ 2 - 1 := by
  rw [← scaleHom_apply, map_sub, map_one, scaleHom_apply, scale_ex, mul_one, ex_two_eq]

/-- $2G = \Psi(2x)\,e^x$. -/
lemma two_GH : C 2 * GH ℤ = scale 2 PsiH * ex 1 := by
  have hw : ex (1 : ℤ) * ex (-1) = 1 := ex_mul_ex_neg 1
  have hU := DtH_mul_hinv
  have hV : (ex 1 ^ 4 - ex 1 ^ 2 + 1) * scale 2 (hinv (ex (2 : ℤ) - ex 1 + 1)) = 1 := by
    have h1 := congrArg (scaleHom (2 : ℤ)) (mul_hinv Bq_coeff_zero)
    rw [map_mul, map_one, scaleHom_apply, scaleHom_apply, scale2_Bq] at h1
    exact h1
  have h2s : 2 * sinhH ℤ = ex 1 - ex (-1) := two_sinhH
  rw [PsiH, scale_mul, scale2_ex_sub_one, C_two, GH_eq]
  set w := ex (1 : ℤ)
  set w' := ex (-1 : ℤ)
  set U := hinv DtH
  set V := scale 2 (hinv (ex (2 : ℤ) - w + 1))
  linear_combination U * h2s - (w - w') * U * hV + (w - w') * w ^ 2 * V * hU +
    (-(w - w') * U * V * (w * w' + 1) - w * V) * hw

/-- $2 G_M = \sum_j \binom{M}{j} 2^j \Psi_j$. -/
lemma two_GH_coeff (M : ℕ) :
    2 * (GH ℤ).coeff M =
      ∑ j ∈ Finset.range (M + 1), (M.choose j : ℤ) * (2 ^ j * PsiH.coeff j) := by
  have h := congrArg (fun F => Hur.coeff F M) two_GH
  rw [C_mul_coeff, coeff_mul_sum] at h
  simp only [coeff_ex, one_pow, mul_one, coeff_scale] at h
  exact h

end Identities

/-! ### The alternating-sum formula modulo an odd number -/

section OddFormula
open Hur

/-- For odd $P$: $4 G_M \equiv \sum_{x < P} (-1)^x \big((5 + 6x)^M - (1 + 6x)^M\big)
\pmod P$. In $H(\mathbb{Z}/P)$, $s = e^{6x}$ satisfies $s^P = e^{6Px} = 1$, so
$(1 + s) \sum_{x < P} (-s)^x = 1 + s^P = 2$, and $2G(1 + s) = e^{5x} - e^x$. -/
theorem four_GH_zmod (P M : ℕ) (hP : Odd P) :
    (4 : ZMod P) * ((GH ℤ).coeff M : ZMod P) =
      ∑ x ∈ Finset.range P, (-1) ^ x *
        (((5 + 6 * x : ℕ) : ZMod P) ^ M - ((1 + 6 * x : ℕ) : ZMod P) ^ M) := by
  set φ := Int.castRingHom (ZMod P)
  set G' := map φ (GH ℤ)
  set w := ex (1 : ZMod P)
  have h : 2 * G' * (w ^ 6 + 1) = w ^ 5 - w := by
    have := congrArg (mapHom φ) two_GH_mul
    rw [map_mul, map_mul, map_add, map_pow, map_one, map_sub, map_pow, map_ofNat,
      mapHom_apply, mapHom_apply, map_ex, map_one] at this
    exact this
  have hsP : (w ^ 6) ^ P = 1 := by
    rw [← pow_mul, ex_natCast]
    have : ((6 * P : ℕ) : ZMod P) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
    rw [this, ex_zero]
  set S := ∑ x ∈ Finset.range P, (-(w ^ 6)) ^ x with hS
  have hgeom : S * (-(w ^ 6) - 1) = (-(w ^ 6)) ^ P - 1 := geom_sum_mul _ _
  rw [hP.neg_pow, hsP] at hgeom
  have h4 : 4 * G' = (w ^ 5 - w) * S := by
    linear_combination (2 * G') * hgeom + S * h
  have hc := congrArg (fun F => Hur.coeff F M) h4
  rw [show (4 : Hur (ZMod P)) = C 4 from (map_ofNat CHom 4).symm, C_mul_coeff, hS,
    Finset.mul_sum, coeff_sum] at hc
  rw [show ((GH ℤ).coeff M : ZMod P) = G'.coeff M from rfl, hc]
  refine Finset.sum_congr rfl fun x _ => ?_
  have e : (w ^ 5 - w) * (-(w ^ 6)) ^ x =
      C ((-1) ^ x) * (w ^ (5 + 6 * x) - w ^ (1 + 6 * x)) := by
    rw [C_pow, C_neg, C_one, neg_pow, pow_add, pow_add, pow_mul]
    ring
  rw [e, C_mul_coeff, coeff_sub, ex_natCast, ex_natCast, coeff_ex, coeff_ex]

/-- The formula as an integer congruence. -/
theorem four_GH_modEq (P M : ℕ) (hP : Odd P) :
    4 * (GH ℤ).coeff M ≡ ∑ x ∈ Finset.range P, (-1) ^ x *
        ((5 + 6 * (x : ℤ)) ^ M - (1 + 6 * (x : ℤ)) ^ M) [ZMOD P] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  have h := four_GH_zmod P M hP
  push_cast at h ⊢
  exact h

end OddFormula

/-! ### Odd primes: the antiperiod (Lemma 10) -/

section OddPrime
open Hur

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

lemma isUnit_four_zmod {P : ℕ} (hP : Odd P) : IsUnit (4 : ZMod P) := by
  have hc : Nat.Coprime 4 P := by
    have h2 : Nat.Coprime 2 P := Nat.coprime_two_left.2 hP
    simpa using Nat.Coprime.pow_left 2 h2
  have := (ZMod.unitOfCoprime 4 hc).isUnit
  rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this

/-- $G_{M + \varphi(p^e)} \equiv G_M \pmod{p^e}$ for odd primes $p$ and $M \ge e$: in the
alternating-sum formula every base satisfies $u^{M + \varphi(p^e)} \equiv u^M$. -/
theorem GH_odd_prime {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : ℕ} (hM : e ≤ M) :
    (GH ℤ).coeff (M + (p ^ e).totient) ≡ (GH ℤ).coeff M [ZMOD p ^ e] := by
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have h : (4 : ZMod (p ^ e)) * ((GH ℤ).coeff (M + (p ^ e).totient) : ZMod (p ^ e)) =
      4 * ((GH ℤ).coeff M : ZMod (p ^ e)) := by
    rw [four_GH_zmod (p ^ e) _ hodd, four_GH_zmod (p ^ e) M hodd]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [zmod_pow_periodic hp _ M hM, zmod_pow_periodic hp _ M hM]
  have h' := (isUnit_four_zmod hodd).mul_left_cancel h
  have := (ZMod.intCast_eq_intCast_iff _ _ _).1 h'
  exact_mod_cast this

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

/-- Lemma 10: $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n) \pmod{p^e}$ for odd
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

/-- Iterating a congruence $x(i + L) \equiv c\,x(i)$ that holds from `N0` on. -/
lemma iter_mul_shift {x : ℕ → ℤ} {m c : ℤ} {L N0 : ℕ}
    (h : ∀ i, N0 ≤ i → x (i + L) ≡ c * x i [ZMOD m]) (k : ℕ) :
    ∀ i, N0 ≤ i → x (i + k * L) ≡ c ^ k * x i [ZMOD m] := by
  induction k with
  | zero => intro i _; simp
  | succ k ih =>
    intro i hi
    rw [show i + (k + 1) * L = (i + k * L) + L by ring]
    calc x (i + k * L + L) ≡ c * x (i + k * L) [ZMOD m] := h _ (le_trans hi (Nat.le_add_right _ _))
      _ ≡ c * (c ^ k * x i) [ZMOD m] := (ih i hi).mul_left c
      _ = c ^ (k + 1) * x i := by ring

end OddPrime

/-! ### The recurrence and a verified evaluator -/

section Eval
open Hur

/-- Split a sum over `range (2 * m)` into even and odd indices. -/
lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), f i = ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

lemma coeff_cos3_odd (k : ℕ) : (scale 3 (cosH ℤ)).coeff (2 * k + 1) = 0 := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  simp [coeff_scale, cosH, h1]

lemma coeff_cos3_even (k : ℕ) : (scale 3 (cosH ℤ)).coeff (2 * k) = (-9) ^ k := by
  have h1 : (2 * k) % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  simp only [coeff_scale, cosH, h1, h2, ↓reduceIte]
  rw [pow_mul, ← mul_pow]
  norm_num

lemma coeff_hsin2_odd (n : ℕ) : (hsin2 ℤ).coeff (2 * n + 1) = (-4) ^ n := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp [hsin2, h1, h2]

/-- The recurrence $\sum_{k \le n} \binom{2n+1}{2k} (-9)^k a(n-k) = (-4)^n$, from
$\cos 3x \cdot g = \frac12 \sin 2x$. -/
lemma A_rec (n : ℕ) :
    A n + ∑ j ∈ Finset.range n,
      ((2 * n + 1).choose (2 * (j + 1)) : ℤ) * (-9) ^ (j + 1) * A (n - 1 - j) = (-4) ^ n := by
  have h := congrArg (fun F => Hur.coeff F (2 * n + 1)) (cos3_mul_gH (R := ℤ))
  simp only [coeff_mul_sum, coeff_hsin2_odd] at h
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, sum_range_two_mul, Finset.sum_range_succ'] at h
  rw [← h, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.1 hj
    rw [coeff_cos3_odd, coeff_cos3_even, zero_mul, mul_zero, add_zero, A,
      show 2 * n + 1 - 2 * (j + 1) = 2 * (n - 1 - j) + 1 by omega]
    ring
  · rw [coeff_cos3_odd, coeff_cos3_even]
    simp [A]

/-- One step of the recurrence: from `l = [A (n-1), ..., A 0]`, the value `A n`. The binomial
coefficients are written with factorials, which the kernel evaluates quickly. -/
def stepA (n : ℕ) (l : List ℤ) : ℤ :=
  (-4) ^ n - ((List.range n).map fun j =>
    (((2 * n + 1).factorial / ((2 * (j + 1)).factorial * (2 * n + 1 - 2 * (j + 1)).factorial) :
      ℕ) : ℤ) * (-9) ^ (j + 1) * l.getD j 0).sum

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
            (2 * n + 1 - 2 * (j + 1)).factorial) : ℕ) : ℤ) * (-9) ^ (j + 1) *
            (listA n).getD j 0).sum =
          ∑ j ∈ Finset.range n,
            ((2 * n + 1).choose (2 * (j + 1)) : ℤ) * (-9) ^ (j + 1) * A (n - 1 - j) := by
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

lemma listA_four : listA 4 = [257543, 1681, 23, 1] := by decide +kernel

lemma A_small : A 0 = 1 ∧ A 1 = 23 ∧ A 2 = 1681 ∧ A 3 = 257543 := by
  have h := listA_getD 4
  rw [listA_four] at h
  exact ⟨(h 3 (by norm_num)).symm, (h 2 (by norm_num)).symm, (h 1 (by norm_num)).symm,
    (h 0 (by norm_num)).symm⟩

end Eval

/-! ### Conjecture 6), corrected (Theorem 3) -/

section Conj6
open Hur

/-- Theorem 3: for a prime $p \ge 5$, $h = (p-1)/2$, $m \ge 1$ and $r = v_p(m-1) \le (p-1) n$,
$a(hnm) \equiv a(hn)^m \pmod{p^{r+1}}$. -/
theorem A_conj6_of_le {p m n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m)
    (hr : (m - 1).factorization p ≤ (p - 1) * n) :
    A ((p - 1) / 2 * n * m) ≡ A ((p - 1) / 2 * n) ^ m
      [ZMOD p ^ ((m - 1).factorization p + 1)] := by
  set r := (m - 1).factorization p with hr_def
  set h := (p - 1) / 2 with hh
  have hp2 : p ≠ 2 := by omega
  have h2h : 2 * h = p - 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  have hrn : r ≤ 2 * (h * n) := by rw [← mul_assoc, h2h]; exact hr
  obtain ⟨t, ht⟩ : p ^ r ∣ m - 1 := Nat.ordProj_dvd (m - 1) p
  have hm' : m = 1 + p ^ r * t := by omega
  set ε : ℤ := ((-1) ^ h) ^ n with hε
  -- the left side, by Lemma 10 at `e = r + 1`, applied `n t` times
  have hL : A (h * n + (n * t) * (h * p ^ (r + 1 - 1))) ≡ ((-1) ^ h) ^ (n * t) * A (h * n)
      [ZMOD p ^ (r + 1)] :=
    iter_mul_shift (fun i hi => A_antiperiod hp hp2 (by omega) (by omega)) (n * t) (h * n)
      le_rfl
  have hidx : h * n + (n * t) * (h * p ^ (r + 1 - 1)) = h * n * m := by
    rw [hm', show r + 1 - 1 = r by omega]
    ring
  rw [hidx] at hL
  -- the right side: `a(hn) ≡ ε (mod p)` by Lemma 10 at `e = 1`
  have h1 : A (h * n) ≡ ε [ZMOD p] := by
    have := iter_mul_shift (x := A) (m := (p : ℤ) ^ 1) (L := h * p ^ (1 - 1)) (N0 := 0)
      (c := (-1) ^ h) (fun i _ => A_antiperiod hp hp2 le_rfl (by omega)) n 0 le_rfl
    rw [show 0 + n * (h * p ^ (1 - 1)) = h * n by simp [mul_comm], pow_one, A_small.1,
      mul_one] at this
    exact this
  have h2 : (p : ℤ) ^ (r + 1) ∣ A (h * n) ^ p ^ r - ε ^ p ^ r :=
    dvd_sub_pow_of_dvd_sub (Int.ModEq.dvd h1.symm) r
  have hε' : ε = (-1) ^ (h * n) := by rw [hε, ← pow_mul]
  have h3 : ε ^ p ^ r = ε := by
    rcases neg_one_pow_eq_or ℤ (h * n) with h' | h' <;> rw [hε', h']
    · rw [one_pow]
    · exact ((hp.odd_of_ne_two hp2).pow).neg_one_pow
  rw [h3] at h2
  have h4 : A (h * n) ^ p ^ r ≡ ε [ZMOD p ^ (r + 1)] := (Int.modEq_iff_dvd.2 h2).symm
  calc A (h * n * m) ≡ ((-1) ^ h) ^ (n * t) * A (h * n) [ZMOD p ^ (r + 1)] := hL
    _ = A (h * n) * ε ^ t := by rw [hε, pow_mul]; ring
    _ ≡ A (h * n) * (A (h * n) ^ p ^ r) ^ t [ZMOD p ^ (r + 1)] := (h4.symm.pow t).mul_left _
    _ = A (h * n) ^ m := by rw [hm', pow_add, pow_one, pow_mul]

end Conj6

/-! ### The counterexample to conjecture 6) (Theorem 2) -/

section Counterexample
open Hur

lemma totient_five_six : (5 ^ 6 : ℕ).totient = 12500 := by
  rw [Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num

lemma pow_of_not_five_dvd {u : ℕ} (hu : ¬ 5 ∣ u) :
    (u : ZMod (5 ^ 6)) ^ 12505 = (u : ZMod (5 ^ 6)) ^ 5 := by
  have hcop : Nat.Coprime u (5 ^ 6) :=
    Nat.Coprime.pow_right 6 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num)).2 hu))
  have hu1 := ZMod.pow_totient (ZMod.unitOfCoprime u hcop)
  have h1 : (u : ZMod (5 ^ 6)) ^ 12500 = 1 := by
    have := congrArg Units.val hu1
    rwa [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one,
      totient_five_six] at this
  rw [show 12505 = 5 + 12500 by norm_num, pow_add, h1, mul_one]

lemma pow_five_mul (v : ℕ) : ((5 * v : ℕ) : ZMod (5 ^ 6)) ^ 12505 = 0 := by
  have h0 : (5 : ZMod (5 ^ 6)) ^ 6 = 0 := by
    rw [show (5 : ZMod (5 ^ 6)) ^ 6 = ((5 ^ 6 : ℕ) : ZMod (5 ^ 6)) by push_cast; ring,
      ZMod.natCast_self]
  have h1 : (5 : ZMod (5 ^ 6)) ^ 12505 = 0 := by
    rw [show 12505 = 6 + 12499 by norm_num, pow_add, h0, zero_mul]
  rw [Nat.cast_mul, Nat.cast_ofNat, mul_pow, h1, zero_mul]

lemma sum_range_five_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (Y : ℕ) :
    ∑ x ∈ Finset.range (5 * Y), f x =
      ∑ y ∈ Finset.range Y, ∑ r ∈ Finset.range 5, f (5 * y + r) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [show 5 * (Y + 1) = 5 * Y + 5 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ _ Y]

/-- The summand of $4 (G_{12505} - G_5)$ in the alternating-sum formula modulo $5^6$. -/
noncomputable def termT (x : ℕ) : ZMod (5 ^ 6) :=
  (-1) ^ x * ((((5 + 6 * x : ℕ) : ZMod (5 ^ 6)) ^ 12505 - ((1 + 6 * x : ℕ) : ZMod (5 ^ 6)) ^ 12505)
    - (((5 + 6 * x : ℕ) : ZMod (5 ^ 6)) ^ 5 - ((1 + 6 * x : ℕ) : ZMod (5 ^ 6)) ^ 5))

lemma neg_one_pow_five_mul (y r : ℕ) :
    (-1 : ZMod (5 ^ 6)) ^ (5 * y + r) = (-1) ^ y * (-1) ^ r := by
  rw [pow_add, pow_mul]
  norm_num

/-- In each block of five consecutive $x$, only the bases divisible by $5$ survive:
$5 + 6 \cdot 5y = 5(1 + 6y)$ and $1 + 6(5y + 4) = 5(5 + 6y)$. -/
lemma block_sum (y : ℕ) : ∑ r ∈ Finset.range 5, termT (5 * y + r) =
    5 ^ 5 * ((-1) ^ y * (((5 + 6 * y : ℕ) : ZMod (5 ^ 6)) ^ 5 -
      ((1 + 6 * y : ℕ) : ZMod (5 ^ 6)) ^ 5)) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, termT,
    neg_one_pow_five_mul]
  rw [show 5 + 6 * (5 * y + 0) = 5 * (1 + 6 * y) by ring, pow_five_mul,
    pow_of_not_five_dvd (by omega : ¬ 5 ∣ 1 + 6 * (5 * y + 0)),
    pow_of_not_five_dvd (by omega : ¬ 5 ∣ 5 + 6 * (5 * y + 1)),
    pow_of_not_five_dvd (by omega : ¬ 5 ∣ 1 + 6 * (5 * y + 1)),
    pow_of_not_five_dvd (by omega : ¬ 5 ∣ 5 + 6 * (5 * y + 2)),
    pow_of_not_five_dvd (by omega : ¬ 5 ∣ 1 + 6 * (5 * y + 2)),
    pow_of_not_five_dvd (by omega : ¬ 5 ∣ 5 + 6 * (5 * y + 3)),
    pow_of_not_five_dvd (by omega : ¬ 5 ∣ 1 + 6 * (5 * y + 3)),
    pow_of_not_five_dvd (by omega : ¬ 5 ∣ 5 + 6 * (5 * y + 4)),
    show 1 + 6 * (5 * y + 4) = 5 * (5 + 6 * y) by ring, pow_five_mul]
  push_cast
  ring

/-- Modulo $5^6$, $4 (G_{12505} - G_5) = 5^5 \sum_{y < 5^5} (-1)^y
\big((5 + 6y)^5 - (1 + 6y)^5\big)$. -/
lemma four_GH_diff :
    (4 : ZMod (5 ^ 6)) * ((GH ℤ).coeff 12505 : ZMod (5 ^ 6)) -
      4 * ((GH ℤ).coeff 5 : ZMod (5 ^ 6)) =
      5 ^ 5 * ∑ y ∈ Finset.range (5 ^ 5), (-1) ^ y *
        (((5 + 6 * y : ℕ) : ZMod (5 ^ 6)) ^ 5 - ((1 + 6 * y : ℕ) : ZMod (5 ^ 6)) ^ 5) := by
  have hodd6 : Odd (5 ^ 6) := ⟨7812, by norm_num⟩
  rw [four_GH_zmod (5 ^ 6) 12505 hodd6, four_GH_zmod (5 ^ 6) 5 hodd6,
    ← Finset.sum_sub_distrib]
  have e : ∀ x ∈ Finset.range (5 ^ 6), (-1 : ZMod (5 ^ 6)) ^ x *
      (((5 + 6 * x : ℕ) : ZMod (5 ^ 6)) ^ 12505 - ((1 + 6 * x : ℕ) : ZMod (5 ^ 6)) ^ 12505) -
      (-1) ^ x * (((5 + 6 * x : ℕ) : ZMod (5 ^ 6)) ^ 5 -
        ((1 + 6 * x : ℕ) : ZMod (5 ^ 6)) ^ 5) = termT x := by
    intro x _
    rw [termT]
    exact (mul_sub _ _ _).symm
  have hr : Finset.range (5 ^ 6) = Finset.range (5 * 5 ^ 5) := by norm_num
  rw [Finset.sum_congr rfl e, hr, sum_range_five_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => block_sum y

/-- The alternating sum for $P = 5^5$: $5^5 \mid 4 G_5 - T$. -/
lemma four_GH_five_dvd : (5 : ℤ) ^ 5 ∣ 4 * (GH ℤ).coeff 5 -
    ∑ y ∈ Finset.range (5 ^ 5), (-1) ^ y * ((5 + 6 * (y : ℤ)) ^ 5 - (1 + 6 * (y : ℤ)) ^ 5) := by
  have h := (four_GH_modEq (5 ^ 5) 5 ⟨1562, by norm_num⟩).symm.dvd
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- Theorem 2: $G_{12505} \equiv (1 + 5^5)\,G_5 \pmod{5^6}$. -/
theorem GH_12505 : (GH ℤ).coeff 12505 ≡ (1 + 5 ^ 5) * (GH ℤ).coeff 5 [ZMOD 5 ^ 6] := by
  set T : ℤ := ∑ y ∈ Finset.range (5 ^ 5), (-1) ^ y *
      ((5 + 6 * (y : ℤ)) ^ 5 - (1 + 6 * (y : ℤ)) ^ 5) with hT
  clear_value T
  have h5 : (5 : ℤ) ^ 5 ∣ 4 * (GH ℤ).coeff 5 - T := by
    rw [hT]
    exact four_GH_five_dvd
  have hcast : ((T : ℤ) : ZMod (5 ^ 6)) = ∑ y ∈ Finset.range (5 ^ 5), (-1) ^ y *
      (((5 + 6 * y : ℕ) : ZMod (5 ^ 6)) ^ 5 - ((1 + 6 * y : ℕ) : ZMod (5 ^ 6)) ^ 5) := by
    rw [hT]
    simp only [Int.cast_mul, Int.cast_sum, Int.cast_pow, Int.cast_sub, Int.cast_neg,
      Int.cast_one, Int.cast_add, Int.cast_ofNat, Int.cast_natCast, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  have h6 : (5 : ℤ) ^ 6 ∣ 4 * (GH ℤ).coeff 12505 - 4 * (GH ℤ).coeff 5 - 5 ^ 5 * T := by
    have h := four_GH_diff
    rw [← hcast] at h
    have h' : ((4 * (GH ℤ).coeff 12505 - 4 * (GH ℤ).coeff 5 : ℤ) : ZMod (5 ^ 6)) =
        ((5 ^ 5 * T : ℤ) : ZMod (5 ^ 6)) := by
      push_cast
      exact h
    have := ((ZMod.intCast_eq_intCast_iff _ _ _).1 h').symm.dvd
    rw [Nat.cast_pow, Nat.cast_ofNat] at this
    exact this
  obtain ⟨c, hc⟩ := h5
  have h7 : (5 : ℤ) ^ 6 ∣ 4 * ((GH ℤ).coeff 12505 - (1 + 5 ^ 5) * (GH ℤ).coeff 5) := by
    have e : 4 * ((GH ℤ).coeff 12505 - (1 + 5 ^ 5) * (GH ℤ).coeff 5) =
        (4 * (GH ℤ).coeff 12505 - 4 * (GH ℤ).coeff 5 - 5 ^ 5 * T) - 5 ^ 6 * (5 ^ 4 * c) := by
      linear_combination (-(5 : ℤ) ^ 5) * hc
    rw [e]
    exact dvd_sub h6 (dvd_mul_right _ _)
  have hc4 : IsCoprime ((5 : ℤ) ^ 6) 4 := IsCoprime.pow_left ⟨1, -1, by norm_num⟩
  exact (Int.modEq_iff_dvd.2 (hc4.dvd_of_dvd_mul_left h7)).symm

/-- $a(6252) \equiv (1 + 5^5)\,a(2) \pmod{5^6}$. -/
theorem A_6252 : A 6252 ≡ (1 + 5 ^ 5) * A 2 [ZMOD 5 ^ 6] := by
  rw [A_eq_GH, A_eq_GH, show 2 * 6252 + 1 = 12505 by norm_num, show 2 * 2 + 1 = 5 by norm_num,
    show (-1 : ℤ) ^ 6252 = 1 by norm_num, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_mul, one_mul]
  exact GH_12505

/-- $1681^{3126} \equiv 1681 \pmod{5^6}$, since $1681 \equiv 1 \pmod 5$. -/
lemma pow_3126 : (1681 : ℤ) ^ 3126 ≡ 1681 [ZMOD 5 ^ 6] := by
  have h := dvd_sub_pow_of_dvd_sub (R := ℤ) (p := 5) (a := 1681) (b := 1) (by norm_num) 5
  rw [one_pow] at h
  have key : ∀ z : ℤ, z ^ 3126 - z = z * (z ^ 5 ^ 5 - 1) := fun z => by ring
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd, key]
  exact Dvd.dvd.mul_left (by exact_mod_cast h) _

/-- If $z \equiv 5^5 \cdot 1681 \pmod{5^6}$, then $v_5(z) = 5$. -/
lemma padicValInt_five_eq {z : ℤ} (hz : z ≡ 5 ^ 5 * 1681 [ZMOD 5 ^ 6]) :
    padicValInt 5 z = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.1 hz.symm
  have hz' : z = 5 ^ 5 * 1681 + 5 ^ 6 * c := by linear_combination hc
  have hd5 : (5 : ℤ) ^ 5 ∣ z := by
    rw [hz']
    exact dvd_add (dvd_mul_right _ _) ⟨5 * c, by ring⟩
  have hd6 : ¬ (5 : ℤ) ^ 6 ∣ z := by
    rw [hz']
    intro h
    have h' : (5 : ℤ) ^ 6 ∣ 5 ^ 5 * 1681 := (dvd_add_left ⟨c, rfl⟩).1 h
    norm_num at h'
  have hne : z ≠ 0 := fun h0 => hd6 (by rw [h0]; exact dvd_zero _)
  have hle := ((padicValInt_dvd_iff (p := 5) 5 z).1 (by exact_mod_cast hd5)).resolve_left hne
  have hlt : ¬ 6 ≤ padicValInt 5 z := fun h6 =>
    hd6 (by exact_mod_cast (padicValInt_dvd_iff (p := 5) 6 z).2 (Or.inr h6))
  omega

/-- $v_5(a(6252) - a(2)^{3126}) = 5$. -/
theorem A_6252_val : padicValInt 5 (A 6252 - A 2 ^ 3126) = 5 := by
  apply padicValInt_five_eq
  have h1 := A_6252
  rw [A_small.2.2.1] at h1 ⊢
  calc A 6252 - 1681 ^ 3126 ≡ (1 + 5 ^ 5) * 1681 - 1681 [ZMOD 5 ^ 6] := h1.sub pow_3126
    _ = 5 ^ 5 * 1681 := by ring

/-- Theorem 2: conjecture 6) fails at $p = 5$, $n = 1$, $m = 3126$. -/
theorem A_not_conj6 : ¬ ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n →
    A ((p - 1) / 2 * n * m) ≡ A ((p - 1) / 2 * n) ^ m
      [ZMOD p ^ ((m - 1).factorization p + 1)] := by
  intro h
  have h1 := h 5 3126 1 (by norm_num) le_rfl (by norm_num) le_rfl
  have hf : (3126 - 1).factorization 5 = 5 := by
    rw [show 3126 - 1 = 5 ^ 5 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self (by norm_num), smul_eq_mul, mul_one]
  rw [hf, show (5 - 1) / 2 * 1 * 3126 = 6252 by norm_num,
    show (5 - 1) / 2 * 1 = 2 by norm_num] at h1
  have hv := A_6252_val
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases (padicValInt_dvd_iff (p := 5) (5 + 1) (A 6252 - A 2 ^ 3126)).1
    (Int.ModEq.dvd h1.symm) with h0 | h6
  · rw [h0] at hv
    simp at hv
  · omega

end Counterexample

section Thm1
open Hur

/-! ### Newton coefficients of $b(n) = a(n)/23^n$ -/

section Newton
open Hur

/-- $f_k = \sum_i \binom{k}{i} (-23)^{k-i} a(i)$, so $f_k / 23^k$ is the $k$-th Newton
coefficient of $b(n) = a(n)/23^n$. -/
def fk (k : ℕ) : ℤ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℤ) * (-23) ^ (k - i) * A i

/-- The polynomial $R_k(u) = u\,(-u^2 - 23)^k$, with $f_k = \Phi(R_k)$ for the functional
$\Phi(u^M) = G_M$. -/
def Rk (k : ℕ) (z : ℤ) : ℤ := z * (-z ^ 2 - 23) ^ k

lemma Rk_eq (k : ℕ) (z : ℤ) : Rk k z = ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℤ) * (-23) ^ (k - i) * (-1) ^ i * z ^ (2 * i + 1) := by
  rw [Rk, sub_eq_add_neg, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show -z ^ 2 = (-1) * z ^ 2 by ring, mul_pow, ← pow_mul]
  ring

lemma fk_eq (k : ℕ) : fk k = ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℤ) * (-23) ^ (k - i) * (-1) ^ i * (GH ℤ).coeff (2 * i + 1) := by
  rw [fk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [A_eq_GH]
  ring

/-- Transfer of a representation $c\,G_M \equiv \sum_x \mu_x (u_x^M - v_x^M) \pmod P$ for odd
$M \le 2k + 1$ to $c\,f_k \equiv \sum_x \mu_x (R_k(u_x) - R_k(v_x)) \pmod P$. -/
lemma fk_transfer {c P : ℤ} (s : Finset ℕ) (μ u v : ℕ → ℤ) (k : ℕ)
    (h : ∀ i ≤ k, P ∣ c * (GH ℤ).coeff (2 * i + 1) -
      ∑ x ∈ s, μ x * (u x ^ (2 * i + 1) - v x ^ (2 * i + 1))) :
    P ∣ c * fk k - ∑ x ∈ s, μ x * (Rk k (u x) - Rk k (v x)) := by
  have h1 : ∑ x ∈ s, μ x * (Rk k (u x) - Rk k (v x)) =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℤ) * (-23) ^ (k - i) * (-1) ^ i *
        ∑ x ∈ s, μ x * (u x ^ (2 * i + 1) - v x ^ (2 * i + 1)) := by
    simp only [Rk_eq, ← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  have e : c * fk k - ∑ x ∈ s, μ x * (Rk k (u x) - Rk k (v x)) =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℤ) * (-23) ^ (k - i) * (-1) ^ i *
        (c * (GH ℤ).coeff (2 * i + 1) -
          ∑ x ∈ s, μ x * (u x ^ (2 * i + 1) - v x ^ (2 * i + 1))) := by
    rw [h1, fk_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  exact Finset.dvd_sum fun i hi =>
    Dvd.dvd.mul_left (h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) _

lemma fk_zero : fk 0 = 1 := by simp [fk, A_small.1]

lemma fk_one : fk 1 = 0 := by
  obtain ⟨h0, h1, -, -⟩ := A_small
  simp [fk, Finset.sum_range_succ, h0, h1]

lemma fk_two : fk 2 = 1152 := by
  obtain ⟨h0, h1, h2, -⟩ := A_small
  simp [fk, Finset.sum_range_succ, h0, h1, h2]

end Newton

/-! ### The 2-adic representation of $G$ -/

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

end Kallat


lemma InK.sub {R : Type*} [CommRing R] {F G : Hur R} (hF : InK F) (hG : InK G) :
    InK (F - G) := by
  rw [sub_eq_add_neg, show -G = C (-1) * G by rw [C_neg, C_one, neg_one_mul]]
  exact hF.add ((inK_C _).mul hG)

lemma inK_one {R : Type*} [CommRing R] : InK (1 : Hur R) := by
  rw [← C_one]
  exact inK_C 1

/-- $\Psi$ agrees, up to every index, with a polynomial in $e^x$. -/
lemma inK_PsiH : InK PsiH := by
  have h1 : InK (ex (1 : ℤ) - 1) := inK_ex_one.sub inK_one
  have h2 : InK (ex (2 : ℤ) - ex 1 + 1) := by
    rw [ex_two_eq]
    exact ((inK_ex_one.pow 2).sub inK_ex_one).add inK_one
  exact h1.mul (InK.inv h2 Bq_coeff_zero (by rw [mul_comm]; exact mul_hinv Bq_coeff_zero))

/-- Lemma 1 (2-adic representation): for every $N$ there are integers $Q_i$ with
$2 G_M = \sum_i Q_i (2i + 1)^M$ for all $M \le N$. -/
lemma two_GH_repr (N : ℕ) : ∃ (D : ℕ) (Q : ℕ → ℤ), ∀ M ≤ N,
    2 * (GH ℤ).coeff M = ∑ i ∈ Finset.range D, Q i * ((2 * i + 1 : ℕ) : ℤ) ^ M := by
  obtain ⟨P, hP⟩ := inK_PsiH N
  set Q := P.comp (Polynomial.X - 1)
  refine ⟨Q.natDegree + 1, fun i => Q.coeff i, fun M hM => ?_⟩
  have hΨ : ∀ j ∈ Finset.range (M + 1), (M.choose j : ℤ) * (2 ^ j * PsiH.coeff j) =
      (M.choose j : ℤ) * (2 ^ j * ∑ i ∈ Finset.range (Q.natDegree + 1),
        Q.coeff i * (i : ℤ) ^ j) := by
    intro j hj
    have hj' : j ≤ N := by have := Finset.mem_range.1 hj; omega
    rw [hP j hj', ev_uH, coeff_ev_ex]
  rw [two_GH_coeff, Finset.sum_congr rfl hΨ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((2 * i + 1 : ℕ) : ℤ) = 2 * (i : ℤ) + 1 by push_cast; ring, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, mul_pow]
  ring

end HurSections

section Bounds

lemma eight_dvd (x : ℕ) : (2 : ℤ) ^ 3 ∣ -((2 * x + 1 : ℕ) : ℤ) ^ 2 - 23 := by
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self (x : ℤ)
  exact ⟨-(r + 3), by push_cast; linear_combination (-4) * hr⟩

/-- Lemma 4: $2^{3k} \mid 2 f_k$, so $v_2(e_k) \ge 3k - 1$. -/
lemma two_pow_dvd_two_fk (k : ℕ) : (2 : ℤ) ^ (3 * k) ∣ 2 * fk k := by
  obtain ⟨D, Q, hQ⟩ := two_GH_repr (2 * k + 1)
  have h := fk_transfer (c := 2) (P := 0) (Finset.range D) Q (fun x => ((2 * x + 1 : ℕ) : ℤ))
    (fun _ => 0) k (fun i hi => by rw [hQ (2 * i + 1) (by omega)]; simp)
  beta_reduce at h
  rw [zero_dvd_iff, sub_eq_zero] at h
  rw [h]
  refine Finset.dvd_sum fun x _ => Dvd.dvd.mul_left ?_ _
  have h0 : Rk k 0 = 0 := by simp [Rk]
  rw [h0, sub_zero, Rk, pow_mul]
  exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (eight_dvd x) k) _

lemma two_pow_dvd_fk {k : ℕ} (hk : 1 ≤ k) : (2 : ℤ) ^ (3 * k - 1) ∣ fk k := by
  have h1 := two_pow_dvd_two_fk k
  rw [show (2 : ℤ) ^ (3 * k) = 2 * 2 ^ (3 * k - 1) by rw [← pow_succ']; congr 1; omega] at h1
  exact (mul_dvd_mul_iff_left two_ne_zero).1 h1

/-- Lemma 5: $3^k \mid f_k$. -/
lemma three_pow_dvd_fk (k : ℕ) : (3 : ℤ) ^ k ∣ fk k := by
  have hodd : Odd (3 ^ k) := Odd.pow ⟨1, rfl⟩
  have h := fk_transfer (c := 4) (P := (3 : ℤ) ^ k) (Finset.range (3 ^ k)) (fun x => (-1) ^ x)
    (fun x => 5 + 6 * (x : ℤ)) (fun x => 1 + 6 * (x : ℤ)) k
    (fun i _ => by
      have := (four_GH_modEq (3 ^ k) (2 * i + 1) hodd).symm.dvd
      push_cast at this
      exact this)
  beta_reduce at h
  have hR : ∀ z : ℤ, (3 : ℤ) ∣ -z ^ 2 - 23 → (3 : ℤ) ^ k ∣ Rk k z := fun z hz =>
    Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hz k) _
  have hS : (3 : ℤ) ^ k ∣ ∑ x ∈ Finset.range (3 ^ k),
      (-1) ^ x * (Rk k (5 + 6 * (x : ℤ)) - Rk k (1 + 6 * (x : ℤ))) :=
    Finset.dvd_sum fun x _ => Dvd.dvd.mul_left (dvd_sub
      (hR _ ⟨-(4 + 5 * (x : ℤ) + 3 * (x : ℤ) ^ 2) * 4, by ring⟩)
      (hR _ ⟨-(2 + (x : ℤ) + 3 * (x : ℤ) ^ 2) * 4, by ring⟩)) _
  have h4 : (3 : ℤ) ^ k ∣ 4 * fk k := by
    have := dvd_add h hS
    rwa [sub_add_cancel] at this
  have hc : IsCoprime ((3 : ℤ) ^ k) 4 := IsCoprime.pow_left ⟨-1, 1, by norm_num⟩
  exact hc.dvd_of_dvd_mul_left h4

end Bounds

/-! ### Forward differences -/

section FwdDiff
open fwdDiff

variable {R : Type*} [CommRing R]

lemma iter_const (c : R) {l : ℕ} (hl : 1 ≤ l) :
    (fwdDiff 1)^[l] (fun _ : ℕ => c) = fun _ => 0 := by
  obtain ⟨l, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Function.iterate_succ_apply, fwdDiff_const]
  exact Function.iterate_fixed (fwdDiff_const 1 (0 : R)) l

lemma iter_succ_apply (F : ℕ → R) (k n : ℕ) :
    (fwdDiff 1)^[k + 1] F n = (fwdDiff 1)^[k] F (n + 1) - (fwdDiff 1)^[k] F n := by
  rw [Function.iterate_succ_apply']
  rfl

/-- The Leibniz rule $\Delta^l (fg)(n) = \sum_a \binom{l}{a} \Delta^a f(n)\,
\Delta^{l-a} g(n + a)$. -/
lemma fwdDiff_iter_mul (f g : ℕ → R) (l : ℕ) : ∀ n, (fwdDiff 1)^[l] (f * g) n =
    ∑ a ∈ Finset.range (l + 1),
      (l.choose a : R) * ((fwdDiff 1)^[a] f n * (fwdDiff 1)^[l - a] g (n + a)) := by
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

/-- If $\pi^{s j + c}$ divides every Newton coefficient of $E$, then $\pi^{s l + c r}$ divides
the $l$-th Newton coefficient of $E^r$. -/
lemma pow_dvd_iter_pow (E : ℕ → R) (π : R) (s c : ℕ)
    (hE : ∀ j, π ^ (s * j + c) ∣ (fwdDiff 1)^[j] E 0) (r : ℕ) :
    ∀ l, π ^ (s * l + c * r) ∣ (fwdDiff 1)^[l] (fun n => E n ^ r) 0 := by
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
    have hfun : (fun n => E n ^ (r + 1)) = (fun n => E n ^ r) * E := by
      funext n
      simp [pow_succ]
    rw [hfun, fwdDiff_iter_mul]
    refine Finset.dvd_sum fun a ha => ?_
    have hal : a ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have hN := shift_eq_sum_fwdDiff_iter 1 ((fwdDiff 1)^[l - a] E) a 0
    simp only [zero_add, smul_eq_mul, mul_one] at hN
    rw [zero_add, hN]
    apply Dvd.dvd.mul_left
    rw [Finset.mul_sum]
    refine Finset.dvd_sum fun c' _ => ?_
    rw [← Function.iterate_add_apply, nsmul_eq_mul]
    have h1 := ih a
    have h2 := hE (c' + (l - a))
    have e1 : s * l = s * a + s * (l - a) := by rw [← mul_add, Nat.add_sub_cancel' hal]
    have e2 : s * (c' + (l - a)) = s * c' + s * (l - a) := mul_add _ _ _
    have e3 : c * (r + 1) = c * r + c := by ring
    have h3 : π ^ (s * l + c * (r + 1)) ∣ π ^ (s * a + c * r) * π ^ (s * (c' + (l - a)) + c) := by
      rw [← pow_add]
      exact pow_dvd_pow π (by omega)
    exact h3.trans (mul_dvd_mul h1 (Dvd.dvd.mul_left h2 _))

/-- The Newton expansion of $F(xy) - y F(x)$ for $F(0) = 1$. -/
lemma newton_sub (F : ℕ → R) (hF0 : F 0 = 1) (x y : ℕ) (hy : 1 ≤ y) :
    F (x * y) - y * F x - (1 - y) = ∑ l ∈ Finset.range (x * y),
      ((((x * y).choose (l + 1) : ℤ) - y * (x.choose (l + 1) : ℤ) : ℤ) : R) *
        (fwdDiff 1)^[l + 1] F 0 := by
  have hNewt : ∀ n, F n = ∑ l ∈ Finset.range (n + 1),
      (n.choose l : R) * (fwdDiff 1)^[l] F 0 := by
    intro n
    have h := shift_eq_sum_fwdDiff_iter 1 F n 0
    simp only [zero_add, smul_eq_mul, mul_one] at h
    rw [h]
    simp only [nsmul_eq_mul]
  have hB0 : (fwdDiff 1)^[0] F 0 = 1 := by simp [hF0]
  have hxy : x ≤ x * y := Nat.le_mul_of_pos_right x hy
  have hBx : F x =
      ∑ l ∈ Finset.range (x * y + 1), (x.choose l : R) * (fwdDiff 1)^[l] F 0 := by
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
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [add_sub_assoc, show (1 : R) - y - (1 - y) = 0 by ring, add_zero]
  refine Finset.sum_congr rfl fun l _ => ?_
  push_cast
  ring

lemma one_add_pow_sub_dvd (z : R) (y : ℕ) : z ^ 2 ∣ (1 + z) ^ y - 1 - y * z := by
  induction y with
  | zero => simp
  | succ y ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(1 + z) * c + y, ?_⟩
    push_cast
    linear_combination (1 + z) * hc

end FwdDiff

/-! ### The $p$-adic integers -/

section Padic
open fwdDiff

variable {p : ℕ} [Fact p.Prime]

lemma isUnit_of_not_dvd {x : ℤ_[p]} (h : ¬ (p : ℤ_[p]) ∣ x) : IsUnit x := by
  rw [PadicInt.isUnit_iff]
  exact le_antisymm (PadicInt.norm_le_one x)
    (not_lt.1 fun hlt => h ((PadicInt.norm_lt_one_iff_dvd x).1 hlt))

lemma isUnit_intCast_of_not_dvd {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : IsUnit (z : ℤ_[p]) := by
  apply isUnit_of_not_dvd
  intro h
  have := (PadicInt.pow_p_dvd_int_iff (p := p) 1 z).1 (by simpa using h)
  exact hz (by simpa using this)

lemma int_dvd_of_padic {K : ℕ} {z : ℤ} (h : (p : ℤ_[p]) ^ K ∣ (z : ℤ_[p])) :
    (p : ℤ) ^ K ∣ z :=
  (PadicInt.pow_p_dvd_int_iff K z).1 h

lemma padic_dvd_of_int {K : ℕ} {z : ℤ} (h : (p : ℤ) ^ K ∣ z) :
    (p : ℤ_[p]) ^ K ∣ (z : ℤ_[p]) :=
  (PadicInt.pow_p_dvd_int_iff K z).2 h

variable (p) in
/-- The inverse of $23$ in $\mathbb{Z}_p$ (for $p \ne 23$). -/
noncomputable def uInv : ℤ_[p] := Ring.inverse (23 : ℤ_[p])

variable (p) in
/-- $b(n) = a(n) / 23^n$ in $\mathbb{Z}_p$. -/
noncomputable def bZ (n : ℕ) : ℤ_[p] := (A n : ℤ_[p]) * uInv p ^ n

variable (p) in
/-- $E(n) = b(n) - 1$. -/
noncomputable def EZ (n : ℕ) : ℤ_[p] := bZ p n - 1

lemma bZ_zero : bZ p 0 = 1 := by simp [bZ, A_small.1]

lemma iter_EZ_zero : (fwdDiff 1)^[0] (EZ p) 0 = 0 := by
  simp [EZ, bZ_zero]

/-- A bound on all Newton coefficients of $E$ gives the same bound for every $E(n)$. -/
lemma dvd_EZ {π : ℤ_[p]} {s : ℕ} (h : ∀ j, π ^ s ∣ (fwdDiff 1)^[j] (EZ p) 0) (n : ℕ) :
    π ^ s ∣ EZ p n := by
  have hN := shift_eq_sum_fwdDiff_iter 1 (EZ p) n 0
  simp only [zero_add, smul_eq_mul, mul_one] at hN
  rw [hN]
  exact Finset.dvd_sum fun j _ => by rw [nsmul_eq_mul]; exact Dvd.dvd.mul_left (h j) _


section Unit
variable (h23 : IsUnit (23 : ℤ_[p]))
include h23

lemma mul_uInv : (23 : ℤ_[p]) * uInv p = 1 := Ring.mul_inverse_cancel _ h23

lemma A_eq_bZ (n : ℕ) : (A n : ℤ_[p]) = 23 ^ n * bZ p n := by
  have h : (23 : ℤ_[p]) ^ n * uInv p ^ n = 1 := by rw [← mul_pow, mul_uInv h23, one_pow]
  rw [bZ]
  linear_combination (-(A n : ℤ_[p])) * h

/-- The Newton coefficients of $b$: $\Delta^k b(0) = f_k / 23^k$. -/
lemma iter_bZ (k : ℕ) : (fwdDiff 1)^[k] (bZ p) 0 = uInv p ^ k * (fk k : ℤ_[p]) := by
  rw [fwdDiff_iter_eq_sum_shift, fk]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : uInv p ^ k = uInv p ^ (k - i) * uInv p ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hik]
  have h2 : (23 : ℤ_[p]) ^ (k - i) * uInv p ^ (k - i) = 1 := by
    rw [← mul_pow, mul_uInv h23, one_pow]
  rw [zsmul_eq_mul, zero_add, smul_eq_mul, mul_one, bZ, h1]
  push_cast
  rw [neg_pow (23 : ℤ_[p])]
  linear_combination (-((k.choose i : ℤ_[p]) * A i * uInv p ^ i * (-1) ^ (k - i))) * h2

lemma iter_EZ_one : (fwdDiff 1)^[1] (EZ p) 0 = 0 := by
  simp [EZ, bZ, fwdDiff, A_small.1, A_small.2.1, mul_uInv h23]

lemma iter_EZ_high {j : ℕ} (hj : 2 ≤ j) :
    (fwdDiff 1)^[j] (EZ p) 0 = uInv p ^ j * (fk j : ℤ_[p]) := by
  have hE : EZ p = bZ p + fun _ => -1 := by
    funext n
    simp [EZ, sub_eq_add_neg]
  rw [hE, fwdDiff_iter_add, Pi.add_apply, iter_bZ h23, iter_const _ (by omega), add_zero]

/-- $a(xy) - a(x)^y = 23^{xy} (b(xy) - b(x)^y)$. -/
lemma A_sub_eq (x y : ℕ) : ((A (x * y) - A x ^ y : ℤ) : ℤ_[p]) =
    23 ^ (x * y) * (bZ p (x * y) - bZ p x ^ y) := by
  push_cast
  rw [A_eq_bZ h23, A_eq_bZ h23, mul_pow, ← pow_mul]
  ring

/-- $a(n) - 23^n = 23^n E(n)$. -/
lemma A_sub_pow_eq (n : ℕ) : ((A n - 23 ^ n : ℤ) : ℤ_[p]) = 23 ^ n * EZ p n := by
  push_cast
  rw [A_eq_bZ h23, EZ]
  ring

end Unit

/-- $p^N \mid \binom{p^N}{r} p^{v_p(r)}$ for $r \ge 1$. -/
lemma pow_dvd_choose_mul_pow (N r : ℕ) (hr : 1 ≤ r) :
    p ^ N ∣ (p ^ N).choose r * p ^ r.factorization p := by
  have hp := (Fact.out : p.Prime)
  have h1 : p ^ N ∣ (p ^ N).choose r * r := by
    have := Nat.add_one_mul_choose_eq (p ^ N - 1) (r - 1)
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos), Nat.sub_add_cancel hr] at this
    exact ⟨_, this.symm⟩
  have e : (p ^ N).choose r * r =
      (p ^ N).choose r * p ^ r.factorization p * (r / p ^ r.factorization p) := by
    rw [mul_assoc, Nat.ordProj_mul_ordCompl_eq_self]
  rw [e] at h1
  have hcop : Nat.Coprime (p ^ N) (r / p ^ r.factorization p) :=
    Nat.Coprime.pow_left N ((Nat.Prime.coprime_iff_not_dvd hp).2
      (Nat.not_dvd_ordCompl hp (by omega)))
  exact hcop.dvd_of_dvd_mul_right h1

/-- One binomial term of $b^{p^N} = \sum_r \binom{p^N}{r} E^r$. -/
lemma pow_dvd_choose_mul (N r : ℕ) (hr : 1 ≤ r) {x : ℤ_[p]} {β γ : ℕ}
    (hx : (p : ℤ_[p]) ^ β ∣ x) (hβ : ∀ v, v + 1 ≤ r → v + γ ≤ β) :
    (p : ℤ_[p]) ^ (N + γ) ∣ ((p ^ N).choose r : ℤ_[p]) * x := by
  have hp := (Fact.out : p.Prime)
  have hv : r.factorization p + 1 ≤ r := by
    have h1 : r.factorization p < p ^ r.factorization p := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ r.factorization p ≤ r := Nat.ordProj_le p (by omega)
    omega
  obtain ⟨d, hd⟩ : ∃ d, β = r.factorization p + γ + d :=
    ⟨β - r.factorization p - γ, by have := hβ _ hv; omega⟩
  obtain ⟨s, hs⟩ := pow_dvd_choose_mul_pow (p := p) N r hr
  have hs' : ((p ^ N).choose r : ℤ_[p]) * (p : ℤ_[p]) ^ r.factorization p =
      (p : ℤ_[p]) ^ N * s := by
    exact_mod_cast hs
  obtain ⟨t, rfl⟩ := hx
  refine ⟨s * (p : ℤ_[p]) ^ d * t, ?_⟩
  rw [hd, pow_add (p : ℤ_[p]) (r.factorization p + γ) d,
    pow_add (p : ℤ_[p]) (r.factorization p) γ, pow_add (p : ℤ_[p]) N γ]
  linear_combination ((p : ℤ_[p]) ^ γ * (p : ℤ_[p]) ^ d * t) * hs'

/-- The Newton coefficients of $F^{p^N}$, from bounds for those of $(F - 1)^r$. -/
lemma iter_pow_dvd (F : ℕ → ℤ_[p]) (N l γ : ℕ) (hl : 1 ≤ l)
    (hE : ∀ r, 1 ≤ r → ∃ β, (∀ v, v + 1 ≤ r → v + γ ≤ β) ∧
      (p : ℤ_[p]) ^ β ∣ (fwdDiff 1)^[l] (fun n => (F n - 1) ^ r) 0) :
    (p : ℤ_[p]) ^ (N + γ) ∣ (fwdDiff 1)^[l] (fun n => F n ^ (p ^ N)) 0 := by
  have hfun : (fun n => F n ^ (p ^ N)) =
      ∑ r ∈ Finset.range (p ^ N + 1), ((p ^ N).choose r) • (fun n => (F n - 1) ^ r) := by
    funext n
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    have e : F n ^ (p ^ N) = ((F n - 1) + 1) ^ (p ^ N) := by rw [sub_add_cancel]
    rw [e, add_pow]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [one_pow, mul_one, nsmul_eq_mul, mul_comm]
  rw [hfun, fwdDiff_iter_finsetSum, Finset.sum_apply]
  refine Finset.dvd_sum fun r _ => ?_
  rw [fwdDiff_iter_const_smul, Pi.smul_apply, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp only [pow_zero]
    rw [iter_const 1 hl]
    simp
  · obtain ⟨β, hβ, hdvd⟩ := hE r hr0
    exact pow_dvd_choose_mul N r hr0 hdvd hβ

/-- One term of the Newton expansion: if $p^K \mid (l+1)!\,P$ and
$p^{M + \lfloor l/(p-1) \rfloor} \mid \beta$, then $p^{K + M} \mid P \beta$, because
$(p - 1)\, v_p((l+1)!) \le l$. -/
lemma term_dvd (K M l : ℕ) (P : ℤ) (β : ℤ_[p])
    (hP : (p : ℤ) ^ K ∣ ((l + 1).factorial : ℤ) * P)
    (hβ : (p : ℤ_[p]) ^ (M + l / (p - 1)) ∣ β) : (p : ℤ_[p]) ^ (K + M) ∣ (P : ℤ_[p]) * β := by
  have hp := (Fact.out : p.Prime)
  have h1 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : l + 1 ≠ 0)
  rw [← Nat.factorization_def _ hp] at h1
  have hwo := Nat.ordProj_mul_ordCompl_eq_self (l + 1).factorial p
  have hnd := Nat.not_dvd_ordCompl hp (Nat.factorial_ne_zero (l + 1))
  generalize hwdef : (l + 1).factorial.factorization p = w at h1 hwo hnd
  generalize hodef : (l + 1).factorial / p ^ w = o at hwo hnd
  have hw : w ≤ l / (p - 1) := by
    have := hp.two_le
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
    omega
  have hcop : IsCoprime ((p : ℤ) ^ K) (o : ℤ) := by
    apply IsCoprime.pow_left
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  have h2P : (p : ℤ) ^ K ∣ (p : ℤ) ^ w * P := by
    rw [← hwo] at hP
    push_cast at hP
    have e : (p : ℤ) ^ w * (o : ℤ) * P = (p : ℤ) ^ w * P * o := by ring
    rw [e] at hP
    exact hcop.dvd_of_dvd_mul_right hP
  obtain ⟨c, hc⟩ := h2P
  obtain ⟨t, ht⟩ := hβ
  have hc' : (p : ℤ_[p]) ^ w * P = (p : ℤ_[p]) ^ K * c := by exact_mod_cast hc
  refine ⟨c * (p : ℤ_[p]) ^ (l / (p - 1) - w) * t, ?_⟩
  have e : (p : ℤ_[p]) ^ (M + l / (p - 1)) = (p : ℤ_[p]) ^ w * (p : ℤ_[p]) ^ M *
      (p : ℤ_[p]) ^ (l / (p - 1) - w) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [ht, e, pow_add (p : ℤ_[p]) K M]
  linear_combination ((p : ℤ_[p]) ^ M * (p : ℤ_[p]) ^ (l / (p - 1) - w) * t) * hc'

/-! #### The polynomial divisibility (from OeisA000464) -/

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

/-- The common core of the power congruences: if $F(0) = 1$, $p^K \mid x^2 y (y - 1)$, the
Newton coefficients $\Delta^{l+1} F(0)$ are divisible by $p^{M + \lfloor l/(p-1) \rfloor}$, and
$p^s \mid F(x) - 1$ with $K + M \le 2s$, then $p^{K+M} \mid F(xy) - F(x)^y$. -/
lemma pow_core (F : ℕ → ℤ_[p]) (hF0 : F 0 = 1) (x y K M s : ℕ) (hy : 1 ≤ y)
    (hK : p ^ K ∣ x ^ 2 * y * (y - 1))
    (hB : ∀ l, (p : ℤ_[p]) ^ (M + l / (p - 1)) ∣ (fwdDiff 1)^[l + 1] F 0)
    (hz : (p : ℤ_[p]) ^ s ∣ F x - 1) (hs : K + M ≤ 2 * s) :
    (p : ℤ_[p]) ^ (K + M) ∣ F (x * y) - F x ^ y := by
  have hterm : (p : ℤ_[p]) ^ (K + M) ∣ F (x * y) - y * F x - (1 - y) := by
    rw [newton_sub F hF0 x y hy]
    refine Finset.dvd_sum fun l _ => ?_
    apply term_dvd K M l
    · have h1 := dvd_factorial_mul_choose_sub x y (l + 1) (by omega)
      have h2 : (p : ℤ) ^ K ∣ (x : ℤ) ^ 2 * y * (y - 1) := by
        have := Int.natCast_dvd_natCast.2 hK
        push_cast [Nat.cast_sub hy] at this
        exact this
      exact h2.trans h1
    · exact hB l
  have hpow : (p : ℤ_[p]) ^ (K + M) ∣ F x ^ y - 1 - y * (F x - 1) := by
    have h1 := one_add_pow_sub_dvd (F x - 1) y
    rw [add_sub_cancel] at h1
    have h2 : (p : ℤ_[p]) ^ (K + M) ∣ (F x - 1) ^ 2 := by
      have := pow_dvd_pow_of_dvd hz 2
      rw [← pow_mul] at this
      exact (pow_dvd_pow _ (by omega)).trans this
    exact h2.trans h1
  have e : F (x * y) - F x ^ y =
      (F (x * y) - y * F x - (1 - y)) - (F x ^ y - 1 - y * (F x - 1)) := by ring
  rw [e]
  exact dvd_sub hterm hpow

end Padic

/-! ### The prime $2$ -/

section TwoAdic
open fwdDiff

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


lemma two_cast : ((2 : ℕ) : ℤ_[2]) = 2 := Nat.cast_ofNat

lemma isUnit_23_two : IsUnit (23 : ℤ_[2]) := by
  have := isUnit_intCast_of_not_dvd (p := 2) (z := 23) (by norm_num)
  simpa using this

/-- $2^{j+5}$ divides the Newton coefficients of $E$: they vanish for $j \le 1$,
$f_2 = 1152 = 2^7 \cdot 9$, and $2^{3j-1} \mid f_j$ for $j \ge 3$. -/
lemma iter_EZ_two (j : ℕ) : (2 : ℤ_[2]) ^ (1 * j + 5) ∣ (fwdDiff 1)^[j] (EZ 2) 0 := by
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · rw [iter_EZ_zero]; exact dvd_zero _
    · rw [iter_EZ_one isUnit_23_two]; exact dvd_zero _
  · rw [iter_EZ_high isUnit_23_two hj]
    apply Dvd.dvd.mul_left
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · obtain rfl : j = 2 := by omega
      rw [fk_two]
      exact ⟨9, by norm_num⟩
    · have h := padic_dvd_of_int (p := 2) (K := 3 * j - 1) (z := fk j)
        (by exact_mod_cast two_pow_dvd_fk (k := j) (by omega))
      rw [two_cast] at h
      exact (pow_dvd_pow 2 (by omega)).trans h

lemma iter_EZ_two_seven (j : ℕ) : (2 : ℤ_[2]) ^ 7 ∣ (fwdDiff 1)^[j] (EZ 2) 0 := by
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · rw [iter_EZ_zero]; exact dvd_zero _
    · rw [iter_EZ_one isUnit_23_two]; exact dvd_zero _
  · exact (pow_dvd_pow 2 (by omega)).trans (iter_EZ_two j)

/-- Corollary 6 at $2$: $b(n) \equiv 1 \pmod{2^7}$. -/
lemma two_pow_seven_dvd_EZ (n : ℕ) : (2 : ℤ_[2]) ^ 7 ∣ EZ 2 n := dvd_EZ iter_EZ_two_seven n

/-- The core congruence at $2$: if $2^K \mid x^2 y (y - 1)$, then
$a(xy) \equiv a(x)^y \pmod{2^{K+6}}$. -/
theorem A_pow_core_two (x y K : ℕ) (hK : 2 ^ K ∣ x ^ 2 * y * (y - 1)) :
    (2 : ℤ) ^ (K + 6) ∣ A (x * y) - A x ^ y := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [A_small.1]
  have h23 := isUnit_23_two
  have hb7 : ∀ n, (2 : ℤ_[2]) ^ 7 ∣ bZ 2 n - 1 := two_pow_seven_dvd_EZ
  have hb4 : ∀ n, (4 : ℤ_[2]) ∣ bZ 2 n - 1 := fun n => by
    have h := (pow_dvd_pow (2 : ℤ_[2]) (by norm_num : 2 ≤ 7)).trans (hb7 n)
    norm_num at h
    exact h
  set B : ℕ → ℤ_[2] := fun m => bZ 2 m ^ (2 ^ K) with hB
  have hB0 : B 0 = 1 := by simp [hB, bZ_zero]
  have hcore := pow_core (p := 2) B hB0 x y K (K + 6) (7 + K) hy hK
    (fun l => by
      have h := iter_pow_dvd (p := 2) (bZ 2) K (l + 1) (l + 6) (by omega) (fun r _ =>
        ⟨1 * (l + 1) + 5 * r, fun v hv => by omega, by
          rw [two_cast]
          exact pow_dvd_iter_pow (EZ 2) 2 1 5 iter_EZ_two r (l + 1)⟩)
      rw [show l / (2 - 1) = l by simp, show K + 6 + l = K + (l + 6) by ring]
      exact h)
    (by
      rw [two_cast]
      exact pow_two_pow_sub_one_dvd (s := 7) (by norm_num) (hb7 x) K)
    (by omega)
  rw [two_cast] at hcore
  have hmain : (2 : ℤ_[2]) ^ ((K + 6) + K) ∣
      bZ 2 (x * y) ^ (2 ^ K) - (bZ 2 x ^ y) ^ (2 ^ K) := by
    have e : (bZ 2 x ^ y) ^ (2 ^ K) = (bZ 2 x ^ (2 ^ K)) ^ y := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e, show K + 6 + K = K + (K + 6) by ring]
    exact hcore
  have hγ : (4 : ℤ_[2]) ∣ bZ 2 x ^ y - 1 := by
    have := sub_dvd_pow_sub_pow (bZ 2 x) 1 y
    rw [one_pow] at this
    exact (hb4 x).trans this
  have hroot := dvd_sub_of_pow_dvd K (K + 6) (hb4 (x * y)) hγ hmain
  have hfin : ((2 : ℕ) : ℤ_[2]) ^ (K + 6) ∣ ((A (x * y) - A x ^ y : ℤ) : ℤ_[2]) := by
    rw [A_sub_eq h23, two_cast]
    exact Dvd.dvd.mul_left hroot _
  have := int_dvd_of_padic hfin
  exact_mod_cast this

end TwoAdic

/-! ### The prime $3$ -/

section ThreeAdic
open fwdDiff

lemma three_cast : ((3 : ℕ) : ℤ_[3]) = 3 := Nat.cast_ofNat

lemma isUnit_23_three : IsUnit (23 : ℤ_[3]) := by
  have := isUnit_intCast_of_not_dvd (p := 3) (z := 23) (by norm_num)
  simpa using this

lemma isUnit_of_not_three_dvd {x : ℤ_[3]} (h : ¬ (3 : ℤ_[3]) ∣ x) : IsUnit x :=
  isUnit_of_not_dvd (by rwa [three_cast])

lemma not_three_dvd_one_add (t : ℤ_[3]) : ¬ (3 : ℤ_[3]) ∣ 1 + 3 * t := by
  intro h
  have h1 : (3 : ℤ_[3]) ∣ 1 := by
    have := dvd_sub h (dvd_mul_right (3 : ℤ_[3]) t)
    rwa [add_sub_cancel_right] at this
  have h2 := PadicInt.p_nonunit (p := 3)
  rw [mem_nonunits_iff] at h2
  exact h2 (by rw [three_cast]; exact isUnit_of_dvd_one h1)

lemma cube_sub_one_dvd {β : ℤ_[3]} {s : ℕ} (hs : 1 ≤ s) (h : (3 : ℤ_[3]) ^ s ∣ β - 1) :
    (3 : ℤ_[3]) ^ (s + 1) ∣ β ^ 3 - 1 := by
  obtain ⟨t, ht⟩ := h
  have hb : β = 1 + 3 ^ s * t := by linear_combination ht
  have h3 : (3 : ℤ_[3]) ^ (s + 1) * 3 ^ (2 * s - 1) = (3 ^ s) ^ 3 := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  refine ⟨t + 3 ^ s * t ^ 2 + 3 ^ (2 * s - 1) * t ^ 3, ?_⟩
  rw [hb]
  linear_combination (-t ^ 3) * h3

lemma pow_three_pow_sub_one_dvd {β : ℤ_[3]} {s : ℕ} (hs : 1 ≤ s)
    (h : (3 : ℤ_[3]) ^ s ∣ β - 1) (N : ℕ) : (3 : ℤ_[3]) ^ (s + N) ∣ β ^ (3 ^ N) - 1 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    rw [show s + (N + 1) = s + N + 1 by ring, pow_succ 3 N, pow_mul]
    exact cube_sub_one_dvd (by omega) ih

/-- The cube root step: for $\beta, \gamma \equiv 1 \pmod 3$,
$\beta^3 - \gamma^3 = (\beta - \gamma) \cdot 3 \cdot \text{unit}$. -/
lemma dvd_sub_of_cube_dvd {β γ : ℤ_[3]} {s : ℕ} (hβ : (3 : ℤ_[3]) ∣ β - 1)
    (hγ : (3 : ℤ_[3]) ∣ γ - 1) (h : (3 : ℤ_[3]) ^ (s + 1) ∣ β ^ 3 - γ ^ 3) :
    (3 : ℤ_[3]) ^ s ∣ β - γ := by
  obtain ⟨t1, h1⟩ := hβ
  obtain ⟨t2, h2⟩ := hγ
  have hu := isUnit_of_not_three_dvd
    (not_three_dvd_one_add (t1 + t2 + t1 ^ 2 + t1 * t2 + t2 ^ 2))
  have hb : β = 1 + 3 * t1 := by linear_combination h1
  have hg : γ = 1 + 3 * t2 := by linear_combination h2
  have he : β ^ 3 - γ ^ 3 =
      (β - γ) * 3 * (1 + 3 * (t1 + t2 + t1 ^ 2 + t1 * t2 + t2 ^ 2)) := by
    rw [hb, hg]
    ring
  rw [he, hu.dvd_mul_right, pow_succ] at h
  exact (mul_dvd_mul_iff_right (by norm_num : (3 : ℤ_[3]) ≠ 0)).1 h

lemma dvd_sub_of_pow_three_dvd (N : ℕ) : ∀ {β γ : ℤ_[3]} (s : ℕ), (3 : ℤ_[3]) ∣ β - 1 →
    (3 : ℤ_[3]) ∣ γ - 1 → (3 : ℤ_[3]) ^ (s + N) ∣ β ^ (3 ^ N) - γ ^ (3 ^ N) →
    (3 : ℤ_[3]) ^ s ∣ β - γ := by
  induction N with
  | zero => intro β γ s _ _ h; simpa using h
  | succ N ih =>
    intro β γ s hβ hγ h
    have hβ3 : (3 : ℤ_[3]) ∣ β ^ 3 - 1 := hβ.trans ⟨β ^ 2 + β + 1, by ring⟩
    have hγ3 : (3 : ℤ_[3]) ∣ γ ^ 3 - 1 := hγ.trans ⟨γ ^ 2 + γ + 1, by ring⟩
    have h' : (3 : ℤ_[3]) ^ ((s + 1) + N) ∣ (β ^ 3) ^ (3 ^ N) - (γ ^ 3) ^ (3 ^ N) := by
      rw [← pow_mul, ← pow_mul, ← pow_succ', show s + 1 + N = s + (N + 1) by ring]
      exact h
    exact dvd_sub_of_cube_dvd hβ hγ (ih (s + 1) hβ3 hγ3 h')

/-- $3^j$ and $3^2$ divide the Newton coefficients of $E$: they vanish for $j \le 1$,
$f_2 = 1152 = 9 \cdot 128$, and $3^j \mid f_j$. -/
lemma iter_EZ_three (j : ℕ) : (3 : ℤ_[3]) ^ (1 * j + 0) ∣ (fwdDiff 1)^[j] (EZ 3) 0 ∧
    (3 : ℤ_[3]) ^ (0 * j + 2) ∣ (fwdDiff 1)^[j] (EZ 3) 0 := by
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · rw [iter_EZ_zero]; exact ⟨dvd_zero _, dvd_zero _⟩
    · rw [iter_EZ_one isUnit_23_three]; exact ⟨dvd_zero _, dvd_zero _⟩
  · rw [iter_EZ_high isUnit_23_three hj]
    have h := padic_dvd_of_int (p := 3) (K := j) (z := fk j)
      (by exact_mod_cast three_pow_dvd_fk j)
    rw [three_cast] at h
    refine ⟨Dvd.dvd.mul_left ?_ _, Dvd.dvd.mul_left ?_ _⟩
    · rw [one_mul, add_zero]
      exact h
    · rw [zero_mul, zero_add]
      exact (pow_dvd_pow 3 hj).trans h

/-- Corollary 6 at $3$: $b(n) \equiv 1 \pmod 9$. -/
lemma three_pow_two_dvd_EZ (n : ℕ) : (3 : ℤ_[3]) ^ 2 ∣ EZ 3 n :=
  dvd_EZ (fun j => by have := (iter_EZ_three j).2; rwa [zero_mul, zero_add] at this) n

lemma max_pow_dvd {R : Type*} [CommRing R] {π x : R} {a b : ℕ} (ha : π ^ a ∣ x)
    (hb : π ^ b ∣ x) : π ^ (max a b) ∣ x := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact hb
  · rw [max_eq_left h]
    exact ha

/-- The core congruence at $3$: if $3^K \mid x^2 y (y - 1)$, then
$a(xy) \equiv a(x)^y \pmod{3^{K+2}}$. -/
theorem A_pow_core_three (x y K : ℕ) (hK : 3 ^ K ∣ x ^ 2 * y * (y - 1)) :
    (3 : ℤ) ^ (K + 2) ∣ A (x * y) - A x ^ y := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [A_small.1]
  have h23 := isUnit_23_three
  have hb9 : ∀ n, (3 : ℤ_[3]) ^ 2 ∣ bZ 3 n - 1 := three_pow_two_dvd_EZ
  have hb3 : ∀ n, (3 : ℤ_[3]) ∣ bZ 3 n - 1 := fun n =>
    (dvd_pow_self 3 two_ne_zero).trans (hb9 n)
  set B : ℕ → ℤ_[3] := fun m => bZ 3 m ^ (3 ^ K) with hB
  have hB0 : B 0 = 1 := by simp [hB, bZ_zero]
  have hcore := pow_core (p := 3) B hB0 x y K (K + 2) (2 + K) hy hK
    (fun l => by
      have h := iter_pow_dvd (p := 3) (bZ 3) K (l + 1) (2 + l / 2) (by omega) (fun r _ =>
        ⟨max (l + 1) (2 * r), fun v hv => by
          rcases le_total (l + 1) (2 * r) with h | h
          · rw [max_eq_right h]; omega
          · rw [max_eq_left h]; omega, by
          rw [three_cast]
          have h1 := pow_dvd_iter_pow (EZ 3) 3 1 0 (fun j => (iter_EZ_three j).1) r (l + 1)
          have h2 := pow_dvd_iter_pow (EZ 3) 3 0 2 (fun j => (iter_EZ_three j).2) r (l + 1)
          rw [one_mul, zero_mul, add_zero] at h1
          rw [zero_mul, zero_add] at h2
          exact max_pow_dvd h1 h2⟩)
      rw [show l / (3 - 1) = l / 2 by norm_num, show K + 2 + l / 2 = K + (2 + l / 2) by ring]
      exact h)
    (by
      rw [three_cast]
      exact pow_three_pow_sub_one_dvd (s := 2) (by norm_num) (hb9 x) K)
    (by omega)
  rw [three_cast] at hcore
  have hmain : (3 : ℤ_[3]) ^ ((K + 2) + K) ∣
      bZ 3 (x * y) ^ (3 ^ K) - (bZ 3 x ^ y) ^ (3 ^ K) := by
    have e : (bZ 3 x ^ y) ^ (3 ^ K) = (bZ 3 x ^ (3 ^ K)) ^ y := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e, show K + 2 + K = K + (K + 2) by ring]
    exact hcore
  have hγ : (3 : ℤ_[3]) ∣ bZ 3 x ^ y - 1 := by
    have := sub_dvd_pow_sub_pow (bZ 3 x) 1 y
    rw [one_pow] at this
    exact (hb3 x).trans this
  have hroot := dvd_sub_of_pow_three_dvd K (K + 2) (hb3 (x * y)) hγ hmain
  have hfin : ((3 : ℕ) : ℤ_[3]) ^ (K + 2) ∣ ((A (x * y) - A x ^ y : ℤ) : ℤ_[3]) := by
    rw [A_sub_eq h23, three_cast]
    exact Dvd.dvd.mul_left hroot _
  have := int_dvd_of_padic hfin
  exact_mod_cast this

end ThreeAdic

/-! ### Theorem 1 -/

section Theorem1

/-- Conjecture 3)(i): $a(mn) \equiv a(m)^n \pmod{2^{2 v_2(m) + 7}}$. -/
theorem A_conj3_two (m n : ℕ) : A (m * n) ≡ A m ^ n [ZMOD 2 ^ (2 * m.factorization 2 + 7)] := by
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  have hm : 2 ^ m.factorization 2 ∣ m := Nat.ordProj_dvd m 2
  have hn : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  have hK : 2 ^ (2 * m.factorization 2 + 1) ∣ m ^ 2 * n * (n - 1) := by
    rw [pow_succ, pow_mul', mul_assoc]
    exact Nat.mul_dvd_mul (pow_dvd_pow_of_dvd hm 2) hn
  exact A_pow_core_two m n _ hK

/-- Conjecture 3)(ii): $a(mn) \equiv a(m)^n \pmod{3^{2 v_3(m) + 2}}$. -/
theorem A_conj3_three (m n : ℕ) :
    A (m * n) ≡ A m ^ n [ZMOD 3 ^ (2 * m.factorization 3 + 2)] := by
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  have hm : 3 ^ m.factorization 3 ∣ m := Nat.ordProj_dvd m 3
  have hK : 3 ^ (2 * m.factorization 3) ∣ m ^ 2 * n * (n - 1) := by
    rw [pow_mul', mul_assoc]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hm 2) _
  exact A_pow_core_three m n _ hK

/-- Conjecture 4): $a(2mn) \equiv a(n)^{2m}$ and $a((2m+1)n) \equiv a(n)^{2m+1}$ modulo
$2^{v_2(m) + 7}$. -/
theorem A_conj4 (m n : ℕ) :
    A (2 * m * n) ≡ A n ^ (2 * m) [ZMOD 2 ^ (m.factorization 2 + 7)] ∧
      A ((2 * m + 1) * n) ≡ A n ^ (2 * m + 1) [ZMOD 2 ^ (m.factorization 2 + 7)] := by
  have hm : 2 ^ (m.factorization 2 + 1) ∣ 2 * m := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 2 (Nat.ordProj_dvd m 2)
  constructor
  · apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, mul_comm (2 * m)]
    refine A_pow_core_two n (2 * m) _ ?_
    exact hm.trans ⟨n ^ 2 * (2 * m - 1), by ring⟩
  · apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, mul_comm (2 * m + 1)]
    refine A_pow_core_two n (2 * m + 1) _ ?_
    exact hm.trans ⟨n ^ 2 * (2 * m + 1), by rw [Nat.add_sub_cancel]; ring⟩

/-- Conjecture 5)(i), (ii): $a(3mn) \equiv a(n)^{3m}$ and $a((3m+1)n) \equiv a(n)^{3m+1}$
modulo $3^{v_3(m) + 2}$ (the proof gives $3^{v_3(m) + 3}$). -/
theorem A_conj5 (m n : ℕ) :
    A (3 * m * n) ≡ A n ^ (3 * m) [ZMOD 3 ^ (m.factorization 3 + 2)] ∧
      A ((3 * m + 1) * n) ≡ A n ^ (3 * m + 1) [ZMOD 3 ^ (m.factorization 3 + 2)] := by
  have hm : 3 ^ (m.factorization 3 + 1) ∣ 3 * m := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 3 (Nat.ordProj_dvd m 3)
  have hw : (3 : ℤ) ^ (m.factorization 3 + 2) ∣ 3 ^ (m.factorization 3 + 1 + 2) :=
    pow_dvd_pow 3 (by omega)
  constructor
  · apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, mul_comm (3 * m)]
    refine hw.trans (A_pow_core_three n (3 * m) _ ?_)
    exact hm.trans ⟨n ^ 2 * (3 * m - 1), by ring⟩
  · apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, mul_comm (3 * m + 1)]
    refine hw.trans (A_pow_core_three n (3 * m + 1) _ ?_)
    exact hm.trans ⟨n ^ 2 * (3 * m + 1), by rw [Nat.add_sub_cancel]; ring⟩

/-- Conjecture 5)(iii): $a((3m+2)n) \equiv a(n)^{3m+2} \pmod 9$. -/
theorem A_conj5_iii (m n : ℕ) : A ((3 * m + 2) * n) ≡ A n ^ (3 * m + 2) [ZMOD 9] := by
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd, mul_comm (3 * m + 2)]
  have h := A_pow_core_three n (3 * m + 2) 0 (by simp)
  rwa [show (3 : ℤ) ^ (0 + 2) = 9 by norm_num] at h

/-- Bala's formula: $a(n) \equiv 23^n \pmod{1152}$. -/
theorem A_mod_1152 (n : ℕ) : A n ≡ 23 ^ n [ZMOD 1152] := by
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  have h2 : (2 : ℤ) ^ 7 ∣ A n - 23 ^ n := by
    have hfin : ((2 : ℕ) : ℤ_[2]) ^ 7 ∣ ((A n - 23 ^ n : ℤ) : ℤ_[2]) := by
      rw [A_sub_pow_eq isUnit_23_two, two_cast]
      exact Dvd.dvd.mul_left (two_pow_seven_dvd_EZ n) _
    have := int_dvd_of_padic hfin
    exact_mod_cast this
  have h3 : (3 : ℤ) ^ 2 ∣ A n - 23 ^ n := by
    have hfin : ((3 : ℕ) : ℤ_[3]) ^ 2 ∣ ((A n - 23 ^ n : ℤ) : ℤ_[3]) := by
      rw [A_sub_pow_eq isUnit_23_three, three_cast]
      exact Dvd.dvd.mul_left (three_pow_two_dvd_EZ n) _
    have := int_dvd_of_padic hfin
    exact_mod_cast this
  have hc : IsCoprime ((2 : ℤ) ^ 7) ((3 : ℤ) ^ 2) :=
    IsCoprime.pow (⟨-1, 1, by norm_num⟩ : IsCoprime (2 : ℤ) 3)
  have := hc.mul_dvd h2 h3
  rwa [show (2 : ℤ) ^ 7 * 3 ^ 2 = 1152 by norm_num] at this

end Theorem1

end Thm1

/-! ### The Euler factor of the antiperiod

For a prime $p \ge 5$, the alternating-sum formula at $P = p^e$ also controls the bases that
are divisible by $p$. They are $5 + 6x = p (c_1 + 6y)$ for $x = x_0 + p y$ and
$1 + 6x = p (c_2 + 6y)$ for $x = x_1 + p y$, where $\{c_1, c_2\} = \{1, 5\}$, and they give
$-\chi_{12}(p)\, p^M$ times the formula at $p^{e-1}$. -/

section Euler
open Hur

/-- For $p \nmid u$: $u^{M + \varphi(p^e)} = u^M$ in $\mathbb{Z}/p^e$, for every $M$. -/
lemma pow_add_totient_of_not_dvd {p e : ℕ} (hp : p.Prime) {u : ℕ} (hu : ¬ p ∣ u) (M : ℕ) :
    (u : ZMod (p ^ e)) ^ (M + (p ^ e).totient) = (u : ZMod (p ^ e)) ^ M := by
  have hcop : Nat.Coprime u (p ^ e) :=
    Nat.Coprime.pow_right e (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu))
  have hu1 := ZMod.pow_totient (ZMod.unitOfCoprime u hcop)
  have h1 : (u : ZMod (p ^ e)) ^ (p ^ e).totient = 1 := by
    have := congrArg Units.val hu1
    rwa [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at this
  rw [pow_add, h1, mul_one]

/-- $(p v)^N = 0$ in $\mathbb{Z}/p^e$ for $N \ge e$. -/
lemma pow_prime_mul_eq_zero {p e : ℕ} (v N : ℕ) (hN : e ≤ N) :
    ((p * v : ℕ) : ZMod (p ^ e)) ^ N = 0 := by
  rw [Nat.cast_mul, mul_pow, show N = e + (N - e) by omega, pow_add (p : ZMod (p ^ e)),
    ← Nat.cast_pow p e, ZMod.natCast_self, zero_mul, zero_mul]

/-- $e \le \varphi(p^e)$ for a prime $p$. -/
lemma le_totient_prime_pow {p e : ℕ} (hp : p.Prime) : e ≤ (p ^ e).totient := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  rw [Nat.totient_prime_pow hp he]
  have h1 : e - 1 < p ^ (e - 1) := Nat.lt_pow_self hp.one_lt
  have h2 : p ^ (e - 1) ≤ p ^ (e - 1) * (p - 1) :=
    Nat.le_mul_of_pos_right _ (by have := hp.two_le; omega)
  omega

lemma sum_range_mul_block {M : Type*} [AddCommMonoid M] (f : ℕ → M) (p Y : ℕ) :
    ∑ x ∈ Finset.range (p * Y), f x =
      ∑ y ∈ Finset.range Y, ∑ r ∈ Finset.range p, f (p * y + r) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [show p * (Y + 1) = p * Y + p by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ _ Y]

/-- Two residues $r, s < p$ with $p \mid c + 6r$ and $p \mid c + 6s$ are equal, for $p \ge 5$. -/
lemma eq_of_prime_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {c r s : ℕ} (hr : r < p)
    (hs : s < p) (h1 : p ∣ c + 6 * r) (h2 : p ∣ c + 6 * s) : r = s := by
  have h6 : ¬ p ∣ 6 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    rcases (by omega : p = 5 ∨ p = 6) with rfl | rfl
    · norm_num at h
    · norm_num at hp
  have hd : (p : ℤ) ∣ 6 * ((r : ℤ) - s) := by
    have h1' : (p : ℤ) ∣ (c : ℤ) + 6 * r := by exact_mod_cast h1
    have h2' : (p : ℤ) ∣ (c : ℤ) + 6 * s := by exact_mod_cast h2
    have := dvd_sub h1' h2'
    rwa [show (c : ℤ) + 6 * r - (c + 6 * s) = 6 * ((r : ℤ) - s) by ring] at this
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd with h | h
  · exact absurd (by exact_mod_cast h) h6
  · have h0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega

lemma not_dvd_add_mul {p a k : ℕ} (h : ¬ p ∣ a) : ¬ p ∣ a + p * k := fun h' => by
  apply h
  have := dvd_sub (Int.natCast_dvd_natCast.2 h') (dvd_mul_right (p : ℤ) k)
  push_cast at this
  rw [add_sub_cancel_right] at this
  exact_mod_cast this

/-- The summand of $4 (G_{M + \varphi(p^e)} - G_M)$ in the alternating-sum formula modulo
$p^e$. -/
noncomputable def termE (p e M x : ℕ) : ZMod (p ^ e) :=
  (-1) ^ x * ((((5 + 6 * x : ℕ) : ZMod (p ^ e)) ^ (M + (p ^ e).totient) -
      ((1 + 6 * x : ℕ) : ZMod (p ^ e)) ^ (M + (p ^ e).totient)) -
    (((5 + 6 * x : ℕ) : ZMod (p ^ e)) ^ M - ((1 + 6 * x : ℕ) : ZMod (p ^ e)) ^ M))

/-- In each block of $p$ consecutive $x$, only the two bases divisible by $p$ survive. -/
lemma block_sum_euler {p e M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {x₀ x₁ c₁ c₂ : ℕ}
    (h0 : 5 + 6 * x₀ = p * c₁) (h1 : 1 + 6 * x₁ = p * c₂) (hx0 : x₀ < p) (hx1 : x₁ < p)
    (y : ℕ) :
    ∑ r ∈ Finset.range p, termE p e M (p * y + r) =
      (p : ZMod (p ^ e)) ^ M * (-1) ^ y *
        ((-1) ^ x₁ * ((c₂ + 6 * y : ℕ) : ZMod (p ^ e)) ^ M -
          (-1) ^ x₀ * ((c₁ + 6 * y : ℕ) : ZMod (p ^ e)) ^ M) := by
  have hL : e ≤ M + (p ^ e).totient := (le_totient_prime_pow hp).trans (Nat.le_add_left _ _)
  have hd0 : p ∣ 5 + 6 * x₀ := ⟨c₁, h0⟩
  have hd1 : p ∣ 1 + 6 * x₁ := ⟨c₂, h1⟩
  have hfour : ∀ z, p ∣ 5 + 6 * z → ¬ p ∣ 1 + 6 * z := by
    intro z hz hz'
    have h4 : (p : ℤ) ∣ 4 := by
      have := dvd_sub (Int.natCast_dvd_natCast.2 hz) (Int.natCast_dvd_natCast.2 hz')
      push_cast at this
      rwa [show (5 : ℤ) + 6 * z - (1 + 6 * z) = 4 by ring] at this
    have h4' : p ∣ 4 := Int.natCast_dvd_natCast.1 (by exact_mod_cast h4)
    have := Nat.le_of_dvd (by norm_num) h4'
    omega
  have hne : x₀ ≠ x₁ := by
    intro h
    subst h
    exact hfour x₀ hd0 hd1
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hsign : ∀ r, (-1 : ZMod (p ^ e)) ^ (p * y + r) = (-1) ^ y * (-1) ^ r := fun r => by
    rw [pow_add, pow_mul, hodd.neg_one_pow]
  have hshift : ∀ r, 5 + 6 * (p * y + r) = (5 + 6 * r) + p * (6 * y) ∧
      1 + 6 * (p * y + r) = (1 + 6 * r) + p * (6 * y) := fun r => ⟨by ring, by ring⟩
  have hzero : ∀ r ∈ Finset.range p, r ≠ x₀ ∧ r ≠ x₁ → termE p e M (p * y + r) = 0 := by
    intro r hr hrne
    have hr' := Finset.mem_range.1 hr
    have hu1 : ¬ p ∣ 5 + 6 * (p * y + r) := by
      rw [(hshift r).1]
      exact not_dvd_add_mul fun h => hrne.1 (eq_of_prime_dvd hp hp5 hr' hx0 h hd0)
    have hu2 : ¬ p ∣ 1 + 6 * (p * y + r) := by
      rw [(hshift r).2]
      exact not_dvd_add_mul fun h => hrne.2 (eq_of_prime_dvd hp hp5 hr' hx1 h hd1)
    rw [termE, pow_add_totient_of_not_dvd hp hu1 M, pow_add_totient_of_not_dvd hp hu2 M,
      sub_self, mul_zero]
  rw [Finset.sum_eq_add_of_mem x₀ x₁ (Finset.mem_range.2 hx0) (Finset.mem_range.2 hx1) hne
    hzero]
  have hb0 : 5 + 6 * (p * y + x₀) = p * (c₁ + 6 * y) := by rw [mul_add p, ← h0]; ring
  have hb1 : 1 + 6 * (p * y + x₁) = p * (c₂ + 6 * y) := by rw [mul_add p, ← h1]; ring
  have hu0 : ¬ p ∣ 1 + 6 * (p * y + x₀) := by
    rw [(hshift x₀).2]
    exact not_dvd_add_mul (hfour x₀ hd0)
  have hu1 : ¬ p ∣ 5 + 6 * (p * y + x₁) := by
    rw [(hshift x₁).1]
    exact not_dvd_add_mul fun h => hfour x₁ h hd1
  simp only [termE]
  rw [pow_add_totient_of_not_dvd hp hu0 M, pow_add_totient_of_not_dvd hp hu1 M, hb0, hb1,
    pow_prime_mul_eq_zero _ _ hL, pow_prime_mul_eq_zero _ _ hL, hsign, hsign]
  simp only [Nat.cast_mul, mul_pow]
  ring

/-- The residues $x_0, x_1$ and the classes $c_1, c_2$ for $p \ge 5$, with the signs
$(-1)^{x_0} = (-1)^{x_1} = \pm \chi_{12}(p)$. -/
lemma euler_data {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ x₀ x₁ c₁ c₂ : ℕ, 5 + 6 * x₀ = p * c₁ ∧ 1 + 6 * x₁ = p * c₂ ∧ x₀ < p ∧ x₁ < p ∧
      ((c₁ = 5 ∧ c₂ = 1 ∧ (-1 : ℤ) ^ x₀ = chi12 p ∧ (-1 : ℤ) ^ x₁ = chi12 p) ∨
        (c₁ = 1 ∧ c₂ = 5 ∧ (-1 : ℤ) ^ x₀ = -chi12 p ∧ (-1 : ℤ) ^ x₁ = -chi12 p)) := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
    omega
  have hcase : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
  rcases hcase with h | h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, p = 12 * k + 1 := ⟨p / 12, by omega⟩
    have hc : chi12 (12 * k + 1) = 1 := by unfold chi12; split_ifs <;> omega
    refine ⟨10 * k, 2 * k, 5, 1, by ring, by ring, by omega, by omega,
      Or.inl ⟨rfl, rfl, ?_, ?_⟩⟩ <;> rw [hc, pow_mul] <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, p = 12 * k + 5 := ⟨p / 12, by omega⟩
    have hc : chi12 (12 * k + 5) = -1 := by unfold chi12; split_ifs <;> omega
    refine ⟨2 * k, 10 * k + 4, 1, 5, by ring, by ring, by omega, by omega,
      Or.inr ⟨rfl, rfl, ?_, ?_⟩⟩ <;> rw [hc] <;> norm_num [pow_add, pow_mul]
  · obtain ⟨k, rfl⟩ : ∃ k, p = 12 * k + 7 := ⟨p / 12, by omega⟩
    have hc : chi12 (12 * k + 7) = -1 := by unfold chi12; split_ifs <;> omega
    refine ⟨10 * k + 5, 2 * k + 1, 5, 1, by ring, by ring, by omega, by omega,
      Or.inl ⟨rfl, rfl, ?_, ?_⟩⟩ <;> rw [hc] <;> norm_num [pow_add, pow_mul]
  · obtain ⟨k, rfl⟩ : ∃ k, p = 12 * k + 11 := ⟨p / 12, by omega⟩
    have hc : chi12 (12 * k + 11) = 1 := by unfold chi12; split_ifs <;> omega
    refine ⟨2 * k + 1, 10 * k + 9, 1, 5, by ring, by ring, by omega, by omega,
      Or.inr ⟨rfl, rfl, ?_, ?_⟩⟩ <;> rw [hc] <;> norm_num [pow_add, pow_mul]

/-- The Euler-factor congruence for $G$: for a prime $p \ge 5$, $e \ge 1$ and $M \ge 1$,
$G_{M + \varphi(p^e)} \equiv (1 - \chi_{12}(p)\, p^M)\, G_M \pmod{p^e}$. -/
theorem GH_euler {p e M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (he : 1 ≤ e) (hM : 1 ≤ M) :
    (GH ℤ).coeff (M + (p ^ e).totient) ≡ (1 - chi12 p * (p : ℤ) ^ M) * (GH ℤ).coeff M
      [ZMOD p ^ e] := by
  obtain ⟨x₀, x₁, c₁, c₂, h0, h1, hx0, hx1, hcase⟩ := euler_data hp hp5
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hodd : Odd (p ^ e) := hpodd.pow
  have hPQ : p ^ e = p * p ^ (e - 1) := by rw [← pow_succ', Nat.sub_add_cancel he]
  have hdiff : (4 : ZMod (p ^ e)) * ((GH ℤ).coeff (M + (p ^ e).totient) : ZMod (p ^ e)) -
      4 * ((GH ℤ).coeff M : ZMod (p ^ e)) =
      -(chi12 p : ZMod (p ^ e)) * (p : ZMod (p ^ e)) ^ M *
        ∑ y ∈ Finset.range (p ^ (e - 1)), (-1) ^ y *
          (((5 + 6 * y : ℕ) : ZMod (p ^ e)) ^ M - ((1 + 6 * y : ℕ) : ZMod (p ^ e)) ^ M) := by
    rw [four_GH_zmod (p ^ e) (M + (p ^ e).totient) hodd, four_GH_zmod (p ^ e) M hodd,
      ← Finset.sum_sub_distrib]
    have e1 : ∀ x ∈ Finset.range (p ^ e), (-1 : ZMod (p ^ e)) ^ x *
        (((5 + 6 * x : ℕ) : ZMod (p ^ e)) ^ (M + (p ^ e).totient) -
          ((1 + 6 * x : ℕ) : ZMod (p ^ e)) ^ (M + (p ^ e).totient)) -
        (-1) ^ x * (((5 + 6 * x : ℕ) : ZMod (p ^ e)) ^ M -
          ((1 + 6 * x : ℕ) : ZMod (p ^ e)) ^ M) = termE p e M x := by
      intro x _
      rw [termE]
      exact (mul_sub _ _ _).symm
    have hr : Finset.range (p ^ e) = Finset.range (p * p ^ (e - 1)) := by rw [← hPQ]
    rw [Finset.sum_congr rfl e1, hr, sum_range_mul_block, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [block_sum_euler hp hp5 h0 h1 hx0 hx1 y]
    rcases hcase with ⟨rfl, rfl, s0, s1⟩ | ⟨rfl, rfl, s0, s1⟩
    · have s0' : (-1 : ZMod (p ^ e)) ^ x₀ = (chi12 p : ZMod (p ^ e)) := by
        have := congrArg (Int.cast : ℤ → ZMod (p ^ e)) s0
        push_cast at this
        exact this
      have s1' : (-1 : ZMod (p ^ e)) ^ x₁ = (chi12 p : ZMod (p ^ e)) := by
        have := congrArg (Int.cast : ℤ → ZMod (p ^ e)) s1
        push_cast at this
        exact this
      rw [s0', s1']
      ring
    · have s0' : (-1 : ZMod (p ^ e)) ^ x₀ = -(chi12 p : ZMod (p ^ e)) := by
        have := congrArg (Int.cast : ℤ → ZMod (p ^ e)) s0
        push_cast at this
        exact this
      have s1' : (-1 : ZMod (p ^ e)) ^ x₁ = -(chi12 p : ZMod (p ^ e)) := by
        have := congrArg (Int.cast : ℤ → ZMod (p ^ e)) s1
        push_cast at this
        exact this
      rw [s0', s1']
      ring
  -- the alternating sum for `p^(e-1)` gives `4 G_M`
  set S : ℤ := ∑ y ∈ Finset.range (p ^ (e - 1)), (-1) ^ y *
      ((5 + 6 * (y : ℤ)) ^ M - (1 + 6 * (y : ℤ)) ^ M) with hS
  clear_value S
  have hQ : (p : ℤ) ^ (e - 1) ∣ 4 * (GH ℤ).coeff M - S := by
    have h := (four_GH_modEq (p ^ (e - 1)) M hpodd.pow).symm.dvd
    rw [Nat.cast_pow] at h
    rw [hS]
    exact h
  have hcast : ((S : ℤ) : ZMod (p ^ e)) = ∑ y ∈ Finset.range (p ^ (e - 1)), (-1) ^ y *
      (((5 + 6 * y : ℕ) : ZMod (p ^ e)) ^ M - ((1 + 6 * y : ℕ) : ZMod (p ^ e)) ^ M) := by
    rw [hS]
    simp only [Int.cast_mul, Int.cast_sum, Int.cast_pow, Int.cast_sub, Int.cast_neg,
      Int.cast_one, Int.cast_add, Int.cast_ofNat, Int.cast_natCast, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  have h6 : (p : ℤ) ^ e ∣ 4 * (GH ℤ).coeff (M + (p ^ e).totient) - 4 * (GH ℤ).coeff M -
      -chi12 p * (p : ℤ) ^ M * S := by
    rw [← hcast] at hdiff
    have h' : ((4 * (GH ℤ).coeff (M + (p ^ e).totient) - 4 * (GH ℤ).coeff M : ℤ) :
        ZMod (p ^ e)) = ((-chi12 p * (p : ℤ) ^ M * S : ℤ) : ZMod (p ^ e)) := by
      push_cast
      exact hdiff
    have := ((ZMod.intCast_eq_intCast_iff _ _ _).1 h').symm.dvd
    rw [Nat.cast_pow] at this
    exact this
  obtain ⟨c, hc⟩ := hQ
  have hpow : (p : ℤ) ^ M * (p : ℤ) ^ (e - 1) = (p : ℤ) ^ e * (p : ℤ) ^ (M - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h7 : (p : ℤ) ^ e ∣
      4 * ((GH ℤ).coeff (M + (p ^ e).totient) - (1 - chi12 p * (p : ℤ) ^ M) * (GH ℤ).coeff M) := by
    have e2 : 4 * ((GH ℤ).coeff (M + (p ^ e).totient) -
        (1 - chi12 p * (p : ℤ) ^ M) * (GH ℤ).coeff M) =
        (4 * (GH ℤ).coeff (M + (p ^ e).totient) - 4 * (GH ℤ).coeff M -
          -chi12 p * (p : ℤ) ^ M * S) + (p : ℤ) ^ e * (chi12 p * (p : ℤ) ^ (M - 1) * c) := by
      linear_combination (chi12 p * (p : ℤ) ^ M) * hc + (chi12 p * c) * hpow
    rw [e2]
    exact dvd_add h6 (dvd_mul_right _ _)
  obtain ⟨k, hk⟩ := hpodd
  have h2 : IsCoprime (p : ℤ) 2 := ⟨1, -k, by rw [hk]; push_cast; ring⟩
  have hc4 : IsCoprime ((p : ℤ) ^ e) 4 := by
    have := IsCoprime.pow (m := e) (n := 2) h2
    rwa [show (2 : ℤ) ^ 2 = 4 by norm_num] at this
  exact (Int.modEq_iff_dvd.2 (hc4.dvd_of_dvd_mul_left h7)).symm

/-- `antiperiod_euler`: for a prime $p \ge 5$, $h = (p-1)/2$, $e \ge 1$ and every $n$,
$a(n + h p^{e-1}) \equiv (-1)^h (1 - \chi_{12}(p)\, p^{2n+1})\, a(n) \pmod{p^e}$. -/
theorem A_antiperiod_euler {p e n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (he : 1 ≤ e) :
    A (n + (p - 1) / 2 * p ^ (e - 1)) ≡
      (-1) ^ ((p - 1) / 2) * (1 - chi12 p * (p : ℤ) ^ (2 * n + 1)) * A n [ZMOD p ^ e] := by
  have hp2 : p ≠ 2 := by omega
  have hL := two_mul_half_totient hp hp2 he
  unfold A
  rw [gH_coeff_odd, gH_coeff_odd, show 2 * (n + (p - 1) / 2 * p ^ (e - 1)) + 1 =
    (2 * n + 1) + (p ^ e).totient by rw [← hL]; ring]
  have hG := GH_euler (M := 2 * n + 1) hp hp5 he (by omega)
  have hs : (-1 : ℤ) ^ (n + (p - 1) / 2 * p ^ (e - 1)) = (-1) ^ ((p - 1) / 2) * (-1) ^ n := by
    rw [pow_add, neg_one_pow_mul_odd _ _ ((hp.odd_of_ne_two hp2).pow), mul_comm]
  rw [hs]
  calc (-1) ^ ((p - 1) / 2) * (-1) ^ n * (GH ℤ).coeff (2 * n + 1 + (p ^ e).totient)
      ≡ (-1) ^ ((p - 1) / 2) * (-1) ^ n *
          ((1 - chi12 p * (p : ℤ) ^ (2 * n + 1)) * (GH ℤ).coeff (2 * n + 1)) [ZMOD p ^ e] :=
        hG.mul_left _
    _ = (-1) ^ ((p - 1) / 2) * (1 - chi12 p * (p : ℤ) ^ (2 * n + 1)) *
          ((-1) ^ n * (GH ℤ).coeff (2 * n + 1)) := by ring

/-- The prime $3$: no base $5 + 6x$ or $1 + 6x$ is divisible by $3$, so
$G_{M + \varphi(3^e)} \equiv G_M \pmod{3^e}$ for every $M$. -/
theorem GH_three (e M : ℕ) :
    (GH ℤ).coeff (M + (3 ^ e).totient) ≡ (GH ℤ).coeff M [ZMOD 3 ^ e] := by
  have hodd : Odd (3 ^ e) := Odd.pow ⟨1, rfl⟩
  have h : (4 : ZMod (3 ^ e)) * ((GH ℤ).coeff (M + (3 ^ e).totient) : ZMod (3 ^ e)) =
      4 * ((GH ℤ).coeff M : ZMod (3 ^ e)) := by
    rw [four_GH_zmod (3 ^ e) _ hodd, four_GH_zmod (3 ^ e) M hodd]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [pow_add_totient_of_not_dvd Nat.prime_three (by omega : ¬ 3 ∣ 5 + 6 * x) M,
      pow_add_totient_of_not_dvd Nat.prime_three (by omega : ¬ 3 ∣ 1 + 6 * x) M]
  have h' := (isUnit_four_zmod hodd).mul_left_cancel h
  have := (ZMod.intCast_eq_intCast_iff _ _ _).1 h'
  exact_mod_cast this

/-- `antiperiod_three`: $a(n + 3^{e-1}) \equiv -a(n) \pmod{3^e}$ for every $e \ge 1$ and every
$n$. -/
theorem A_antiperiod_three {e : ℕ} (n : ℕ) (he : 1 ≤ e) :
    A (n + 3 ^ (e - 1)) ≡ -A n [ZMOD 3 ^ e] := by
  have hL : 2 * 3 ^ (e - 1) = (3 ^ e).totient := by
    rw [Nat.totient_prime_pow Nat.prime_three (by omega)]
    omega
  unfold A
  rw [gH_coeff_odd, gH_coeff_odd, show 2 * (n + 3 ^ (e - 1)) + 1 =
    (2 * n + 1) + (3 ^ e).totient by rw [← hL]; ring]
  have hG := GH_three e (2 * n + 1)
  have hs : (-1 : ℤ) ^ (n + 3 ^ (e - 1)) = -(-1) ^ n := by
    rw [pow_add, (Odd.pow ⟨1, rfl⟩ : Odd (3 ^ (e - 1))).neg_one_pow]
    ring
  rw [hs]
  calc -(-1) ^ n * (GH ℤ).coeff (2 * n + 1 + (3 ^ e).totient)
      ≡ -(-1) ^ n * (GH ℤ).coeff (2 * n + 1) [ZMOD 3 ^ e] := hG.mul_left _
    _ = -((-1) ^ n * (GH ℤ).coeff (2 * n + 1)) := by ring

end Euler

/-! ### Conjecture 6), exactly -/

section Conj6Iff
open Hur

/-- The power side of conjecture 6): with $\varepsilon = (-1)^{hn}$,
$a(hn) \equiv \varepsilon \pmod p$ and $a(hn)^{1 + p^r t} \equiv \varepsilon^t a(hn)
\pmod{p^{r+1}}$. -/
lemma A_pow_side {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (r t : ℕ) :
    A ((p - 1) / 2 * n) ≡ ((-1) ^ ((p - 1) / 2)) ^ n [ZMOD p] ∧
      A ((p - 1) / 2 * n) ^ (1 + p ^ r * t) ≡
        A ((p - 1) / 2 * n) * (((-1) ^ ((p - 1) / 2)) ^ n) ^ t [ZMOD p ^ (r + 1)] := by
  set h := (p - 1) / 2
  have hp2 : p ≠ 2 := by omega
  set ε : ℤ := ((-1) ^ h) ^ n with hε
  have h1 : A (h * n) ≡ ε [ZMOD p] := by
    have := iter_mul_shift (x := A) (m := (p : ℤ) ^ 1) (L := h * p ^ (1 - 1)) (N0 := 0)
      (c := (-1) ^ h) (fun i _ => A_antiperiod hp hp2 le_rfl (by omega)) n 0 le_rfl
    rw [show 0 + n * (h * p ^ (1 - 1)) = h * n by simp [mul_comm], pow_one, A_small.1,
      mul_one] at this
    exact this
  have h2 : (p : ℤ) ^ (r + 1) ∣ A (h * n) ^ p ^ r - ε ^ p ^ r :=
    dvd_sub_pow_of_dvd_sub (Int.ModEq.dvd h1.symm) r
  have hε' : ε = (-1) ^ (h * n) := by rw [hε, ← pow_mul]
  have h3 : ε ^ p ^ r = ε := by
    rcases neg_one_pow_eq_or ℤ (h * n) with h' | h' <;> rw [hε', h']
    · rw [one_pow]
    · exact ((hp.odd_of_ne_two hp2).pow).neg_one_pow
  rw [h3] at h2
  have h4 : A (h * n) ^ p ^ r ≡ ε [ZMOD p ^ (r + 1)] := (Int.modEq_iff_dvd.2 h2).symm
  refine ⟨h1, ?_⟩
  calc A (h * n) ^ (1 + p ^ r * t) = A (h * n) * (A (h * n) ^ p ^ r) ^ t := by
        rw [pow_add, pow_one, pow_mul]
    _ ≡ A (h * n) * ε ^ t [ZMOD p ^ (r + 1)] := (h4.pow t).mul_left _

/-- `conjecture6_iff`: for a prime $p \ge 5$ and $m, n \ge 1$, conjecture 6) holds exactly
when $v_p(m-1) \le (p-1) n$. -/
theorem A_conj6_iff {p m n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (A ((p - 1) / 2 * n * m) ≡ A ((p - 1) / 2 * n) ^ m
      [ZMOD p ^ ((m - 1).factorization p + 1)] ↔ (m - 1).factorization p ≤ (p - 1) * n) := by
  refine ⟨fun hcong => ?_, fun hr => A_conj6_of_le hp hp5 hm hr⟩
  by_contra hlt'
  have hlt := not_le.1 hlt'
  set r := (m - 1).factorization p with hr_def
  set h := (p - 1) / 2 with hh
  have hp2 : p ≠ 2 := by omega
  have h2h : 2 * h = p - 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  have hh1 : 1 ≤ h := by omega
  have hrn : 2 * (h * n) < r := by rw [← mul_assoc, h2h]; exact hlt
  have hm1 : m - 1 ≠ 0 := by
    intro h0
    rw [h0] at hr_def
    simp at hr_def
    omega
  obtain ⟨t, ht⟩ : p ^ r ∣ m - 1 := Nat.ordProj_dvd (m - 1) p
  have ht0 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, mul_zero] at ht
      exact absurd ht hm1
    · exact h0
  have hm' : m = 1 + p ^ r * t := by omega
  obtain ⟨q, hq⟩ : ∃ q, n * t = q + 1 := ⟨n * t - 1, by
    have : 0 < n * t := Nat.mul_pos hn ht0
    omega⟩
  set N := h * n with hN
  set χ := chi12 p with hχ
  set ε : ℤ := ((-1) ^ h) ^ n with hε
  -- the left side: one step with the Euler factor, then `q` steps of Lemma 10
  have hpr : r < p ^ r := Nat.lt_pow_self hp.one_lt
  have hhp : p ^ r ≤ h * p ^ r := Nat.le_mul_of_pos_left _ hh1
  have s1 : A (N + h * p ^ (r + 1 - 1)) ≡
      (-1) ^ h * (1 - χ * (p : ℤ) ^ (2 * N + 1)) * A N [ZMOD p ^ (r + 1)] :=
    A_antiperiod_euler hp hp5 (by omega)
  have s2 : A ((N + h * p ^ (r + 1 - 1)) + q * (h * p ^ (r + 1 - 1))) ≡
      ((-1) ^ h) ^ q * A (N + h * p ^ (r + 1 - 1)) [ZMOD p ^ (r + 1)] :=
    iter_mul_shift (fun i hi => A_antiperiod hp hp2 (by omega) (by
      rw [show r + 1 - 1 = r by omega] at hi
      omega)) q _ le_rfl
  have hidx : (N + h * p ^ (r + 1 - 1)) + q * (h * p ^ (r + 1 - 1)) = h * n * m := by
    rw [hm', show r + 1 - 1 = r by omega, hN]
    have e1 : h * n * (1 + p ^ r * t) = h * n + h * p ^ r * (n * t) := by ring
    rw [e1, hq]
    ring
  rw [hidx] at s2
  have hL : A (h * n * m) ≡ ε ^ t * (1 - χ * (p : ℤ) ^ (2 * N + 1)) * A N
      [ZMOD p ^ (r + 1)] := by
    calc A (h * n * m) ≡ ((-1) ^ h) ^ q * A (N + h * p ^ (r + 1 - 1)) [ZMOD p ^ (r + 1)] := s2
      _ ≡ ((-1) ^ h) ^ q * ((-1) ^ h * (1 - χ * (p : ℤ) ^ (2 * N + 1)) * A N)
          [ZMOD p ^ (r + 1)] := s1.mul_left _
      _ = ((-1) ^ h) ^ (n * t) * (1 - χ * (p : ℤ) ^ (2 * N + 1)) * A N := by
          rw [hq]
          ring
      _ = ε ^ t * (1 - χ * (p : ℤ) ^ (2 * N + 1)) * A N := by rw [hε, pow_mul]
  -- the right side
  obtain ⟨hA1, hpow⟩ := A_pow_side (n := n) hp hp5 r t
  rw [← hm'] at hpow
  have hA1' : A N ≡ ε [ZMOD p] := hA1
  have hpow' : A N ^ m ≡ A N * ε ^ t [ZMOD p ^ (r + 1)] := hpow
  have hcong' : A (h * n * m) ≡ A N ^ m [ZMOD p ^ (r + 1)] := hcong
  -- compare
  have hcmp : ε ^ t * (1 - χ * (p : ℤ) ^ (2 * N + 1)) * A N ≡ A N * ε ^ t
      [ZMOD p ^ (r + 1)] := (hL.symm.trans hcong').trans hpow'
  have hd : (p : ℤ) ^ (r + 1) ∣ ε ^ t * χ * ((p : ℤ) ^ (2 * N + 1) * A N) := by
    have := hcmp.dvd
    have e : A N * ε ^ t - ε ^ t * (1 - χ * (p : ℤ) ^ (2 * N + 1)) * A N =
        ε ^ t * χ * ((p : ℤ) ^ (2 * N + 1) * A N) := by ring
    rwa [e] at this
  have hu : (ε ^ t * χ) * (ε ^ t * χ) = 1 := by
    have hε1 : ε ^ t = 1 ∨ ε ^ t = -1 := by
      rw [hε, ← pow_mul, ← pow_mul]
      exact neg_one_pow_eq_or ℤ _
    have hχ1 : χ = 1 ∨ χ = -1 := by
      rw [hχ, chi12]
      split_ifs <;> simp
    rcases hε1 with h1 | h1 <;> rcases hχ1 with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have hd' : (p : ℤ) ^ (r + 1) ∣ (p : ℤ) ^ (2 * N + 1) * A N := by
    have := Dvd.dvd.mul_left hd (ε ^ t * χ)
    rwa [← mul_assoc, hu, one_mul] at this
  have hp0 : (p : ℤ) ^ (2 * N + 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hpA : (p : ℤ) ∣ A N := by
    have h3 : (p : ℤ) ^ (2 * N + 1) * p ∣ (p : ℤ) ^ (2 * N + 1) * A N := by
      rw [← pow_succ]
      exact (pow_dvd_pow (p : ℤ) (by omega : 2 * N + 1 + 1 ≤ r + 1)).trans hd'
    exact (mul_dvd_mul_iff_left hp0).1 h3
  have hpε : (p : ℤ) ∣ ε := by
    have := Int.ModEq.dvd hA1'.symm
    have h4 := dvd_sub hpA this
    rwa [sub_sub_cancel] at h4
  have hε1 : ε = 1 ∨ ε = -1 := by
    rw [hε, ← pow_mul]
    exact neg_one_pow_eq_or ℤ _
  have hp1 : (p : ℤ) ∣ 1 := by
    rcases hε1 with h1 | h1
    · rwa [h1] at hpε
    · rwa [h1, dvd_neg] at hpε
  have := Int.natCast_dvd_natCast.1 (by exact_mod_cast hp1 : (p : ℤ) ∣ ((1 : ℕ) : ℤ))
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- `conjecture5_strong`: 5)(i), (ii) hold modulo $3^{v_3(m) + 3}$. -/
theorem A_conj5_strong (m n : ℕ) :
    A (3 * m * n) ≡ A n ^ (3 * m) [ZMOD 3 ^ (m.factorization 3 + 3)] ∧
      A ((3 * m + 1) * n) ≡ A n ^ (3 * m + 1) [ZMOD 3 ^ (m.factorization 3 + 3)] := by
  have hm : 3 ^ (m.factorization 3 + 1) ∣ 3 * m := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 3 (Nat.ordProj_dvd m 3)
  constructor
  · apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, mul_comm (3 * m)]
    exact A_pow_core_three n (3 * m) _ (hm.trans ⟨n ^ 2 * (3 * m - 1), by ring⟩)
  · apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd, mul_comm (3 * m + 1)]
    exact A_pow_core_three n (3 * m + 1) _
      (hm.trans ⟨n ^ 2 * (3 * m + 1), by rw [Nat.add_sub_cancel]; ring⟩)

end Conj6Iff

/-! ### The statements -/

/-- The first terms agree with the OEIS data. -/
theorem a_first_terms : a 0 = 1 ∧ a 1 = 23 ∧ a 2 = 1681 ∧ a 3 = 257543 := by
  obtain ⟨h0, h1, h2, h3⟩ := A_small
  simp only [a_eq, h0, h1, h2, h3]
  norm_num

/-- Bala's conjecture 3)(i): $a(mn) \equiv a(m)^n \pmod{2^{2 v_2(m) + 7}}$ for all
$m, n \ge 1$. -/
theorem conjecture3_two :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (m * n) ≡ b m ^ n [ZMOD 2 ^ (2 * m.factorization 2 + 7)] :=
  ⟨A, fun n => (a_eq n).symm, fun m n _ _ => A_conj3_two m n⟩

/-- Bala's conjecture 3)(ii): $a(mn) \equiv a(m)^n \pmod{3^{2 v_3(m) + 2}}$ for all
$m, n \ge 1$. -/
theorem conjecture3_three :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (m * n) ≡ b m ^ n [ZMOD 3 ^ (2 * m.factorization 3 + 2)] :=
  ⟨A, fun n => (a_eq n).symm, fun m n _ _ => A_conj3_three m n⟩

/-- Bala's conjecture 4): for all $m, n \ge 1$, $a(2mn) \equiv a(n)^{2m}$ and
$a((2m+1)n) \equiv a(n)^{2m+1}$ modulo $2^{v_2(m) + 7}$. -/
theorem conjecture4 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (2 * m * n) ≡ b n ^ (2 * m) [ZMOD 2 ^ (m.factorization 2 + 7)] ∧
          b ((2 * m + 1) * n) ≡ b n ^ (2 * m + 1) [ZMOD 2 ^ (m.factorization 2 + 7)] :=
  ⟨A, fun n => (a_eq n).symm, fun m n _ _ => A_conj4 m n⟩

/-- Bala's conjecture 5)(i), (ii): for all $m, n \ge 1$, $a(3mn) \equiv a(n)^{3m}$ and
$a((3m+1)n) \equiv a(n)^{3m+1}$ modulo $3^{v_3(m) + 2}$. -/
theorem conjecture5 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (3 * m * n) ≡ b n ^ (3 * m) [ZMOD 3 ^ (m.factorization 3 + 2)] ∧
          b ((3 * m + 1) * n) ≡ b n ^ (3 * m + 1) [ZMOD 3 ^ (m.factorization 3 + 2)] :=
  ⟨A, fun n => (a_eq n).symm, fun m n _ _ => A_conj5 m n⟩

/-- Bala's conjecture 5)(iii): $a((3m+2)n) \equiv a(n)^{3m+2} \pmod 9$ for all $m \ge 0$ and
$n \ge 1$. -/
theorem conjecture5_iii :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ n → b ((3 * m + 2) * n) ≡ b n ^ (3 * m + 2) [ZMOD 9] :=
  ⟨A, fun n => (a_eq n).symm, fun m n _ => A_conj5_iii m n⟩

/-- Bala's congruence $a(n) \equiv 23^n \pmod{1152}$ for all $n \ge 0$. -/
theorem a_mod_1152 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ ∀ n : ℕ, b n ≡ 23 ^ n [ZMOD 1152] :=
  ⟨A, fun n => (a_eq n).symm, A_mod_1152⟩

/-- Bala's conjecture 6) is false: it is not true that for every prime $p \ge 5$ and all
$m, n \ge 1$, $a(hnm) \equiv a(hn)^m \pmod{p^{v_p(m-1) + 1}}$, where $h = (p-1)/2$. -/
theorem not_conjecture6 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ¬ ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n →
        b ((p - 1) / 2 * n * m) ≡ b ((p - 1) / 2 * n) ^ m
          [ZMOD p ^ ((m - 1).factorization p + 1)] :=
  ⟨A, fun n => (a_eq n).symm, A_not_conj6⟩

/-- The counterexample to conjecture 6) at $p = 5$, $n = 1$, $m = 3126$: $a(2) = 1681$,
$a(6252) \equiv (1 + 5^5)\,a(2) \pmod{5^6}$, and $v_5(a(6252) - a(2)^{3126}) = 5$, while 6)
asks for $v_5 \ge v_5(3125) + 1 = 6$. -/
theorem conjecture6_counterexample :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ b 2 = 1681 ∧
      b 6252 ≡ (1 + 5 ^ 5) * b 2 [ZMOD 5 ^ 6] ∧ padicValInt 5 (b 6252 - b 2 ^ 3126) = 5 :=
  ⟨A, fun n => (a_eq n).symm, A_small.2.2.1, A_6252, A_6252_val⟩

/-- Odd primes: $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n) \pmod{p^e}$ for every
odd prime $p$, every $e \ge 1$ and every $n$ with $2n + 1 \ge e$. -/
theorem antiperiod_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n + 1 →
        b (n + (p - 1) / 2 * p ^ (e - 1)) ≡ (-1) ^ ((p - 1) / 2) * b n [ZMOD p ^ e] :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ _ hp hp2 he hn => A_antiperiod hp hp2 he hn⟩

/-- Conjecture 6), corrected: for every prime $p \ge 5$ and all $m, n \ge 1$ with
$v_p(m-1) \le (p-1) n$, $a(hnm) \equiv a(hn)^m \pmod{p^{v_p(m-1) + 1}}$, where
$h = (p-1)/2$. -/
theorem conjecture6_of_le :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n → (m - 1).factorization p ≤ (p - 1) * n →
        b ((p - 1) / 2 * n * m) ≡ b ((p - 1) / 2 * n) ^ m
          [ZMOD p ^ ((m - 1).factorization p + 1)] :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ _ hp hp5 hm _ hr => A_conj6_of_le hp hp5 hm hr⟩

/-- For every prime $p \ge 5$, with $h = (p-1)/2$, every $e \ge 1$ and every $n \ge 0$,
$a(n + h p^{e-1}) \equiv (-1)^h \big(1 - \chi_{12}(p)\, p^{2n+1}\big)\, a(n) \pmod{p^e}$. -/
theorem antiperiod_euler :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → 5 ≤ p → 1 ≤ e →
        b (n + (p - 1) / 2 * p ^ (e - 1)) ≡
          (-1) ^ ((p - 1) / 2) * (1 - chi12 p * (p : ℤ) ^ (2 * n + 1)) * b n [ZMOD p ^ e] :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ _ hp hp5 he => A_antiperiod_euler hp hp5 he⟩

/-- Conjecture 6), exactly: for every prime $p \ge 5$ and all $m, n \ge 1$, with
$h = (p-1)/2$, $a(hnm) \equiv a(hn)^m \pmod{p^{v_p(m-1) + 1}}$ holds if and only if
$v_p(m-1) \le (p-1) n$. -/
theorem conjecture6_iff :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n →
        (b ((p - 1) / 2 * n * m) ≡ b ((p - 1) / 2 * n) ^ m
          [ZMOD p ^ ((m - 1).factorization p + 1)] ↔ (m - 1).factorization p ≤ (p - 1) * n) :=
  ⟨A, fun n => (a_eq n).symm, fun _ _ _ hp hp5 hm hn => A_conj6_iff hp hp5 hm hn⟩

/-- The prime $3$: $a(n + 3^{e-1}) \equiv -a(n) \pmod{3^e}$ for every $e \ge 1$ and every
$n \ge 0$. -/
theorem antiperiod_three :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 1 ≤ e → b (n + 3 ^ (e - 1)) ≡ -b n [ZMOD 3 ^ e] :=
  ⟨A, fun n => (a_eq n).symm, fun _ n he => A_antiperiod_three n he⟩

/-- Conjecture 5)(i), (ii) with one more power of $3$: for all $m, n \ge 1$,
$a(3mn) \equiv a(n)^{3m}$ and $a((3m+1)n) \equiv a(n)^{3m+1}$ modulo $3^{v_3(m) + 3}$. -/
theorem conjecture5_strong :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (3 * m * n) ≡ b n ^ (3 * m) [ZMOD 3 ^ (m.factorization 3 + 3)] ∧
          b ((3 * m + 1) * n) ≡ b n ^ (3 * m + 1) [ZMOD 3 ^ (m.factorization 3 + 3)] :=
  ⟨A, fun n => (a_eq n).symm, fun m n _ _ => A_conj5_strong m n⟩

end OeisA002439

end
