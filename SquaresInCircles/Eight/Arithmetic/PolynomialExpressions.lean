module

public import Mathlib.Data.List.GetD
public import SquaresInCircles.Eight.Arithmetic.FastPolynomials
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Arithmetic.TensorWholeIntervalPolynomial
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds

/-!
# Eight squares: polynomial expressions with integer values

A `PolyExpr` is a polynomial expression built from rational constants, the variable, sums,
differences, negatives, products, powers, derivatives, `divX` and translations
`p ↦ p.comp (C q + X)`. Its meaning `poly` is a polynomial in `ℚ[X]`; its value `z` is an
integer coefficient list with a common denominator (`WholeIntervalPolynomial.Certificate.Scaled`),
which the kernel computes with the integer list operations of `FastPolynomials`:
`rep e : e.z.Rep e.poly` and `scale_ne_zero e : e.z.s ≠ 0` hold for every expression, with no
side condition. Sums are taken over the least common multiple of the scales.
`simp only [definitions…, reify_C, reify_X, reify_add, …]` rewrites a polynomial into
`PolyExpr.poly` of an expression, and `rfl` names it.

The checks are `Bool`s on the integer value; a proof of `check … = true` by `decide +kernel` gives
the statement through the matching theorem. Rational numbers are computed only for the constants
of an expression and the parameters of a check, and the only divisions are of two scales by their
gcd.

* `cmSeries n e` (`natDegree_of_check`, `series_of_check`): `e.poly` has degree at most `n`, so
  `CenteredMonomialBounds.translated m e.poly` is its own `series n`, for every `m`.
* `cmLowerGt n m r ρ e` (`lowerOn_of_check`): `ρ < CenteredMonomialBounds.lowerOn n m r e.poly`.
* `cmUpperLt n l h ρ e` (`upperOn_of_check`): `CenteredMonomialBounds.upperOn n l h e.poly < ρ`.
* `valueGt x ρ e`, `valueAbsLt x ρ e`: `ρ < e.poly.eval x`, `|e.poly.eval x| < ρ`.
* `coeffGt k ρ e`, `coeffGe`, `coeffAbsLt`, `coeffZero`: single coefficients; `tailSum_eq` writes a
  tail sum `∑ j, g (p.coeff (j+a)) * r^(j+e)` as an integer sum (`tailSumZ`), and
  `quadReserveGt n r ρ e` checks `ρ < coeff 2 - ∑_{j<n} |coeff (j+3)| r^(j+1)`.
* `chebLowerGt D num den s t ρ e` (`chebLower_of_check`): the degree-`D` Chebyshev expansion of
  `WholeIntervalPolynomial.centered a b e.poly` and `ρ < WholeIntervalPolynomial.lowerOn D a b
  e.poly`, for `(a+b)/2 = num*s/den` and `(b-a)/2 = num*t/den`.
* Cubics in closed form: `translated_cubic`, `lowerOn_cubic`, `natDegree_cubic_le`.
* Bivariate polynomials (`TensorWholeIntervalPolynomial.Bivar`): `BExpr` with integer rows
  (`BScaled`), `tensor_eq_expansion` for bounded degrees, and `tensorCheck D ρ₀ ρ₁ e`
  (`tensor_of_check`): the tensor expansion, `ρ₀ < coefficient D e.poly 0 0` and
  `norm D (coefficient D e.poly) < ρ₁`, from the Chebyshev transforms of the rows and then of the
  columns (`tensorZ`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.PolynomialExpressions
open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

/-! ## Operations on scaled lists -/

/-- The sum, over the least common multiple of the two scales. -/
def addL (a b : Scaled) : Scaled :=
  ⟨Fast.lincF ((b.s/Nat.gcd a.s b.s : ℕ) : ℤ) ((a.s/Nat.gcd a.s b.s : ℕ) : ℤ) a.l b.l,
    a.s/Nat.gcd a.s b.s*b.s⟩

/-- The difference, over the least common multiple of the two scales. -/
def subL (a b : Scaled) : Scaled :=
  ⟨Fast.lincF ((b.s/Nat.gcd a.s b.s : ℕ) : ℤ) (-((a.s/Nat.gcd a.s b.s : ℕ) : ℤ)) a.l b.l,
    a.s/Nat.gcd a.s b.s*b.s⟩

theorem gcd_cross (x y : ℕ) : y/Nat.gcd x y*x=x/Nat.gcd x y*y := by
  obtain ⟨k,hk⟩ := Nat.gcd_dvd_left x y
  obtain ⟨m,hm⟩ := Nat.gcd_dvd_right x y
  generalize Nat.gcd x y=g at hk hm ⊢
  subst hk hm
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  · rw [Nat.mul_div_cancel_left _ hg,Nat.mul_div_cancel_left _ hg]
    ring

theorem C_cross (a b : Scaled) :
    C ((b.s/Nat.gcd a.s b.s : ℕ) : ℚ)*C (a.s : ℚ)=
      C ((a.s/Nat.gcd a.s b.s : ℕ) : ℚ)*C (b.s : ℚ) := by
  rw [← map_mul,← map_mul]
  congr 1
  exact_mod_cast gcd_cross a.s b.s

theorem rep_addL {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (addL a b).Rep (p+q) := by
  unfold Scaled.Rep at *
  simp only [addL,Fast.lincF_eq,toPoly_add,toPoly_smul,ha,hb,Int.cast_natCast,Nat.cast_mul,
    map_mul]
  linear_combination p*C_cross a b

theorem rep_subL {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (subL a b).Rep (p-q) := by
  unfold Scaled.Rep at *
  simp only [subL,Fast.lincF_eq,toPoly_add,toPoly_smul,ha,hb,Int.cast_neg,Int.cast_natCast,
    Nat.cast_mul,map_mul,map_neg]
  linear_combination p*C_cross a b

theorem lcm_ne_zero {x y : ℕ} (hx : x≠0) (hy : y≠0) : x/Nat.gcd x y*y≠0 := by
  have hg : 0<Nat.gcd x y := Nat.gcd_pos_of_pos_left y (Nat.pos_of_ne_zero hx)
  have h1 : 0<x/Nat.gcd x y := Nat.div_pos (Nat.gcd_le_left y (Nat.pos_of_ne_zero hx)) hg
  exact Nat.mul_ne_zero h1.ne' hy

/-- `k a₀, (k+1) a₁, …`, written with the recursor (fewer kernel steps). -/
def derivAux (l : List ℤ) : ℤ → List ℤ :=
  List.rec (motive := fun _ => ℤ → List ℤ) (fun _ => [])
    (fun a _ ih k => Int.mul k a :: ih (Int.add k 1)) l

/-- The coefficient list of the derivative. -/
def derivL (l : List ℤ) : List ℤ :=
  List.casesOn (motive := fun _ => List ℤ) l [] (fun _ t => derivAux t 1)

theorem toPoly_derivAux : ∀ (l : List ℤ) (k : ℤ),
    toPoly (derivAux l k)=C (k:ℚ)*toPoly l+X*derivative (toPoly l)
  | [],k => by simp [derivAux,toPoly]
  | a :: l,k => by
    show toPoly (Int.mul k a :: derivAux l (Int.add k 1))=_
    rw [toPoly,toPoly_derivAux l (Int.add k 1),toPoly,derivative_add,derivative_C,
      derivative_mul,derivative_X]
    simp only [Int.mul_def,Int.add_def,Int.cast_mul,Int.cast_add,Int.cast_one,map_mul,map_add,
      map_one]
    ring

theorem toPoly_derivL : ∀ l : List ℤ,toPoly (derivL l)=derivative (toPoly l)
  | [] => by simp [derivL,toPoly]
  | a :: l => by
    show toPoly (derivAux l 1)=_
    rw [toPoly_derivAux,toPoly,derivative_add,derivative_C,derivative_mul,derivative_X]
    simp only [Int.cast_one,map_one]
    ring

/-- The derivative of a scaled list. -/
def derivS (c : Scaled) : Scaled := ⟨derivL c.l,c.s⟩

theorem rep_derivS {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (derivS c).Rep (derivative p) := by
  unfold Scaled.Rep at *
  rw [derivS,toPoly_derivL,hc,derivative_C_mul]

/-- The translation `p ↦ p.comp (C q + X)`: the centering of `[q-1,q+1]`. -/
def transS (c : Scaled) (q : ℚ) : Scaled := c.centerF 1 q.den q.num q.den

theorem rep_transS {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (q : ℚ) :
    (transS c q).Rep (p.comp (C q+X)) := by
  have hd : (q.den:ℚ)≠0 := by exact_mod_cast q.den_nz
  have h := hc.centeredF 1 q.den q.num q.den (a := q-1) (b := q+1) q.den_nz
    (by rw [Nat.cast_one,one_mul,Rat.num_div_den]; ring)
    (by rw [Int.cast_natCast,Nat.cast_one,one_mul,div_self hd]; ring)
  have e : affine (q-1) (q+1)=C q+X := by
    rw [affine,show (q-1+(q+1))/2=q by ring,show (q+1-(q-1))/2=1 by ring,map_one,one_mul]
  rwa [WholeIntervalPolynomial.centered,e] at h

theorem transS_ne_zero {c : Scaled} (hs : c.s≠0) (q : ℚ) : (transS c q).s≠0 :=
  Nat.mul_ne_zero hs (pow_ne_zero _ q.den_nz)

/-! ## Polynomial expressions -/

/-- A polynomial expression; `poly` is its meaning and `z` its integer value. -/
inductive PolyExpr where
  | cst : ℚ → PolyExpr
  | X : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | sub : PolyExpr → PolyExpr → PolyExpr
  | neg : PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  | deriv : PolyExpr → PolyExpr
  | divX : PolyExpr → PolyExpr
  | trans : ℚ → PolyExpr → PolyExpr

namespace PolyExpr

instance : Add PolyExpr := ⟨add⟩
instance : Sub PolyExpr := ⟨sub⟩
instance : Neg PolyExpr := ⟨neg⟩
instance : Mul PolyExpr := ⟨mul⟩
instance : HPow PolyExpr ℕ PolyExpr := ⟨pow⟩

/-- The polynomial of an expression. -/
def poly : PolyExpr → ℚ[X]
  | cst q => C q
  | X => Polynomial.X
  | add a b => a.poly+b.poly
  | sub a b => a.poly-b.poly
  | neg a => -a.poly
  | mul a b => a.poly*b.poly
  | pow a n => a.poly^n
  | deriv a => derivative a.poly
  | divX a => Polynomial.divX a.poly
  | trans q a => a.poly.comp (C q+Polynomial.X)

/-- The integer value of an expression. -/
def z : PolyExpr → Scaled
  | cst q => Scaled.const q
  | X => Scaled.var
  | add a b => addL a.z b.z
  | sub a b => subL a.z b.z
  | neg a => a.z.negF
  | mul a b => a.z.mulF b.z
  | pow a n => a.z.powF n
  | deriv a => derivS a.z
  | divX a => a.z.divX
  | trans q a => transS a.z q

theorem poly_neg (a : PolyExpr) : (-a).poly=-a.poly := rfl
theorem poly_deriv (a : PolyExpr) : (deriv a).poly=derivative a.poly := rfl
theorem poly_divX (a : PolyExpr) : (divX a).poly=Polynomial.divX a.poly := rfl
theorem poly_trans (q : ℚ) (a : PolyExpr) :
    (trans q a).poly=a.poly.comp (C q+Polynomial.X) := rfl

/-- The integer value represents the polynomial. -/
theorem rep : ∀ e : PolyExpr,e.z.Rep e.poly
  | cst q => Scaled.rep_const q
  | X => Scaled.rep_var
  | add a b => rep_addL (rep a) (rep b)
  | sub a b => rep_subL (rep a) (rep b)
  | neg a => (rep a).negF
  | mul a b => (rep a).mulF (rep b)
  | pow a n => (rep a).powF n
  | deriv a => rep_derivS (rep a)
  | divX a => (rep a).divX
  | trans q a => rep_transS (rep a) q

theorem scale_ne_zero : ∀ e : PolyExpr,e.z.s≠0
  | cst q => q.den_nz
  | X => one_ne_zero
  | add a b => lcm_ne_zero (scale_ne_zero a) (scale_ne_zero b)
  | sub a b => lcm_ne_zero (scale_ne_zero a) (scale_ne_zero b)
  | neg a => scale_ne_zero a
  | mul a b => Nat.mul_ne_zero (scale_ne_zero a) (scale_ne_zero b)
  | pow a n => pow_ne_zero n (scale_ne_zero a)
  | deriv a => scale_ne_zero a
  | divX a => scale_ne_zero a
  | trans q a => transS_ne_zero (scale_ne_zero a) q

/-- The coefficients of an expression. -/
theorem coeff_eq (e : PolyExpr) (i : ℕ) : e.poly.coeff i=(e.z.l.getD i 0:ℚ)/e.z.s :=
  e.rep.coeff e.scale_ne_zero i

theorem natDegree_le (e : PolyExpr) : e.poly.natDegree≤e.z.l.length-1 :=
  e.rep.natDegree_le e.scale_ne_zero

end PolyExpr

/-! ### Reification

`simp only [definitions…, reify_C, reify_X, …]` rewrites a polynomial built from these
operations into `PolyExpr.poly` of an expression, from the leaves up; `rfl` then names the
expression. -/

theorem reify_C (q : ℚ) : C q=(PolyExpr.cst q).poly := rfl
theorem reify_X : (X:ℚ[X])=PolyExpr.X.poly := rfl
theorem reify_one : (1:ℚ[X])=(PolyExpr.cst 1).poly := (map_one C).symm
theorem reify_zero : (0:ℚ[X])=(PolyExpr.cst 0).poly := (map_zero C).symm
theorem reify_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : ℚ[X]))=(PolyExpr.cst (OfNat.ofNat n)).poly := (map_ofNat C n).symm
theorem reify_add (a b : PolyExpr) : a.poly+b.poly=(a+b).poly := rfl
theorem reify_sub (a b : PolyExpr) : a.poly-b.poly=(a-b).poly := rfl
theorem reify_neg (a : PolyExpr) : -a.poly=(-a).poly := rfl
theorem reify_mul (a b : PolyExpr) : a.poly*b.poly=(a*b).poly := rfl
theorem reify_pow (a : PolyExpr) (n : ℕ) : a.poly^n=(a^n).poly := rfl
theorem reify_comp (q : ℚ) (a : PolyExpr) :
    a.poly.comp (PolyExpr.cst q+PolyExpr.X).poly=(PolyExpr.trans q a).poly := rfl

theorem natDegree_derivative_of_le {p : ℚ[X]} {n : ℕ} (h : p.natDegree≤n) :
    (derivative p).natDegree≤n :=
  (natDegree_derivative_le p).trans (by omega)

/-! ## Rational comparisons from integer ones -/

theorem lt_div_of_int {ρ : ℚ} {N : ℤ} {M : ℕ} (hM : M≠0) (h : ρ.num*M<N*ρ.den) :
    ρ<(N:ℚ)/M := by
  have hM' : (0:ℚ)<M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hd : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  rw [← Rat.num_div_den ρ,div_lt_div_iff₀ hd hM']
  exact_mod_cast h

theorem div_lt_of_int {ρ : ℚ} {N : ℤ} {M : ℕ} (hM : M≠0) (h : N*ρ.den<ρ.num*M) :
    (N:ℚ)/M<ρ := by
  have hM' : (0:ℚ)<M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hd : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  rw [← Rat.num_div_den ρ,div_lt_div_iff₀ hM' hd]
  exact_mod_cast h

theorem le_div_of_int {ρ : ℚ} {N : ℤ} {M : ℕ} (hM : M≠0) (h : ρ.num*M≤N*ρ.den) :
    ρ≤(N:ℚ)/M := by
  have hM' : (0:ℚ)<M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hd : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  rw [← Rat.num_div_den ρ,div_le_div_iff₀ hd hM']
  exact_mod_cast h

/-! ## Values at rational points -/

/-- `xd^(n-1)` times the value at `xn/xd` of a list of length `n`, by Horner's rule. -/
def evalZ (xn : ℤ) (xd : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a*((xd^l.length : ℕ) : ℤ)+xn*evalZ xn xd l

theorem eval_toPoly (xn : ℤ) {xd : ℕ} (hxd : xd≠0) : ∀ l : List ℤ,
    (toPoly l).eval ((xn:ℚ)/xd)*(xd:ℚ)^l.length=xd*(evalZ xn xd l:ℚ)
  | [] => by simp [toPoly,evalZ]
  | a :: l => by
    have ih := eval_toPoly xn hxd l
    have hx : (xd:ℚ)≠0 := by exact_mod_cast hxd
    simp only [toPoly,eval_add,eval_C,eval_mul,eval_X,List.length_cons,evalZ]
    push_cast
    rw [pow_succ]
    have e : (xn:ℚ)/xd*xd=xn := div_mul_cancel₀ _ hx
    linear_combination (xn:ℚ)*ih+(eval ((xn:ℚ)/xd) (toPoly l))*(xd:ℚ)^l.length*e

theorem eval_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (x : ℚ) :
    p.eval x=((x.den*evalZ x.num x.den c.l : ℤ):ℚ)/((c.s*x.den^c.l.length : ℕ):ℚ) := by
  have hs' : (c.s:ℚ)≠0 := by exact_mod_cast hs
  have hd : (x.den:ℚ)≠0 := by exact_mod_cast x.den_nz
  have h := eval_toPoly x.num x.den_nz c.l
  rw [Rat.num_div_den,hc,eval_mul,eval_C] at h
  push_cast
  rw [eq_div_iff (mul_ne_zero hs' (pow_ne_zero _ hd))]
  linear_combination h

/-- `ρ < e.poly.eval x`. -/
def valueGt (x ρ : ℚ) (e : PolyExpr) : Bool :=
  decide (ρ.num*((e.z.s*x.den^e.z.l.length : ℕ):ℤ)<(x.den*evalZ x.num x.den e.z.l)*ρ.den)

/-- `|e.poly.eval x| < ρ`. -/
def valueAbsLt (x ρ : ℚ) (e : PolyExpr) : Bool :=
  decide (|x.den*evalZ x.num x.den e.z.l| * ρ.den<ρ.num*((e.z.s*x.den^e.z.l.length : ℕ):ℤ))

theorem value_of_check {x ρ : ℚ} {e : PolyExpr} (h : valueGt x ρ e=true) :
    ρ<e.poly.eval x := by
  rw [eval_eq e.rep e.scale_ne_zero x]
  exact lt_div_of_int (Nat.mul_ne_zero e.scale_ne_zero (pow_ne_zero _ x.den_nz))
    (of_decide_eq_true h)

theorem value_abs_of_check {x ρ : ℚ} {e : PolyExpr} (h : valueAbsLt x ρ e=true) :
    |e.poly.eval x|<ρ := by
  have hM : (0:ℚ)<((e.z.s*x.den^e.z.l.length : ℕ):ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero e.scale_ne_zero (pow_ne_zero _ x.den_nz))
  rw [eval_eq e.rep e.scale_ne_zero x,abs_div,abs_of_pos hM,← Int.cast_abs]
  exact div_lt_of_int (Nat.mul_ne_zero e.scale_ne_zero (pow_ne_zero _ x.den_nz))
    (of_decide_eq_true h)

/-! ## Single coefficients and tail sums -/

theorem pow_scaled {r : ℚ} (hr : 0≤r) {k n : ℕ} (hk : k≤n) :
    r^k=((r.num.natAbs^k*r.den^(n-k) : ℕ):ℚ)/(r.den^n : ℕ) := by
  have hd : (r.den:ℚ)≠0 := by exact_mod_cast r.den_nz
  have hn : ((r.num.natAbs : ℕ):ℚ)=r.num := by
    rw [Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.mpr hr)]
  rw [eq_div_iff (by positivity)]
  push_cast
  rw [hn,← Rat.num_div_den r,div_pow,Rat.num_div_den r]
  have e : (r.den:ℚ)^n=r.den^k*r.den^(n-k) := by rw [← pow_add,Nat.add_sub_cancel' hk]
  rw [e]
  field_simp

/-- `ρ < e.poly.coeff k`. -/
def coeffGt (k : ℕ) (ρ : ℚ) (e : PolyExpr) : Bool :=
  decide (ρ.num*(e.z.s:ℤ)<e.z.l.getD k 0*ρ.den)

/-- `ρ ≤ e.poly.coeff k`. -/
def coeffGe (k : ℕ) (ρ : ℚ) (e : PolyExpr) : Bool :=
  decide (ρ.num*(e.z.s:ℤ)≤e.z.l.getD k 0*ρ.den)

/-- `|e.poly.coeff k| < ρ`. -/
def coeffAbsLt (k : ℕ) (ρ : ℚ) (e : PolyExpr) : Bool :=
  decide (|e.z.l.getD k 0| * ρ.den<ρ.num*(e.z.s:ℤ))

/-- `e.poly.coeff k = 0`. -/
def coeffZero (k : ℕ) (e : PolyExpr) : Bool := decide (e.z.l.getD k 0=0)

theorem coeff_gt_of_check {k : ℕ} {ρ : ℚ} {e : PolyExpr} (h : coeffGt k ρ e=true) :
    ρ<e.poly.coeff k := by
  rw [e.coeff_eq k]
  exact lt_div_of_int e.scale_ne_zero (of_decide_eq_true h)

theorem coeff_ge_of_check {k : ℕ} {ρ : ℚ} {e : PolyExpr} (h : coeffGe k ρ e=true) :
    ρ≤e.poly.coeff k := by
  rw [e.coeff_eq k]
  exact le_div_of_int e.scale_ne_zero (of_decide_eq_true h)

theorem coeff_abs_of_check {k : ℕ} {ρ : ℚ} {e : PolyExpr} (h : coeffAbsLt k ρ e=true) :
    |e.poly.coeff k|<ρ := by
  have hS : (0:ℚ)<e.z.s := by exact_mod_cast Nat.pos_of_ne_zero e.scale_ne_zero
  rw [e.coeff_eq k,abs_div,abs_of_pos hS,← Int.cast_abs]
  exact div_lt_of_int e.scale_ne_zero (of_decide_eq_true h)

theorem coeff_zero_of_check {k : ℕ} {e : PolyExpr} (h : coeffZero k e=true) :
    e.poly.coeff k=0 := by
  rw [e.coeff_eq k,of_decide_eq_true h,Int.cast_zero,zero_div]

theorem sum_range_list {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n,f i=((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,List.range_succ,List.map_append,List.sum_append]; simp

/-- `∑_{j<n} g(T_{j+a}) rn^(j+e) rd^(n-1-j)`: `S rd^(n-1+e)` times a tail sum of `T/S`. -/
def tailSumZ (g : ℤ → ℤ) (n a e rn rd : ℕ) (T : List ℤ) : ℤ :=
  ((List.range n).map (fun j => g (T.getD (j+a) 0)*((rn^(j+e)*rd^(n-1-j) : ℕ) : ℤ))).sum

/-- A tail sum `∑_{j<n} g(p_{j+a}) r^(j+e)` of a represented polynomial, for a positively
homogeneous `g` with integer form `gZ`. -/
theorem tailSum_eq (g : ℚ → ℚ) (gZ : ℤ → ℤ)
    (hg : ∀ (x : ℤ) (s : ℚ),0<s → g ((x:ℚ)/s)=(gZ x:ℚ)/s) {c : Scaled} {p : ℚ[X]}
    (hc : c.Rep p) (hs : c.s≠0) (n a e : ℕ) {r : ℚ} (hr : 0≤r) :
    ∑ j : Fin n,g (p.coeff (j.val+a))*r^(j.val+e)=
      (tailSumZ gZ n a e r.num.natAbs r.den c.l:ℚ)/(c.s*r.den^(n-1+e) : ℕ) := by
  have hS : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hD : (0:ℚ)<(c.s*r.den^(n-1+e) : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero hs (pow_ne_zero _ r.den_nz))
  simp only [hc.coeff hs]
  rw [Fin.sum_univ_eq_sum_range (fun j => g ((c.l.getD (j+a) 0:ℚ)/c.s)*r^(j+e)) n]
  have hterm : ∀ j∈Finset.range n,g ((c.l.getD (j+a) 0:ℚ)/c.s)*r^(j+e)=
      ((gZ (c.l.getD (j+a) 0)*((r.num.natAbs^(j+e)*r.den^(n-1-j) : ℕ):ℤ) : ℤ):ℚ)/
        (c.s*r.den^(n-1+e) : ℕ) := by
    intro j hj
    have hj' : j+e≤n-1+e := by have := Finset.mem_range.mp hj; omega
    have hk : n-1+e-(j+e)=n-1-j := by omega
    rw [hg _ _ hS,pow_scaled hr hj',hk]
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_pow,Nat.cast_mul,Nat.cast_pow]
    field_simp
  rw [Finset.sum_congr rfl hterm,← Finset.sum_div,tailSumZ,← sum_range_list]
  push_cast
  rfl

theorem abs_div_pos (x : ℤ) (s : ℚ) (hs : 0<s) : |(x:ℚ)/s|=((|x| : ℤ):ℚ)/s := by
  rw [abs_div,abs_of_pos hs,Int.cast_abs]

theorem negPart_div_pos (x : ℤ) (s : ℚ) (hs : 0<s) :
    max 0 (-((x:ℚ)/s))=((max 0 (-x) : ℤ):ℚ)/s := by
  rw [Int.cast_max,Int.cast_zero,Int.cast_neg,← neg_div]
  rcases le_total (-(x:ℚ)) 0 with h | h
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg h hs.le),max_eq_left h,zero_div]
  · rw [max_eq_right (div_nonneg h hs.le),max_eq_right h]

/-- `ρ < e.poly.coeff 2 - ∑_{j<n} |e.poly.coeff (j+3)| r^(j+1)`: a quadratic coefficient that
dominates the tail on `|x| ≤ r`. -/
def quadReserveGt (n : ℕ) (r ρ : ℚ) (e : PolyExpr) : Bool :=
  decide (0≤r) && decide (ρ.num*((e.z.s*r.den^(n-1+1) : ℕ) : ℤ)<
    (e.z.l.getD 2 0*((r.den^(n-1+1) : ℕ) : ℤ)-
      tailSumZ (fun x => |x|) n 3 1 r.num.natAbs r.den e.z.l)*ρ.den)

theorem quadReserve_of_check {n : ℕ} {r ρ : ℚ} {e : PolyExpr}
    (h : quadReserveGt n r ρ e=true) :
    ρ<e.poly.coeff 2-∑ j : Fin n,|e.poly.coeff (j.val+3)| *r^(j.val+1) := by
  simp only [quadReserveGt,Bool.and_eq_true,decide_eq_true_eq] at h
  rw [tailSum_eq (fun y => |y|) (fun x => |x|) abs_div_pos e.rep e.scale_ne_zero n 3 1 h.1,
    e.coeff_eq 2]
  have hS : (e.z.s:ℚ)≠0 := by exact_mod_cast e.scale_ne_zero
  have hd : (r.den:ℚ)≠0 := by exact_mod_cast r.den_nz
  have e1 : (e.z.l.getD 2 0:ℚ)/e.z.s-
      (tailSumZ (fun x => |x|) n 3 1 r.num.natAbs r.den e.z.l:ℚ)/(e.z.s*r.den^(n-1+1) : ℕ)=
      ((e.z.l.getD 2 0*((r.den^(n-1+1) : ℕ) : ℤ)-
        tailSumZ (fun x => |x|) n 3 1 r.num.natAbs r.den e.z.l : ℤ):ℚ)/
          (e.z.s*r.den^(n-1+1) : ℕ) := by
    push_cast
    field_simp
  rw [e1]
  exact lt_div_of_int (Nat.mul_ne_zero e.scale_ne_zero (pow_ne_zero _ r.den_nz)) h.2

/-! ## Monomial coefficient bounds of `CenteredMonomialBounds` -/

/-- `CenteredMonomialBounds.lowerTerm` of an integer, without the power. -/
def lowerTermZ (k : ℕ) (c : ℤ) : ℤ := if k%2=0 then min c 0 else -|c|

/-- `S rd^n` times `CenteredMonomialBounds.lower n (rn/rd)` of `T/S`. -/
def lowerSumZ (n rn rd : ℕ) (T : List ℤ) : ℤ :=
  T.getD 0 0*((rd^n : ℕ) : ℤ)+((List.range n).map (fun j =>
    lowerTermZ (j+1) (T.getD (j+1) 0)*((rn^(j+1)*rd^(n-(j+1)) : ℕ) : ℤ))).sum

/-- `S rd^n` times `CenteredMonomialBounds.upper n (rn/rd)` of `T/S`. -/
def upperSumZ (n rn rd : ℕ) (T : List ℤ) : ℤ :=
  T.getD 0 0*((rd^n : ℕ) : ℤ)+((List.range n).map (fun j =>
    max (T.getD (j+1) 0) 0*((rn^(j+1)*rd^(n-(j+1)) : ℕ) : ℤ))).sum

theorem lowerTerm_eq {S : ℕ} (hS : S≠0) {r : ℚ} (hr : 0≤r) {k n : ℕ} (hk : k≤n)
    (T : ℤ) :
    CenteredMonomialBounds.lowerTerm ((T:ℚ)/S) r k=
      ((lowerTermZ k T*((r.num.natAbs^k*r.den^(n-k) : ℕ):ℤ) : ℤ):ℚ)/(S*r.den^n : ℕ) := by
  have hS' : (0:ℚ)<S := by exact_mod_cast Nat.pos_of_ne_zero hS
  have hd : (0:ℚ)<(r.den^n : ℕ) := by exact_mod_cast pow_pos r.den_pos n
  rw [CenteredMonomialBounds.lowerTerm,lowerTermZ,pow_scaled hr hk]
  split_ifs
  · have hmin : min ((T:ℚ)/S) 0=((min T 0 : ℤ):ℚ)/S := by
      rw [Int.cast_min,Int.cast_zero]
      rcases le_total (T:ℚ) 0 with h | h
      · rw [min_eq_left h,min_eq_left (div_nonpos_of_nonpos_of_nonneg h hS'.le)]
      · rw [min_eq_right h,min_eq_right (div_nonneg h hS'.le),zero_div]
    rw [hmin]
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_pow,Nat.cast_mul,Nat.cast_pow]
    field_simp
  · rw [abs_div,abs_of_pos hS']
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_pow,Int.cast_neg,Int.cast_abs,Nat.cast_mul,
      Nat.cast_pow]
    field_simp

theorem lower_eq {c : Scaled} {q : ℚ[X]} (hc : c.Rep q) (hs : c.s≠0) (n : ℕ) {r : ℚ}
    (hr : 0≤r) :
    CenteredMonomialBounds.lower n r q=
      (lowerSumZ n r.num.natAbs r.den c.l:ℚ)/(c.s*r.den^n : ℕ) := by
  have hS : (0:ℚ)<(c.s*r.den^n : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero hs (pow_ne_zero _ r.den_nz))
  rw [CenteredMonomialBounds.lower,hc.coeff hs]
  simp only [hc.coeff hs]
  rw [Fin.sum_univ_eq_sum_range (fun j => CenteredMonomialBounds.lowerTerm
    ((c.l.getD (j+1) 0:ℚ)/c.s) r (j+1)) n]
  rw [Finset.sum_congr rfl (fun j hj => lowerTerm_eq hs hr
    (show j+1≤n from Finset.mem_range.mp hj) (c.l.getD (j+1) 0)),← Finset.sum_div,
    lowerSumZ,← sum_range_list]
  have hd : (c.s:ℚ)≠0 := by exact_mod_cast hs
  have hr' : (r.den:ℚ)≠0 := by exact_mod_cast r.den_nz
  rw [eq_div_iff hS.ne']
  push_cast
  field_simp

theorem upper_eq {c : Scaled} {q : ℚ[X]} (hc : c.Rep q) (hs : c.s≠0) (n : ℕ) {r : ℚ}
    (hr : 0≤r) :
    CenteredMonomialBounds.upper n r q=
      (upperSumZ n r.num.natAbs r.den c.l:ℚ)/(c.s*r.den^n : ℕ) := by
  have hS : (0:ℚ)<(c.s*r.den^n : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero hs (pow_ne_zero _ r.den_nz))
  have hS' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  rw [CenteredMonomialBounds.upper]
  simp only [hc.coeff hs]
  rw [Fin.sum_univ_eq_sum_range (fun j => max ((c.l.getD (j+1) 0:ℚ)/c.s) 0*r^(j+1)) n]
  have hterm : ∀ j∈Finset.range n,max ((c.l.getD (j+1) 0:ℚ)/c.s) 0*r^(j+1)=
      ((max (c.l.getD (j+1) 0) 0*((r.num.natAbs^(j+1)*r.den^(n-(j+1)) : ℕ):ℤ) : ℤ):ℚ)/
        (c.s*r.den^n : ℕ) := by
    intro j hj
    have hmax : max ((c.l.getD (j+1) 0:ℚ)/c.s) 0=((max (c.l.getD (j+1) 0) 0 : ℤ):ℚ)/c.s := by
      rw [Int.cast_max,Int.cast_zero]
      rcases le_total (c.l.getD (j+1) 0:ℚ) 0 with h | h
      · rw [max_eq_right h,max_eq_right (div_nonpos_of_nonpos_of_nonneg h hS'.le),zero_div]
      · rw [max_eq_left h,max_eq_left (div_nonneg h hS'.le)]
    rw [hmax,pow_scaled hr (show j+1≤n from Finset.mem_range.mp hj)]
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_pow,Nat.cast_mul,Nat.cast_pow]
    field_simp
  rw [Finset.sum_congr rfl hterm,← Finset.sum_div,upperSumZ,← sum_range_list]
  rw [eq_div_iff hS.ne']
  push_cast
  field_simp

/-- `e.poly` has degree at most `n`. -/
def cmSeries (n : ℕ) (e : PolyExpr) : Bool := decide (e.z.l.length≤n+1)

theorem natDegree_of_check {n : ℕ} {e : PolyExpr} (h : cmSeries n e=true) :
    e.poly.natDegree≤n :=
  e.natDegree_le.trans (by have := of_decide_eq_true h; omega)

theorem series_self {n : ℕ} {q : ℚ[X]} (hq : q.natDegree≤n) :
    q=CenteredMonomialBounds.series n q := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow' q (n := n+1) (by omega)]
  rw [CenteredMonomialBounds.series,Finset.sum_range_succ',add_comm]
  congr 1
  · simp
  · exact (Fin.sum_univ_eq_sum_range (fun j => C (q.coeff (j+1))*X^(j+1)) n).symm

/-- A polynomial of degree at most `n` is its own translated `series n`. -/
theorem series_of_natDegree {n : ℕ} {p : ℚ[X]} (hp : p.natDegree≤n) (m : ℚ) :
    CenteredMonomialBounds.translated m p=
      CenteredMonomialBounds.series n (CenteredMonomialBounds.translated m p) := by
  apply series_self
  rw [CenteredMonomialBounds.translated]
  refine natDegree_comp_le.trans ?_
  have h1 : (C m+X : ℚ[X]).natDegree≤1 := by
    rw [add_comm]; exact (natDegree_X_add_C m).le
  calc p.natDegree*(C m+X : ℚ[X]).natDegree≤p.natDegree*1 := Nat.mul_le_mul_left _ h1
    _≤n := by omega

theorem series_of_check {n : ℕ} {e : PolyExpr} (h : cmSeries n e=true) (m : ℚ) :
    CenteredMonomialBounds.translated m e.poly=
      CenteredMonomialBounds.series n (CenteredMonomialBounds.translated m e.poly) :=
  series_of_natDegree (natDegree_of_check h) m

/-! ### Cubics in closed form -/

theorem translated_cubic (m a b c d : ℚ) :
    CenteredMonomialBounds.translated m (C a+C b*X+C c*X^2+C d*X^3)=
      C (a+b*m+c*m^2+d*m^3)+C (b+2*c*m+3*d*m^2)*X+C (c+3*d*m)*X^2+C d*X^3 := by
  apply Polynomial.funext
  intro x
  simp only [CenteredMonomialBounds.translated,eval_comp,eval_add,eval_mul,eval_pow,eval_C,
    eval_X]
  ring

theorem natDegree_cubic_le (a b c d : ℚ) :
    (C a+C b*X+C c*X^2+C d*X^3 : ℚ[X]).natDegree≤3 := by
  compute_degree!

theorem coeff_cubic (a b c d : ℚ) :
    (C a+C b*X+C c*X^2+C d*X^3 : ℚ[X]).coeff 0=a ∧
      (C a+C b*X+C c*X^2+C d*X^3 : ℚ[X]).coeff 1=b ∧
      (C a+C b*X+C c*X^2+C d*X^3 : ℚ[X]).coeff 2=c ∧
      (C a+C b*X+C c*X^2+C d*X^3 : ℚ[X]).coeff 3=d := by
  simp [coeff_X,coeff_C,coeff_X_pow]

/-- `lowerOn 3` of a cubic. -/
theorem lowerOn_cubic (m r a b c d : ℚ) :
    CenteredMonomialBounds.lowerOn 3 m r (C a+C b*X+C c*X^2+C d*X^3)=
      (a+b*m+c*m^2+d*m^3)-|b+2*c*m+3*d*m^2| * r+min (c+3*d*m) 0*r^2-|d| * r^3 := by
  obtain ⟨h0,h1,h2,h3⟩ := coeff_cubic (a+b*m+c*m^2+d*m^3) (b+2*c*m+3*d*m^2) (c+3*d*m) d
  simp only [CenteredMonomialBounds.lowerOn,CenteredMonomialBounds.lower,translated_cubic,
    Fin.sum_univ_three,Fin.val_zero,Fin.val_one,Fin.val_two,Nat.reduceAdd,h0,h1,h2,h3,
    CenteredMonomialBounds.lowerTerm,Nat.reduceMod,one_ne_zero,↓reduceIte]
  ring

theorem neg_cubic (a b c d : ℚ) :
    -(C a+C b*X+C c*X^2+C d*X^3 : ℚ[X])=C (-a)+C (-b)*X+C (-c)*X^2+C (-d)*X^3 := by
  simp only [map_neg]
  ring

/-- `ρ < CenteredMonomialBounds.lowerOn n m r e.poly`. -/
def cmLowerGt (n : ℕ) (m r ρ : ℚ) (e : PolyExpr) : Bool :=
  decide (0≤r) && decide (ρ.num*(((PolyExpr.trans m e).z.s*r.den^n : ℕ) : ℤ)<
    lowerSumZ n r.num.natAbs r.den (PolyExpr.trans m e).z.l*ρ.den)

theorem lowerOn_of_check {n : ℕ} {m r ρ : ℚ} {e : PolyExpr} (h : cmLowerGt n m r ρ e=true) :
    ρ<CenteredMonomialBounds.lowerOn n m r e.poly := by
  simp only [cmLowerGt,Bool.and_eq_true,decide_eq_true_eq] at h
  have hc := (PolyExpr.trans m e).rep
  rw [PolyExpr.poly_trans] at hc
  have hs := (PolyExpr.trans m e).scale_ne_zero
  rw [CenteredMonomialBounds.lowerOn,CenteredMonomialBounds.translated,lower_eq hc hs n h.1]
  exact lt_div_of_int (Nat.mul_ne_zero hs (pow_ne_zero _ r.den_nz)) h.2

/-- `CenteredMonomialBounds.upperOn n l h e.poly < ρ`. -/
def cmUpperLt (n : ℕ) (l h ρ : ℚ) (e : PolyExpr) : Bool :=
  decide (0≤h-l) && decide (upperSumZ n (h-l).num.natAbs (h-l).den (PolyExpr.trans l e).z.l*
    ρ.den<ρ.num*(((PolyExpr.trans l e).z.s*(h-l).den^n : ℕ) : ℤ))

theorem upperOn_of_check {n : ℕ} {l h ρ : ℚ} {e : PolyExpr} (hc : cmUpperLt n l h ρ e=true) :
    CenteredMonomialBounds.upperOn n l h e.poly<ρ := by
  simp only [cmUpperLt,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hr := (PolyExpr.trans l e).rep
  rw [PolyExpr.poly_trans] at hr
  have hs := (PolyExpr.trans l e).scale_ne_zero
  rw [CenteredMonomialBounds.upperOn,CenteredMonomialBounds.translated,upper_eq hr hs n hc.1]
  exact div_lt_of_int (Nat.mul_ne_zero hs (pow_ne_zero _ (h-l).den_nz)) hc.2

/-! ## Chebyshev bounds of `WholeIntervalPolynomial` -/

/-- `lowerZ` on a list. -/
def lowerChebZ (D : ℕ) (B : List ℤ) : ℤ :=
  B.getD 0 0-((List.range D).map (fun j => ((B.getD (j+1) 0).natAbs : ℤ))).sum

theorem lowerZ_eq (D : ℕ) (B : List ℤ) :
    Certificate.lowerZ D (fun j => B.getD j 0)=lowerChebZ D B := by
  simp only [Certificate.lowerZ,lowerChebZ,
    Fin.sum_univ_eq_sum_range (fun j => |B.getD (j+1) 0|) D,sum_range_list,Int.natCast_natAbs]

/-- The degree-`D` expansion of the polynomial represented by `c`, and
`ρ < WholeIntervalPolynomial.lowerOn D a b` of it, for `c` the centered list. -/
def chebLowerGtS (D : ℕ) (ρ : ℚ) (c : Scaled) : Bool :=
  decide (c.l.length≤D+1) && decide (ρ.num*((c.s*2^c.l.length : ℕ) : ℤ)<
    lowerChebZ D (Fast.chebF c.l)*((2*ρ.den : ℕ) : ℤ))

/-- `chebLowerGtS` of the centering of `e` by `num den s t`. -/
def chebLowerGt (D num den : ℕ) (s t : ℤ) (ρ : ℚ) (e : PolyExpr) : Bool :=
  chebLowerGtS D ρ (e.z.centerF num den s t)

theorem chebLower_of_checkS {D : ℕ} {ρ a b : ℚ} {c : Scaled} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b p)) (hs : c.s≠0)
    (h : chebLowerGtS D ρ c=true) :
    WholeIntervalPolynomial.centered a b p=expansion D (WholeIntervalPolynomial.centered a b p) ∧
      ρ<WholeIntervalPolynomial.lowerOn D a b p := by
  simp only [chebLowerGtS,Bool.and_eq_true,decide_eq_true_eq,Fast.chebF_eq] at h
  refine ⟨hc.eq_expansion hs h.1,?_⟩
  rw [lowerOn_eq_of_rep hc hs h.1,lowerZ_eq]
  have hK : (0:ℚ)<c.s*2^c.l.length :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hs) (by positivity)
  have hρ : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  rw [← Rat.num_div_den ρ,div_lt_div_iff₀ hρ (half_pos hK)]
  have h2 := (Int.cast_lt (R := ℚ)).mpr h.2
  push_cast at h2
  linarith

theorem chebLower_of_check {D num den : ℕ} {s t : ℤ} {ρ a b : ℚ} {e : PolyExpr}
    (h : chebLowerGt D num den s t ρ e=true) (hden : den≠0) (hm : (a+b)/2=num*s/den)
    (hh : (b-a)/2=num*t/den) :
    WholeIntervalPolynomial.centered a b e.poly=
        expansion D (WholeIntervalPolynomial.centered a b e.poly) ∧
      ρ<WholeIntervalPolynomial.lowerOn D a b e.poly :=
  chebLower_of_checkS (e.rep.centeredF num den s t hden hm hh)
    (Nat.mul_ne_zero e.scale_ne_zero (pow_ne_zero _ hden)) h

/-! ## Bivariate expressions and tensor Chebyshev coefficients

A bivariate polynomial (`TensorWholeIntervalPolynomial.Bivar`, outer variable `X`, inner
variable `C X`) is carried by integer rows `L` (row `a`: the coefficients of `X^a`, constant term
first) and a scale `s`: `BScaled.Rep c p` says `toPolyB c.L = C (C s) * p`. A `BExpr` has the
meaning `poly` and the value `z`. `tensorCheck D ρ₀ ρ₁ e` (`tensor_of_check`) checks the
degree-`D` tensor Chebyshev expansion of `e.poly`, `ρ₀ < coefficient D e.poly 0 0` and
`norm D (coefficient D e.poly) < ρ₁`; the coefficients are the Chebyshev transforms (`chebList`)
of the rows and then of the columns. -/

section Bivariate
open TensorWholeIntervalPolynomial

/-- The bivariate polynomial with rows `L`. -/
def toPolyB : List (List ℤ) → Bivar
  | [] => 0
  | l :: L => C (toPoly l)+X*toPolyB L

def addB : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [],M => M
  | l :: L,[] => l :: L
  | l :: L,m :: M => Fast.addF l m :: addB L M

/-- Every row times the inner polynomial `c`. -/
def rowMulB (c : List ℤ) : List (List ℤ) → List (List ℤ)
  | [] => []
  | l :: L => Fast.mulF c l :: rowMulB c L

def mulB : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [],_ => []
  | l :: L,M => addB (rowMulB l M) ([] :: mulB L M)

def powB (L : List (List ℤ)) : ℕ → List (List ℤ)
  | 0 => [[1]]
  | n+1 => mulB (powB L n) L

def scaleB (k : ℤ) (L : List (List ℤ)) : List (List ℤ) := L.map (Fast.smulF k)

theorem toPolyB_addB : ∀ L M : List (List ℤ),toPolyB (addB L M)=toPolyB L+toPolyB M
  | [],M => by simp [addB,toPolyB]
  | l :: L,[] => by simp [addB,toPolyB]
  | l :: L,m :: M => by
    simp only [addB,toPolyB,toPolyB_addB L M,Fast.addF_eq,toPoly_add,map_add]
    ring

theorem toPolyB_rowMulB (c : List ℤ) : ∀ L : List (List ℤ),
    toPolyB (rowMulB c L)=C (toPoly c)*toPolyB L
  | [] => by simp [rowMulB,toPolyB]
  | l :: L => by
    simp only [rowMulB,toPolyB,toPolyB_rowMulB c L,Fast.mulF_eq,toPoly_mul,map_mul]
    ring

theorem toPolyB_mulB : ∀ L M : List (List ℤ),toPolyB (mulB L M)=toPolyB L*toPolyB M
  | [],M => by simp [mulB,toPolyB]
  | l :: L,M => by
    rw [mulB,toPolyB_addB,toPolyB_rowMulB]
    simp only [toPolyB,toPolyB_mulB L M,toPoly,map_zero,zero_add]
    ring

theorem toPolyB_powB (L : List (List ℤ)) : ∀ n : ℕ,toPolyB (powB L n)=toPolyB L^n
  | 0 => by simp [powB,toPolyB,toPoly]
  | n+1 => by rw [powB,toPolyB_mulB,toPolyB_powB L n,pow_succ]

theorem toPolyB_scaleB (k : ℤ) : ∀ L : List (List ℤ),
    toPolyB (scaleB k L)=C (C (k:ℚ))*toPolyB L
  | [] => by simp [scaleB,toPolyB]
  | l :: L => by
    have ih := toPolyB_scaleB k L
    simp only [scaleB,List.map_cons,toPolyB] at ih ⊢
    rw [ih,Fast.smulF_eq,toPoly_smul,map_mul]
    ring

theorem coeff_toPolyB : ∀ (L : List (List ℤ)) (a : ℕ),(toPolyB L).coeff a=toPoly (L.getD a [])
  | [],a => by simp [toPolyB,toPoly]
  | l :: L,0 => by simp [toPolyB]
  | l :: L,a+1 => by simp [toPolyB,coeff_toPolyB L a]

/-- Integer rows with a scale. -/
structure BScaled where
  L : List (List ℤ)
  s : ℕ

/-- `c` represents `p`: its rows are `s` times the coefficients of `p`. -/
def BScaled.Rep (c : BScaled) (p : Bivar) : Prop := toPolyB c.L=C (C (c.s:ℚ))*p

/-- The sum, over the least common multiple of the scales. -/
def addBS (a b : BScaled) : BScaled :=
  ⟨addB (scaleB ((b.s/Nat.gcd a.s b.s : ℕ) : ℤ) a.L)
    (scaleB ((a.s/Nat.gcd a.s b.s : ℕ) : ℤ) b.L),a.s/Nat.gcd a.s b.s*b.s⟩

/-- The difference, over the least common multiple of the scales. -/
def subBS (a b : BScaled) : BScaled :=
  ⟨addB (scaleB ((b.s/Nat.gcd a.s b.s : ℕ) : ℤ) a.L)
    (scaleB (-((a.s/Nat.gcd a.s b.s : ℕ) : ℤ)) b.L),a.s/Nat.gcd a.s b.s*b.s⟩

def mulBS (a b : BScaled) : BScaled := ⟨mulB a.L b.L,a.s*b.s⟩

def powBS (a : BScaled) (n : ℕ) : BScaled := ⟨powB a.L n,a.s^n⟩

theorem CC_cross (a b : ℕ) :
    (C (C ((b/Nat.gcd a b : ℕ) : ℚ)) : Bivar)*C (C (a : ℚ))=
      C (C ((a/Nat.gcd a b : ℕ) : ℚ))*C (C (b : ℚ)) := by
  rw [← map_mul,← map_mul,← map_mul,← map_mul]
  congr 2
  exact_mod_cast gcd_cross a b

theorem rep_addBS {a b : BScaled} {p q : Bivar} (ha : a.Rep p) (hb : b.Rep q) :
    (addBS a b).Rep (p+q) := by
  unfold BScaled.Rep at *
  simp only [addBS,toPolyB_addB,toPolyB_scaleB,ha,hb,Int.cast_natCast,Nat.cast_mul,map_mul]
  linear_combination p*CC_cross a.s b.s

theorem rep_subBS {a b : BScaled} {p q : Bivar} (ha : a.Rep p) (hb : b.Rep q) :
    (subBS a b).Rep (p-q) := by
  unfold BScaled.Rep at *
  simp only [subBS,toPolyB_addB,toPolyB_scaleB,ha,hb,Int.cast_neg,Int.cast_natCast,Nat.cast_mul,
    map_mul,map_neg]
  linear_combination p*CC_cross a.s b.s

theorem rep_mulBS {a b : BScaled} {p q : Bivar} (ha : a.Rep p) (hb : b.Rep q) :
    (mulBS a b).Rep (p*q) := by
  unfold BScaled.Rep at *
  simp only [mulBS,toPolyB_mulB,ha,hb,Nat.cast_mul,map_mul]
  ring

theorem rep_powBS {a : BScaled} {p : Bivar} (ha : a.Rep p) (n : ℕ) : (powBS a n).Rep (p^n) := by
  unfold BScaled.Rep at *
  simp only [powBS,toPolyB_powB,ha,Nat.cast_pow,map_pow]
  ring

theorem BScaled.Rep.coeff_coeff {c : BScaled} {p : Bivar} (hc : c.Rep p) (hs : c.s≠0)
    (a b : ℕ) :
    (p.coeff a).coeff b=((c.L.getD a []).getD b 0:ℚ)/c.s := by
  have hs' : (c.s:ℚ)≠0 := by exact_mod_cast hs
  have h := congrArg (fun q : Bivar => (q.coeff a).coeff b) hc
  simp only [coeff_toPolyB,coeff_toPoly,coeff_C_mul] at h
  rw [h]
  field_simp

/-- A bivariate polynomial expression. -/
inductive BExpr where
  | cst : ℚ → BExpr
  | X : BExpr
  | Y : BExpr
  | add : BExpr → BExpr → BExpr
  | sub : BExpr → BExpr → BExpr
  | mul : BExpr → BExpr → BExpr
  | pow : BExpr → ℕ → BExpr

namespace BExpr

instance : Add BExpr := ⟨add⟩
instance : Sub BExpr := ⟨sub⟩
instance : Mul BExpr := ⟨mul⟩
instance : HPow BExpr ℕ BExpr := ⟨pow⟩

/-- The polynomial of an expression; `Y` is the inner variable. -/
def poly : BExpr → Bivar
  | cst q => scalar q
  | X => Polynomial.X
  | Y => C Polynomial.X
  | add a b => a.poly+b.poly
  | sub a b => a.poly-b.poly
  | mul a b => a.poly*b.poly
  | pow a n => a.poly^n

/-- The integer value of an expression. -/
def z : BExpr → BScaled
  | cst q => ⟨[[q.num]],q.den⟩
  | X => ⟨[[],[1]],1⟩
  | Y => ⟨[[0,1]],1⟩
  | add a b => addBS a.z b.z
  | sub a b => subBS a.z b.z
  | mul a b => mulBS a.z b.z
  | pow a n => powBS a.z n

theorem rep : ∀ e : BExpr,e.z.Rep e.poly
  | cst q => by
    unfold BScaled.Rep
    simp only [z,poly,scalar,toPolyB,toPoly,mul_zero,add_zero,← map_mul,Rat.den_mul_eq_num]
  | X => by simp [BScaled.Rep,z,poly,toPolyB,toPoly]
  | Y => by simp [BScaled.Rep,z,poly,toPolyB,toPoly]
  | add a b => rep_addBS (rep a) (rep b)
  | sub a b => rep_subBS (rep a) (rep b)
  | mul a b => rep_mulBS (rep a) (rep b)
  | pow a n => rep_powBS (rep a) n

theorem scale_ne_zero : ∀ e : BExpr,e.z.s≠0
  | cst q => q.den_nz
  | X => one_ne_zero
  | Y => one_ne_zero
  | add a b => lcm_ne_zero (scale_ne_zero a) (scale_ne_zero b)
  | sub a b => lcm_ne_zero (scale_ne_zero a) (scale_ne_zero b)
  | mul a b => Nat.mul_ne_zero (scale_ne_zero a) (scale_ne_zero b)
  | pow a n => pow_ne_zero n (scale_ne_zero a)

end BExpr

theorem reifyB_scalar (q : ℚ) : scalar q=(BExpr.cst q).poly := rfl
theorem reifyB_one : (1:Bivar)=(BExpr.cst 1).poly := by simp [BExpr.poly,scalar]
theorem reifyB_X : (X:Bivar)=BExpr.X.poly := rfl
theorem reifyB_Y : (C X:Bivar)=BExpr.Y.poly := rfl
theorem reifyB_add (a b : BExpr) : a.poly+b.poly=(a+b).poly := rfl
theorem reifyB_sub (a b : BExpr) : a.poly-b.poly=(a-b).poly := rfl
theorem reifyB_mul (a b : BExpr) : a.poly*b.poly=(a*b).poly := rfl
theorem reifyB_pow (a : BExpr) (n : ℕ) : a.poly^n=(a^n).poly := rfl

/-! ### The tensor expansion of a polynomial of bounded degrees -/

theorem monomial_outer {a D : ℕ} (ha : a≤D) :
    (X:Bivar)^a=∑ i : Fin (D+1),scalar (monomialCoefficient a i)*Chebyshev.T ℚ[X] (i:ℕ) := by
  have h := congrArg (Polynomial.map (C : ℚ →+* ℚ[X]))
    (sum_monomialCoefficient_mul_T_of_le ha)
  simp only [Polynomial.map_pow,Polynomial.map_X,Polynomial.map_sum,Polynomial.map_mul,
    Polynomial.map_C,Chebyshev.map_T] at h
  rw [← h,Fin.sum_univ_eq_sum_range (fun i => scalar (monomialCoefficient a i)*
    Chebyshev.T ℚ[X] (i:ℕ)) (D+1)]
  rfl

theorem monomial_inner {b D : ℕ} (hb : b≤D) :
    (C (X^b) : Bivar)=
      ∑ j : Fin (D+1),scalar (monomialCoefficient b j)*C (Chebyshev.T ℚ (j:ℕ)) := by
  rw [← sum_monomialCoefficient_mul_T_of_le hb,map_sum,Fin.sum_univ_eq_sum_range (fun j => scalar
    (monomialCoefficient b j)*C (Chebyshev.T ℚ (j:ℕ))) (D+1)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [scalar,map_mul]

theorem series_full (D : ℕ) (c : ℕ → ℕ → ℚ) :
    TensorWholeIntervalPolynomial.series D c=
      ∑ i : Fin (D+1),∑ j : Fin (D+1),scalar (c i j)*basis i j := by
  rw [← Fintype.sum_prod_type' (fun (i j : Fin (D+1)) => scalar (c i j)*basis i j),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ((0:Fin (D+1)),(0:Fin (D+1))))]
  simp only [TensorWholeIntervalPolynomial.series,indices]
  congr 1
  simp [basis]

theorem sum_swap4 {M : Type*} [AddCommMonoid M] {D : ℕ}
    (F : Fin (D+1) → Fin (D+1) → Fin (D+1) → Fin (D+1) → M) :
    ∑ a,∑ b,∑ i,∑ j,F a b i j=∑ i,∑ j,∑ a,∑ b,F a b i j := by
  calc ∑ a,∑ b,∑ i,∑ j,F a b i j=∑ a,∑ i,∑ b,∑ j,F a b i j :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _=∑ a,∑ i,∑ j,∑ b,F a b i j :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _=∑ i,∑ a,∑ j,∑ b,F a b i j := Finset.sum_comm
    _=∑ i,∑ j,∑ a,∑ b,F a b i j := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

/-- A bivariate polynomial of degree at most `D` in each variable equals its tensor expansion. -/
theorem tensor_eq_expansion {D : ℕ} {p : Bivar} (hp : p.natDegree≤D)
    (hq : ∀ a,(p.coeff a).natDegree≤D) : p=TensorWholeIntervalPolynomial.expansion D p := by
  have hsplit : p=∑ a : Fin (D+1),∑ b : Fin (D+1),∑ i : Fin (D+1),∑ j : Fin (D+1),
      scalar ((p.coeff a).coeff b*monomialCoefficient a i*monomialCoefficient b j)*basis i j := by
    conv_lhs => rw [as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)]
    rw [← Fin.sum_univ_eq_sum_range (fun a => C (p.coeff a)*X^a) (D+1)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    conv_lhs => rw [as_sum_range_C_mul_X_pow' (p.coeff a) (Nat.lt_succ_of_le (hq a))]
    rw [← Fin.sum_univ_eq_sum_range (fun b => C ((p.coeff a).coeff b)*X^b) (D+1),map_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [map_mul,monomial_inner (Nat.lt_succ_iff.mp b.2),monomial_outer (Nat.lt_succ_iff.mp a.2),
      Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [basis,scalar,map_mul]
    ring
  rw [TensorWholeIntervalPolynomial.expansion,series_full]
  conv_lhs => rw [hsplit]
  rw [sum_swap4]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [TensorWholeIntervalPolynomial.coefficient,scalar,map_sum,Finset.sum_mul]

/-! ### Tensor Chebyshev coefficients in integers -/

/-- `l` padded with zeros to length `n`. -/
def padL (n : ℕ) (l : List ℤ) : List ℤ := l++List.replicate (n-l.length) 0

/-- The Chebyshev transforms of the first `D+1` rows, each padded to `D+1` entries. -/
def rowChebZ (D : ℕ) (L : List (List ℤ)) : List (List ℤ) :=
  (List.range (D+1)).map (fun a => Fast.chebF (padL (D+1) (L.getD a [])))

/-- The Chebyshev transforms of the columns of `rowChebZ`: entry `i` of list `j` is
`4^D s` times the tensor coefficient `(i,j)`. -/
def tensorZ (D : ℕ) (L : List (List ℤ)) : List (List ℤ) :=
  (List.range (D+1)).map (fun j => Fast.chebF ((rowChebZ D L).map (fun r => r.getD j 0)))

/-- The sum of the absolute values of all entries `(i,j)`, `i, j ≤ D`. -/
def normZ (D : ℕ) (T : List (List ℤ)) : ℤ :=
  ((List.range (D+1)).map (fun j =>
    ((List.range (D+1)).map (fun i => |(T.getD j []).getD i 0|)).sum)).sum

theorem getD_range_map {α : Type*} (f : ℕ → α) {n i : ℕ} (d : α) (h : i<n) :
    ((List.range n).map f).getD i d=f i := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range h]
  rfl

theorem getD_padL (n : ℕ) (l : List ℤ) (b : ℕ) : (padL n l).getD b 0=l.getD b 0 := by
  rcases lt_or_ge b l.length with h | h
  · exact List.getD_append _ _ _ _ h
  · rw [padL,List.getD_append_right _ _ _ _ h,List.getD_eq_default _ _ h]
    rcases lt_or_ge (b-l.length) (n-l.length) with h' | h'
    · exact List.getD_replicate _ h'
    · exact List.getD_eq_default _ _ (by simpa using h')

theorem length_padL {n : ℕ} {l : List ℤ} (h : l.length≤n) : (padL n l).length=n := by
  simp only [padL,List.length_append,List.length_replicate]
  omega

theorem getD_map_getD (M : List (List ℤ)) (a j : ℕ) :
    (M.map (fun r => r.getD j 0)).getD a 0=(M.getD a []).getD j 0 := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getD_eq_getElem?_getD (l := M)]
  cases M[a]? <;> simp

theorem chebQ_padL {n : ℕ} {l : List ℤ} (hl : l.length≤n) (j : ℕ) :
    chebQ (padL n l) j=∑ b ∈ Finset.range n,(l.getD b 0:ℚ)*monomialCoefficient b j := by
  rw [chebQ,length_padL hl]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [getD_padL]

theorem length_getD_le {D : ℕ} {L : List (List ℤ)} (hrows : ∀ l∈L,l.length≤D+1)
    (a : ℕ) :
    (L.getD a []).length≤D+1 := by
  rcases lt_or_ge a L.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hrows _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    simp

theorem rowChebZ_spec {D : ℕ} {L : List (List ℤ)} (hrows : ∀ l∈L,l.length≤D+1) {a : ℕ}
    (ha : a<D+1) (j : ℕ) :
    (((rowChebZ D L).getD a []).getD j 0:ℚ)=
      2^D*∑ b ∈ Finset.range (D+1),((L.getD a []).getD b 0:ℚ)*monomialCoefficient b j := by
  have hl := length_getD_le hrows a
  rw [rowChebZ,getD_range_map _ _ ha,Fast.chebF_eq]
  have hs := chebList_spec (padL (D+1) (L.getD a [])) j
  rw [length_padL hl,chebQ_padL hl,pow_succ] at hs
  linear_combination hs/2

theorem tensorZ_spec {D : ℕ} {L : List (List ℤ)} (hrows : ∀ l∈L,l.length≤D+1) {i j : ℕ}
    (hj : j<D+1) :
    (((tensorZ D L).getD j []).getD i 0:ℚ)=4^D*∑ a ∈ Finset.range (D+1),
      ∑ b ∈ Finset.range (D+1),((L.getD a []).getD b 0:ℚ)*monomialCoefficient a i*
        monomialCoefficient b j := by
  rw [tensorZ,getD_range_map _ _ hj,Fast.chebF_eq]
  have hlen : ((rowChebZ D L).map (fun r => r.getD j 0)).length=D+1 := by
    simp [rowChebZ]
  have hs := chebList_spec ((rowChebZ D L).map (fun r => r.getD j 0)) i
  rw [hlen,chebQ,hlen] at hs
  have hsum : ∑ a ∈ Finset.range (D+1),
      ((((rowChebZ D L).map (fun r => r.getD j 0)).getD a 0 : ℤ):ℚ)*monomialCoefficient a i=
      2^D*∑ a ∈ Finset.range (D+1),∑ b ∈ Finset.range (D+1),
        ((L.getD a []).getD b 0:ℚ)*monomialCoefficient a i*monomialCoefficient b j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [getD_map_getD,rowChebZ_spec hrows (Finset.mem_range.mp ha),Finset.mul_sum,Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsum,pow_succ] at hs
  have h4 : (4:ℚ)^D=2^D*2^D := by rw [← mul_pow]; norm_num
  rw [h4]
  linear_combination hs/2

theorem coefficient_eq_tensorZ {c : BScaled} {p : Bivar} (hc : c.Rep p) (hs : c.s≠0) {D : ℕ}
    (hrows : ∀ l∈c.L,l.length≤D+1) {i j : ℕ} (hj : j<D+1) :
    TensorWholeIntervalPolynomial.coefficient D p i j=
      (((tensorZ D c.L).getD j []).getD i 0:ℚ)/(c.s*4^D) := by
  have hs' : (c.s:ℚ)≠0 := by exact_mod_cast hs
  rw [tensorZ_spec hrows hj,TensorWholeIntervalPolynomial.coefficient]
  simp only [hc.coeff_coeff hs]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (D+1),((c.L.getD a []).getD b 0:ℚ)/c.s*
    monomialCoefficient a i*monomialCoefficient b j) (D+1)]
  rw [eq_div_iff (mul_ne_zero hs' (pow_ne_zero _ (by norm_num))),Finset.sum_mul,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Fin.sum_univ_eq_sum_range (fun b => ((c.L.getD a []).getD b 0:ℚ)/c.s*
    monomialCoefficient a i*monomialCoefficient b j) (D+1),Finset.sum_mul,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  field_simp

theorem norm_eq_normZ {c : BScaled} {p : Bivar} (hc : c.Rep p) (hs : c.s≠0) {D : ℕ}
    (hrows : ∀ l∈c.L,l.length≤D+1) :
    TensorWholeIntervalPolynomial.norm D (TensorWholeIntervalPolynomial.coefficient D p)=
      ((normZ D (tensorZ D c.L)-|((tensorZ D c.L).getD 0 []).getD 0 0| : ℤ):ℚ)/(c.s*4^D) := by
  have hS : (0:ℚ)<c.s*4^D :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hs) (by positivity)
  have habs : ∀ x y : Fin (D+1),|TensorWholeIntervalPolynomial.coefficient D p x.val y.val|=
      ((|((tensorZ D c.L).getD y.val []).getD x.val 0| : ℤ):ℚ)/(c.s*4^D) := by
    intro x y
    rw [coefficient_eq_tensorZ hc hs hrows y.is_lt,abs_div,abs_of_pos hS,Int.cast_abs]
  have hZ : normZ D (tensorZ D c.L)=∑ j ∈ Finset.range (D+1),∑ i ∈ Finset.range (D+1),
      |((tensorZ D c.L).getD j []).getD i 0| := by
    simp only [normZ,← sum_range_list]
  rw [TensorWholeIntervalPolynomial.norm,indices,Finset.sum_erase_eq_sub (Finset.mem_univ _),
    Fintype.sum_prod_type]
  simp only [habs,← Finset.sum_div]
  rw [Finset.sum_comm,← sub_div,hZ]
  push_cast
  congr 2
  rw [Fin.sum_univ_eq_sum_range (fun j => ∑ i : Fin (D+1),
    |(((tensorZ D c.L).getD j []).getD i.val 0 : ℚ)|) (D+1)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact Fin.sum_univ_eq_sum_range (fun i => |(((tensorZ D c.L).getD j []).getD i 0 : ℚ)|) (D+1)

theorem natDegree_of_rows {c : BScaled} {p : Bivar} (hc : c.Rep p) (hs : c.s≠0) {D : ℕ}
    (hL : c.L.length≤D+1) (hrows : ∀ l∈c.L,l.length≤D+1) :
    p.natDegree≤D ∧ ∀ a,(p.coeff a).natDegree≤D := by
  have hrow : ∀ a,(p.coeff a).natDegree≤D := by
    intro a
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hl := length_getD_le hrows a
    rw [hc.coeff_coeff hs,List.getD_eq_default _ _ (by omega)]
    simp
  refine ⟨?_,hrow⟩
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  ext b
  rw [hc.coeff_coeff hs,List.getD_eq_default c.L _ (by omega)]
  simp

/-- The tensor expansion of `e.poly` of degree `D`, `ρ₀ < coefficient D e.poly 0 0` and
`norm D (coefficient D e.poly) < ρ₁`. -/
def tensorCheck (D : ℕ) (ρ0 ρ1 : ℚ) (e : BExpr) : Bool :=
  decide (e.z.L.length≤D+1) && (e.z.L.all (fun l => decide (l.length≤D+1)) &&
    (decide (ρ0.num*((e.z.s*4^D : ℕ):ℤ)<((tensorZ D e.z.L).getD 0 []).getD 0 0*ρ0.den) &&
      decide ((normZ D (tensorZ D e.z.L)-|((tensorZ D e.z.L).getD 0 []).getD 0 0|)*ρ1.den<
        ρ1.num*((e.z.s*4^D : ℕ):ℤ))))

theorem tensor_of_check {D : ℕ} {ρ0 ρ1 : ℚ} {e : BExpr} (h : tensorCheck D ρ0 ρ1 e=true) :
    e.poly=TensorWholeIntervalPolynomial.expansion D e.poly ∧
      ρ0<TensorWholeIntervalPolynomial.coefficient D e.poly 0 0 ∧
      TensorWholeIntervalPolynomial.norm D (TensorWholeIntervalPolynomial.coefficient D e.poly)<
        ρ1 := by
  simp only [tensorCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  obtain ⟨hL,hrows,h0,h1⟩ := h
  have hs := e.scale_ne_zero
  have hM : e.z.s*4^D≠0 := Nat.mul_ne_zero hs (pow_ne_zero _ (by norm_num))
  have hcast : ((e.z.s*4^D : ℕ):ℚ)=(e.z.s:ℚ)*4^D := by push_cast; ring
  obtain ⟨hp,hq⟩ := natDegree_of_rows e.rep hs hL hrows
  refine ⟨tensor_eq_expansion hp hq,?_,?_⟩
  · rw [coefficient_eq_tensorZ e.rep hs hrows (Nat.succ_pos D),← hcast]
    exact lt_div_of_int hM h0
  · rw [norm_eq_normZ e.rep hs hrows,← hcast]
    exact div_lt_of_int hM h1

end Bivariate

end SquaresInCircles.Eight.PolynomialExpressions
