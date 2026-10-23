module

public import SquaresInCircles.Eight.TableFree.TensorWholeIntervalPolynomial
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# Exact substitutions for the two continuous coefficient domains

Uncompiled source draft.  These are ordinary operations on nested rational
polynomials.  The triangle and rectangle are covered once by a whole square;
there is no division into angular states or smaller domains.  The cubic mass
is the total-degree-three polynomial specified in the hand proof.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.TwoVariablePolynomial
open TensorWholeIntervalPolynomial

/-- Insert a rational polynomial in one chosen bivariate argument. -/
def lift (f : Bivar) : ℚ[X] →+* Bivar :=
  Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C) f

def substitute (f g : Bivar) : Bivar →+* Bivar :=
  Polynomial.eval₂RingHom (lift g) f

def restrict (p : Bivar) (f g : ℚ[X]) : ℚ[X] :=
  p.eval₂ (Polynomial.eval₂RingHom Polynomial.C g) f

def swap (p : Bivar) : Bivar := substitute (C X) X p

def derivativeY (p : Bivar) : Bivar := swap (swap p).derivative

def divY (p : Bivar) : Bivar := swap (swap p).divX

def baseX (p : Bivar) : ℚ[X] := restrict p 0 X

def baseY (p : Bivar) : ℚ[X] := restrict p X 0

@[simp] theorem evaluate_lift (x y : ℝ) (f : Bivar) (p : ℚ[X]) :
    evaluate x y (lift f p)=aeval (evaluate x y f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n r =>
      simp [lift,Polynomial.eval₂_monomial,Polynomial.aeval_def,
        Polynomial.C_mul_X_pow_eq_monomial.symm,scalar,evaluate]

@[simp] theorem evaluate_substitute (x y : ℝ) (f g p : Bivar) :
    evaluate x y (substitute f g p)=
      evaluate (evaluate x y f) (evaluate x y g) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n r =>
      simp [substitute,Polynomial.eval₂_monomial,
        Polynomial.C_mul_X_pow_eq_monomial.symm,evaluate_lift,evaluate]

theorem evaluate_restrict (p : Bivar) (f g : ℚ[X]) (t : ℝ) :
    aeval t (restrict p f g)=evaluate (aeval t f) (aeval t g) p := by
  have hcoeff (r : ℚ[X]) :
      aeval t (Polynomial.eval₂RingHom Polynomial.C g r)=aeval (aeval t g) r := by
    change aeval t (r.comp g)=_
    exact Polynomial.aeval_comp _ _ _
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [restrict,hp,hq]
  | monomial n r =>
      simp only [restrict,Polynomial.eval₂_monomial,map_mul,map_pow,hcoeff]
      simp [evaluate,Polynomial.eval₂_monomial]

@[simp] theorem evaluate_swap (p : Bivar) (x y : ℝ) :
    evaluate x y (swap p)=evaluate y x p := by
  simp [swap]

@[simp] theorem evaluate_baseX (p : Bivar) (y : ℝ) :
    aeval y (baseX p)=evaluate 0 y p := by
  simp [baseX,evaluate_restrict]

@[simp] theorem evaluate_baseY (p : Bivar) (x : ℝ) :
    aeval x (baseY p)=evaluate x 0 p := by
  simp [baseY,evaluate_restrict]

theorem hasDerivAt_X (p : Bivar) (x y : ℝ) :
    HasDerivAt (fun t => evaluate t y p) (evaluate x y p.derivative) x := by
  let f : ℚ[X] →+* ℝ := (Polynomial.aeval y : ℚ[X] →ₐ[ℚ] ℝ).toRingHom
  have h := (p.map f).hasDerivAt x
  simpa only [Polynomial.derivative_map,Polynomial.eval_map,evaluate,
    Polynomial.coe_eval₂RingHom] using h

theorem hasDerivAt_Y (p : Bivar) (x y : ℝ) :
    HasDerivAt (fun t => evaluate x t p) (evaluate x y (derivativeY p)) y := by
  simpa only [derivativeY,evaluate_swap] using hasDerivAt_X (swap p) y x

/-- Exact division after removing the indicated edge; it is valid at zero. -/
theorem divX_identity (p : Bivar) (x y : ℝ) :
    evaluate x y p=evaluate 0 y p+x*evaluate x y p.divX := by
  have h := congrArg (fun q : Bivar => evaluate x y q) (Polynomial.X_mul_divX_add p)
  have h0 := congrArg (fun q : Bivar => evaluate 0 y q) (Polynomial.X_mul_divX_add p)
  simp only [map_add,map_mul,evaluate_X,evaluate_C,zero_mul,zero_add] at h h0
  linarith

theorem divY_identity (p : Bivar) (x y : ℝ) :
    evaluate x y p=evaluate x 0 p+y*evaluate x y (divY p) := by
  simpa only [divY,evaluate_swap] using divX_identity (swap p) y x

def truncate3 (p : Bivar) : Bivar :=
  ∑ i : Fin 4,∑ j : Fin 4,
    if i.val+j.val≤3 then scalar ((p.coeff i.val).coeff j.val)*X^i.val*(C X)^j.val
    else 0

def constant (p : Bivar) : ℚ := (p.coeff 0).coeff 0

def cubicMass (rho : ℚ) (p : Bivar) : Bivar :=
  let w := scalar (1/constant p)*(truncate3 p-scalar (constant p))
  scalar rho*truncate3 (1+scalar (1/2)*w-scalar (1/8)*w^2+scalar (1/16)*w^3)

/-- Centered square coordinates, with values in `[0,1]`. -/
def unitX : Bivar := scalar (1/2)*(X+1)
def unitY : Bivar := scalar (1/2)*(C X+1)

def rectangle (a b : ℚ) (p : Bivar) : Bivar :=
  substitute (scalar a*unitX) (scalar b*unitY) p

def triangle (d : ℚ) (p : Bivar) : Bivar :=
  substitute (scalar d*unitX*(1-unitY)) (scalar d*unitX*unitY) p

def trapezoid (l d : ℚ) (p : Bivar) : Bivar :=
  substitute (scalar d*unitX) ((scalar l+scalar d*unitX)*unitY) p

def upper (D : ℕ) (c : ℕ → ℕ → ℚ) : ℚ := c 0 0+norm D c

theorem series_upper (D : ℕ) (c : ℕ → ℕ → ℚ) {x y : ℝ}
    (hx : |x|≤1) (hy : |y|≤1) :
    evaluate x y (series D c)≤(upper D c:ℝ) := by
  have hterm (ij : Fin (D+1) × Fin (D+1)) :
      (c ij.1.val ij.2.val:ℝ)*evaluate x y (basis ij.1.val ij.2.val)≤
        |(c ij.1.val ij.2.val:ℝ)| :=
    (WholeIntervalPolynomial.scalar_bounds
      (basis_abs_le_one hx hy ij.1.val ij.2.val)).2
  have hs := Finset.sum_le_sum (s := indices D) (fun ij _ => hterm ij)
  simp only [series,map_add,map_sum,map_mul,evaluate_scalar]
  dsimp [upper,norm]
  push_cast
  exact add_le_add_left hs _

theorem square_bounds {D : ℕ} {p : Bivar}
    (hidentity : p=expansion D p) {x y : ℝ}
    (hx : |x|≤1) (hy : |y|≤1) :
    (lower D (coefficient D p):ℝ)≤evaluate x y p ∧
      evaluate x y p≤(upper D (coefficient D p):ℝ) := by
  refine ⟨lower_bound hidentity hx hy,?_⟩
  have he := congrArg (fun q : Bivar => evaluate x y q) hidentity
  rw [he]
  exact series_upper D (coefficient D p) hx hy

theorem centered_unit {u : ℝ} (hu : u∈Icc 0 1) : |2*u-1|≤1 := by
  apply abs_le.mpr
  constructor <;> linarith [hu.1,hu.2]

@[simp] theorem evaluate_unitX (u v : ℝ) : evaluate (2*u-1) (2*v-1) unitX=u := by
  simp [unitX]
  ring

@[simp] theorem evaluate_unitY (u v : ℝ) : evaluate (2*u-1) (2*v-1) unitY=v := by
  simp [unitY]
  ring

theorem rectangle_bounds {D : ℕ} {a b : ℚ} {p : Bivar}
    (ha : 0<a) (hb : 0<b)
    (hid : rectangle a b p=expansion D (rectangle a b p))
    {x y : ℝ} (hx : x∈Icc 0 (a:ℝ)) (hy : y∈Icc 0 (b:ℝ)) :
    (lower D (coefficient D (rectangle a b p)):ℝ)≤evaluate x y p ∧
      evaluate x y p≤(upper D (coefficient D (rectangle a b p)):ℝ) := by
  have ha' : (0:ℝ)<(a:ℝ) := by exact_mod_cast ha
  have hb' : (0:ℝ)<(b:ℝ) := by exact_mod_cast hb
  have hu : x/(a:ℝ)∈Icc 0 1 :=
    ⟨div_nonneg hx.1 ha'.le,(div_le_one ha').2 hx.2⟩
  have hv : y/(b:ℝ)∈Icc 0 1 :=
    ⟨div_nonneg hy.1 hb'.le,(div_le_one hb').2 hy.2⟩
  have h := square_bounds hid (centered_unit hu) (centered_unit hv)
  simpa [rectangle,evaluate_substitute,ha'.ne',hb'.ne',mul_div_cancel₀] using h

theorem triangle_bounds {D : ℕ} {d : ℚ} {p : Bivar}
    (hd : 0<d) (hid : triangle d p=expansion D (triangle d p))
    {x y : ℝ} (hx : 0≤x) (hy : 0≤y) (hxy : x+y≤(d:ℝ)) :
    (lower D (coefficient D (triangle d p)):ℝ)≤evaluate x y p ∧
      evaluate x y p≤(upper D (coefficient D (triangle d p)):ℝ) := by
  have hd' : (0:ℝ)<(d:ℝ) := by exact_mod_cast hd
  by_cases hzero : x+y=0
  · have hx0 : x=0 := by linarith
    have hy0 : y=0 := by linarith
    have h := square_bounds hid (x:= -1) (y:= -1) (by norm_num) (by norm_num)
    simpa [triangle,unitX,unitY,hx0,hy0] using h
  · have hpos : 0<x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hzero)
    let u : ℝ := (x+y)/(d:ℝ)
    let v : ℝ := y/(x+y)
    have hu : u∈Icc 0 1 :=
      ⟨div_nonneg hpos.le hd'.le,(div_le_one hd').2 hxy⟩
    have hv : v∈Icc 0 1 :=
      ⟨div_nonneg hy hpos.le,(div_le_one hpos).2 (by linarith)⟩
    have hx' : (d:ℝ)*u*(1-v)=x := by
      dsimp [u,v]
      field_simp [hd'.ne',hzero]
      ring
    have hy' : (d:ℝ)*u*v=y := by
      dsimp [u,v]
      field_simp [hd'.ne',hzero]
      ring
    have h := square_bounds hid (centered_unit hu) (centered_unit hv)
    simpa only [triangle,evaluate_substitute,map_mul,map_sub,map_one,
      evaluate_scalar,evaluate_unitX,evaluate_unitY,hx',hy'] using h

theorem trapezoid_bounds {D : ℕ} {l d : ℚ} {p : Bivar}
    (hl : 0<l) (hd : 0<d)
    (hid : trapezoid l d p=expansion D (trapezoid l d p))
    {x y : ℝ} (hx : x∈Icc 0 (d:ℝ)) (hy : y∈Icc 0 ((l:ℝ)+x)) :
    (lower D (coefficient D (trapezoid l d p)):ℝ)≤evaluate x y p ∧
      evaluate x y p≤(upper D (coefficient D (trapezoid l d p)):ℝ) := by
  have hl' : (0:ℝ)<(l:ℝ) := by exact_mod_cast hl
  have hd' : (0:ℝ)<(d:ℝ) := by exact_mod_cast hd
  have hsum : 0<(l:ℝ)+x := by linarith [hx.1]
  let u : ℝ := x/(d:ℝ)
  let v : ℝ := y/((l:ℝ)+x)
  have hu : u∈Icc 0 1 :=
    ⟨div_nonneg hx.1 hd'.le,(div_le_one hd').2 hx.2⟩
  have hv : v∈Icc 0 1 :=
    ⟨div_nonneg hy.1 hsum.le,(div_le_one hsum).2 hy.2⟩
  have hx' : (d:ℝ)*u=x := by dsimp [u]; field_simp
  have hy' : ((l:ℝ)+(d:ℝ)*u)*v=y := by
    rw [hx']
    dsimp [v]
    field_simp
  have h := square_bounds hid (centered_unit hu) (centered_unit hv)
  simpa only [trapezoid,evaluate_substitute,map_mul,map_add,evaluate_scalar,
    evaluate_unitX,evaluate_unitY,hx',hy'] using h

end SquaresInCircles.Eight.TableFree.TwoVariablePolynomial
