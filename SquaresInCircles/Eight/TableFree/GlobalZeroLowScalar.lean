module

public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorScalar
public import SquaresInCircles.Eight.Arithmetic.Taylor

/-!
# The complete scalar triangle for propagation across a zero and a low quarter

A single degree-eight polynomial is a lower bound on the entire intrinsic
triangle. Its displayed homogeneous identity has positive rational
coefficients in the three nonnegative barycentric coordinates. This is an
algebraic whole-domain certificate; there is no angle subdivision, sampled
minimum, or configuration inventory. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalZeroLow

abbrev lam : ℝ := 111/100
abbrev eta : ℝ := 2/5
abbrev kap : ℝ := 37/75
abbrev nu : ℝ := 1369/1000
abbrev rho : ℝ := 1369/2000
abbrev gam : ℝ := 13921/18000
abbrev bcoef : ℝ := 20313/20000
abbrev kcoef : ℝ := 5663/25000
abbrev acoef : ℝ := 263/250
abbrev radiusUpper : ℝ := 1979/1000

def sine5 (x : ℝ) : ℝ := x-x^3/6+x^5/120
def cosine4 (x : ℝ) : ℝ := 1-x^2/2+x^4/24
def cosine6 (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
def cosineSquare8 (x : ℝ) : ℝ := 1-x^2+x^4/3-2*x^6/45+x^8/315
def sineSquare8 (x : ℝ) : ℝ := x^2-x^4/3+2*x^6/45-x^8/315
def sineCosine7 (x : ℝ) : ℝ := x-2*x^3/3+2*x^5/15-4*x^7/315

def base (v : ℝ) : ℝ :=
  (v+acoef)*Real.cos v-bcoef*Real.sin v-gam*(Real.cos v)^2-kcoef

def scalar (v x : ℝ) : ℝ :=
  base v+Real.cos v*x+(lam-kap*Real.cos v)*(Real.cos x-1)+
    rho*(Real.sin x)^2+lam*Real.sin x*(Real.cos x-radiusUpper)

def secondaryError (v x : ℝ) : ℝ :=
  Real.cos v*x+(lam-kap*Real.cos v)*(Real.cos x-1)+
    lam*max (Real.sin x) 0-nu*Real.cos v*Real.sin x

def lowerPolynomial (v x : ℝ) : ℝ :=
  cosine6 v*(v+x+acoef+kap*(1-cosine4 x))-bcoef*sine5 v-
    gam*cosineSquare8 v-kcoef+lam*(cosine6 x-1)+rho*sineSquare8 x+
    lam*sineCosine7 x-lam*radiusUpper*sine5 x-(37/1296000)*v^6*x^4

/-- The positive homogeneous reserve for the complete angle triangle. -/
def simplexReserve (u v w : ℝ) : ℝ :=
  (120205922669/162000000000000:ℝ)*u^8 +
  (296526606593/6480000000000:ℝ)*u^7*v +
  (1756434735293/6480000000000:ℝ)*u^7*w +
  (5691190367947/16200000000000:ℝ)*u^6*v^2 +
  (5353144906711/3240000000000:ℝ)*u^6*v*w +
  (9440037591061/6480000000000:ℝ)*u^6*w^2 +
  (2551206607481/2160000000000:ℝ)*u^5*v^3 +
  (1179985538627/240000000000:ℝ)*u^5*v^2*w +
  (4964429990681/720000000000:ℝ)*u^5*v*w^2 +
  (7101630650681/2160000000000:ℝ)*u^5*w^3 +
  (3039100928521/1440000000000:ℝ)*u^4*v^4 +
  (12434286011/1350000000:ℝ)*u^4*v^3*w +
  (6139530117/400000000:ℝ)*u^4*v^2*w^2 +
  (6662994569/540000000:ℝ)*u^4*v*w^3 +
  (4366110847/1080000000:ℝ)*u^4*w^4 +
  (7555849421351/3600000000000:ℝ)*u^3*v^5 +
  (9761493889/900000000:ℝ)*u^3*v^4*w +
  (1906417373/90000000:ℝ)*u^3*v^3*w^2 +
  (766500581/36000000:ℝ)*u^3*v^2*w^3 +
  (852714317/72000000:ℝ)*u^3*v*w^4 +
  (1067375477/360000000:ℝ)*u^3*w^5 +
  (1344419251861/1200000000000:ℝ)*u^2*v^6 +
  (26493579102053/3600000000000:ℝ)*u^2*v^5*w +
  (64229029333/3600000000:ℝ)*u^2*v^4*w^2 +
  (438034569/20000000:ℝ)*u^2*v^3*w^3 +
  (46596893/3000000:ℝ)*u^2*v^2*w^4 +
  (6564677/1000000:ℝ)*u^2*v*w^5 +
  (200263/150000:ℝ)*u^2*w^6 +
  (987421186633/3600000000000:ℝ)*u*v^7 +
  (1484849380861/600000000000:ℝ)*u*v^6*w +
  (3134236075117/400000000000:ℝ)*u*v^5*w^2 +
  (554690731/45000000:ℝ)*u*v^4*w^3 +
  (3973971001/360000000:ℝ)*u*v^3*w^4 +
  (18211487/3000000:ℝ)*u*v^2*w^5 +
  (9358363/4500000:ℝ)*u*v*w^6 +
  (643993/1800000:ℝ)*u*w^7 +
  (100698298757/6000000000000:ℝ)*v^8 +
  (1026859186633/3600000000000:ℝ)*v^7*w +
  (1530860380861/1200000000000:ℝ)*v^6*w^2 +
  (3226258075117/1200000000000:ℝ)*v^5*w^3 +
  (71493107/22500000:ℝ)*v^4*w^4 +
  (4112004001/1800000000:ℝ)*v^3*w^5 +
  (4725413/4500000:ℝ)*v^2*w^6 +
  (2772413/9000000:ℝ)*v*w^7 +
  (20741/450000:ℝ)*w^8


theorem simplexReserve_nonneg {u v w : ℝ} (hu : 0≤u) (hv : 0≤v) (hw : 0≤w) :
    0≤ simplexReserve u v w := by
  unfold simplexReserve
  positivity

theorem lowerPolynomial_identity (v x : ℝ) :
    lowerPolynomial v x-3/500=
      simplexReserve ((10/7)*v) ((10/7)*x) (1-(10/7)*v-(10/7)*x) := by
  unfold lowerPolynomial simplexReserve cosine6 cosine4 sine5 cosineSquare8
    sineSquare8 sineCosine7
  dsimp [lam,kap,rho,gam,bcoef,kcoef,acoef,radiusUpper]
  ring

theorem lowerPolynomial_lower {v x : ℝ} (hv : 0≤v) (hx : 0≤x)
    (hsum : v+x≤frameCap) : 3/500≤lowerPolynomial v x := by
  have hw : 0≤1-(10/7)*v-(10/7)*x := by dsimp [frameCap] at hsum; linarith
  have hh := simplexReserve_nonneg (show 0≤(10/7)*v by positivity)
    (show 0≤(10/7)*x by positivity) hw
  rw [← lowerPolynomial_identity] at hh
  linarith

theorem cosine6_nonneg {x : ℝ} (hx : x∈Icc 0 frameCap) : 0≤cosine6 x := by
  have hx1 : x≤1 := hx.2.trans (by norm_num [frameCap])
  have hsq : x^2≤1 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx1)]
  have h6 : x^6≤x^4 := by
    have hh := mul_nonneg (sq_nonneg (x^2)) (sub_nonneg.mpr hsq)
    nlinarith
  dsimp [cosine6]
  nlinarith [sq_nonneg (x^2)]

theorem cosine4_le_one {x : ℝ} (hx : x∈Icc 0 frameCap) : cosine4 x≤1 := by
  have hx1 : x≤1 := hx.2.trans (by norm_num [frameCap])
  have hsq : x^2≤1 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx1)]
  have h4 : x^4≤x^2 := by
    have hh := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hsq)
    nlinarith
  dsimp [cosine4]
  nlinarith [sq_nonneg x]

theorem square_trig_bounds {x : ℝ} (hx : 0≤x) :
    (Real.cos x)^2≤cosineSquare8 x ∧
    sineSquare8 x≤(Real.sin x)^2 ∧
    sineCosine7 x≤Real.sin x*Real.cos x := by
  have hc := Arithmetic.cos_le_cos8 (show 0≤2*x by positivity)
  have hs := sin_lower_seven (show 0≤2*x by positivity)
  dsimp [Arithmetic.cos8] at hc
  have hdouble := Real.cos_two_mul x
  have hsine := Real.sin_two_mul x
  have hunit := Real.sin_sq_add_cos_sq x
  dsimp [cosineSquare8,sineSquare8,sineCosine7]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem lowerPolynomial_le_scalar {v x : ℝ}
    (hv : v∈Icc 0 frameCap) (hx : x∈Icc 0 frameCap) :
    lowerPolynomial v x≤ scalar v x := by
  have hvtrig := transport_trig hv
  have hcV : cosine6 v≤Real.cos v := cos_lower_six hv.1
  have hcX : cosine6 x≤Real.cos x := cos_lower_six hx.1
  have hcX' : Real.cos x≤cosine4 x := cos_upper_four hx.1
  have hsV : Real.sin v≤ sine5 v := sin_upper_five hv.1
  have hsX : Real.sin x≤ sine5 x := sin_upper_five hx.1
  have hV := (square_trig_bounds hv.1).1
  have hX := square_trig_bounds hx.1
  have hfactor : v+x+acoef+kap*(1-cosine4 x)≤
      v+x+acoef+kap*(1-Real.cos x) := by dsimp [kap]; linarith
  have hfactor0 : 0≤v+x+acoef+kap*(1-cosine4 x) := by
    have hh := cosine4_le_one hx
    dsimp [acoef,kap]
    linarith [hv.1,hx.1]
  have hproduct := mul_le_mul hcV hfactor hfactor0
    (show 0≤Real.cos v by linarith [hvtrig.1])
  have hextra : 0≤(37/1296000:ℝ)*v^6*x^4 := by positivity
  unfold lowerPolynomial scalar base
  dsimp [lam,kap,rho,gam,bcoef,kcoef,acoef,radiusUpper] at *
  nlinarith only [hproduct,hcX,hsV,hsX,hV,hX.2.1,hX.2.2,hextra]

theorem scalar_lower {v x : ℝ} (hv : 0≤v) (hx : 0≤x)
    (hsum : v+x≤frameCap) : 3/500≤ scalar v x :=
  (lowerPolynomial_lower hv hx hsum).trans
    (lowerPolynomial_le_scalar ⟨hv,by linarith⟩ ⟨hx,by linarith⟩)

theorem base_positive {v : ℝ} (hv : v∈Icc 0 frameCap) : 0<base v := by
  have hh := scalar_lower hv.1 (le_refl (0:ℝ)) (by simpa using hv.2)
  simp [scalar] at hh
  linarith

theorem secondaryError_nonnegative {v x : ℝ}
    (hv : v∈Icc 0 frameCap) (hx : x∈Icc 0 frameCap) :
    0≤ secondaryError v x := by
  have tv := transport_trig hv
  have tx := transport_trig hx
  have hcv : 3/4≤Real.cos v := by linarith [tv.1]
  have hc : 0≤lam-kap*Real.cos v := by dsimp [lam,kap]; linarith [tv.2.1]
  have hcupper : lam-kap*Real.cos v≤37/50 := by dsimp [lam,kap]; linarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=x)
  have hsin := Real.sin_le hx.1
  have hp1 := mul_nonneg (sub_nonneg.mpr hcv) hx.1
  have hp2 := mul_nonneg (show 0≤lam-nu*Real.cos v+259/1000 by
    dsimp [lam,nu]; linarith [tv.2.1]) tx.2.2.1
  have hp3 := mul_le_mul_of_nonneg_left
    (show 1-Real.cos x≤x^2/2 by linarith) hc
  have hp4 := mul_le_mul_of_nonneg_right hcupper (by positivity : 0≤x^2/2)
  have hx2 : x^2≤(7/10)*x := by
    dsimp [frameCap] at hx
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  unfold secondaryError
  rw [max_eq_left tx.2.2.1]
  dsimp [lam,nu] at *
  linarith [hx.1]

theorem secondaryError_negative_nonnegative {v z : ℝ}
    (hv : v∈Icc 0 frameCap) (hz : z∈Icc 0 (23/100:ℝ)) :
    0≤ secondaryError v (-z) := by
  have tv := transport_trig hv
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have tz := transport_trig hzframe
  have hc : 0≤lam-kap*Real.cos v := by dsimp [lam,kap]; linarith [tv.2.1]
  have hcupper : lam-kap*Real.cos v≤37/50 := by dsimp [lam,kap]; linarith [tv.1]
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hsin := Real.sin_ge_sub_cube hz.1
  have hz2 : z^2≤(23/100)*z := by
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have hz3 : z^3≤(529/10000)*z := by
    have hh := mul_le_mul_of_nonneg_left hz2 hz.1
    nlinarith
  have hangle : (1/3)*z≤ -z+nu*Real.sin z := by dsimp [nu]; nlinarith
  have hp1 := mul_le_mul_of_nonneg_left hangle
    (show 0≤Real.cos v by linarith [tv.1])
  have hp2 := mul_nonneg (show 0≤Real.cos v-3/4 by linarith [tv.1]) hz.1
  have hp3 := mul_le_mul_of_nonneg_left
    (show 1-Real.cos z≤z^2/2 by linarith) hc
  have hp4 := mul_le_mul_of_nonneg_right hcupper (by positivity : 0≤z^2/2)
  unfold secondaryError
  rw [Real.cos_neg,Real.sin_neg,max_eq_right (by linarith [tz.2.2.1])]
  dsimp only [lam,kap,nu] at *
  linarith [hz.1]

end SquaresInCircles.Eight.TableFree.GlobalZeroLow
