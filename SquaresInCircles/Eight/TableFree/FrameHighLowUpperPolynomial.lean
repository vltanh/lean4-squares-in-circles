module

public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperSupport

/-!
# One positive quadratic for the affine upper-high support

The displayed Taylor expression is expanded about `.135`.  On
each sign of that centered variable its remainder has nonnegative
coefficients.  A single geometric power bound absorbs all powers
from degree eight onward.  The resulting positive quadratic holds
throughout the whole interval `[.11,.46]`.
Uncompiled source draft of HAND_LOW_HIGH_SCALAR_REPLACEMENTS §1.2.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowUpperPolynomial
open FrameCircleArc FrameLowMidArc FrameHighLowUpperSupport

def domain : Set ℝ := Icc (11/100:ℝ) (23/50)
def lam (x : ℝ) : ℝ := 201/200-(407/1000)*x
def T (x : ℝ) : ℝ :=
  x+9/100+(314159/100000)/4+FrameLowArc.u*(141457567/100000000)+
    (FrameLowArc.u+FrameLowArc.v)/2-8833/10000+
      (1/2-449607033/500000000)*lam x+
        (lam x-9/100)*Arithmetic.sin7 x-(9/100)*Arithmetic.cos8 x
def V (x : ℝ) : ℝ := FrameLowArc.u^2+FrameLowArc.v^2+(lam x)^2+
  2*lam x*(FrameLowArc.u*Arithmetic.sin9 x-FrameLowArc.v*Arithmetic.cos10 x)
def P (x : ℝ) : ℝ := (T x)^2-Q0*V x
def tail (u : ℝ) : ℝ := u^6+u^7+u^8+u^9+u^10+u^11+u^12+u^13+u^14
def positiveCoefficient (u : ℝ) : ℝ :=
  163/625-(111/1000)*u^2-(7/250)*u^4-(29/1000)*u^5-tail u
def negativeCoefficient (u : ℝ) : ℝ :=
  163/625-(207/500)*u-(111/1000)*u^2-(26/125)*u^3-(7/250)*u^4-tail u
def positiveLower (u : ℝ) : ℝ :=
  173/500000-(169/125000)*u+positiveCoefficient u*u^2
def negativeLower (u : ℝ) : ℝ :=
  173/500000-(169/125000)*u+negativeCoefficient u*u^2

theorem lam_bounds {x : ℝ} (hx : x∈domain) : (9/100:ℝ)<lam x ∧ lam x≤K := by
  dsimp [lam,K]
  constructor <;> linarith [hx.1,hx.2]

theorem positive_remainder {u : ℝ} (hu : 0≤u) : positiveLower u<P (27/200+u) := by
  simp only [positiveLower,positiveCoefficient,tail,P,T,V,lam,Q0,
    FrameLowArc.u,FrameLowArc.v,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8]
  linarith [hu,pow_nonneg hu 2,pow_nonneg hu 3,pow_nonneg hu 4,pow_nonneg hu 5,pow_nonneg hu 6,pow_nonneg hu 7,pow_nonneg hu 8,pow_nonneg hu 9,pow_nonneg hu 10,pow_nonneg hu 11,pow_nonneg hu 12,pow_nonneg hu 13,pow_nonneg hu 14,pow_nonneg hu 15,pow_nonneg hu 16]

theorem negative_remainder {u : ℝ} (hu : 0≤u) : negativeLower u<P (27/200-u) := by
  simp only [negativeLower,negativeCoefficient,tail,P,T,V,lam,Q0,
    FrameLowArc.u,FrameLowArc.v,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8]
  linarith [hu,pow_nonneg hu 2,pow_nonneg hu 3,pow_nonneg hu 4,pow_nonneg hu 5,pow_nonneg hu 6,pow_nonneg hu 7,pow_nonneg hu 8,pow_nonneg hu 9,pow_nonneg hu 10,pow_nonneg hu 11,pow_nonneg hu 12,pow_nonneg hu 13,pow_nonneg hu 14,pow_nonneg hu 15,pow_nonneg hu 16]

theorem tail_bound {u : ℝ} (hu : u∈Icc (0:ℝ) (1/3)) : tail u<1/400 := by
  have ht : 0≤tail u := by
    simp only [tail]
    linarith [pow_nonneg hu.1 6,pow_nonneg hu.1 7,pow_nonneg hu.1 8,pow_nonneg hu.1 9,pow_nonneg hu.1 10,pow_nonneg hu.1 11,pow_nonneg hu.1 12,pow_nonneg hu.1 13,pow_nonneg hu.1 14]
  have hid : (1-u)*tail u=u^6-u^15 := by simp only [tail]; ring
  have h6 := pow_le_pow_left₀ hu.1 hu.2 6
  have h15 := pow_nonneg hu.1 15
  have hm := mul_nonneg (show 0≤1/3-u by linarith [hu.2]) ht
  linarith

theorem positive_coefficient {u : ℝ} (hu : u∈Icc (0:ℝ) (13/40)) :
    (119/500:ℝ)<positiveCoefficient u := by
  have h2 := pow_le_pow_left₀ hu.1 hu.2 2
  have h4 := pow_le_pow_left₀ hu.1 hu.2 4
  have h5 := pow_le_pow_left₀ hu.1 hu.2 5
  have ht := tail_bound (show u∈Icc (0:ℝ) (1/3) from ⟨hu.1,by linarith [hu.2]⟩)
  dsimp [positiveCoefficient]
  linarith

theorem negative_coefficient {u : ℝ} (hu : u∈Icc (0:ℝ) (1/40)) :
    (119/500:ℝ)<negativeCoefficient u := by
  have h2 := pow_le_pow_left₀ hu.1 hu.2 2
  have h3 := pow_le_pow_left₀ hu.1 hu.2 3
  have h4 := pow_le_pow_left₀ hu.1 hu.2 4
  have ht := tail_bound (show u∈Icc (0:ℝ) (1/3) from ⟨hu.1,by linarith [hu.2]⟩)
  dsimp [negativeCoefficient]
  linarith [hu.2]

theorem quadratic_reserve (u : ℝ) :
    (1/3000:ℝ)<173/500000-(169/125000)*u+(119/500)*u^2 := by
  nlinarith [sq_nonneg ((119/250:ℝ)*u-169/125000)]

theorem positive_lower {u : ℝ} (hu : u∈Icc (0:ℝ) (13/40)) :
    (1/3000:ℝ)<positiveLower u := by
  have hm := mul_le_mul_of_nonneg_right (positive_coefficient hu).le (sq_nonneg u)
  dsimp [positiveLower]
  nlinarith [quadratic_reserve u]

theorem negative_lower {u : ℝ} (hu : u∈Icc (0:ℝ) (1/40)) :
    (1/3000:ℝ)<negativeLower u := by
  have hm := mul_le_mul_of_nonneg_right (negative_coefficient hu).le (sq_nonneg u)
  dsimp [negativeLower]
  nlinarith [quadratic_reserve u]

theorem polynomial_positive {x : ℝ} (hx : x∈domain) : (1/3000:ℝ)<P x := by
  by_cases hsign : (27/200:ℝ)≤x
  · have hu : x-27/200∈Icc (0:ℝ) (13/40) := by constructor <;> linarith [hx.2]
    have hh := (positive_lower hu).trans (positive_remainder hu.1)
    simpa only [show 27/200+(x-27/200)=x by ring] using hh
  · have hu : 27/200-x∈Icc (0:ℝ) (1/40) := by constructor <;> linarith [hx.1]
    have hh := (negative_lower hu).trans (negative_remainder hu.1)
    simpa only [show 27/200-(27/200-x)=x by ring] using hh

theorem taylor_signs {x : ℝ} (hx : x∈domain) :
    0≤Arithmetic.sin7 x ∧ Arithmetic.cos8 x≤2 := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hx1 : x≤1 := by linarith [hx.2]
  have h2 := pow_le_pow_left₀ hx0 hx1 2
  have h4 := pow_le_pow_left₀ hx0 hx1 4
  have h6 := pow_le_pow_left₀ hx0 hx1 6
  have h8 := pow_le_pow_left₀ hx0 hx1 8
  have hcoef : 0≤1-x^2/6+x^4/120-x^6/5040 := by
    nlinarith [pow_nonneg hx0 4]
  have hm := mul_nonneg hx0 hcoef
  constructor
  · dsimp [Arithmetic.sin7]
    nlinarith only [hm]
  · dsimp [Arithmetic.cos8]
    nlinarith [sq_nonneg x,pow_nonneg hx0 6]

theorem T_positive {x : ℝ} (hx : x∈domain) : 0<T x := by
  have hl := lam_bounds hx
  have ht := taylor_signs hx
  have hs := mul_nonneg (sub_nonneg.mpr hl.1.le) ht.1
  have hm := mul_le_mul_of_nonpos_left hl.2
    (by norm_num : (1/2-449607033/500000000:ℝ)≤0)
  dsimp [T,K,FrameLowArc.u,FrameLowArc.v] at *
  nlinarith [hx.1]

end SquaresInCircles.Eight.TableFree.FrameHighLowUpperPolynomial
