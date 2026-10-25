module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3SourceData
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2GainComparison
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowABSlope
public import SquaresInCircles.Eight.Owners.GA.ChargedPairs
public import SquaresInCircles.Eight.Owners.Positive.ScalarPolynomials

/-!
# Eight squares: the coefficient certificates of the common gain on the whole domain

`P_positive` and `J_positive` bound `P` from below on `[0, 129/200]` and `J` on `[0, frameCap]`.
Each polynomial is centered at the midpoint of its interval (`centeredP`, `centeredJ`) and its low
coefficients are bounded by integer comparisons (`P_coefficients`, `J_coefficients`). The two odd
terms of the second certificate are kept together. All remaining powers receive a single rational
tail bound; no angular samples or assumed reserves occur.
-/

section
/-!
## The joint-negative BT3 and TD0 stress

The secants of the two negative primaries cancel the flat A and E tangents in the seven
inequalities of the cycle (`decomposition`, `stress_nonpositive`). The signed TD0 angle, independent
of the others, stays in the force on D (`actualD`), and T is supported in the direction
`(1, eta)` (`actual_T_support`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

def exactBaseline (atG atH : Bool) (k m c eta r s z : ℝ) : ℝ :=
  k+lambdaG atG r+lambdaB atG r+m*edgeWidth z+c+
    lambdaD atH s+lambdaH atH s-m*sigma eta*Real.sin z-
    fullSupport (lambdaH atH s) k-fullSupport (lambdaG atG r) k-
    fullSupport m (lambdaB atG r)-clippedSupport (lambdaD atH s) c+
    sec r*(edgeWidth r-1)+(7/12)*Real.tan r+
    sec s*(edgeWidth s-1)+(7/12)*Real.tan s

def actualStress (C : SignedCycle) (hg : Fin 4) (atG atH : Bool)
    (k m c r s : ℝ) : ℝ :=
  demand C (weights atG atH k m c r s)-
    ∑i,work (force C (owners hg atG atH) (weights atG atH k m c r s) i) (C.point i)

def actualD (C : SignedCycle) (atH : Bool) (c s : ℝ) : ℝ :=
  let x := delta C.theta T
  let y := if atH then delta C.theta D else 0
  c*(edgeWidth x-1)+lambdaD atH s*(edgeWidth y-1)+clippedSupport (lambdaD atH s) c-
    (pairF c (lambdaD atH s) x y*(C.point D).a+
      pairG c (lambdaD atH s) x y*(-(C.point D).y))

def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG atH : Bool)
    (k m c r s : ℝ) : Fin 5→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg atG atH k m c r s 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg atG atH k m c r s 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg atG atH k m c r s 2) (C.point B).reflect,
    actualD C atH c s,0]

def tReserve (C : SignedCycle) (m eta : ℝ) : ℝ :=
  m*Real.sin (delta C.theta B)*(sigma eta-((C.point T).a+eta*(C.point T).y))

theorem actual_T_support {q eta : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap) (he : 0≤eta) :
    P.a+eta*P.y≤ sigma eta := by
  have hC : P.Contained (R^2) := by rw [radius_sq]; exact hc.trans hq
  have hh := work_le_circleSupport (Real.sqrt_nonneg qCap) hs hC (1,eta)
  simpa [work,circleSupport,sigma,fullSupport,abs_of_nonneg he] using hh

theorem tReserve_nonnegative {q m eta : ℝ} {C : SignedCycle}
    (hs : (C.point T).Sorted) (hc : (C.point T).Contained q) (hq : q≤qCap)
    (hm : 0≤ m) (he : 0≤eta) (hz : delta C.theta B∈Icc 0 frameCap) :
    0≤tReserve C m eta := by
  exact mul_nonneg (mul_nonneg hm (transport_trig hz).2.2.1)
    (sub_nonneg.mpr (actual_T_support hs hc hq he))

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG atH : Bool)
    (k m eta : ℝ) {c r s : ℝ} (hhg : hg=0 ∨ hg=2)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (ha : aError C atG= -r) (he : eError C atH= -s)
    (hA : (C.point A).a=7/12) (hE : (C.point E).a=7/12)
    (hrot : c=m*tilt eta (delta C.theta B)) :
    actualStress C hg atG atH k m c r s=
      exactBaseline atG atH k m c eta r s (delta C.theta B)+
        (∑i,actualBlocks C hg atG atH k m c r s i)+tReserve C m eta := by
  have hcr : Real.cos r≠0 := (show 0<Real.cos r by linarith [(transport_trig hr).1]).ne'
  have hcs : Real.cos s≠0 := (show 0<Real.cos s by linarith [(transport_trig hs).1]).ne'
  have hA' : (C.point 2).a=7/12 := hA
  have hE' : (C.point 6).a=7/12 := hE
  cases atG <;> cases atH <;> rcases hhg with rfl|rfl <;>
    simp only [aError,eError,JointNegativeAETD2.Source.aError,
      JointNegativeAETD2.Source.eError,Bool.false_eq_true,↓reduceIte,G,A,D,E] at ha he <;>
    simp only [actualStress,demand,weights,lambdaG,JointNegativeAETD2.Source.lambdaG,
      Bool.false_eq_true,↓reduceIte,lambdaB,JointNegativeAETD2.Source.lambdaB,
      SecantNormCurvature.secant,one_div,hrot,tilt,B,Fin.isValue,lambdaD,
      JointNegativeAETD2.Source.lambdaD,lambdaH,JointNegativeAETD2.Source.lambdaH,
      Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.succ_zero_eq_one,one_mul,
      Fin.succ_one_eq_two,ha,edgeWidth_neg,Fin.reduceSucc,he,Finset.univ_unique,
      Fin.default_eq_zero,Matrix.cons_val_fin_one,Finset.sum_singleton,work,force,add,scale,
      source,word,Nat.succ_eq_add_one,Nat.reduceAdd,owners,previous,target,mul_zero,
      Matrix.cons_val,one_ne_zero,zero_add,mul_one,mul_neg,Real.cos_neg,Real.sin_neg,
      Matrix.cons_val_one,add_zero,hA',neg_mul,neg_neg,hE',exactBaseline,sec,
      Real.tan_eq_sin_div_cos,actualBlocks,PositiveTD.actualPairIncrement,blocks,E,H,G,T,
      edgeWidth_zero,sub_self,pairF,Real.sin_zero,pairG,Real.cos_zero,SignedPoint.reflect,
      zero_sub,neg_add_rev,actualD,D,Finset.sum_const_zero,tReserve,Fin.reduceEq,A,
      inv_mul_cancel₀ hcr,inv_mul_cancel₀ hcs] <;>
    ring

theorem weights_nonnegative (atG atH : Bool) {k m c r s : ℝ}
    (hk : 0≤k) (hm : 0≤ m) (hc : 0≤c) (hr : r∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) (i : Vertex) : 0≤weights atG atH k m c r s i := by
  have hcr : 0<Real.cos r := by linarith [(transport_trig hr).1]
  have hcs : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hr0 : 0≤ sec r := div_nonneg (by norm_num) hcr.le
  have hs0 : 0≤ sec s := div_nonneg (by norm_num) hcs.le
  cases atG <;> cases atH <;> fin_cases i <;>
    simp [weights,lambdaG,lambdaB,lambdaH,lambdaD,
      JointNegativeAETD2.Source.lambdaG,JointNegativeAETD2.Source.lambdaB,
      JointNegativeAETD2.Source.lambdaH,JointNegativeAETD2.Source.lambdaD] <;> positivity

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG atH : Bool)
    {k m c r s : ℝ} (hk : 0≤k) (hm : 0≤ m) (hc : 0≤c)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if atH then 2 else 3))
    (hEH : C.Feasible E (if atH then 1 else 0)) :
    actualStress C hg atG atH k m c r s≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg atG atH i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonnegative atG atH hk hm hc hr hs) hf)

def aGain (atG : Bool) (k m r : ℝ) : ℝ := F (if atG then k else m) r
def eGain (atH : Bool) (k c s : ℝ) : ℝ :=
  if atH then F k s else JointNegativeAETD2.sortedGain c s

theorem baseline_identity (atG atH : Bool) (k m c eta z : ℝ) {r s : ℝ}
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hf : tilt eta z≠0) (hrot : c=m*tilt eta z) :
    exactBaseline atG atH k m c eta r s z=
      baseline k c eta z+aGain atG k m r+eGain atH k c s := by
  have hm : c/tilt eta z=m := by rw [hrot]; exact mul_div_cancel_right₀ m hf
  have hrw := NegativeAPositiveTD.secant_width_identity (l:=1) hr
  have hsw := NegativeAPositiveTD.secant_width_identity (l:=1) hs
  dsimp [NegativeAPositiveTD.secant] at hrw hsw
  have hw := edgeWidth_positive_formula hz
  cases atG <;> cases atH <;>
    simp only [exactBaseline,baseline,aGain,eGain,lambdaG,lambdaB,lambdaH,lambdaD,
      JointNegativeAETD2.Source.lambdaG,JointNegativeAETD2.Source.lambdaB,
      JointNegativeAETD2.Source.lambdaH,JointNegativeAETD2.Source.lambdaD,
      Bool.false_eq_true,↓reduceIte,JointNegativeAETD2.clipped_norm,
      JointNegativeAETD2.sortedNorm_one,fullSupport,F,JointNegativeAETD2.F,
      JointNegativeAETD2.sortedGain,SecantNormCurvature.normalized,
      SecantNormCurvature.supportNorm,one_pow,hw,hm,JointNegativeAETD2.Source.sec]
  all_goals
    simp only [add_comm (k^2) ((sec r)^2),add_comm (k^2) ((sec s)^2),
      add_comm (m^2) ((sec r)^2),add_comm (k^2) 1,add_comm (m^2) 1]
    dsimp only [sec,SecantNormCurvature.secant,tilt,JointNegativeAETD2.Source.sec] at *
    linarith [hrw,hsw,hrot]

theorem common_baseline_lower {k m c eta r s z : ℝ} (atG atH : Bool)
    (hk : 0<k) (hk1 : k≤1) (hkc : k≤c) (hkm : k≤ m)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hf : tilt eta z≠0) (hrot : c=m*tilt eta z) :
    baseline k c eta z+F k r+F k s≤exactBaseline atG atH k m c eta r s z := by
  have ha : F k r≤aGain atG k m r := by
    cases atG
    · exact JointNegativeAETD2.fullGain_monotone hk.le hkm hr
    · exact le_rfl
  have he : F k s≤eGain atH k c s := by
    cases atH
    · exact JointNegativeAETD2.sortedGain_lower hk hk1 hkc hs
    · exact le_rfl
  rw [baseline_identity atG atH k m c eta z hr hs hz hf hrot]
  linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Source
end
end
end

section
/-!
## The derivative and polynomial data of the common secant gain

Inverse half-powers are written as odd powers of the positive square root `D k x`. The two
coefficient certificates are the rational polynomials `P`, of degree 13, and `J`, of degree 150,
with their shifts `centeredP` and `centeredJ`.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary

abbrev K : ℝ := 13/12
def shapeA (k y : ℝ) : ℝ := 1+k^2-k^2*y^2
def shapeB (k y : ℝ) : ℝ := (1+k^2)*(1+y^2)-2*k^2*y^4
def shapeC (k y : ℝ) : ℝ :=
  (1+k^2)*(5+8*k^2)+(1+k^2)*(1-12*k^2)*y^2-2*k^2*y^4+4*k^4*y^6
def D (k x : ℝ) : ℝ := Real.sqrt (1+k^2*Real.cos x^2)
def F1 (k x : ℝ) : ℝ :=
  (K+Real.sin x-R*Real.sin x/D k x)/Real.cos x^2
def F2 (k x : ℝ) : ℝ :=
  (2*K*Real.sin x+1+Real.sin x^2-R*shapeB k (Real.sin x)/(D k x)^3)/Real.cos x^3
def F3 (k x : ℝ) : ℝ :=
  (2*K+5*Real.sin x+4*K*Real.sin x^2+Real.sin x^3-
    R*Real.sin x*shapeC k (Real.sin x)/(D k x)^5)/Real.cos x^4
def F2k (k x : ℝ) : ℝ :=
  R*k*Real.cos x*(1+k^2*(1+2*Real.sin x^2))/(D k x)^5
def signPolynomial (p u : ℝ) : ℝ :=
  (1+p)*(8*p-1)-2*p*(5+2*p)*u-4*p^2*u^2
def F3k (k x : ℝ) : ℝ :=
  R*k*Real.sin x*signPolynomial (k^2) (Real.sin x^2)/(D k x)^7
def E2 (x : ℝ) : ℝ :=
  -1/250+(33/25)*(x-7/20)-(1/10)*(x-7/20)^2+(19/10)*(x-7/20)^3
def L (v : ℝ) : ℝ := 1+(5/2)*v+(35/8)*v^2+8*v^3
def L2 (v : ℝ) : ℝ := 1+(3/2)*v+(15/8)*v^2+(35/16)*v^3

namespace Certificate
open Polynomial
abbrev pLow : ℚ := 169/400
abbrev pHigh : ℚ := (751/1000)^2
def b (p : ℚ) : ℚ[X] := C (1+p)*(1+X^2)-C (2*p)*X^4
def c (p : ℚ) : ℚ[X] :=
  C ((1+p)*(5+8*p))+C ((1+p)*(1-12*p))*X^2-C (2*p)*X^4+C (4*p^2)*X^6
def l : ℚ[X] := 1+C (5/2)*X+C (35/8)*X^2+C 8*X^3
def l2 : ℚ[X] := 1+C (3/2)*X+C (15/8)*X^2+C (35/16)*X^3
def e2 : ℚ[X] := -C (1/250)+C (33/25)*(X-C (7/20))-
  C (1/10)*(X-C (7/20))^2+C (19/10)*(X-C (7/20))^3
def P : ℚ[X] :=
  C (13/6-11/10)+C 5*X+C (13/3+11/5)*X^2+X^3-C (11/10)*X^4-
    C (163983/200000)*X*c pLow*(l.comp (C (pLow/(1+pLow))*X^2))
def J : ℚ[X] :=
  e2*PositiveScalarPolynomials.cosine^3-C (13/6)*PositiveScalarPolynomials.sine-
    1-PositiveScalarPolynomials.sine^2+C (6323/6250)*
      ((b pHigh).comp PositiveScalarPolynomials.sine)*
      (l2.comp (C (pHigh/(1+pHigh))*PositiveScalarPolynomials.sine^2))
def centeredP : ℚ[X] := DirectedPowerBounds.shift (2/5) P
def centeredJ : ℚ[X] := DirectedPowerBounds.shift (7/20) J
def jTailNorm : ℚ :=
  ∑i:Fin 145,|centeredJ.coeff (i.val+6)| *(7/20)^(i.val+4)

end Certificate
end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
end
end
end

section
/-!
## Exact derivatives of the common secant gain

The square-root
identities are used before clearing denominators, so each derivative
reduces to the displayed polynomial identity in sine and cosine.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary

theorem D_positive (k x : ℝ) : 0<D k x := Real.sqrt_pos.mpr (by positivity)
theorem D_square (k x : ℝ) : (D k x)^2=1+k^2*Real.cos x^2 :=
  Real.sq_sqrt (by positivity)
theorem cos_square (x : ℝ) : Real.cos x^2=1-Real.sin x^2 := by
  linarith [Real.sin_sq_add_cos_sq x]
theorem D_shape (k x : ℝ) : (D k x)^2=shapeA k (Real.sin x) := by
  rw [D_square,cos_square]
  dsimp [shapeA]
  ring

theorem D_angle_derivative (k x : ℝ) :
    HasDerivAt (D k) (-k^2*Real.sin x*Real.cos x/D k x) x := by
  have hd := ((((Real.hasDerivAt_cos x).pow 2).const_mul (k^2)).const_add 1).sqrt
    (show 1+k^2*Real.cos x^2≠0 by positivity)
  convert hd using 1
  · rfl
  · dsimp [D]
    ring
theorem D_parameter_derivative (k x : ℝ) :
    HasDerivAt (fun k => D k x) (k*Real.cos x^2/D k x) k := by
  have hd := ((((hasDerivAt_id k).pow 2).mul_const (Real.cos x^2)).const_add 1).sqrt
    (show 1+k^2*Real.cos x^2≠0 by positivity)
  convert hd using 1
  · rfl
  · dsimp [D]
    ring

theorem B_angle_derivative (k x : ℝ) :
    HasDerivAt (fun x => shapeB k (Real.sin x))
      ((2*(1+k^2)*Real.sin x-8*k^2*Real.sin x^3)*Real.cos x) x := by
  refine ((((Real.hasDerivAt_sin x).fun_pow 2).const_add 1).const_mul (1+k^2)).fun_sub
    (((Real.hasDerivAt_sin x).fun_pow 4).const_mul (2*k^2)) |>.congr_deriv ?_
  norm_num
  ring
theorem B_parameter_derivative (k y : ℝ) :
    HasDerivAt (fun k => shapeB k y) (2*k*(1+y^2)-4*k*y^4) k := by
  refine ((((hasDerivAt_id' k).fun_pow 2).const_add 1).mul_const (1+y^2)).fun_sub
    ((((hasDerivAt_id' k).fun_pow 2).const_mul 2).mul_const (y^4)) |>.congr_deriv ?_
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
  ring
theorem C_parameter_derivative (k y : ℝ) :
    HasDerivAt (fun k => shapeC k y)
      (2*k*(13+16*k^2)+2*k*(-11-24*k^2)*y^2-4*k*y^4+16*k^3*y^6) k := by
  have hp := (hasDerivAt_id' k).fun_pow 2
  refine ((((hp.const_add 1).fun_mul ((hp.const_mul 8).const_add 5)).fun_add
    (((hp.const_add 1).fun_mul ((hp.const_mul 12).const_sub 1)).mul_const (y^2))).fun_sub
      ((hp.const_mul 2).mul_const (y^4))).fun_add
      ((((hasDerivAt_id' k).fun_pow 4).const_mul 4).mul_const (y^6)) |>.congr_deriv ?_
  norm_num
  ring

theorem F_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (F k) (F1 k x) x := by
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  have hh := SecantNormCurvature.normalized_hasDerivAt (R:=R) (a:=k) hc
  have he := NegativeAPositiveTD.SecantBaseline.angleSlope_eq (l:=1) (r:=k) hc
  have he' : SecantNormCurvature.gainFirst R k x=F1 k x := by
    simpa [F1,D,K,NegativeAPositiveTD.SecantBaseline.angleSlope,
      NegativeAPositiveTD.SecantBaseline.denominator] using he
  rw [he'] at hh
  exact hh

theorem F1_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (F1 k) (F2 k x) x := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hB : shapeB k (Real.sin x)=
      (Real.cos x^2+2*Real.sin x^2)*(D k x)^2+
        k^2*Real.sin x^2*Real.cos x^2 := by
    rw [D_square,cos_square]
    dsimp [shapeB]
    ring
  have h1 : 2*K*Real.sin x+1+Real.sin x^2=2*K*Real.sin x+(Real.cos x^2+2*Real.sin x^2) := by
    rw [cos_square]; ring
  have hd := (((Real.hasDerivAt_sin x).const_add K).fun_sub
    (((Real.hasDerivAt_sin x).const_mul R).fun_div (D_angle_derivative k x) hD)).fun_div
      ((Real.hasDerivAt_cos x).fun_pow 2) (pow_ne_zero _ hc)
  refine hd.congr_deriv ?_
  rw [F2,hB,h1]
  norm_num
  field_simp
  ring

theorem F2_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (F2 k) (F3 k x) x := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hC : Real.sin x*shapeC k (Real.sin x)=
      Real.cos x^2*((2*(1+k^2)*Real.sin x-8*k^2*Real.sin x^3)*(D k x)^2+
        3*k^2*Real.sin x*shapeB k (Real.sin x))+
      3*Real.sin x*shapeB k (Real.sin x)*(D k x)^2 := by
    rw [D_square,cos_square]
    dsimp [shapeB,shapeC]
    ring
  have hK : 2*K+5*Real.sin x+4*K*Real.sin x^2+Real.sin x^3=
      (2*K+2*Real.sin x)*Real.cos x^2+
        3*Real.sin x*(2*K*Real.sin x+1+Real.sin x^2) := by
    rw [cos_square]
    ring
  have hd := (((((Real.hasDerivAt_sin x).const_mul (2*K)).add_const 1).add
    ((Real.hasDerivAt_sin x).pow 2)).sub
      (((B_angle_derivative k x).const_mul R).div ((D_angle_derivative k x).pow 3)
        (pow_ne_zero _ hD))).div ((Real.hasDerivAt_cos x).pow 3) (pow_ne_zero _ hc)
  convert hd using 1
  · rfl
  · dsimp [F3]
    rw [show R*Real.sin x*shapeC k (Real.sin x)=R*(Real.sin x*shapeC k (Real.sin x)) by ring,hC,hK]
    field_simp [hc,hD]
    ring

theorem F1_parameter_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (fun k => F1 k x) (R*k*Real.sin x/(D k x)^3) k := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hd := (((hasDerivAt_const k (R*Real.sin x)).div
    (D_parameter_derivative k x) hD).const_sub (K+Real.sin x)).div_const (Real.cos x^2)
  convert hd using 1
  · rfl
  · field_simp [hc,hD]
    ring

theorem F2_parameter_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (fun k => F2 k x) (F2k k x) k := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hid : -(2*k*(1+Real.sin x^2)-4*k*Real.sin x^4)*(D k x)^2+
      3*shapeB k (Real.sin x)*k*Real.cos x^2=
        k*Real.cos x^4*(1+k^2*(1+2*Real.sin x^2)) := by
    rw [D_square,show Real.cos x^4=(Real.cos x^2)^2 by ring,cos_square]
    dsimp [shapeB]
    ring
  have hout : F2k k x=R*(-(2*k*(1+Real.sin x^2)-4*k*Real.sin x^4)*(D k x)^2+
      3*shapeB k (Real.sin x)*k*Real.cos x^2)/((D k x)^5*Real.cos x^3) := by
    rw [hid]
    dsimp [F2k]
    field_simp
  have hd := ((((B_parameter_derivative k (Real.sin x)).const_mul R).fun_div
    ((D_parameter_derivative k x).fun_pow 3) (pow_ne_zero _ hD)).const_sub
      (2*K*Real.sin x+1+Real.sin x^2)).div_const (Real.cos x^3)
  refine hd.congr_deriv ?_
  rw [hout]
  norm_num
  field_simp
  ring

theorem F3_parameter_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (fun k => F3 k x) (F3k k x) k := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hid : -(2*k*(13+16*k^2)+2*k*(-11-24*k^2)*Real.sin x^2-
      4*k*Real.sin x^4+16*k^3*Real.sin x^6)*(D k x)^2+
      5*shapeC k (Real.sin x)*k*Real.cos x^2=
        k*Real.cos x^4*signPolynomial (k^2) (Real.sin x^2) := by
    rw [D_square,show Real.cos x^4=(Real.cos x^2)^2 by ring,cos_square]
    dsimp [shapeC,signPolynomial]
    ring
  have hout : F3k k x=R*Real.sin x*
      (-(2*k*(13+16*k^2)+2*k*(-11-24*k^2)*Real.sin x^2-
        4*k*Real.sin x^4+16*k^3*Real.sin x^6)*(D k x)^2+
        5*shapeC k (Real.sin x)*k*Real.cos x^2)/((D k x)^7*Real.cos x^4) := by
    rw [hid]
    dsimp [F3k]
    field_simp
  have hd := ((((C_parameter_derivative k (Real.sin x)).const_mul (R*Real.sin x)).fun_div
    ((D_parameter_derivative k x).fun_pow 5) (pow_ne_zero _ hD)).const_sub
      (2*K+5*Real.sin x+4*K*Real.sin x^2+Real.sin x^3)).div_const (Real.cos x^4)
  refine hd.congr_deriv ?_
  rw [hout]
  norm_num
  field_simp
  ring

@[simp] theorem F_zero (k : ℝ) : F k 0=0 := by
  simp [F,SecantNormCurvature.normalized,SecantNormCurvature.secant,SecantNormCurvature.supportNorm]

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain.Certificate
open Polynomial PowerTailBounds DirectedPowerBounds
open WholeIntervalPolynomial.Certificate (Scaled toPoly)


/-! ### Normalization of scaled lists by their gcd -/

private def r67_gcd (s : ℕ) : List ℤ → ℕ
  | [] => s
  | a :: l => Nat.gcd a.natAbs (r67_gcd s l)

private theorem r67_gcd_dvd (s : ℕ) : ∀ l : List ℤ,
    r67_gcd s l ∣ s ∧ ∀ a ∈ l,((r67_gcd s l : ℕ):ℤ) ∣ a
  | [] => by simp [r67_gcd]
  | a :: l => by
    obtain ⟨h1,h2⟩ := r67_gcd_dvd s l
    refine ⟨(Nat.gcd_dvd_right _ _).trans h1,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (h2 b hb)

private theorem r67_smul_div (g : ℤ) : ∀ l : List ℤ,(∀ a ∈ l,g ∣ a) →
    WholeIntervalPolynomial.Certificate.smul g (l.map (fun a => a/g))=l
  | [],_ => rfl
  | a :: l,h => by
    simp only [List.map_cons,WholeIntervalPolynomial.Certificate.smul]
    rw [Int.mul_ediv_cancel' (h a List.mem_cons_self),
      r67_smul_div g l (fun b hb => h b (List.mem_cons_of_mem a hb))]

private theorem r67_toPoly_zero : ∀ l : List ℤ,toPoly (l.map (fun _ => (0:ℤ)))=0
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons,toPoly,r67_toPoly_zero l,Int.cast_zero,map_zero,mul_zero,add_zero]

/-- Division of a scaled list by the gcd of its entries and its scale. -/
private def r67_red (c : Scaled) : Scaled :=
  ⟨c.l.map (fun a => a/((r67_gcd c.s c.l : ℕ):ℤ)),c.s/r67_gcd c.s c.l⟩

private theorem r67_rep_red {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (r67_red c).Rep p := by
  obtain ⟨h1,h2⟩ := r67_gcd_dvd c.s c.l
  set g := r67_gcd c.s c.l with hg
  have hl := r67_smul_div (g:ℤ) c.l h2
  unfold Scaled.Rep at *
  rw [← hl,WholeIntervalPolynomial.Certificate.toPoly_smul] at hc
  obtain ⟨k,hk⟩ := h1
  simp only [r67_red,← hg]
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · have hs : c.s=0 := by rw [hk,h0,zero_mul]
    rw [h0,hs]
    simp only [Nat.cast_zero,Int.ediv_zero,Nat.zero_div,map_zero,zero_mul]
    exact r67_toPoly_zero _
  · have hg0 : (g:ℚ)≠0 := by exact_mod_cast hpos.ne'
    rw [hk,Nat.mul_div_cancel_left k hpos]
    rw [hk] at hc
    push_cast at hc
    exact mul_left_cancel₀ (show C (g:ℚ)≠0 from C_ne_zero.mpr hg0)
      (hc.trans (by rw [map_mul,mul_assoc]))

/-! ### Shifts, splittings and coefficient sums -/

private theorem r67_shift_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) (h1 : (1:ℚ)=num*t/den) :
    (S.center num den s t).Rep (DirectedPowerBounds.shift a p) := by
  have hc := hp.centered num den s t (a:=a-1) (b:=a+1) hden (by rw [← ha]; ring)
    (by rw [← h1]; ring)
  have he : WholeIntervalPolynomial.centered (a-1) (a+1) p=DirectedPowerBounds.shift a p := by
    rw [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,DirectedPowerBounds.shift,
      show (a-1+(a+1))/2=a by ring,show (a+1-(a-1))/2=1 by ring,map_one,one_mul]
  rwa [he] at hc

/-- A polynomial of degree below `start+count` is its head plus its power tail. -/
private theorem r67_split (p : ℚ[X]) (start count : ℕ) (h : p.natDegree<start+count) :
    p=(∑ i ∈ Finset.range start,C (p.coeff i)*X^i)+PowerTailBounds.tail p start count := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' h,Finset.sum_range_add]
  congr 1
  rw [PowerTailBounds.tail,Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+start))*X^(j+start))]
  exact Finset.sum_congr rfl fun j _ => by rw [add_comm start j]

private theorem r67_natDegree_lt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) {n : ℕ}
    (hl : c.l.length≤n) (hn : 0<n) : p.natDegree<n :=
  lt_of_le_of_lt (hc.natDegree_le hs) (by omega)

/-- Horner form of `∑ j<k, |a_j| num^j den^(k-j)`. -/
private def r67_hsum (num den : ℕ) : List ℤ → ℕ → ℤ
  | [],_ => 0
  | _ :: _,0 => 0
  | a :: l,k+1 => |a| *((den^(k+1):ℕ):ℤ)+(num:ℤ)*r67_hsum num den l k

private theorem r67_hsum_eq (num den : ℕ) : ∀ (l : List ℤ) (k : ℕ),
    (r67_hsum num den l k:ℚ)=∑ j : Fin k,|(l.getD j.val 0:ℚ)| *(num:ℚ)^j.val*(den:ℚ)^(k-j.val)
  | [],k => by simp [r67_hsum]
  | a :: l,0 => by simp [r67_hsum]
  | a :: l,k+1 => by
    rw [Fin.sum_univ_succ]
    simp only [r67_hsum,Fin.val_zero,Fin.val_succ,List.getD_cons_zero,List.getD_cons_succ,
      pow_zero,mul_one,Nat.sub_zero]
    push_cast
    rw [r67_hsum_eq num den l k,Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

private theorem r67_getD_drop (l : List ℤ) (s j : ℕ) : (l.drop s).getD j 0=l.getD (j+s) 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_drop,add_comm s j]

private theorem r67_wsum_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (start e count num den : ℕ) (hden : den≠0) :
    ∑ j : Fin count,|p.coeff (j.val+start)| *((num:ℚ)/den)^(j.val+e)=
      ((num:ℚ)^e*(r67_hsum num den (c.l.drop start) count:ℚ))/(c.s*(den:ℚ)^(count+e)) := by
  rw [r67_hsum_eq,Finset.mul_sum,Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (den:ℚ)≠0 := by exact_mod_cast hden
  rw [hc.coeff hs,r67_getD_drop,abs_div,abs_of_pos hs',div_pow,
    show (den:ℚ)^(count+e)=den^(j.val+e)*den^(count-j.val) by
      rw [← pow_add]; congr 1; omega,pow_add]
  field_simp

private theorem r67_norm_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (start count num den : ℕ) (hden : den≠0) :
    PowerTailBounds.norm p start count ((num:ℚ)/den)=
      (((num*r67_hsum num den (c.l.drop start) count:ℤ)):ℚ)/(c.s*(den:ℚ)^(count+1)) := by
  rw [PowerTailBounds.norm,r67_wsum_eq hc hs start 1 count num den hden]
  push_cast
  ring

/-! ### Rational comparisons from integer ones -/

private theorem r67_gt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (i : ℕ)
    {Z : ℤ} {D : ℕ} (hD : 0<D) {a : ℤ} {b : ℕ} (hb : 0<b)
    (h : a*((c.s:ℤ)*D)<(c.l.getD i 0*D-Z)*b) :
    (a:ℚ)/b<p.coeff i-(Z:ℚ)/(c.s*D) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have e : p.coeff i-(Z:ℚ)/(c.s*D)=(((c.l.getD i 0*D-Z:ℤ)):ℚ)/((c.s:ℚ)*D) := by
    rw [hc.coeff hs]; push_cast; field_simp
  rw [e,div_lt_div_iff₀ hb' (by positivity)]
  exact_mod_cast h

private theorem r67_coeff_gt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (i : ℕ)
    {a : ℤ} {b : ℕ} (hb : 0<b) (h : a*c.s<c.l.getD i 0*b) : (a:ℚ)/b<p.coeff i := by
  have hh := r67_gt hc hs i (Z:=0) (D:=1) one_pos hb (by simpa using h)
  simpa using hh

private theorem r67_coeff_lt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (i : ℕ)
    {a : ℤ} {b : ℕ} (hb : 0<b) (h : c.l.getD i 0*b<a*c.s) : p.coeff i<(a:ℚ)/b := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  rw [hc.coeff hs,div_lt_div_iff₀ hs' hb']
  exact_mod_cast h

private theorem r67_coeff_abs_lt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (i : ℕ)
    {a : ℤ} {b : ℕ} (hb : 0<b) (h : |c.l.getD i 0| *b<a*c.s) : |p.coeff i|<(a:ℚ)/b := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  rw [hc.coeff hs,abs_div,abs_of_pos hs',div_lt_div_iff₀ hs' hb']
  exact_mod_cast h

/-! ### The degree-13 certificate -/

private theorem r67_l_comp (q : ℚ[X]) :
    l.comp q=1+C (5/2)*q+C (35/8)*q^2+C 8*q^3 := by
  simp only [l,add_comp,mul_comp,C_comp,X_comp,pow_comp,one_comp]

private def r67_qP : Scaled := (Scaled.const (pLow/(1+pLow))).mul (Scaled.var.pow 2)
private theorem r67_qP_rep : r67_qP.Rep (C (pLow/(1+pLow))*X^2) :=
  (Scaled.rep_const _).mul (Scaled.rep_var.pow 2)

private def r67_P : Scaled :=
  (((((Scaled.const (13/6-11/10)).add ((Scaled.const 5).mul Scaled.var)).add
    ((Scaled.const (13/3+11/5)).mul (Scaled.var.pow 2))).add (Scaled.var.pow 3)).sub
    ((Scaled.const (11/10)).mul (Scaled.var.pow 4))).sub
    ((((Scaled.const (163983/200000)).mul Scaled.var).mul
      ((((Scaled.const ((1+pLow)*(5+8*pLow))).add
        ((Scaled.const ((1+pLow)*(1-12*pLow))).mul (Scaled.var.pow 2))).sub
        ((Scaled.const (2*pLow)).mul (Scaled.var.pow 4))).add
        ((Scaled.const (4*pLow^2)).mul (Scaled.var.pow 6)))).mul
      ((((Scaled.ofNat 1).add ((Scaled.const (5/2)).mul r67_qP)).add
        ((Scaled.const (35/8)).mul (r67_qP.pow 2))).add ((Scaled.const 8).mul (r67_qP.pow 3))))
private theorem r67_P_rep : r67_P.Rep P := by
  have h := (((((Scaled.rep_const (13/6-11/10)).add ((Scaled.rep_const 5).mul Scaled.rep_var)).add
    ((Scaled.rep_const (13/3+11/5)).mul (Scaled.rep_var.pow 2))).add (Scaled.rep_var.pow 3)).sub
    ((Scaled.rep_const (11/10)).mul (Scaled.rep_var.pow 4))).sub
    ((((Scaled.rep_const (163983/200000)).mul Scaled.rep_var).mul
      ((((Scaled.rep_const ((1+pLow)*(5+8*pLow))).add
        ((Scaled.rep_const ((1+pLow)*(1-12*pLow))).mul (Scaled.rep_var.pow 2))).sub
        ((Scaled.rep_const (2*pLow)).mul (Scaled.rep_var.pow 4))).add
        ((Scaled.rep_const (4*pLow^2)).mul (Scaled.rep_var.pow 6)))).mul
      (((Scaled.rep_one.add ((Scaled.rep_const (5/2)).mul r67_qP_rep)).add
        ((Scaled.rep_const (35/8)).mul (r67_qP_rep.pow 2))).add
        ((Scaled.rep_const 8).mul (r67_qP_rep.pow 3))))
  rw [P,c,r67_l_comp]
  exact h

private def r67_cP : Scaled := r67_red (r67_P.center 1 5 2 5)
private theorem r67_cP_rep : r67_cP.Rep centeredP :=
  r67_rep_red (r67_shift_rep r67_P_rep 1 5 2 5 (by norm_num) (by norm_num) (by norm_num))

private theorem r67_cP_facts :
    r67_cP.s≠0 ∧ r67_cP.l.length≤14 ∧
    4097*(r67_cP.s:ℤ)<r67_cP.l.getD 0 0*50000 ∧
    |r67_cP.l.getD 1 0| *4000<2001*(r67_cP.s:ℤ) ∧
    133*((r67_cP.s:ℤ)*((5^12:ℕ):ℤ))<
      (r67_cP.l.getD 2 0*((5^12:ℕ):ℤ)-2*r67_hsum 2 5 (r67_cP.l.drop 3) 11)*50 := by
  decide +kernel

/-! ### The degree-150 certificate -/

private def r67_S : Scaled := r67_red
  ((((((((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))).sub
    ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
    ((Scaled.const (1/362880)).mul (Scaled.var.pow 9))).sub
    ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11))).add
    ((Scaled.const (1/6227020800)).mul (Scaled.var.pow 13))).sub
    ((Scaled.const (1/1307674368000)).mul (Scaled.var.pow 15))))
private theorem r67_S_rep : r67_S.Rep PositiveScalarPolynomials.sine := r67_rep_red
  ((((((((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 13))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 15))))

private def r67_C : Scaled := r67_red
  (((((((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))).sub
    ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
    ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
    ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10))).add
    ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12))).sub
    ((Scaled.const (1/87178291200)).mul (Scaled.var.pow 14))).add
    ((Scaled.const (1/20922789888000)).mul (Scaled.var.pow 16)))
private theorem r67_C_rep : r67_C.Rep PositiveScalarPolynomials.cosine := r67_rep_red
  ((((((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 14))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 16)))

private theorem r67_l2_comp (q : ℚ[X]) :
    l2.comp q=1+C (3/2)*q+C (15/8)*q^2+C (35/16)*q^3 := by
  simp only [l2,add_comp,mul_comp,C_comp,X_comp,pow_comp,one_comp]
private theorem r67_b_comp (p : ℚ) (q : ℚ[X]) :
    (b p).comp q=C (1+p)*(1+q^2)-C (2*p)*q^4 := by
  simp only [b,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp,one_comp]

private def r67_X7 : Scaled := Scaled.var.sub (Scaled.const (7/20))
private theorem r67_X7_rep : r67_X7.Rep (X-C (7/20)) := Scaled.rep_var.sub (Scaled.rep_const _)
private def r67_q : Scaled := (Scaled.const (pHigh/(1+pHigh))).mul (r67_S.pow 2)
private theorem r67_q_rep : r67_q.Rep (C (pHigh/(1+pHigh))*PositiveScalarPolynomials.sine^2) :=
  (Scaled.rep_const _).mul (r67_S_rep.pow 2)

private def r67_J : Scaled := r67_red
  ((((((((Scaled.const (1/250)).neg.add ((Scaled.const (33/25)).mul r67_X7)).sub
    ((Scaled.const (1/10)).mul (r67_X7.pow 2))).add ((Scaled.const (19/10)).mul (r67_X7.pow 3))).mul
    (r67_C.pow 3)).sub ((Scaled.const (13/6)).mul r67_S)).sub (Scaled.ofNat 1)).sub
    (r67_S.pow 2) |>.add (((Scaled.const (6323/6250)).mul
      (((Scaled.const (1+pHigh)).mul ((Scaled.ofNat 1).add (r67_S.pow 2))).sub
        ((Scaled.const (2*pHigh)).mul (r67_S.pow 4)))).mul
      ((((Scaled.ofNat 1).add ((Scaled.const (3/2)).mul r67_q)).add
        ((Scaled.const (15/8)).mul (r67_q.pow 2))).add ((Scaled.const (35/16)).mul (r67_q.pow 3)))))
private theorem r67_J_rep : r67_J.Rep J := by
  rw [J,e2,r67_b_comp,r67_l2_comp]
  exact r67_rep_red
    ((((((((Scaled.rep_const _).neg.add ((Scaled.rep_const _).mul r67_X7_rep)).sub
      ((Scaled.rep_const _).mul (r67_X7_rep.pow 2))).add
      ((Scaled.rep_const _).mul (r67_X7_rep.pow 3))).mul
      (r67_C_rep.pow 3)).sub ((Scaled.rep_const _).mul r67_S_rep)).sub Scaled.rep_one).sub
      (r67_S_rep.pow 2) |>.add (((Scaled.rep_const _).mul
        (((Scaled.rep_const _).mul (Scaled.rep_one.add (r67_S_rep.pow 2))).sub
          ((Scaled.rep_const _).mul (r67_S_rep.pow 4)))).mul
        (((Scaled.rep_one.add ((Scaled.rep_const _).mul r67_q_rep)).add
          ((Scaled.rep_const _).mul (r67_q_rep.pow 2))).add
          ((Scaled.rep_const _).mul (r67_q_rep.pow 3)))))

/-- Composition with `(num/den) X`: the coefficient `a_i` becomes `a_i num^i den^(n-i)`. -/
private def r67_scale (c : Scaled) (num den : ℕ) : Scaled :=
  ⟨WholeIntervalPolynomial.Certificate.prescale num den (c.l.length-1) 0 c.l,
    c.s*den^(c.l.length-1)⟩

private theorem r67_scale_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ)
    (hden : den≠0) : (r67_scale c num den).Rep (p.comp (C ((num:ℚ)/den)*X)) := by
  have h := WholeIntervalPolynomial.Certificate.toPoly_prescale (num:=num) hden
    (c.l.length-1) c.l 0 (by omega)
  simp only [pow_zero,one_mul,map_one] at h
  unfold Scaled.Rep at *
  simp only [r67_scale]
  rw [← h,hc,mul_comp,C_comp]
  push_cast
  rw [map_mul]
  ring

/-- The shift by `a=num/den`, through the fast centering on `[0,2a]`. -/
private theorem r67_fast_shift {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) {a : ℚ}
    (hden : den≠0) (hnum : num≠0) (ha : a=num/den) :
    (r67_scale (c.center num den 1 1) den num).Rep (DirectedPowerBounds.shift a p) := by
  have h1 := hc.centered num den 1 1 (a:=0) (b:=2*a) hden (by rw [ha]; push_cast; ring)
    (by rw [ha]; push_cast; ring)
  have h2 := r67_scale_rep h1 den num hnum
  have hq : (WholeIntervalPolynomial.affine 0 (2*a)).comp (C ((den:ℚ)/num)*X)=C a+X := by
    have e1 : (0+2*a)/2=a := by ring
    have e2 : (2*a-0)/2*((den:ℚ)/num)=1 := by
      have : (num:ℚ)≠0 := by exact_mod_cast hnum
      have : (den:ℚ)≠0 := by exact_mod_cast hden
      rw [ha]; field_simp; ring
    rw [WholeIntervalPolynomial.affine,add_comp,mul_comp,C_comp,C_comp,X_comp,← mul_assoc,
      ← map_mul,e1,e2,map_one,one_mul]
  rwa [WholeIntervalPolynomial.centered,comp_assoc,hq] at h2

private def r67_cJ : Scaled := r67_red (r67_scale (r67_J.center 7 20 1 1) 20 7)
private theorem r67_cJ_rep : r67_cJ.Rep centeredJ :=
  r67_rep_red (r67_fast_shift r67_J_rep 7 20 (by norm_num) (by norm_num) (by norm_num))

private theorem r67_cJ_facts :
    r67_cJ.s≠0 ∧ r67_cJ.l.length≤151 ∧
    1589*(r67_cJ.s:ℤ)<r67_cJ.l.getD 0 0*250000 ∧
    |r67_cJ.l.getD 1 0| *200000<361*(r67_cJ.s:ℤ) ∧
    23599*(r67_cJ.s:ℤ)<r67_cJ.l.getD 2 0*100000 ∧
    19703*(r67_cJ.s:ℤ)<r67_cJ.l.getD 3 0*100000 ∧
    r67_cJ.l.getD 3 0*12500<2463*(r67_cJ.s:ℤ) ∧
    -85627*(r67_cJ.s:ℤ)<r67_cJ.l.getD 4 0*100000 ∧
    -144289*(r67_cJ.s:ℤ)<r67_cJ.l.getD 5 0*100000 ∧
    r67_cJ.l.getD 5 0*1<0*(r67_cJ.s:ℤ) ∧
    7^4*r67_hsum 7 20 (r67_cJ.l.drop 6) 145*125000<3033*((r67_cJ.s:ℤ)*((20^149:ℕ):ℤ)) := by
  decide +kernel

/-! ### The two certificates -/

theorem P_identity :
    centeredP=C (centeredP.coeff 0)+C (centeredP.coeff 1)*X+
      C (centeredP.coeff 2)*X^2+tail centeredP 3 11 := by
  have hf := r67_cP_facts
  have hd := r67_natDegree_lt r67_cP_rep hf.1 hf.2.1 (by norm_num)
  conv_lhs => rw [r67_split centeredP 3 11 hd]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]

theorem P_coefficients :
    (4097/50000:ℚ)<centeredP.coeff 0 ∧ |centeredP.coeff 1|<(2001/4000:ℚ) ∧
      (133/50:ℚ)<centeredP.coeff 2-PowerTailBounds.norm centeredP 3 11 (2/5) := by
  obtain ⟨hs,-,h0,h1,h2⟩ := r67_cP_facts
  refine ⟨?_,?_,?_⟩
  · have h := r67_coeff_gt r67_cP_rep hs 0 (a:=4097) (b:=50000) (by norm_num) h0
    norm_num at h
    exact h
  · have h := r67_coeff_abs_lt r67_cP_rep hs 1 (a:=2001) (b:=4000) (by norm_num) h1
    norm_num at h
    exact h
  · have hn := r67_norm_eq r67_cP_rep hs 3 11 2 5 (by norm_num)
    have h := r67_gt r67_cP_rep hs 2 (Z:=2*r67_hsum 2 5 (r67_cP.l.drop 3) 11) (D:=5^12)
      (by positivity) (a:=133) (b:=50) (by norm_num) (by exact_mod_cast h2)
    have e1 : PowerTailBounds.norm centeredP 3 11 (2/5)=
        ((2*r67_hsum 2 5 (r67_cP.l.drop 3) 11:ℤ):ℚ)/((r67_cP.s:ℚ)*((5^12:ℕ):ℚ)) := by
      rw [show (2/5:ℚ)=((2:ℕ):ℚ)/((5:ℕ):ℚ) by norm_num,hn]
      push_cast
      ring
    rw [e1]
    convert h using 1

theorem P_positive {y : ℝ} (hy : y∈Icc (0:ℝ) (129/200)) :
    (73/1250:ℝ)<aeval y P := by
  let u := y-2/5
  have hu : |u|≤(2/5:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hh := PowerTailBounds.quadratic_lower (r:=2/5) P_identity (by norm_num)
    (show |u|≤((2/5:ℚ):ℝ) by rw [show ((2/5:ℚ):ℝ)=2/5 by norm_num]; exact hu)
  have hc :
      (4097/50000:ℝ)<(centeredP.coeff 0:ℝ) ∧ |(centeredP.coeff 1:ℝ)|<(2001/4000:ℝ) ∧
      (133/50:ℝ)<(centeredP.coeff 2:ℝ)-(PowerTailBounds.norm centeredP 3 11 (2/5):ℝ) := by
    obtain ⟨p0,p1,p2⟩ := P_coefficients
    have q0 := (Rat.cast_lt (K:=ℝ)).mpr p0
    have q1 := (Rat.cast_lt (K:=ℝ)).mpr p1
    have q2 := (Rat.cast_lt (K:=ℝ)).mpr p2
    push_cast at q0 q1 q2
    exact ⟨q0,q1,q2⟩
  have hl : -(2001/4000:ℝ)*|u|≤(centeredP.coeff 1:ℝ)*u := by
    have ht := mul_le_mul_of_nonneg_right hc.2.1.le (abs_nonneg u)
    rw [←abs_mul] at ht
    rw [neg_mul]
    exact (abs_le.mp ht).1
  have hq := mul_le_mul_of_nonneg_right hc.2.2.le (sq_nonneg u)
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(4097/50000:ℝ))
    (b:=-(2001/4000:ℝ)) (x:=|u|) (show (0:ℝ)<133/50 by norm_num)
  have hid : aeval u centeredP=aeval y P := by simp [centeredP,u]
  rw [hid] at hh
  rw [sq_abs] at hm
  norm_num at hm
  linarith

theorem J_identity :
    centeredJ=C (centeredJ.coeff 0)+C (centeredJ.coeff 1)*X+
      C (centeredJ.coeff 2)*X^2+C (centeredJ.coeff 3)*X^3+
      C (centeredJ.coeff 4)*X^4+C (centeredJ.coeff 5)*X^5+tail centeredJ 6 145 := by
  have hf := r67_cJ_facts
  have hd := r67_natDegree_lt r67_cJ_rep hf.1 hf.2.1 (by norm_num)
  conv_lhs => rw [r67_split centeredJ 6 145 hd]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]

theorem J_coefficients :
    (1589/250000:ℚ)<centeredJ.coeff 0 ∧ |centeredJ.coeff 1|<(361/200000:ℚ) ∧
    (23599/100000:ℚ)<centeredJ.coeff 2 ∧
    (19703/100000:ℚ)<centeredJ.coeff 3 ∧ centeredJ.coeff 3<(2463/12500:ℚ) ∧
    (-85627/100000:ℚ)<centeredJ.coeff 4 ∧
    (-144289/100000:ℚ)<centeredJ.coeff 5 ∧ centeredJ.coeff 5<0 ∧
    jTailNorm<(3033/125000:ℚ) := by
  obtain ⟨hs,-,h0,h1,h2,h3,h3',h4,h5,h5',ht⟩ := r67_cJ_facts
  have c0 := r67_coeff_gt r67_cJ_rep hs 0 (a:=1589) (b:=250000) (by norm_num) h0
  have c1 := r67_coeff_abs_lt r67_cJ_rep hs 1 (a:=361) (b:=200000) (by norm_num) h1
  have c2 := r67_coeff_gt r67_cJ_rep hs 2 (a:=23599) (b:=100000) (by norm_num) h2
  have c3 := r67_coeff_gt r67_cJ_rep hs 3 (a:=19703) (b:=100000) (by norm_num) h3
  have c3' := r67_coeff_lt r67_cJ_rep hs 3 (a:=2463) (b:=12500) (by norm_num) h3'
  have c4 := r67_coeff_gt r67_cJ_rep hs 4 (a:=-85627) (b:=100000) (by norm_num) h4
  have c5 := r67_coeff_gt r67_cJ_rep hs 5 (a:=-144289) (b:=100000) (by norm_num) h5
  have c5' := r67_coeff_lt r67_cJ_rep hs 5 (a:=0) (b:=1) (by norm_num) h5'
  have hw := r67_wsum_eq r67_cJ_rep hs 6 4 145 7 20 (by norm_num)
  have hs' : (0:ℚ)<r67_cJ.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have htail : jTailNorm<(3033/125000:ℚ) := by
    have he : jTailNorm=∑ j : Fin 145,|centeredJ.coeff (j.val+6)| *((7:ℕ)/(20:ℕ):ℚ)^(j.val+4) := by
      simp only [jTailNorm,Nat.cast_ofNat]
    rw [he,hw,div_lt_div_iff₀ (by positivity) (by norm_num)]
    have ht' := (Int.cast_lt (R:=ℚ)).mpr ht
    push_cast at ht' ⊢
    linarith
  norm_num at c0 c1 c2 c3 c3' c4 c5 c5'
  exact ⟨c0,c1,c2,c3,c3',by rw [neg_div]; exact c4,by rw [neg_div]; exact c5,c5',htail⟩

theorem J_tail_lower {u : ℝ} (hu : |u|≤(7/20:ℝ)) :
    -(jTailNorm:ℝ)*u^2≤aeval u (tail centeredJ 6 145) := by
  have hterm (i : Fin 145) :
      -|(centeredJ.coeff (i.val+6):ℝ)| *(7/20:ℝ)^(i.val+4)*u^2≤
        (centeredJ.coeff (i.val+6):ℝ)*u^(i.val+6) := by
    have hp : |u^(i.val+4)|≤(7/20:ℝ)^(i.val+4) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg u) hu _
    have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (centeredJ.coeff (i.val+6):ℝ))
    rw [←abs_mul] at hm
    have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hm).1 (sq_nonneg u)
    have he : (centeredJ.coeff (i.val+6):ℝ)*u^(i.val+6)=
        ((centeredJ.coeff (i.val+6):ℝ)*u^(i.val+4))*u^2 := by
      rw [show i.val+6=(i.val+4)+2 by omega,pow_add]
      ring
    rw [he]
    linarith
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hterm i)
  simp only [tail,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  have he : (jTailNorm:ℝ)=∑i:Fin 145,|(centeredJ.coeff (i.val+6):ℝ)| *(7/20:ℝ)^(i.val+4) := by
    simp [jTailNorm]
  rw [he]
  simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using hh

theorem J_positive {x : ℝ} (hx : x∈Icc 0 frameCap) :
    (3167/500000:ℝ)<aeval x J := by
  let u := x-7/20
  have hu : |u|≤(7/20:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hx.1],by norm_num [frameCap] at hx; linarith [hx.2]⟩
  have hu2 : u^2≤(7/20:ℝ)^2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hc :
      (1589/250000:ℝ)<(centeredJ.coeff 0:ℝ) ∧ |(centeredJ.coeff 1:ℝ)|<(361/200000:ℝ) ∧
      (23599/100000:ℝ)<(centeredJ.coeff 2:ℝ) ∧
      (19703/100000:ℝ)<(centeredJ.coeff 3:ℝ) ∧ (centeredJ.coeff 3:ℝ)<(2463/12500:ℝ) ∧
      (-85627/100000:ℝ)<(centeredJ.coeff 4:ℝ) ∧
      (-144289/100000:ℝ)<(centeredJ.coeff 5:ℝ) ∧ (centeredJ.coeff 5:ℝ)<0 ∧
      (jTailNorm:ℝ)<(3033/125000:ℝ) := by
    obtain ⟨p0,p1,p2,p3,p3',p4,p5,p5',pt⟩ := J_coefficients
    have q0 := (Rat.cast_lt (K:=ℝ)).mpr p0
    have q1 := (Rat.cast_lt (K:=ℝ)).mpr p1
    have q2 := (Rat.cast_lt (K:=ℝ)).mpr p2
    have q3 := (Rat.cast_lt (K:=ℝ)).mpr p3
    have q3' := (Rat.cast_lt (K:=ℝ)).mpr p3'
    have q4 := (Rat.cast_lt (K:=ℝ)).mpr p4
    have q5 := (Rat.cast_lt (K:=ℝ)).mpr p5
    have q5' := (Rat.cast_lt (K:=ℝ)).mpr p5'
    have qt := (Rat.cast_lt (K:=ℝ)).mpr pt
    push_cast at q0 q1 q2 q3 q3' q4 q5 q5' qt
    exact ⟨q0,q1,q2,q3,q3',q4,q5,q5',qt⟩
  have hbracket : 0≤(centeredJ.coeff 3:ℝ)+(centeredJ.coeff 5:ℝ)*u^2 ∧
      (centeredJ.coeff 3:ℝ)+(centeredJ.coeff 5:ℝ)*u^2≤2463/12500 := by
    have hl := mul_le_mul_of_nonneg_right hc.2.2.2.2.2.2.1.le (sq_nonneg u)
    have hh := mul_nonpos_of_nonpos_of_nonneg hc.2.2.2.2.2.2.2.1.le (sq_nonneg u)
    have hs := mul_le_mul_of_nonneg_left hu2 (show (0:ℝ)≤144289/100000 by norm_num)
    exact ⟨by linarith [hc.2.2.2.1],by linarith [hc.2.2.2.2.1]⟩
  have hodd : -(2463/12500:ℝ)*(7/20)≤
      ((centeredJ.coeff 3:ℝ)+(centeredJ.coeff 5:ℝ)*u^2)*u := by
    have hl := mul_le_mul_of_nonneg_left (abs_le.mp hu).1 hbracket.1
    have hh := mul_le_mul_of_nonpos_right hbracket.2 (show -(7/20:ℝ)≤0 by norm_num)
    linarith
  have heven : -(85627/100000:ℝ)*(7/20)^2≤(centeredJ.coeff 4:ℝ)*u^2 := by
    have hl := mul_le_mul_of_nonneg_right hc.2.2.2.2.2.1.le (sq_nonneg u)
    linarith
  have hquadratic : (3786/100000:ℝ)≤(centeredJ.coeff 2:ℝ)+
      (centeredJ.coeff 3:ℝ)*u+(centeredJ.coeff 4:ℝ)*u^2+
      (centeredJ.coeff 5:ℝ)*u^3-(jTailNorm:ℝ) := by
    linarith [hc.2.2.1,hc.2.2.2.2.2.2.2.2]
  have hq := mul_le_mul_of_nonneg_right hquadratic (sq_nonneg u)
  have hl : -(361/200000:ℝ)*|u|≤(centeredJ.coeff 1:ℝ)*u := by
    have ht := mul_le_mul_of_nonneg_right hc.2.1.le (abs_nonneg u)
    rw [←abs_mul] at ht
    rw [neg_mul]
    exact (abs_le.mp ht).1
  have ht := J_tail_lower hu
  have hi := congrArg (fun p : ℚ[X] => aeval u p) J_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hi
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(1589/250000:ℝ))
    (b:=-(361/200000:ℝ)) (x:=|u|) (show (0:ℝ)<3786/100000 by norm_num)
  rw [sq_abs] at hm
  norm_num at hm
  have hid : aeval u centeredJ=aeval x J := by simp [centeredJ,u]
  rw [hid] at hi
  linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain.Certificate
end
end
end
