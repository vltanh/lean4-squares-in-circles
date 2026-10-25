module

public import SquaresInCircles.Eight.Frames.High.LowSecondNormPolynomial
public import SquaresInCircles.Eight.Frames.Mid.HighTargetReferences

/-!
# Eight squares: exact fixed-endpoint bounds for high/high

Every reference substitutes the actual two intrinsic endpoints and the
same circle radius.  The circle-source norm is bounded by squaring the
positive reserve of the linear part.  No tabulated norm value is needed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighFixedReferences
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameHighHighFixedCalculus
open StationaryPrimitives (Interval)
open FrameMidHighVaryingReferences (rBox sinBox cosBox)

def a0Box : Interval FrameDiagonalArc.a0 := Interval.of_bounds ⟨a0_precise.1.le,a0_precise.2.le⟩
def endpointABox (cut : Bool) : Interval (endA cut) := by
  cases cut
  · exact a0Box
  · exact FrameMidHighTargetReferences.aBox
def endpointBBox (cut : Bool) : Interval (endB cut) := by
  cases cut
  · exact Interval.point 0
  · exact FrameMidHighTargetReferences.bBox
def labelBox (cut : Bool) : Interval (H (endB cut)) := by
  rw [H,endpoint_A]
  exact ((Interval.point u).mul ((endpointABox cut).sub a0Box)).add
    ((Interval.point v).mul (endpointBBox cut))
def sourceBox (circle i : Bool) (l : ℝ) : Interval (sourceBase circle i l) := by
  cases circle
  · exact (Interval.point (sourceU i l)).mul a0Box
  · exact Interval.point (-sourceU i l)
def constantBox (circle i j cut : Bool) (l : ℝ) :
    Interval (constantBase circle i j cut l) :=
  ((((Interval.point (9/100+l)).sub ((Interval.point (sign i*u)).mul a0Box)).sub ((Interval.point (sign j)).mul (labelBox cut))).add (sourceBox circle i l))
def cBox (j cut : Bool) (l : ℝ) : Interval (Cc j cut l) :=
  ((Interval.point l).mul (((Interval.point 1).add (endpointABox cut)).add ((Interval.point (sign j)).mul (endpointBBox cut)))).sub (Interval.point (9/100))
def sBox (j cut : Bool) (l : ℝ) : Interval (Ss j cut l) :=
  ((Interval.point l).mul (((Interval.point 1).sub (endpointABox cut)).add ((Interval.point (sign j)).mul (endpointBBox cut)))).sub (Interval.point (9/100))
def baseBox (circle i j cut : Bool) (l : ℝ) {x : ℝ} (hx : 0≤x) :
    Interval (x+constantBase circle i j cut l+Cc j cut l*Real.cos x+Ss j cut l*Real.sin x) :=
  ((((Interval.point x).add (constantBox circle i j cut l)).add ((cBox j cut l).mul (cosBox hx))).add ((sBox j cut l).mul (sinBox hx)))
def derivativeBox (j cut : Bool) (l : ℝ) {x : ℝ} (hx : 0≤x) : Interval (Fd j cut l x) :=
  (((Interval.point 1).sub ((cBox j cut l).mul (sinBox hx))).add ((sBox j cut l).mul (cosBox hx)))

theorem reference_lower (circle i j cut : Bool) (l : ℝ) {x : ℝ} (hx : 0≤x)
    (hreserve : gamma<(baseBox circle i j cut l hx).lo)
    (hsquare : sourceEnergy circle i l<
      (((baseBox circle i j cut l hx).lo-gamma)/(139921407/50000000:ℝ))^2) :
    gamma<F circle i j cut l x := by
  let B := baseBox circle i j cut l hx
  let cap : ℝ := (B.lo-gamma)/(139921407/50000000:ℝ)
  have hcap : 0<cap := div_pos (sub_pos.mpr hreserve) (by norm_num)
  have hn := sourceNorm_nonneg circle i l
  have hs := sourceNorm_sq circle i l
  have hsq : (sourceNorm circle i l)^2<cap^2 := by rw [hs]; exact hsquare
  have hnorm : sourceNorm circle i l<cap := lt_of_pow_lt_pow_left₀ 2 hcap.le hsq
  have hprod : R*sourceNorm circle i l<(139921407/50000000:ℝ)*cap :=
    (mul_lt_mul_of_pos_left hnorm R_pos).trans (mul_lt_mul_of_pos_right R_precise.2 hcap)
  have heq : (139921407/50000000:ℝ)*cap=B.lo-gamma := by dsimp [cap]; ring
  rw [heq] at hprod
  dsimp [F]
  linarith [B.mem.1]

private lemma r55_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r55_mpr_hi {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).hi=S.hi := by subst e; rfl

private lemma r55_bBox_lo : FrameMidHighTargetReferences.bBox.lo=
    ((Interval.point (2/5:ℝ)).mul FrameMidHighTargetReferences.aBox).lo :=
  r55_mpr_lo b1_eq _ _
private lemma r55_bBox_hi : FrameMidHighTargetReferences.bBox.hi=
    ((Interval.point (2/5:ℝ)).mul FrameMidHighTargetReferences.aBox).hi :=
  r55_mpr_hi b1_eq _ _

private lemma r55_eA_lo_t : (endpointABox true).lo=FrameMidHighTargetReferences.aBox.lo := rfl
private lemma r55_eA_hi_t : (endpointABox true).hi=FrameMidHighTargetReferences.aBox.hi := rfl
private lemma r55_eA_lo_f : (endpointABox false).lo=a0Box.lo := rfl
private lemma r55_eA_hi_f : (endpointABox false).hi=a0Box.hi := rfl
private lemma r55_eB_lo_t : (endpointBBox true).lo=FrameMidHighTargetReferences.bBox.lo := rfl
private lemma r55_eB_hi_t : (endpointBBox true).hi=FrameMidHighTargetReferences.bBox.hi := rfl
private lemma r55_eB_lo_f : (endpointBBox false).lo=0 := rfl
private lemma r55_eB_hi_f : (endpointBBox false).hi=0 := rfl

private lemma r55_labelBox_lo (cut : Bool) : (labelBox cut).lo=
    (((Interval.point u).mul ((endpointABox cut).sub a0Box)).add
      ((Interval.point v).mul (endpointBBox cut))).lo := by
  unfold labelBox
  rw [r55_mpr_lo,r55_mpr_lo]
  · rw [endpoint_A]
  · rw [H]
private lemma r55_labelBox_hi (cut : Bool) : (labelBox cut).hi=
    (((Interval.point u).mul ((endpointABox cut).sub a0Box)).add
      ((Interval.point v).mul (endpointBBox cut))).hi := by
  unfold labelBox
  rw [r55_mpr_hi,r55_mpr_hi]
  · rw [endpoint_A]
  · rw [H]

local macro "hh_fixed_arithmetic" : tactic => `(tactic|
  norm_num [baseBox,derivativeBox,constantBox,sourceBox,cBox,sBox,r55_labelBox_lo,
    r55_labelBox_hi,r55_eA_lo_t,r55_eA_hi_t,r55_eA_lo_f,r55_eA_hi_f,r55_eB_lo_t,r55_eB_hi_t,
    r55_eB_lo_f,r55_eB_hi_f,a0Box,FrameMidHighTargetReferences.aBox,
    r55_bBox_lo,r55_bBox_hi,rBox,sinBox,cosBox,sourceEnergy,sourceU,sourceV,
    gamma,sign,u,v,Interval.point,Interval.of_bounds,Interval.add,Interval.sub,
    Interval.neg,Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,
    Arithmetic.cos10,Arithmetic.cos8])

theorem positive_left (cut : Bool) : gamma<F false true true cut (39/100) (7/20) := by
  apply reference_lower false true true cut (39/100) (by norm_num)
  all_goals cases cut <;> hh_fixed_arithmetic

theorem positive_right (cut : Bool) : gamma<F false true true cut (39/100) (6/5) := by
  apply reference_lower false true true cut (39/100) (by norm_num)
  all_goals cases cut <;> hh_fixed_arithmetic

theorem plus_minus_first_left : gamma<F true true false true (11/20) (7/20) := by
  apply reference_lower true true false true (11/20) (by norm_num) <;> hh_fixed_arithmetic

theorem plus_minus_first_right : gamma<F true true false true (11/20) (3/5) := by
  apply reference_lower true true false true (11/20) (by norm_num) <;> hh_fixed_arithmetic

theorem plus_minus_middle_left : gamma<F false true false true (43/100) (3/5) := by
  apply reference_lower false true false true (43/100) (by norm_num) <;> hh_fixed_arithmetic

theorem plus_minus_middle_right : gamma<F false true false true (43/100) (4/5) := by
  apply reference_lower false true false true (43/100) (by norm_num) <;> hh_fixed_arithmetic

theorem plus_minus_last_left (cut : Bool) : gamma<F false true false cut (17/50) (4/5) := by
  apply reference_lower false true false cut (17/50) (by norm_num)
  all_goals cases cut <;> hh_fixed_arithmetic

theorem minus_minus_last_left (cut : Bool) : gamma<F true false false cut (17/50) (19/20) := by
  apply reference_lower true false false cut (17/50) (by norm_num)
  all_goals cases cut <;> hh_fixed_arithmetic

theorem minus_plus_first_left : gamma<F true false true false (2/5) 1 := by
  apply reference_lower true false true false (2/5) (by norm_num) <;> hh_fixed_arithmetic

theorem minus_plus_first_right : gamma<F true false true false (2/5) (13/10) := by
  apply reference_lower true false true false (2/5) (by norm_num) <;> hh_fixed_arithmetic

theorem positive_coefficients (cut : Bool) :
    0<Cc true cut (39/100) ∧ Ss true cut (39/100)<0 := by
  have hc := (cBox true cut (39/100)).mem
  have hs := (sBox true cut (39/100)).mem
  have hcl : 0<(cBox true cut (39/100)).lo := by cases cut <;> hh_fixed_arithmetic
  have hsu : (sBox true cut (39/100)).hi<0 := by cases cut <;> hh_fixed_arithmetic
  exact ⟨hcl.trans_le hc.1,hs.2.trans_lt hsu⟩

theorem plus_minus_first_coefficients :
    0<Cc false true (11/20) ∧ Ss false true (11/20)<0 := by
  have hc := (cBox false true (11/20)).mem
  have hs := (sBox false true (11/20)).mem
  have hcl : 0<(cBox false true (11/20)).lo := by hh_fixed_arithmetic
  have hsu : (sBox false true (11/20)).hi<0 := by hh_fixed_arithmetic
  exact ⟨hcl.trans_le hc.1,hs.2.trans_lt hsu⟩

theorem plus_minus_middle_coefficients :
    0<Cc false true (43/100) ∧ Ss false true (43/100)<0 := by
  have hc := (cBox false true (43/100)).mem
  have hs := (sBox false true (43/100)).mem
  have hcl : 0<(cBox false true (43/100)).lo := by hh_fixed_arithmetic
  have hsu : (sBox false true (43/100)).hi<0 := by hh_fixed_arithmetic
  exact ⟨hcl.trans_le hc.1,hs.2.trans_lt hsu⟩

theorem minus_plus_first_coefficients :
    0<Cc true false (2/5) ∧ Ss true false (2/5)<0 := by
  have hc := (cBox true false (2/5)).mem
  have hs := (sBox true false (2/5)).mem
  have hcl : 0<(cBox true false (2/5)).lo := by hh_fixed_arithmetic
  have hsu : (sBox true false (2/5)).hi<0 := by hh_fixed_arithmetic
  exact ⟨hcl.trans_le hc.1,hs.2.trans_lt hsu⟩

theorem positive_last_slope (cut : Bool) : Fd true cut (39/100) (6/5)<0 := by
  have hh := (derivativeBox true cut (39/100) (show (0:ℝ)≤6/5 by norm_num)).mem.2
  have hu : (derivativeBox true cut (39/100) (show (0:ℝ)≤6/5 by norm_num)).hi<0 := by
    cases cut <;> hh_fixed_arithmetic
  exact hh.trans_lt hu

theorem plus_minus_first_slope : Fd false true (11/20) (3/5)<0 := by
  have hh := (derivativeBox false true (11/20) (show (0:ℝ)≤3/5 by norm_num)).mem.2
  have hu : (derivativeBox false true (11/20) (show (0:ℝ)≤3/5 by norm_num)).hi<0 := by
    hh_fixed_arithmetic
  exact hh.trans_lt hu

theorem plus_minus_middle_slope : Fd false true (43/100) (4/5)<0 := by
  have hh := (derivativeBox false true (43/100) (show (0:ℝ)≤4/5 by norm_num)).mem.2
  have hu : (derivativeBox false true (43/100) (show (0:ℝ)≤4/5 by norm_num)).hi<0 := by
    hh_fixed_arithmetic
  exact hh.trans_lt hu

theorem minus_plus_first_slope : Fd true false (2/5) (13/10)<0 := by
  have hh := (derivativeBox true false (2/5) (show (0:ℝ)≤13/10 by norm_num)).mem.2
  have hu : (derivativeBox true false (2/5) (show (0:ℝ)≤13/10 by norm_num)).hi<0 := by
    hh_fixed_arithmetic
  exact hh.trans_lt hu

end SquaresInCircles.Eight.FrameHighHighFixedReferences
