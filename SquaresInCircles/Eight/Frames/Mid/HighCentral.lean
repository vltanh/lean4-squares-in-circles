module

public import SquaresInCircles.Eight.Frames.Diagonal.Tails
public import SquaresInCircles.Eight.Frames.Mid.HighVaryingCalculus
public import SquaresInCircles.Eight.Frames.Mid.HighQuarterStrip
public import SquaresInCircles.Eight.Frames.Mid.HighSupportForms
public import SquaresInCircles.Eight.Frames.Mid.HighTargetReferences

/-!
# Eight squares: all actual middle/high central witnesses

The source and target are the original circle points.  The initial
barriers, exact supports, quarter-strip contact, and complete angular
tails cover every nonnegative folded angle and every tangent sign.
-/

section
/-!
## Fixed references for the remaining middle/high supports

The enclosing intervals are attached to the actual endpoint coordinates,
marker constants and trigonometric values.  Circle-source references
compare the exact squared norm with the positive remaining reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighFixedReferences
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameMidHighFixedCalculus
open StationaryPrimitives (Interval)
open FrameMidHighVaryingReferences (rBox piBox sinBox cosBox)
open FrameMidHighTargetReferences (quarter quarterX quarterS quarterC)

def a0Box : Interval FrameDiagonalArc.a0 := Interval.of_bounds ⟨a0_precise.1.le,a0_precise.2.le⟩
def firstABox : Interval (A b1) := by rw [A_b1]; exact FrameMidHighTargetReferences.aBox
def firstBBox : Interval b1 := FrameMidHighTargetReferences.bBox
def lastABox : Interval (A b2) := by rw [A_b2]; exact FrameMidHighVaryingReferences.aBox
def lastBBox : Interval b2 := FrameMidHighVaryingReferences.bBox
def zeroABox : Interval (A 0) := by rw [A_zero]; exact a0Box
def targetABox (cut : Bool) : Interval (A (targetB cut)) := by
  cases cut
  · exact firstABox
  · exact lastABox
def targetBBox (cut : Bool) : Interval (targetB cut) := by
  cases cut
  · exact firstBBox
  · exact lastBBox

def constantBox (m : Bool) : Interval (constant m) := by
  cases m
  · exact (Interval.point (-u)).mul a0Box
  · exact (piBox.div (Interval.point 4) (by norm_num [Interval.point])).add (Interval.point (85723/40000))
def markerBox (n : Bool) {B : ℝ} (AB : Interval (A B)) (BB : Interval B) :
    Interval (marker n B) := by
  rw [marker_affine]
  exact ((constantBox n).add ((Interval.point (primary n)).mul AB)).add ((Interval.point (transverse n)).mul BB)
def cBox (before j : Bool) (l : ℝ) {B : ℝ} (AB : Interval (A B)) (BB : Interval B) :
    Interval (Cc before j l B) := by
  cases before
  · exact ((Interval.point l).mul ((AB.add ((Interval.point (sign j)).mul BB)).sub (Interval.point 1))).add (Interval.point (9/100))
  · exact ((Interval.point l).mul (((Interval.point 1).add AB).add ((Interval.point (sign j)).mul BB))).sub (Interval.point (9/100))
def sBox (j : Bool) (l : ℝ) {B : ℝ} (AB : Interval (A B)) (BB : Interval B) :
    Interval (Ss j l B) :=
  ((Interval.point l).mul (((Interval.point 1).sub AB).add ((Interval.point (sign j)).mul BB))).sub (Interval.point (9/100))
def kBox (m n i j : Bool) (l : ℝ) {S B : ℝ} (SB : Interval S)
    (AB : Interval (A B)) (BB : Interval B) : Interval (K m n i j l S B) :=
  ((((Interval.point (9/100+l)).add ((Interval.point (sign i)).mul (constantBox m))).sub ((Interval.point (sign j)).mul (markerBox n AB BB))).add SB)
def baseBox (before m n i j : Bool) (l : ℝ) {S B x : ℝ}
    (SB : Interval S) (AB : Interval (A B)) (BB : Interval B)
    (XB : Interval x) (Sin : Interval (Real.sin x)) (Cos : Interval (Real.cos x)) :
    Interval (F before m n i j l S B x) :=
  (((XB.add (kBox m n i j l SB AB BB)).add ((cBox before j l AB BB).mul Cos)).add ((sBox j l AB BB).mul Sin))
def derivativeBox (before j : Bool) (l : ℝ) {B x : ℝ}
    (AB : Interval (A B)) (BB : Interval B)
    (Sin : Interval (Real.sin x)) (Cos : Interval (Real.cos x)) :
    Interval (Fd before j l B x) :=
  (((Interval.point 1).sub ((cBox before j l AB BB).mul Sin)).add ((sBox j l AB BB).mul Cos))

def middleSourceBox : Interval middleSource := by
  have hh := ((Interval.point (k-2/5)).mul FrameMidHighTargetReferences.aBox).add ((Interval.point (2/5-q)).mul firstBBox)
  convert hh using 1
  dsimp [middleSource,FrameDiagonalSupport.source,FrameDiagonalSupport.sourceU,
    FrameDiagonalSupport.sourceV,linear,primary,transverse,sign]
  rw [A_b1]
  ring

private theorem r56_mpr_ends {x y : ℝ} (hxy : x=y) (h : Interval x=Interval y)
    (X : Interval y) : (h.mpr X).lo=X.lo ∧ (h.mpr X).hi=X.hi := by
  subst hxy; exact ⟨rfl,rfl⟩

/-! Endpoints of the enclosures built with `rw`/`convert`. -/

private theorem r56_firstABox :
    firstABox.lo=FrameMidHighTargetReferences.aBox.lo ∧
      firstABox.hi=FrameMidHighTargetReferences.aBox.hi := by
  unfold firstABox; exact r56_mpr_ends A_b1 _ _
private theorem r56_lastABox :
    lastABox.lo=FrameMidHighVaryingReferences.aBox.lo ∧
      lastABox.hi=FrameMidHighVaryingReferences.aBox.hi := by
  unfold lastABox; exact r56_mpr_ends A_b2 _ _
private theorem r56_zeroABox : zeroABox.lo=a0Box.lo ∧ zeroABox.hi=a0Box.hi := by
  unfold zeroABox; exact r56_mpr_ends A_zero _ _
private theorem r56_targetBBox :
    FrameMidHighTargetReferences.bBox.lo=
        ((Interval.point (2/5:ℝ)).mul FrameMidHighTargetReferences.aBox).lo ∧
      FrameMidHighTargetReferences.bBox.hi=
        ((Interval.point (2/5:ℝ)).mul FrameMidHighTargetReferences.aBox).hi := by
  unfold FrameMidHighTargetReferences.bBox; exact r56_mpr_ends b1_eq _ _
private theorem r56_varyingBBox :
    FrameMidHighVaryingReferences.bBox.lo=
        ((Interval.point (3/5:ℝ)).mul FrameMidHighVaryingReferences.aBox).lo ∧
      FrameMidHighVaryingReferences.bBox.hi=
        ((Interval.point (3/5:ℝ)).mul FrameMidHighVaryingReferences.aBox).hi := by
  unfold FrameMidHighVaryingReferences.bBox; exact r56_mpr_ends b2_eq _ _
private theorem r56_markerBox (n : Bool) {B : ℝ} (AB : Interval (A B)) (BB : Interval B) :
    (markerBox n AB BB).lo=(((constantBox n).add ((Interval.point (primary n)).mul AB)).add
        ((Interval.point (transverse n)).mul BB)).lo ∧
      (markerBox n AB BB).hi=(((constantBox n).add ((Interval.point (primary n)).mul AB)).add
        ((Interval.point (transverse n)).mul BB)).hi := by
  unfold markerBox; exact r56_mpr_ends (marker_affine n B) _ _
private theorem r56_middleSource : middleSource=(k-2/5)*a1+(2/5-q)*b1 := by
  dsimp [middleSource,FrameDiagonalSupport.source,FrameDiagonalSupport.sourceU,
    FrameDiagonalSupport.sourceV,linear,primary,transverse,sign]
  rw [A_b1]
  ring
private theorem r56_middleSourceBox :
    middleSourceBox.lo=(((Interval.point (k-2/5)).mul FrameMidHighTargetReferences.aBox).add
        ((Interval.point (2/5-q)).mul firstBBox)).lo ∧
      middleSourceBox.hi=(((Interval.point (k-2/5)).mul FrameMidHighTargetReferences.aBox).add
        ((Interval.point (2/5-q)).mul firstBBox)).hi := by
  unfold middleSourceBox; exact r56_mpr_ends r56_middleSource _ _
private theorem r56_quarterS (after : Bool) :
    (quarterS after).lo=(cosBox (show (0:ℝ)≤1/50 by norm_num)).lo ∧
      (quarterS after).hi=(cosBox (show (0:ℝ)≤1/50 by norm_num)).hi := by
  unfold quarterS
  exact r56_mpr_ends (FrameMidHighTargetReferences.quarter_trig after).1 _ _
private theorem r56_quarterC (after : Bool) :
    (quarterC after).lo=((Interval.point (-sign after)).mul
        (sinBox (show (0:ℝ)≤1/50 by norm_num))).lo ∧
      (quarterC after).hi=((Interval.point (-sign after)).mul
        (sinBox (show (0:ℝ)≤1/50 by norm_num))).hi := by
  unfold quarterC
  exact r56_mpr_ends (FrameMidHighTargetReferences.quarter_trig after).2 _ _

theorem circle_reference (before m n i j : Bool) (l : ℝ) {B x : ℝ}
    (AB : Interval (A B)) (BB : Interval B)
    (XB : Interval x) (Sin : Interval (Real.sin x)) (Cos : Interval (Real.cos x))
    (hreserve : gamma<(baseBox before m n i j l
      (Interval.point (-FrameDiagonalSupport.sourceU m i l)) AB BB XB Sin Cos).lo)
    (hsquare : (FrameDiagonalSupport.sourceU m i l)^2+(FrameDiagonalSupport.sourceV m i l)^2<
      (((baseBox before m n i j l (Interval.point (-FrameDiagonalSupport.sourceU m i l))
        AB BB XB Sin Cos).lo-gamma)/(139921407/50000000:ℝ))^2) :
    gamma<F before m n i j l (FrameDiagonalSupport.sourceCircle m i l) B x := by
  let Z := Real.sqrt ((FrameDiagonalSupport.sourceU m i l)^2+(FrameDiagonalSupport.sourceV m i l)^2)
  let E := baseBox before m n i j l (Interval.point (-FrameDiagonalSupport.sourceU m i l))
    AB BB XB Sin Cos
  let cap : ℝ := (E.lo-gamma)/(139921407/50000000:ℝ)
  have hcap : 0<cap := div_pos (sub_pos.mpr hreserve) (by norm_num)
  have hz : 0≤Z := Real.sqrt_nonneg _
  have hz2 : Z^2=(FrameDiagonalSupport.sourceU m i l)^2+(FrameDiagonalSupport.sourceV m i l)^2 :=
    Real.sq_sqrt (by positivity)
  have hsq : Z^2<cap^2 := by rw [hz2]; exact hsquare
  have hnorm : Z<cap := lt_of_pow_lt_pow_left₀ 2 hcap.le hsq
  have hprod : R*Z<(139921407/50000000:ℝ)*cap :=
    (mul_lt_mul_of_pos_left hnorm R_pos).trans (mul_lt_mul_of_pos_right R_precise.2 hcap)
  have heq : (139921407/50000000:ℝ)*cap=E.lo-gamma := by dsimp [cap]; ring
  rw [heq] at hprod
  have hidentity : F before m n i j l (FrameDiagonalSupport.sourceCircle m i l) B x=
      F before m n i j l (-FrameDiagonalSupport.sourceU m i l) B x-R*Z := by
    dsimp [F,K,FrameDiagonalSupport.sourceCircle,Z]
    ring
  rw [hidentity]
  linarith [E.mem.1]

local macro "mh_fixed_arithmetic" : tactic => `(tactic|
  norm_num [baseBox,derivativeBox,kBox,constantBox,r56_markerBox,cBox,sBox,r56_middleSourceBox,
    targetABox,targetBBox,r56_firstABox,firstBBox,r56_lastABox,lastBBox,r56_zeroABox,a0Box,
    FrameMidHighTargetReferences.aBox,r56_targetBBox,
    FrameMidHighVaryingReferences.aBox,r56_varyingBBox,r56_quarterS,r56_quarterC,
    rBox,piBox,sinBox,cosBox,quarterX,
    FrameDiagonalSupport.sourceU,FrameDiagonalSupport.sourceV,
    gamma,sign,u,v,k,q,primary,transverse,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.div,Interval.inv,Interval.square,
    HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8])

theorem mh_plus_minus_left : gamma< mhPlusMinus (1/10) := by
  apply circle_reference true true false true false (11/20) firstABox firstBBox
    (Interval.point (1/10)) (sinBox (show (0:ℝ)≤1/10 by norm_num))
    (cosBox (show (0:ℝ)≤1/10 by norm_num)) <;> mh_fixed_arithmetic

theorem mh_plus_minus_right : gamma< mhPlusMinus (61/100) := by
  apply circle_reference true true false true false (11/20) firstABox firstBBox
    (Interval.point (61/100)) (sinBox (show (0:ℝ)≤61/100 by norm_num))
    (cosBox (show (0:ℝ)≤61/100 by norm_num)) <;> mh_fixed_arithmetic

theorem mh_negative_left : gamma< mhNegative (9/10) := by
  let B := baseBox true true false false false (2/5) middleSourceBox firstABox firstBBox
    (Interval.point (9/10)) (sinBox (show (0:ℝ)≤9/10 by norm_num))
    (cosBox (show (0:ℝ)≤9/10 by norm_num))
  have hh : gamma<B.lo := by dsimp [B]; mh_fixed_arithmetic
  exact hh.trans_le B.mem.1

theorem mh_opposite_left : gamma< mhOpposite (6/5) := by
  let B := baseBox true true false false true (2/5) middleSourceBox zeroABox (Interval.point 0)
    (Interval.point (6/5)) (sinBox (show (0:ℝ)≤6/5 by norm_num))
    (cosBox (show (0:ℝ)≤6/5 by norm_num))
  have hh : gamma<B.lo := by dsimp [B]; mh_fixed_arithmetic
  exact hh.trans_le B.mem.1

theorem mh_opposite_right : gamma< mhOpposite (13/10) := by
  let B := baseBox true true false false true (2/5) middleSourceBox zeroABox (Interval.point 0)
    (Interval.point (13/10)) (sinBox (show (0:ℝ)≤13/10 by norm_num))
    (cosBox (show (0:ℝ)≤13/10 by norm_num))
  have hh : gamma<B.lo := by dsimp [B]; mh_fixed_arithmetic
  exact hh.trans_le B.mem.1

theorem hm_positive_left : gamma<hmPositive (11/10) := by
  apply circle_reference true false true true true (1/2) firstABox firstBBox
    (Interval.point (11/10)) (sinBox (show (0:ℝ)≤11/10 by norm_num))
    (cosBox (show (0:ℝ)≤11/10 by norm_num)) <;> mh_fixed_arithmetic

theorem hm_positive_right : gamma<hmPositive (71/50) := by
  apply circle_reference true false true true true (1/2) firstABox firstBBox
    (Interval.point (71/50)) (sinBox (show (0:ℝ)≤71/50 by norm_num))
    (cosBox (show (0:ℝ)≤71/50 by norm_num)) <;> mh_fixed_arithmetic

theorem hm_opposite_left (cut : Bool) : gamma<hmOpposite true cut (13/10) := by
  cases cut
  · apply circle_reference true false true false true (2/5) firstABox firstBBox
      (Interval.point (13/10)) (sinBox (show (0:ℝ)≤13/10 by norm_num))
      (cosBox (show (0:ℝ)≤13/10 by norm_num)) <;> mh_fixed_arithmetic
  · apply circle_reference true false true false true (2/5) lastABox lastBBox
      (Interval.point (13/10)) (sinBox (show (0:ℝ)≤13/10 by norm_num))
      (cosBox (show (0:ℝ)≤13/10 by norm_num)) <;> mh_fixed_arithmetic

theorem hm_opposite_before_quarter (cut : Bool) :
    gamma<hmOpposite true cut (Real.pi/2-1/50) := by
  have e : quarter false=Real.pi/2-1/50 := by
    simp only [quarter,sign,Bool.false_eq_true,↓reduceIte]; ring
  rw [← e]
  cases cut
  · apply circle_reference true false true false true (2/5) firstABox firstBBox
      (quarterX false) (quarterS false) (quarterC false) <;> mh_fixed_arithmetic
  · apply circle_reference true false true false true (2/5) lastABox lastBBox
      (quarterX false) (quarterS false) (quarterC false) <;> mh_fixed_arithmetic

theorem hm_opposite_after_quarter (cut : Bool) :
    gamma<hmOpposite false cut (Real.pi/2+1/50) := by
  have e : quarter true=Real.pi/2+1/50 := by
    simp only [quarter,sign,↓reduceIte]
  rw [← e]
  cases cut
  · apply circle_reference false false true false true (2/5) firstABox firstBBox
      (quarterX true) (quarterS true) (quarterC true) <;> mh_fixed_arithmetic
  · apply circle_reference false false true false true (2/5) lastABox lastBBox
      (quarterX true) (quarterS true) (quarterC true) <;> mh_fixed_arithmetic

theorem mh_plus_minus_coefficients :
    0<Cc true false (11/20) b1 ∧ Ss false (11/20) b1<0 := by
  constructor
  · have hh := (cBox true false (11/20) firstABox firstBBox).mem.1
    have hl : 0<(cBox true false (11/20) firstABox firstBBox).lo := by mh_fixed_arithmetic
    exact hl.trans_le hh
  · have hh := (sBox false (11/20) firstABox firstBBox).mem.2
    have hu : (sBox false (11/20) firstABox firstBBox).hi<0 := by mh_fixed_arithmetic
    exact hh.trans_lt hu

theorem mh_opposite_coefficients :
    0<Cc true true (2/5) 0 ∧ Ss true (2/5) 0<0 := by
  constructor
  · have hh := (cBox true true (2/5) zeroABox (Interval.point 0)).mem.1
    have hl : 0<(cBox true true (2/5) zeroABox (Interval.point 0)).lo := by mh_fixed_arithmetic
    exact hl.trans_le hh
  · have hh := (sBox true (2/5) zeroABox (Interval.point 0)).mem.2
    have hu : (sBox true (2/5) zeroABox (Interval.point 0)).hi<0 := by mh_fixed_arithmetic
    exact hh.trans_lt hu

theorem hm_positive_coefficients :
    0<Cc true true (1/2) b1 ∧ Ss true (1/2) b1<0 := by
  constructor
  · have hh := (cBox true true (1/2) firstABox firstBBox).mem.1
    have hl : 0<(cBox true true (1/2) firstABox firstBBox).lo := by mh_fixed_arithmetic
    exact hl.trans_le hh
  · have hh := (sBox true (1/2) firstABox firstBBox).mem.2
    have hu : (sBox true (1/2) firstABox firstBBox).hi<0 := by mh_fixed_arithmetic
    exact hh.trans_lt hu

theorem hm_opposite_first_coefficients :
    0<Cc true true (2/5) b1 ∧ Ss true (2/5) b1<0 := by
  constructor
  · have hh := (cBox true true (2/5) firstABox firstBBox).mem.1
    have hl : 0<(cBox true true (2/5) firstABox firstBBox).lo := by mh_fixed_arithmetic
    exact hl.trans_le hh
  · have hh := (sBox true (2/5) firstABox firstBBox).mem.2
    have hu : (sBox true (2/5) firstABox firstBBox).hi<0 := by mh_fixed_arithmetic
    exact hh.trans_lt hu

theorem hm_opposite_last_coefficients :
    0<Cc true true (2/5) b2 ∧ 0<Ss true (2/5) b2 := by
  constructor
  · have hh := (cBox true true (2/5) lastABox lastBBox).mem.1
    have hl : 0<(cBox true true (2/5) lastABox lastBBox).lo := by mh_fixed_arithmetic
    exact hl.trans_le hh
  · have hh := (sBox true (2/5) lastABox lastBBox).mem.1
    have hl : 0<(sBox true (2/5) lastABox lastBBox).lo := by mh_fixed_arithmetic
    exact hl.trans_le hh

theorem mh_plus_minus_last_slope : Fd true false (11/20) b1 (61/100)<0 := by
  let D := derivativeBox true false (11/20) firstABox firstBBox
    (sinBox (show (0:ℝ)≤61/100 by norm_num)) (cosBox (show (0:ℝ)≤61/100 by norm_num))
  have hh : D.hi<0 := by dsimp [D]; mh_fixed_arithmetic
  exact D.mem.2.trans_lt hh

theorem mh_opposite_last_slope : Fd true true (2/5) 0 (13/10)<0 := by
  let D := derivativeBox true true (2/5) zeroABox (Interval.point 0)
    (sinBox (show (0:ℝ)≤13/10 by norm_num)) (cosBox (show (0:ℝ)≤13/10 by norm_num))
  have hh : D.hi<0 := by dsimp [D]; mh_fixed_arithmetic
  exact D.mem.2.trans_lt hh

theorem hm_positive_last_slope : Fd true true (1/2) b1 (71/50)<0 := by
  let D := derivativeBox true true (1/2) firstABox firstBBox
    (sinBox (show (0:ℝ)≤71/50 by norm_num)) (cosBox (show (0:ℝ)≤71/50 by norm_num))
  have hh : D.hi<0 := by dsimp [D]; mh_fixed_arithmetic
  exact D.mem.2.trans_lt hh

theorem hm_opposite_first_last_slope : Fd true true (2/5) b1 (Real.pi/2-1/50)<0 := by
  have hh : Fd true true (2/5) b1 (quarter false)<0 := by
    let D := derivativeBox true true (2/5) firstABox firstBBox (quarterS false) (quarterC false)
    have hu : D.hi<0 := by dsimp [D]; mh_fixed_arithmetic
    exact D.mem.2.trans_lt hu
  have e : quarter false=Real.pi/2-1/50 := by
    simp only [quarter,sign,Bool.false_eq_true,↓reduceIte]; ring
  rwa [← e]

theorem mh_negative_amplitude : (Cc true false (2/5) b1)^2+(Ss false (2/5) b1)^2<1 := by
  have hc := (cBox true false (2/5) firstABox firstBBox).square.mem.2
  have hs := (sBox false (2/5) firstABox firstBBox).square.mem.2
  have hh : (cBox true false (2/5) firstABox firstBBox).square.hi+
      (sBox false (2/5) firstABox firstBBox).square.hi<1 := by mh_fixed_arithmetic
  linarith

theorem hm_opposite_after_amplitude (cut : Bool) :
    (Cc false true (2/5) (targetB cut))^2+(Ss true (2/5) (targetB cut))^2<1 := by
  have hc := (cBox false true (2/5) (targetABox cut) (targetBBox cut)).square.mem.2
  have hs := (sBox true (2/5) (targetABox cut) (targetBBox cut)).square.mem.2
  have hh : (cBox false true (2/5) (targetABox cut) (targetBBox cut)).square.hi+
      (sBox true (2/5) (targetABox cut) (targetBBox cut)).square.hi<1 := by
    cases cut <;> mh_fixed_arithmetic
  linarith

end SquaresInCircles.Eight.FrameMidHighFixedReferences
end
end
end

section
/-!
## The remaining fixed-target middle/high support intervals

Each estimate belongs to the literal signed source and target support.
The first-quadrant intervals use endpoint minima or concavity, and the
two small-amplitude families are increasing on their entire real domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighFixedScalars
open FrameDiagonalArc FrameMidHighFixedCalculus FrameMidHighFixedReferences

theorem mh_plus_minus_lower {x : ℝ} (hx : x∈Icc (1/10:ℝ) (61/100)) :
    (4463/5000:ℝ)< mhPlusMinus x := by
  have hc := mh_plus_minus_coefficients
  have hm := endpoint_minimum true true false true false
    (S := FrameDiagonalSupport.sourceCircle true true (11/20))
    (by norm_num) (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le mh_plus_minus_last_slope
  exact (lt_min mh_plus_minus_left mh_plus_minus_right).trans_le hm

theorem mh_negative_lower {x : ℝ} (hx : (9/10:ℝ)≤x) :
    (4463/5000:ℝ)< mhNegative x :=
  mh_negative_left.trans_le
    (amplitude_monotone true true false false false (S := middleSource) mh_negative_amplitude hx)

theorem mh_opposite_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (13/10)) :
    (4463/5000:ℝ)< mhOpposite x := by
  have hc := mh_opposite_coefficients
  have hm := endpoint_minimum true true false false true (S := middleSource)
    (by norm_num) (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le mh_opposite_last_slope
  exact (lt_min mh_opposite_left mh_opposite_right).trans_le hm

theorem hm_positive_lower {x : ℝ} (hx : x∈Icc (11/10:ℝ) (71/50)) :
    (4463/5000:ℝ)<hmPositive x := by
  have hc := hm_positive_coefficients
  have hm := endpoint_minimum true false true true true
    (S := FrameDiagonalSupport.sourceCircle false true (1/2))
    (by norm_num) (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le hm_positive_last_slope
  exact (lt_min hm_positive_left hm_positive_right).trans_le hm

theorem hm_opposite_before_lower (cut : Bool) {x : ℝ}
    (hx : x∈Icc (13/10:ℝ) (Real.pi/2-1/50)) :
    (4463/5000:ℝ)<hmOpposite true cut x := by
  cases cut
  · have hc := hm_opposite_first_coefficients
    have hm := endpoint_minimum true false true false true
      (S := FrameDiagonalSupport.sourceCircle false false (2/5))
      (by norm_num) (by linarith) hx hc.1.le hc.2.le hm_opposite_first_last_slope
    exact (lt_min (hm_opposite_left false) (hm_opposite_before_quarter false)).trans_le hm
  · have hc := hm_opposite_last_coefficients
    have hcon := concave true false true false true (2/5)
      (FrameDiagonalSupport.sourceCircle false false (2/5)) b2
      (by norm_num : (0:ℝ)≤13/10) (by linarith : Real.pi/2-1/50≤Real.pi/2) hc.1.le hc.2.le
    exact concave_gt_of_endpoints hcon hx (hm_opposite_left true) (hm_opposite_before_quarter true)

theorem hm_opposite_after_lower (cut : Bool) {x : ℝ} (hx : Real.pi/2+1/50≤x) :
    (4463/5000:ℝ)<hmOpposite false cut x :=
  (hm_opposite_after_quarter cut).trans_le
    (amplitude_monotone false false true false true
      (S := FrameDiagonalSupport.sourceCircle false false (2/5)) (hm_opposite_after_amplitude cut) hx)

end SquaresInCircles.Eight.FrameMidHighFixedScalars
end
end
end

section
/-!
## Complete target-high circular support intervals

The first three supports are concave; the last is increasing.  Their
endpoint comparisons therefore supply the original strengthened bound
on all four closed intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighTargetScalars
open FrameMidHighTargetCalculus FrameMidHighTargetReferences

theorem positive_lower {x : ℝ} (hx : x∈Icc (7/10:ℝ) (93/100)) :
    (4463/5000:ℝ)<F true true (7/20) x :=
  concave_gt_of_endpoints positive_concave hx positive_left positive_right

theorem negative_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (71/50)) :
    (4463/5000:ℝ)<F false false (2/5) x :=
  concave_gt_of_endpoints negative_concave hx negative_left negative_right

theorem opposite_before_lower {x : ℝ} (hx : x∈Icc (13/10:ℝ) (Real.pi/2-1/50)) :
    (4463/5000:ℝ)<F false true (2/5) x :=
  concave_gt_of_endpoints opposite_concave hx opposite_left opposite_before_quarter

theorem opposite_after_lower {x : ℝ} (hx : x∈Icc (Real.pi/2+1/50) (171/100:ℝ)) :
    (4463/5000:ℝ)<after false true (2/5) x := by
  have hh := after_monotone ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  exact opposite_after_quarter.trans_le hh

end SquaresInCircles.Eight.FrameMidHighTargetScalars
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighCentral
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameDiagonalSupport FrameMidHighSupportForms FrameMidHighSupports
open FrameDiagonalTrigonometry

theorem positive {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (7/10:ℝ) (93/100))
    (hm : 0≤central true true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false true true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := FrameDiagonalSupport.support (by norm_num : (0:ℝ)≤7/20) hm (positive_source hb)
    (target_circle_lower false true (7/20) x hB)
  rw [high_target_first true true (Or.inl rfl) hxq] at hs
  exact (FrameMidHighTargetScalars.positive_lower hx).trans_le hs

theorem plus_minus {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (1/10:ℝ) (61/100))
    (hm : 0≤central true false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false true false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := FrameDiagonalSupport.support (by norm_num : (0:ℝ)≤11/20) hm
    (source_circle_lower true true (11/20) hb)
    (high_target_early hB ⟨by linarith [hx.1],hx.2⟩)
  rw [FrameMidHighFixedCalculus.first_formula true false true false (11/20)
    (sourceCircle true true (11/20)) b1 hxq] at hs
  exact (FrameMidHighFixedScalars.mh_plus_minus_lower hx).trans_le hs

theorem negative_first {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (9/10:ℝ) (6/5))
    (hm : 0≤central false false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := FrameDiagonalSupport.support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (high_target_negative hB hx)
  rw [FrameMidHighFixedCalculus.first_formula true false false false (2/5)
    (source true false (2/5) b1) b1 hxq] at hs
  exact (FrameMidHighFixedScalars.mh_negative_lower hx.1).trans_le hs

theorem negative_last {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (6/5:ℝ) (71/50))
    (hm : 0≤central false false (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false false b B x := by
  have hxq := rational_quadrant ⟨by linarith [hx.1],hx.2⟩
  have hs := FrameDiagonalSupport.support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (target_circle_lower false false (2/5) x hB)
  rw [high_target_first false false (Or.inr rfl) hxq] at hs
  exact (FrameMidHighTargetScalars.negative_lower hx).trans_le hs

theorem opposite_first {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (6/5:ℝ) (13/10))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := rational_quadrant ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := FrameDiagonalSupport.support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (high_target_opposite hB ⟨by linarith [hx.1],hx.2⟩)
  rw [FrameMidHighFixedCalculus.first_formula true false false true (2/5)
    (source true false (2/5) b1) 0 hxq] at hs
  exact (FrameMidHighFixedScalars.mh_opposite_lower hx).trans_le hs

theorem opposite_before {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (13/10:ℝ) (Real.pi/2-1/50))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hs := FrameDiagonalSupport.support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (target_circle_lower false true (2/5) x hB)
  rw [high_target_first false true (Or.inr rfl) hxq] at hs
  exact (FrameMidHighTargetScalars.opposite_before_lower hx).trans_le hs

theorem opposite_after {b B x : ℝ} (hb : b∈arc true) (hB : B∈arc false)
    (hx : x∈Icc (Real.pi/2+1/50) (171/100:ℝ))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false true b B x := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1],by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩
  have hs := FrameDiagonalSupport.support (by norm_num : (0:ℝ)≤2/5) hm (negative_source hb)
    (target_circle_lower false true (2/5) x hB)
  rw [high_target_second false true (Or.inr rfl) hxq] at hs
  exact (FrameMidHighTargetScalars.opposite_after_lower hx).trans_le hs

theorem central_lower (i j : Bool) {b B x : ℝ}
    (hb : b∈arc true) (hB : B∈arc false) (hx : 0≤x)
    (hm : 0≤central i j (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false i j b B x := by
  by_cases ht : FrameDiagonalTails.mhTail true i j≤x
  · exact FrameDiagonalTails.middle_high i j hb hB ht
  have hc := FrameDiagonalCuts.central_cut true false i j (Or.inr rfl) hb hB hx hm
  cases i <;> cases j
  · change ¬(71/50:ℝ)≤x at ht
    change (9/10:ℝ)<x at hc
    by_cases h : x≤6/5
    · exact negative_first hb hB ⟨hc.le,h⟩ hm
    · exact negative_last hb hB ⟨(lt_of_not_ge h).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(171/100:ℝ)≤x at ht
    change (6/5:ℝ)<x at hc
    by_cases h1 : x≤13/10
    · exact opposite_first hb hB ⟨hc.le,h1⟩ hm
    by_cases h2 : x≤Real.pi/2-1/50
    · exact opposite_before hb hB ⟨(lt_of_not_ge h1).le,h2⟩ hm
    by_cases h3 : x≤Real.pi/2+1/50
    · exact FrameMidHighQuarterStrip.middle_high hb hB ⟨(lt_of_not_ge h2).le,h3⟩ hm
    · exact opposite_after hb hB ⟨(lt_of_not_ge h3).le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(61/100:ℝ)≤x at ht
    change (1/10:ℝ)<x at hc
    exact plus_minus hb hB ⟨hc.le,(lt_of_not_ge ht).le⟩ hm
  · change ¬(93/100:ℝ)≤x at ht
    change (7/10:ℝ)<x at hc
    exact positive hb hB ⟨hc.le,(lt_of_not_ge ht).le⟩ hm

end SquaresInCircles.Eight.FrameMidHighCentral
end
end
end
