module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3SourceData
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2GainComparison

/-!
# Eight squares: the joint-negative BT3 and TD0 stress

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
