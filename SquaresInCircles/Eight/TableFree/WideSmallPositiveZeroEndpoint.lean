module

public import SquaresInCircles.Eight.TableFree.SmallPositiveZeroEndpoint
public import SquaresInCircles.Eight.TableFree.WideSmallHardEnvelope

/-!
# Ordered positive zero endpoints down to the .28 tangent threshold

Uncompiled source draft.  The source H/D/E budget and the unchanged
opposite hard contact exclude the actual G-zero endpoint on the full
small-tangent interval [.28,.5].  Only the candidate GA angle is bounded;
no unproved enlarged spread for a replacement cycle is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate EndpointRotationPenalty EndpointBudgetScalars

namespace SignedCycle

/-- The transverse-zero alternative in the positive HG0 small-side
boundary construction is excluded using the unchanged source cycle.
P and Q are its actual candidate A/G points, and theta is its candidate
G frame.  Neither a source-radius lift nor total spread for Q is hidden
in the statement. -/
theorem HardOuterGeometry.wide_small_positive_G_zero_impossible {q θ : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hTy : 0≤(I.cycle.point T).y)
    (P Q : SignedPoint) (hPs : P.Sorted) (hPc : P.AvoidsCore)
    (hPq : P.Contained q) (hPy : P.y=(I.cycle.point A).y)
    (hQq : Q.Contained q) (hQy : Q.y=0)
    (hHθ : I.cycle.theta H<θ) (hθA : θ-I.cycle.theta A≤frameCap)
    (hHG : zeroFeasible (I.cycle.point H) Q (θ-I.cycle.theta H) 0)
    (hGA : quarterFeasible Q P (I.cycle.theta A-θ) 0) : False := by
  let z := θ-I.cycle.theta A
  let v := I.cycle.theta A-I.cycle.theta T
  let h := θ-I.cycle.theta H
  have hz : z∈Icc 0 frameCap := by
    dsimp [z]
    exact ⟨by linarith,hθA⟩
  have hv : v∈Icc 0 frameCap := by
    refine ⟨sub_nonneg.mpr hTA,?_⟩
    exact (le_abs_self v).trans (I.necessary.spread A T)
  have hPa : 1/2<P.a := SignedPoint.primary_gt_half hPs hPc
  have hPy0 : 0≤P.y := by rw [hPy]; linarith [hsmall.1]
  have hAc : (P.a+1/2)^2+((I.cycle.point A).y+1/2)^2≤qCap := by
    have hh := hPq.trans hq
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hPy0,hPy] using hh
  have hBc : ((I.cycle.point B).a+1/2)^2+(3/2-(I.cycle.point A).y)^2≤qCap := by
    have hh := (I.necessary.contained B).trans hq
    have hy : -(I.cycle.point B).y+1/2=3/2-(I.cycle.point A).y := by linarith
    simpa [SignedPoint.Contained,SignedPoint.circle,
      abs_of_nonpos I.anchors_normal.B_nonpos,hy] using hh
  have hGA' : 1/2≤(P.a-1/2)*Real.cos z-
      ((I.cycle.point A).y+1/2)*Real.sin z := by
    have hf : quarterFeasible Q P (-z) 0 := by
      simpa [z,neg_sub] using hGA
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy,hPy] at hf
    nlinarith
  have hBT' : (I.cycle.point T).y+1/2≤
      ((I.cycle.point B).a-1/2)*Real.cos v-
        (3/2-(I.cycle.point A).y)*Real.sin v := by
    have hf : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
      have hδ : I.cycle.theta T-I.cycle.theta B= -v := by dsimp [v]; rw [←hAB]; ring
      simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,hδ]
        using I.BT_hard
    rw [quarterFeasible,edgeWidth_negative_formula hv] at hf
    simp only [quarterProjection,Matrix.cons_val_two,Real.cos_neg,Real.sin_neg] at hf
    have hBy : (I.cycle.point B).y=(I.cycle.point A).y-1 := by linarith
    rw [hBy] at hf
    nlinarith
  have hzmax := WideSmallHardEnvelope.hard_angle_upper hsmall hPa hAc hz hGA'
  have hd : (I.cycle.point A).y-67/200∈Icc (-(11/200) : ℝ) (33/200) := by
    constructor <;> linarith [hsmall.1,hsmall.2]
  have hhi : h∈Ioc 0 (2/5 : ℝ) := by
    have hzbound := (WideSmallHardEnvelope.majorant_bounds hd).1.2
    dsimp [h,z] at *
    constructor <;> linarith
  have hHy : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hHcharge := SmallPositiveZeroEndpoint.zero_outer_strict_charge
    hq hQq hQy hHy hhi hHG
  have hmiddle := WideSmallHardEnvelope.actual_middle_bound hsmall hPa hAc hBc
    hz hv hTy hGA' hBT'
  have hTDcharge := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).2
  have hbudget := I.endpoint_bound hq
  have hS := SmallPositiveZeroEndpoint.endpoint_constant_lower
  dsimp [h,z,v,charge,epsilon] at *
  linarith

end SignedCycle
end SquaresInCircles.Eight.TableFree
