module

public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint
public import SquaresInCircles.Eight.Owners.Wide.SmallHardEnvelope

/-!
# Eight squares: positive zero endpoints down to the tangent `0.28`

The H/D/E budget of the cycle and the opposite hard contact exclude the endpoint with G at zero
tangent on the whole small-tangent interval `[0.28, 0.5]`
(`HardOuterGeometry.wide_small_positive_G_zero_impossible`). Only the GA angle of the candidate is
bounded; the moved cycle needs no larger spread bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate EndpointRotationPenalty EndpointBudgetScalars

namespace SignedCycle

/-- The transverse-zero alternative of the small-side construction of a positive HG0 is impossible
for middle tangents in `[7/25, 1/2]`, by the cycle itself: `P` and `Q` are the candidate points of
A and G, and `θ` the candidate frame of G. The statement assumes no lift to the radius of the cycle
and no spread bound for `Q`. -/
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
  obtain ⟨z,hzdef⟩ : ∃ z,z=θ-I.cycle.theta A := ⟨_,rfl⟩
  obtain ⟨v,hvdef⟩ : ∃ v,v=I.cycle.theta A-I.cycle.theta T := ⟨_,rfl⟩
  obtain ⟨h,hhdef⟩ : ∃ h,h=θ-I.cycle.theta H := ⟨_,rfl⟩
  have hz : z∈Icc 0 frameCap := ⟨by rw [hzdef]; linarith,by rw [hzdef]; exact hθA⟩
  have hv : v∈Icc 0 frameCap := by
    refine ⟨by rw [hvdef]; exact sub_nonneg.mpr hTA,?_⟩
    rw [hvdef]
    exact (le_abs_self _).trans (I.necessary.spread A T)
  have hPa : 1/2<P.a := SignedPoint.primary_gt_half hPs hPc
  have hPy0 : 0≤P.y := by rw [hPy]; linarith [hsmall.1]
  have hAc : (P.a+1/2)^2+((I.cycle.point A).y+1/2)^2≤qCap := by
    have hh := hPq.trans hq
    change (P.a+1/2)^2+(|P.y|+1/2)^2≤qCap at hh
    rw [abs_of_nonneg hPy0,hPy] at hh
    exact hh
  have hBc : ((I.cycle.point B).a+1/2)^2+(3/2-(I.cycle.point A).y)^2≤qCap := by
    have hc := (I.necessary.contained B).trans hq
    have hy : -(I.cycle.point B).y+1/2=3/2-(I.cycle.point A).y := by linarith
    change ((I.cycle.point B).a+1/2)^2+(|(I.cycle.point B).y|+1/2)^2≤qCap at hc
    rw [abs_of_nonpos I.anchors_normal.B_nonpos,hy] at hc
    exact hc
  have hGA' : 1/2≤(P.a-1/2)*Real.cos z-
      ((I.cycle.point A).y+1/2)*Real.sin z := by
    have hf : quarterFeasible Q P (-z) 0 := by
      have hd : I.cycle.theta A-θ= -z := by rw [hzdef]; ring
      rw [hd] at hGA
      exact hGA
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy,hPy] at hf
    linarith
  have hBT' : (I.cycle.point T).y+1/2≤
      ((I.cycle.point B).a-1/2)*Real.cos v-
        (3/2-(I.cycle.point A).y)*Real.sin v := by
    have hf : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
      have hd : I.cycle.theta 4-I.cycle.theta 3= -v := by
        change I.cycle.theta T-I.cycle.theta B= -v; rw [hvdef,←hAB]; ring
      simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,hd]
        using I.BT_hard
    rw [quarterFeasible,edgeWidth_negative_formula hv] at hf
    simp [quarterProjection,Real.cos_neg,Real.sin_neg] at hf
    have hBy : (I.cycle.point B).y=(I.cycle.point A).y-1 := by linarith
    rw [hBy] at hf
    linarith
  have hzmax := WideSmallHardEnvelope.hard_angle_upper hsmall hPa hAc hz hGA'
  have hd : (I.cycle.point A).y-67/200∈Icc (-(11/200) : ℝ) (33/200) := by
    constructor <;> linarith [hsmall.1,hsmall.2]
  have hhi : h∈Ioc 0 (2/5 : ℝ) := by
    have hzbound := (WideSmallHardEnvelope.majorant_bounds hd).1.2
    rw [hhdef]
    rw [hzdef] at hzmax
    constructor <;> linarith
  have hHy : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hHcharge := SmallPositiveZeroEndpoint.zero_outer_strict_charge
    hq hQq hQy hHy hhi (by rw [hhdef]; exact hHG)
  have hmiddle := WideSmallHardEnvelope.actual_middle_bound hsmall hPa hAc hBc
    hz hv hTy hGA' hBT'
  have hTDcharge := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).2
  have hbudget := I.endpoint_bound hq
  have hS := SmallPositiveZeroEndpoint.endpoint_constant_lower
  rw [hhdef] at hHcharge
  rw [hzdef,hvdef] at hmiddle
  simp only [EndpointRotationPenalty.charge,epsilon] at hHcharge hmiddle hTDcharge hbudget
  linarith

end SignedCycle
end SquaresInCircles.Eight
