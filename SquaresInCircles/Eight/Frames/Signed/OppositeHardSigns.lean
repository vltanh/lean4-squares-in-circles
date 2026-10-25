module

public import SquaresInCircles.Eight.Owners.Hard.OuterGeometry
public import SquaresInCircles.Eight.Frames.Signed.OppositeHardEnvelope
public import SquaresInCircles.Eight.Words.Zero.SignedCharge

/-!
# Eight squares: a large middle tangent gives G or T its normal sign

Let A and B have a common frame with `yA - yB = 1` and `θT ≤ θA ≤ θG`. If the tangent of A is at
least `1/2`, then `yG < 0` (`HardOuterGeometry.large_middle_G_negative`); if that of B is, then
`yT > 0` (`large_middle_T_positive`), and the same holds for hard inputs. The opposite envelope
of `SignedOppositeHardEnvelope`, with the charges of H–G and T–D and the endpoint budget of H, D
and E, which exceeds `83/200` (`budget_reserve`), excludes the other sign; the opposite point may
have either sign. The case of T is the reflection of that of G, applied to the outer geometry
only, whose endpoint budget the reflection keeps; the sign of E is not normalized again.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace SignedOppositeHardEnvelope
open EndpointRotationPenalty EndpointBudgetScalars

theorem budget_reserve : (83/200 : ℝ)<S0 := by
  have hs := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
  have hs0 := Real.sqrt_nonneg (qCap-1)
  dsimp [S0,qCap] at *
  nlinarith

theorem negative_hard_contact {G A : SignedPoint} {z : ℝ}
    (hz : z∈Icc 0 frameCap) (hGA : quarterFeasible G A (-z) 0) :
    -G.y+1/2≤(A.a-1/2)*Real.cos z-(A.y+1/2)*Real.sin z := by
  have hh := hGA
  rw [quarterFeasible,edgeWidth_negative_formula hz] at hh
  simp [quarterProjection,Real.cos_neg,Real.sin_neg] at hh
  linarith

end SignedOppositeHardEnvelope

namespace SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars SignedOppositeHardEnvelope

/-- With A and B on a common frame, `yA - yB = 1`, `θT ≤ θA ≤ θG` and `yA ≥ 1/2`, G has `yG < 0`;
the tangent of T, the signs of the two outer errors and the zero owners are unrestricted. -/
theorem HardOuterGeometry.large_middle_G_negative {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hlarge : 1/2≤(I.cycle.point A).y) :
    (I.cycle.point G).y<0 := by
  by_contra! hwrong
  let z := I.cycle.theta G-I.cycle.theta A
  let v := I.cycle.theta B-I.cycle.theta T
  have hz : z∈Icc 0 frameCap := by
    refine ⟨sub_nonneg.mpr hAG,?_⟩
    exact (le_abs_self z).trans (I.necessary.spread G A)
  have hv : v∈Icc 0 frameCap := by
    refine ⟨by dsimp [v]; linarith,?_⟩
    exact (le_abs_self v).trans (I.necessary.spread B T)
  have hyB : -(I.cycle.point B).y+1/2=3/2-(I.cycle.point A).y := by linarith
  have hA : ((I.cycle.point A).a+1/2)^2+((I.cycle.point A).y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,
      abs_of_nonneg I.anchors_normal.A_nonneg] using
        (I.necessary.contained A).trans hq
  have hB : ((I.cycle.point B).a+1/2)^2+(3/2-(I.cycle.point A).y)^2≤qCap := by
    have hh := (I.necessary.contained B).trans hq
    change ((I.cycle.point B).a+1/2)^2+(|(I.cycle.point B).y|+1/2)^2≤qCap at hh
    rw [abs_of_nonpos I.anchors_normal.B_nonpos,hyB] at hh
    exact hh
  have hb : (I.cycle.point A).y∈Icc (1/2 : ℝ) (9/10) := by
    have hh := SignedPoint.coordinate_bounds (I.necessary.sorted A) (I.necessary.core A)
      (I.necessary.contained A) hq
    exact ⟨hlarge,(le_abs_self _).trans hh.2.2.le⟩
  have haA := SignedPoint.primary_gt_half (I.necessary.sorted A) (I.necessary.core A)
  have hga : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,delta,next,word,G,A,quarterFeasible] using I.GA_hard
  have hbt : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
    simpa [v,Feasible,slack,edge,delta,next,word,B,T,quarterFeasible] using I.BT_hard
  have hgaBound := negative_hard_contact hz hga
  have hbtReflected : quarterFeasible (I.cycle.point T).reflect
      (I.cycle.point B).reflect (-v) 0 := by
    simpa [reflectedOwner] using
      (quarterFeasible_reflect (I.cycle.point B) (I.cycle.point T) (-v) 2).2 hbt
  have hbtBound := negative_hard_contact hv hbtReflected
  simp only [SignedPoint.reflect,neg_neg] at hbtBound
  rw [hyB] at hbtBound
  have hscalar := actual_middle_wrong_bound hb haA hA hB hz hv
    (show -(I.cycle.point G).y≤0 by linarith) hgaBound hbtBound
  obtain ⟨hHG,hTD⟩ := signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs
  have hendpoint := I.endpoint_bound hq
  have hreserve := budget_reserve
  dsimp [z,v,EndpointRotationPenalty.charge,epsilon] at hscalar hHG hTD hendpoint
  nlinarith

/-- The reflected statement: with `-yB ≥ 1/2`, T has `yT > 0`. The point E and the sign of G are
kept as they are. -/
theorem HardOuterGeometry.large_middle_T_positive {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hlarge : 1/2≤ -(I.cycle.point B).y) :
    0<(I.cycle.point T).y := by
  have hAB' : I.reflected.cycle.theta A=I.reflected.cycle.theta B := by
    change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta A
    linarith
  have hsum' : (I.reflected.cycle.point A).y-(I.reflected.cycle.point B).y=1 := by
    change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
    linarith
  have hTA' : I.reflected.cycle.theta T≤I.reflected.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta B
    linarith
  have hAG' : I.reflected.cycle.theta A≤I.reflected.cycle.theta G := by
    change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta T
    linarith
  have hlarge' : 1/2≤(I.reflected.cycle.point A).y := hlarge
  have hh := I.reflected.large_middle_G_negative hq hAB' hsum' hTA' hAG' hlarge'
  change -(I.cycle.point T).y<0 at hh
  linarith

theorem HardInput.large_middle_G_negative {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hlarge : 1/2≤(I.cycle.point A).y) :
    (I.cycle.point G).y<0 :=
  I.outerGeometry.large_middle_G_negative hq hAB hsum hTA hAG hlarge

theorem HardInput.large_middle_T_positive {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hlarge : 1/2≤ -(I.cycle.point B).y) :
    0<(I.cycle.point T).y :=
  I.outerGeometry.large_middle_T_positive hq hAB hsum hTA hAG hlarge

end SignedCycle
end SquaresInCircles.Eight
