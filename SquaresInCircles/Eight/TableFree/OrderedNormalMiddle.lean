module

public import SquaresInCircles.Eight.TableFree.HardOuterGeometry
public import SquaresInCircles.Eight.TableFree.PositiveNoncancelingCycle
public import SquaresInCircles.Eight.TableFree.OrderedCancelingCycle

/-!
# Original middle tangent bounds in the ordered normal hard sector

Uncompiled source draft.  A nonpositive outer error forces the actual
intermediate tangent past one tenth by the signed outer charge.  Its
hard quarter contact then forces the original middle primary past 1.1,
and its actual circle bounds the tangent by .665.  On a positive large
side the actual same-q local alignment gives the same original tangent
bound.  The normalized tangent sum supplies the lower bound on the
opposite small side without changing either original anchor.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardOuterGeometry.nonpositive_HG_middle_upper {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H) :
    (I.cycle.point A).y<133/200 := by
  have hc := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).1
  have hHupper : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hGy : (I.cycle.point G).y< -(1/10 : ℝ) := by
    dsimp [EndpointRotationPenalty.charge] at hc
    linarith
  let z := I.cycle.theta G-I.cycle.theta A
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hGA : -(I.cycle.point G).y+1/2≤
      PositiveCancelingOuter.V (I.cycle.point A) z := by
    have hf : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
      simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,z,neg_sub]
        using I.GA_hard
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hf
    simp [quarterProjection,Real.cos_neg,Real.sin_neg] at hf
    dsimp [PositiveCancelingOuter.V]
    linarith
  have hAprimary := SignedPoint.primary_gt_half
    (I.necessary.sorted A) (I.necessary.core A)
  have hVupper := PositiveCancelingOuter.V_upper hAprimary I.anchors_normal.A_nonneg hz
  have hAa : 11/10<(I.cycle.point A).a := by linarith
  have hcircle := (I.necessary.contained A).trans hq
  rw [SignedPoint.circle,abs_of_nonneg I.anchors_normal.A_nonneg] at hcircle
  dsimp [qCap] at hcircle
  nlinarith [I.anchors_normal.A_nonneg]

theorem HardOuterGeometry.nonpositive_TD_middle_upper {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B) :
    -(I.cycle.point B).y<133/200 := by
  have hAG : I.reflected.cycle.theta A≤I.reflected.cycle.theta G := by
    change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta T
    linarith
  have hGH : I.reflected.cycle.theta G≤I.reflected.cycle.theta H := by
    change I.cycle.theta B-I.cycle.theta T≤I.cycle.theta B-I.cycle.theta D
    linarith
  exact I.reflected.nonpositive_HG_middle_upper hq hAG hGH

theorem HardInput.ordered_large_A_upper {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hlarge : 1/2≤(I.cycle.point A).y) :
    (I.cycle.point A).y<133/200 := by
  by_cases hGH : I.cycle.theta G≤I.cycle.theta H
  · exact I.outerGeometry.nonpositive_HG_middle_upper hq hAG hGH
  have hHGorder : I.cycle.theta H≤I.cycle.theta G := (lt_of_not_ge hGH).le
  have howners : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  rcases howners with ho | ho
  · have hf : I.cycle.Feasible H 0 := by simpa [ho] using I.witnesses.feasible H
    obtain ⟨O⟩ := I.positive_HG0_large_output hqL hq hAH hHGorder hGy hlarge hf
    simpa only [O.A_tangent] using O.A_tangent_upper
  · have hf : I.cycle.Feasible H 2 := by simpa [ho] using I.witnesses.feasible H
    obtain ⟨O⟩ := I.ordered_canceling_HG_output hqL hq hAH hAG (by linarith) hf
    simpa only [O.A_tangent] using O.A_tangent_upper

theorem HardInput.ordered_large_B_upper {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTy : 0≤(I.cycle.point T).y) (hlarge : 1/2≤ -(I.cycle.point B).y) :
    -(I.cycle.point B).y<133/200 := by
  by_cases hDT : I.cycle.theta D≤I.cycle.theta T
  · exact I.outerGeometry.nonpositive_TD_middle_upper hq hDT hTB
  have hTDorder : I.cycle.theta T≤I.cycle.theta D := (lt_of_not_ge hDT).le
  have howners : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  rcases howners with ho | ho
  · have hf : I.cycle.Feasible T 0 := by simpa [ho] using I.witnesses.feasible T
    obtain ⟨O⟩ := I.ordered_canceling_TD_output hqL hq hDB hTB (by linarith) hf
    have hh := O.B_tangent_lower
    rw [O.B_tangent] at hh
    linarith
  · have hf : I.cycle.Feasible T 2 := by simpa [ho] using I.witnesses.feasible T
    obtain ⟨O⟩ := I.positive_TD2_large_output hqL hq hDB hTDorder hTy hlarge hf
    have hh := O.B_tangent_lower
    rw [O.B_tangent] at hh
    linarith

/-- Both bounds concern the original A/B tangents and follow from the
actual tangent sum, both hard contacts and the original normal signs. -/
theorem HardInput.ordered_normal_middle_range {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    (I.cycle.point A).y∈Ioo (67/200 : ℝ) (133/200) ∧
      -(I.cycle.point B).y∈Ioo (67/200 : ℝ) (133/200) := by
  have hAupper : (I.cycle.point A).y<133/200 := by
    by_cases hlarge : 1/2≤(I.cycle.point A).y
    · exact I.ordered_large_A_upper hqL hq hAH hAG hGy hlarge
    · linarith
  have hBupper : -(I.cycle.point B).y<133/200 := by
    by_cases hlarge : 1/2≤ -(I.cycle.point B).y
    · exact I.ordered_large_B_upper hqL hq hDB hTB hTy hlarge
    · linarith
  exact ⟨⟨by linarith,hAupper⟩,⟨by linarith,hBupper⟩⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
