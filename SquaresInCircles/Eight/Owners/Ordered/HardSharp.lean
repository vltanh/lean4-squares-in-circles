module

public import SquaresInCircles.Eight.Frames.Signed.OppositeHardSigns
public import SquaresInCircles.Eight.Owners.Hard.CancelingOuterCycle
public import SquaresInCircles.Eight.Owners.Hard.OuterOrder
public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Owners.Nonpositive.OuterSharp
public import SquaresInCircles.Eight.Owners.Positive.CancelingOuter
public import SquaresInCircles.Eight.Owners.Positive.NoncancelingCycle
public import SquaresInCircles.Eight.Owners.Small.PositiveReflection
public import SquaresInCircles.Eight.Owners.Small.WrongZeroEndpoint
public import SquaresInCircles.Eight.Words.Zero.SignedCharge

/-!
# Eight squares: ordered hard sharpness with arbitrary original G/T signs

The signed opposite envelope excludes a wrong
sign on the larger middle tangent.  Its normal large-side geometry then
places the opposite original tangent above .335.  A small wrong sign
would reach the actual zero endpoint excluded by the unchanged mixed
budget.  Both original signs are therefore recovered before applying
the complete four-owner ordered sharpness theorem to the source itself.
-/

section
/-!
## Both signs of both canceling outer errors in an ordered common middle

Once D ≤ A = B ≤ H, the actual canceling HG2
and TD0 pairs align at the same radius.  The larger middle tangent is
treated first only to prove that the opposite original tangent exceeds
one fifth.  Both concrete outputs are then constructed from the separate
original anchor circles.  No descendant circle equality is substituted
for a source circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate HardCancelingOuter PositiveCancelingOuter
namespace SignedCycle

theorem HardInput.ordered_canceling_HG_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hAy : 1/5≤(I.cycle.point A).y)
    (hHG : I.cycle.Feasible H 2) :
    Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A)
      ((I.cycle.theta H-I.cycle.theta A)-|I.cycle.theta G-I.cycle.theta H|/3)) := by
  have hΘ : I.cycle.theta H-I.cycle.theta A∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread H A
    refine ⟨sub_nonneg.mpr hAH,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have ht : I.cycle.theta G-I.cycle.theta A∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread G A
    refine ⟨sub_nonneg.mpr hAG,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      ((I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)) 2 := by
    rw [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
      I.cycle.theta G-I.cycle.theta H by ring]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  have hh := ordered_G_alignment hqL hq (I.necessary.sorted H) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A) (I.necessary.contained H)
    (I.necessary.contained A) I.anchors_normal.H_nonneg hAy hΘ ht hHG' hGA'
  simpa [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
    I.cycle.theta G-I.cycle.theta H by ring] using hh

theorem HardInput.ordered_canceling_TD_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hBy : (I.cycle.point B).y≤ -(1/5 : ℝ))
    (hTD : I.cycle.Feasible T 0) :
    Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D)
      ((I.cycle.theta B-I.cycle.theta D)-|I.cycle.theta T-I.cycle.theta D|/3)) := by
  have hΘ : I.cycle.theta B-I.cycle.theta D∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread B D
    refine ⟨sub_nonneg.mpr hDB,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have ht : I.cycle.theta B-I.cycle.theta T∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread B T
    refine ⟨sub_nonneg.mpr hTB,?_⟩
    dsimp [frameCap] at hh
    exact (le_abs_self _).trans hh
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)) 0 := by
    rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
      I.cycle.theta D-I.cycle.theta T by ring]
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta B-I.cycle.theta T)) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,neg_sub]
      using I.BT_hard
  have hh := ordered_T_alignment hqL hq (I.necessary.sorted B) (I.necessary.sorted D)
    (I.necessary.core B) (I.necessary.core D) (I.necessary.contained B)
    (I.necessary.contained D) hBy I.anchors_normal.D_nonpos hΘ ht hBT' hTD'
  rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
    I.cycle.theta D-I.cycle.theta T by ring,abs_sub_comm] at hh
  exact hh

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
/-!
## Original middle tangent bounds in the ordered normal hard sector

A nonpositive outer error forces the actual
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
namespace SquaresInCircles.Eight
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
end SquaresInCircles.Eight
end
end
end

section
/-!
## A positive outer error with ordered normal hard contacts aligns

The weak owner chooses one of the two local constructions: the noncanceling owner uses the circle
of the large side or the convexity argument of the small side, and the canceling owner uses its
support reserve on the same circle (`HardInput.positive_HG_normal_output`,
`HardInput.positive_TD_normal_output`). Each construction spends a strict loss on the original
circle of A or of B, and keeps the opposite side and all of H, D, E
(`HardInput.align_positive_HG_normal`, `HardInput.align_positive_TD_normal`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardInput.positive_HG_normal_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤(I.cycle.point A).y)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H<I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ t, t<I.cycle.theta H-I.cycle.theta A ∧
      Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
        (I.cycle.theta H-I.cycle.theta A) t) := by
  have howners : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  rcases howners with ho | ho
  · have hf : I.cycle.Feasible H 0 := by simpa [ho] using I.witnesses.feasible H
    by_cases hlarge : 1/2≤(I.cycle.point A).y
    · obtain ⟨O⟩ := I.positive_HG0_large_output hqL hq hAH hHGorder.le hGy hlarge hf
      exact ⟨_,by linarith,⟨O⟩⟩
    · exact I.outerGeometry.positive_HG0_small_output hqL hq hAB hnorm
        ⟨hfloor,(lt_of_not_ge hlarge).le⟩ hTA hAH hHGorder hGy hTy hf
  · have hf : I.cycle.Feasible H 2 := by simpa [ho] using I.witnesses.feasible H
    obtain ⟨O⟩ := I.ordered_canceling_HG_output hqL hq hAH
      (hAH.trans hHGorder.le) (by linarith) hf
    have hp : 0 < |I.cycle.theta G-I.cycle.theta H| :=
      abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hHGorder))
    exact ⟨_,by linarith,⟨O⟩⟩

theorem HardInput.positive_TD_normal_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤ -(I.cycle.point B).y)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T<I.cycle.theta D)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ t, t<I.cycle.theta B-I.cycle.theta D ∧
      Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
        (I.cycle.theta B-I.cycle.theta D) t) := by
  have howners : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  rcases howners with ho | ho
  · have hf : I.cycle.Feasible T 0 := by simpa [ho] using I.witnesses.feasible T
    obtain ⟨O⟩ := I.ordered_canceling_TD_output hqL hq hDB
      (hTDorder.le.trans hDB) (by linarith) hf
    have hp : 0< |I.cycle.theta T-I.cycle.theta D| :=
      abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hTDorder))
    exact ⟨_,by linarith,⟨O⟩⟩
  · have hf : I.cycle.Feasible T 2 := by simpa [ho] using I.witnesses.feasible T
    by_cases hlarge : 1/2≤ -(I.cycle.point B).y
    · obtain ⟨O⟩ := I.positive_TD2_large_output hqL hq hDB hTDorder.le hTy hlarge hf
      exact ⟨_,by linarith,⟨O⟩⟩
    · exact I.positive_TD2_small_output hqL hq hAB hnorm
        ⟨hfloor,by linarith⟩ hAG hDB hTDorder hGy hTy hf

theorem HardInput.align_positive_HG_normal {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤(I.cycle.point A).y)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H<I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧ J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧
      (J.cycle.point G).y< -(1/10 : ℝ) ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨t,ht,⟨O⟩⟩ := I.positive_HG_normal_output hqL hq hAB hnorm hfloor
    hTA hAH hHGorder hGy hTy
  refine ⟨I.fromCancelingHG hAB O,rfl,hAB,O.A_tangent,O.G_normal,?_,?_,?_,?_⟩
  · intro i hi
    by_cases hiA : i=A
    · subst i; exact O.A_circle
    by_cases hiG : i=G
    · subst i; simp [anchorVertices,H,G,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1).le
  · exact ⟨A,by simp [anchorVertices],O.A_strict ht⟩
  · intro i hi
    change (alignGACycle I.cycle O.pointG O.pointA).theta i=I.cycle.theta i
    simp [alignGACycle_theta,hi]
  · intro i hiG hiA
    exact (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1

theorem HardInput.align_positive_TD_normal {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤ -(I.cycle.point B).y)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T<I.cycle.theta D)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ J : HardInput q,
      J.cycle.theta T=J.cycle.theta D ∧ J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point B).y=(I.cycle.point B).y ∧
      (1/10 : ℝ)<(J.cycle.point T).y ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i,i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠T → i≠B → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨t,ht,⟨O⟩⟩ := I.positive_TD_normal_output hqL hq hAB hnorm hfloor
    hAG hDB hTDorder hGy hTy
  refine ⟨I.fromCancelingTD hAB O,rfl,hAB,O.B_tangent,O.T_normal,?_,?_,?_,?_⟩
  · intro i hi
    by_cases hiB : i=B
    · subst i; exact O.B_circle
    by_cases hiT : i=T
    · subst i; simp [anchorVertices,H,T,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1).le
  · exact ⟨B,by simp [anchorVertices],O.B_strict ht⟩
  · intro i hi
    change (alignBTCycle I.cycle O.pointT O.pointB).theta i=I.cycle.theta i
    simp [alignBTCycle_theta,hi]
  · intro i hiT hiB
    exact (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
/-!
## Sharpness of all four outer-owner cells in the ordered normal sector

Positive outer errors are removed on their
actual source circles, with losses charged to A/B.  The resulting hard
cycle has both nonpositive errors, so its sharp theorem forces all five
rigid anchors onto the extremal circle.  The strict-loss ledger then
rules out either positive error on the original source.  The final
sharp theorem is applied to that original source, recovering its own
frames, anchor circles, and all terminal contacts.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
open Stationary (qStar qStar_limits)
namespace SignedCycle

private theorem HardInput.reduce_positive_HG_normal {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤(I.cycle.point A).y)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ J : HardInput q,
      J.cycle.theta G≤J.cycle.theta H ∧ J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧ (J.cycle.point G).y≤0 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta H<I.cycle.theta G → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) ∧
      J.cycle.theta A≤J.cycle.theta G := by
  by_cases hGH : I.cycle.theta G≤I.cycle.theta H
  · exact ⟨I,hGH,hAB,rfl,hGy,anchorNonincrease_refl _,
      fun h => False.elim ((not_lt_of_ge hGH) h),
      fun _ _ => rfl,fun _ _ _ => rfl,hAG⟩
  have hHG : I.cycle.theta H<I.cycle.theta G := lt_of_not_ge hGH
  obtain ⟨J,hJG,hJAB,hJAy,hJGy,hnon,hstrict,hθ,hpoint⟩ :=
    I.align_positive_HG_normal hqL hq hAB hnorm hfloor hTA hAH hHG hGy hTy
  refine ⟨J,hJG.le,hJAB,hJAy,by linarith,hnon,fun _ => hstrict,hθ,hpoint,?_⟩
  rw [hJG,hθ A (by decide),hθ H (by decide)]
  exact hAH

/-- An actual same-q descendant with nonpositive outer errors.  The
strictness predicate still concerns either original positive error. -/
theorem HardInput.ordered_normal_to_nonpositive {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ J : HardInput q,
      J.cycle.theta G≤J.cycle.theta H ∧ J.cycle.theta D≤J.cycle.theta T ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta H<I.cycle.theta G ∨ I.cycle.theta T<I.cycle.theta D →
        StrictAnchorLoss I.cycle J.cycle) := by
  have hrange := I.ordered_normal_middle_range hqL hq hnorm hAH hAG hDB hTB hGy hTy
  have hTA : I.cycle.theta T≤I.cycle.theta A := by rw [hAB]; exact hTB
  obtain ⟨K,hKGH,hKAB,hKAy,hKGy,hnonK,hstrictK,hKθ,hKpoint,hKAG⟩ :=
    I.reduce_positive_HG_normal hqL hq hAB hnorm hrange.1.1.le hTA hAH hAG hGy hTy
  have hKB : K.cycle.point B=I.cycle.point B := hKpoint B (by decide) (by decide)
  have hKT : K.cycle.point T=I.cycle.point T := hKpoint T (by decide) (by decide)
  have hKnorm : (K.cycle.point A).y-(K.cycle.point B).y=1 := by
    rw [hKAy,hKB]
    exact hnorm
  have hKfloor : 67/200≤ -(K.cycle.point B).y := by rw [hKB]; exact hrange.2.1.le
  have hKDB : K.cycle.theta D≤K.cycle.theta B := by
    rw [hKθ D (by decide),hKθ B (by decide)]
    exact hDB
  have hKTy : 0≤(K.cycle.point T).y := by rw [hKT]; exact hTy
  by_cases hKDT : K.cycle.theta D≤K.cycle.theta T
  · refine ⟨K,hKGH,hKDT,hnonK,?_⟩
    rintro (hG | hT)
    · exact hstrictK hG
    · have hh := hKDT
      rw [hKθ D (by decide),hKθ T (by decide)] at hh
      exact False.elim ((not_lt_of_ge hh) hT)
  · have hKTD : K.cycle.theta T<K.cycle.theta D := lt_of_not_ge hKDT
    obtain ⟨J,hJT,hJAB,hJBy,hJTy,hnonJ,hstrictJ,hJθ,hJpoint⟩ :=
      K.align_positive_TD_normal hqL hq hKAB hKnorm hKfloor hKAG hKDB hKTD hKGy hKTy
    have hJGH : J.cycle.theta G≤J.cycle.theta H := by
      rw [hJθ G (by decide),hJθ H (by decide)]
      exact hKGH
    exact ⟨J,hJGH,hJT.symm.le,hnonK.trans hnonJ,
      fun _ => hnonK.then_strict hstrictJ⟩

/-- Equality recovers the signs of both original outer errors before
the sharp theorem is applied to the literal original geometry. -/
theorem HardInput.ordered_normal_original_nonpositive {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    I.cycle.theta G≤I.cycle.theta H ∧ I.cycle.theta D≤I.cycle.theta T := by
  have hQ : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J,hJGH,hJDT,hnon,hstrict⟩ :=
    I.ordered_normal_to_nonpositive hqL hQ hAB hnorm hAH hAG hDB hTB hGy hTy
  obtain ⟨_,_,_,_,_,_,_,_,hcircle,_⟩ := J.nonpositive_outer_sharp hqL hq hJGH hJDT
  have hnoloss : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle
      (fun i _ => (I.necessary.contained i).trans hq) hcircle
  constructor
  · by_contra! h
    exact hnoloss (hstrict (Or.inl h))
  · by_contra! h
    exact hnoloss (hstrict (Or.inr h))

/-- All four originally selected HG/TD owner combinations have the
same source sharpness conclusion in the ordered normal sector. -/
theorem HardInput.ordered_normal_sharp {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hn := I.ordered_normal_original_nonpositive hqL hq hAB hnorm hAH hAG hDB hTB hGy hTy
  exact I.nonpositive_outer_sharp hqL hq hn.1 hn.2

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
open Stationary (qStar qStar_limits)
namespace SignedCycle

theorem HardInput.ordered_intermediate_signs {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B) :
    (I.cycle.point G).y<0 ∧ 0<(I.cycle.point T).y := by
  have hTA : I.cycle.theta T≤I.cycle.theta A := by rw [hAB]; exact hTB
  have hsmall := I.small_intermediate_signs hq
  constructor
  · by_contra! hwrong
    have hAsmall : (I.cycle.point A).y<1/2 := by
      by_contra! hlarge
      exact not_lt_of_ge hwrong (I.large_middle_G_negative hq hAB hnorm hTA hAG hlarge)
    have hBlarge : 1/2≤ -(I.cycle.point B).y := by linarith
    have hTnormal := I.large_middle_T_positive hq hAB hnorm hTA hAG hBlarge
    have hBupper := I.ordered_large_B_upper hqL hq hDB hTB hTnormal.le hBlarge
    have hArange : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) :=
      ⟨by linarith,hAsmall.le⟩
    exact I.outerGeometry.small_wrong_G_impossible hqL hq hAB hnorm hArange
      hTA hAH hTnormal.le hwrong hsmall.1
  · by_contra! hwrong
    have hBsmall : -(I.cycle.point B).y<1/2 := by
      by_contra! hlarge
      exact not_lt_of_ge hwrong (I.large_middle_T_positive hq hAB hnorm hTA hAG hlarge)
    have hAlarge : 1/2≤(I.cycle.point A).y := by linarith
    have hGnormal := I.large_middle_G_negative hq hAB hnorm hTA hAG hAlarge
    have hAupper := I.ordered_large_A_upper hqL hq hAH hAG hGnormal.le hAlarge
    let J := I.outerGeometry.reflected
    have hJAB : J.cycle.theta A=J.cycle.theta B := by
      change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta A
      linarith
    have hJnorm : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
      change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
      linarith
    have hJrange : (J.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) := by
      change -(I.cycle.point B).y∈Icc (67/200 : ℝ) (1/2)
      exact ⟨by linarith,hBsmall.le⟩
    have hJTA : J.cycle.theta T≤J.cycle.theta A := by
      change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta B
      linarith
    have hJAH : J.cycle.theta A≤J.cycle.theta H := by
      change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta D
      linarith
    have hJTy : 0≤(J.cycle.point T).y := by
      change 0≤ -(I.cycle.point G).y
      linarith
    have hJGy : 0≤(J.cycle.point G).y := by
      change 0≤ -(I.cycle.point T).y
      linarith
    have hJGsmall : (J.cycle.point G).y<1/10 := by
      change -(I.cycle.point T).y<1/10
      linarith [hsmall.2]
    exact J.small_wrong_G_impossible hqL hq hJAB hJnorm hJrange
      hJTA hJAH hJTy hJGy hJGsmall

/-- No original intermediate sign or outer-error sign is assumed.
All selected normal HG/TD owners and all original mixed E owners are
covered, and the conclusions concern the literal original source. -/
theorem HardInput.ordered_hard_sharp {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hsigns := I.ordered_intermediate_signs hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hAH hAG hDB hTB
  exact I.ordered_normal_sharp hqL hq hAB hnorm hAH hAG hDB hTB hsigns.1.le hsigns.2.le

end SignedCycle
end SquaresInCircles.Eight
end
end
end
