module

public import SquaresInCircles.Eight.TableFree.EInteriorCycle
public import SquaresInCircles.Eight.TableFree.NonpositiveChainBounds

/-!
# Actual E minimization before the negative outer errors are aligned

Uncompiled draft.  The retained original HG0/TD2 composites supply the
shared .27 span and H/D primary-sum bounds.  The exact E contact curve
then gives an actual boundary descendant, retaining every non-E point,
frame, witness and separate circle loss.  An interior source E is
strictly above its own descendant circle, independently of radial slack.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate EInteriorGeometry
namespace SignedCycle

def HardInput.fromNonpositiveEInterior {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hb : NonpositiveChainBounds.Bounds I.cycle) {P : State}
    (hp : EInteriorGeometry.Feasible (I.cycle.point H).a (I.cycle.point D).a
      (I.cycle.theta H-I.cycle.theta D) q P) : HardInput q where
  cycle := eInteriorCycle I.cycle P
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=E
      · subst i
        have ha := primary_lower_wide hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
        have hs := strict_sorting_wide hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
        exact ⟨by simpa [eInteriorCycle,E] using (show 0<P.1 by linarith),
          by simpa [eInteriorCycle,E,abs_neg,abs_of_nonneg hp.b_nonneg] using hs.le⟩
      · rw [(eInteriorCycle_unchanged I.cycle P i hi).1]
        exact I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=E
      · subst i
        change ((eInteriorCycle I.cycle P).point E).circle≤q
        rw [eInteriorCycle_circle hp.b_nonneg]
        exact hp.circle
      · rw [(eInteriorCycle_unchanged I.cycle P i hi).1]
        exact I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=E
      · subst i
        have ha := primary_lower_wide hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
        change (1/12 : ℝ)^2≤(max (P.1-1/2) 0)^2+(max (|-P.2.1|-1/2) 0)^2
        rw [abs_neg,abs_of_nonneg hp.b_nonneg,max_eq_left (by linarith : 0≤P.1-1/2)]
        nlinarith [sq_nonneg (max (P.2.1-1/2) 0)]
      · rw [(eInteriorCycle_unchanged I.cycle P i hi).1]
        exact I.necessary.core i
    spread := eInteriorCycle_spread I.necessary.spread hp.angle }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := I.anchors_normal.A_nonneg
    B_nonpos := I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  E_nonpos := by simpa [eInteriorCycle,E] using neg_nonpos.mpr hp.b_nonneg
  witnesses := I.witnesses.eInterior (by linarith [hb.span_lt]) hp
  GA_hard := by
    simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,G,A] using I.GA_hard
  BT_hard := by
    simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,B,T] using I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro h
      have hh : I.witnesses.owner H=2 := by simpa [Witnesses.eInterior,H,D,E] using h
      exact I.zero_signs.HG_canceling hh
    TD_canceling := by
      intro h
      have hh : I.witnesses.owner T=0 := by simpa [Witnesses.eInterior,T,D,E] using h
      exact I.zero_signs.TD_canceling hh }
  E_radial := by
    right
    have ha := primary_lower_wide hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
    change max |(I.cycle.point H).y| |(I.cycle.point D).y|≤P.1
    apply max_le
    · rw [abs_of_nonneg I.anchors_normal.H_nonneg]
      linarith [hb.H_tangent.2]
    · rw [abs_of_nonpos I.anchors_normal.D_nonpos]
      linarith [hb.D_tangent.2]

/-- Actual source-point version of the complete E boundary reduction
for nonpositive outer composites.  The original E sign and the two
original primary mixed witnesses are retained in the relaxation. -/
theorem HardInput.reduce_nonpositive_E {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E∈Icc (I.cycle.theta D) (I.cycle.theta H) ∧
      ((J.cycle.point E).y=0 ∨ J.cycle.theta E=I.cycle.theta D ∨
        J.cycle.theta E=I.cycle.theta H) ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (((I.cycle.point E).y<0 ∧ I.cycle.theta D<I.cycle.theta E ∧
        I.cycle.theta E<I.cycle.theta H) → StrictAnchorLoss I.cycle J.cycle) ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hb := I.nonpositive_composite_bounds hq hAB hAG hGH hDT hTB hHG hTD
  have hp := I.E_source_relaxation hDEorder hEHorder hDE hEH
  obtain ⟨P,hP,hcircle,hboundary,hstrict⟩ := exists_boundary_minimum hq
    ⟨hb.span_nonneg,hb.span_lt⟩ hb.H_primary.1 hb.D_primary.1 hb.primary_sum hp
  let J := I.fromNonpositiveEInterior hq hb hP
  have hcircle_source : corner
      ((I.cycle.point E).a,-(I.cycle.point E).y,I.cycle.theta E-I.cycle.theta D)=
      (I.cycle.point E).circle := by
    simp [corner,SignedPoint.circle,abs_of_nonpos I.E_nonpos]
  have hcircleJ : (J.cycle.point E).circle=corner P := eInteriorCycle_circle hP.b_nonneg
  have hunchanged (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle P i hi
  refine ⟨J,hunchanged,?_,?_,?_,?_,eInteriorCycle_DE (by linarith [hb.span_lt]) hP,
    eInteriorCycle_EH (by linarith [hb.span_lt]) hP⟩
  · change I.cycle.theta D+P.2.2∈Icc (I.cycle.theta D) (I.cycle.theta H)
    constructor <;> linarith [hP.angle.1,hP.angle.2]
  · rcases hboundary with hb0 | hδ0 | hε0
    · left
      change -P.2.1=0
      linarith
    · right; left
      change I.cycle.theta D+P.2.2=I.cycle.theta D
      linarith
    · right; right
      change I.cycle.theta D+P.2.2=I.cycle.theta H
      linarith
  · intro i hi
    by_cases hiE : i=E
    · subst i
      rw [hcircleJ,←hcircle_source]
      exact hcircle
    · rw [(hunchanged i hiE).1]
  · rintro ⟨hy,hD,hH⟩
    refine ⟨E,by norm_num [anchorVertices,E],?_⟩
    rw [hcircleJ,←hcircle_source]
    apply hstrict
    exact ⟨by simpa using neg_pos.mpr hy,by constructor <;> linarith⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
