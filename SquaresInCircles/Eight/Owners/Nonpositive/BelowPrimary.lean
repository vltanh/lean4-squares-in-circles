module

public import SquaresInCircles.Eight.Owners.Nonpositive.BelowPrimaryState

/-!
# Eight squares: strict original-circle loss for an E below D with primary DE3

The original-circle descent reaches D with
strict actual DE slack.  An explicit positive tangent decrease keeps
that frame, improves EH, and strictly reduces E's original circle.
The resulting necessary cycle retains H,A,B,D and all intermediate
points and frames literally, so every earlier anchor loss survives.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace EInteriorGeometry

theorem lower_tangent_at_D {h d α q : ℝ} {P : State}
    (hα : α≤7/10) (hp : Feasible h d α q P) (hPangle : P.2.2=0)
    (hb : 0<P.2.1) (hDE : W P.2.2<deValue d P) :
    ∃Q : State, Feasible h d α q Q ∧ Q.2.2=0 ∧ Q.1=P.1 ∧
      0<Q.2.1 ∧ Q.2.1<P.2.1 ∧ corner Q<corner P := by
  have hslack : 0<d+P.2.1-1 := by
    simp [W,deValue,hPangle] at hDE
    linarith
  let ε : ℝ := min (P.2.1/2) ((d+P.2.1-1)/2)
  have hε : 0<ε := lt_min (by linarith) (by linarith)
  have hεb : ε≤P.2.1/2 := min_le_left _ _
  have hεDE : ε≤(d+P.2.1-1)/2 := min_le_right _ _
  let Q : State := (P.1,P.2.1-ε,0)
  have hbQ : 0<Q.2.1 := by dsimp [Q]; linarith
  have hangle : α∈Icc 0 (7/10:ℝ) :=
    ⟨by simpa [hPangle] using hp.angle.2,hα⟩
  have hcos : 0≤Real.cos α := by linarith [(transport_trig hangle).1]
  have hgain := mul_nonneg hε.le hcos
  have hdrop : corner Q<corner P := by
    have hh := mul_pos hε (show 0<2*P.2.1+1-ε by linarith)
    dsimp [corner,Q]
    nlinarith
  refine ⟨Q,?_,rfl,rfl,hbQ,by dsimp [Q]; linarith,hdrop⟩
  refine {
    b_nonneg := hbQ.le
    sorted := by dsimp [Q]; linarith [hp.sorted]
    angle := ⟨le_rfl,hangle.1⟩
    circle := hdrop.le.trans hp.circle
    DE := ?_
    EH := ?_ }
  · simp [Q,W,deValue]
    linarith
  · have hh := hp.EH
    dsimp only [ehValue] at hh
    simp only [hPangle,sub_zero] at hh
    dsimp only [Q,ehValue]
    simp only [sub_zero]
    linarith

end EInteriorGeometry

namespace SignedCycle
open Candidate

/-- The strict loss is on the original E circle.  No common-circle
lift is used at any stage of this primary outside branch. -/
theorem HardInput.reduce_nonpositive_below_primary {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D)
    (hDE3 : I.cycle.Feasible D 3) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E=I.cycle.theta D ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (J.cycle.point E).circle<(I.cycle.point E).circle ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  obtain ⟨P,hP,hPangle,hPcircle,hPb,hPDE,hPEH⟩ :=
    I.nonpositive_below_primary_state hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD hED hDE3
  obtain ⟨Q,hQ,hQangle,hQa,hQb,hQbP,hQcircle⟩ :=
    EInteriorGeometry.lower_tangent_at_D (by linarith [hb.span_lt]) hP hPangle hPb.1 hPDE
  let J := I.fromNonpositiveEInterior hcap hb hQ
  have hfixed (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle Q i hi
  have hJcircle : (J.cycle.point E).circle<(I.cycle.point E).circle := by
    rw [show (J.cycle.point E).circle=EInteriorGeometry.corner Q from
      eInteriorCycle_circle hQ.b_nonneg]
    exact hQcircle.trans_eq hPcircle
  have hJframe : J.cycle.theta E=I.cycle.theta D := by
    change I.cycle.theta D+Q.2.2=I.cycle.theta D
    rw [hQangle]
    ring
  have hnon : AnchorNonincrease I.cycle J.cycle := by
    intro i hi
    by_cases hiE : i=E
    · subst i; exact hJcircle.le
    · rw [(hfixed i hiE).1]
  have hstrict : StrictAnchorLoss I.cycle J.cycle :=
    ⟨E,by norm_num [anchorVertices,E],hJcircle⟩
  exact ⟨J,hfixed,hJframe,hnon,hstrict,hJcircle,
    eInteriorCycle_DE (by linarith [hb.span_lt]) hQ,
    eInteriorCycle_EH (by linarith [hb.span_lt]) hQ⟩

end SignedCycle
end SquaresInCircles.Eight
