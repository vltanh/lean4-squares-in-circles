module

public import SquaresInCircles.Eight.Owners.Nonpositive.BelowRotatedState

/-!
# Eight squares: strict original E-circle loss after the rotated DE2 descent

At the actual E=D contact, the primary
decreases by an explicit amount bounded by its sorting margin and the
strict actual EH reserve.  DE remains exact.  The resulting same-q
hard cycle keeps all non-E points and frames literal, and its E circle
is strictly smaller than the original source E circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace EInteriorGeometry

theorem lower_primary_at_D {h d α q : ℝ} {P : State}
    (hp : Feasible h d α q P) (hPangle : P.2.2=0)
    (hsort : P.2.1<P.1) (hEH : W (α-P.2.2)<ehValue h α P) :
    ∃Q : State, Feasible h d α q Q ∧ Q.2.2=0 ∧ Q.2.1=P.2.1 ∧
      Q.1<P.1 ∧ corner Q<corner P := by
  let ε : ℝ := min ((P.1-P.2.1)/4) (ehSlack h α P/2)
  have hslack : 0<ehSlack h α P := sub_pos.mpr hEH
  have hε : 0<ε := lt_min (by linarith) (by linarith)
  have hεsort : ε≤(P.1-P.2.1)/4 := min_le_left _ _
  have hεEH : ε≤ehSlack h α P/2 := min_le_right _ _
  let Q : State := (P.1-ε,P.2.1,0)
  have hdrop : corner Q<corner P := by
    have hh := mul_pos hε (show 0<2*P.1+1-ε by linarith [hp.b_nonneg])
    dsimp [Q,corner]
    nlinarith
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le_one α) hε.le
  refine ⟨Q,?_,rfl,rfl,by dsimp [Q]; linarith,hdrop⟩
  refine {
    b_nonneg := hp.b_nonneg
    sorted := by dsimp [Q]; linarith
    angle := ⟨le_rfl,by simpa [hPangle] using hp.angle.2⟩
    circle := hdrop.le.trans hp.circle
    DE := ?_
    EH := ?_ }
  · have hh := hp.DE
    simpa [Q,deValue,W,hPangle] using hh
  · have hh := hp.EH
    dsimp [ehSlack] at hεEH
    dsimp [Q,ehValue] at hh hεEH ⊢
    simp only [hPangle,sub_zero] at hh hεEH ⊢
    nlinarith

end EInteriorGeometry

namespace SignedCycle
open Candidate

theorem HardInput.reduce_nonpositive_below_rotated {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D) (hDE2 : I.cycle.Feasible D 2) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E=I.cycle.theta D ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (J.cycle.point E).circle<(I.cycle.point E).circle ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  obtain ⟨P,hP,hPangle,hPcircle,hPb,hPDE,hPEH⟩ :=
    I.nonpositive_below_rotated_state hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD hED hDE2
  have hsort := EInteriorGeometry.strict_sorting_wide hcap
    ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hP
  obtain ⟨Q,hQ,hQangle,hQb,hQa,hQcircle⟩ :=
    EInteriorGeometry.lower_primary_at_D hP hPangle hsort hPEH
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
