module

public import SquaresInCircles.Eight.Owners.Nonpositive.BelowPrimary
public import SquaresInCircles.Eight.Owners.Nonpositive.BelowRotated

/-!
# Eight squares: exhaustive original mixed-owner E ordering for nonpositive outer composites

The original E may begin at any frame in
the actual spread interval and may retain either allowed mixed owner.
Above H is excluded.  Each below-D owner has its concrete original-circle
descent with strict E loss.  An E already between D and H retains its
literal point and frame, and its actual radial alternative supplies
both primary axes there.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate

theorem HardInput.order_nonpositive_E {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E∈Icc (I.cycle.theta D) (I.cycle.theta H) ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta E<I.cycle.theta D → StrictAnchorLoss I.cycle J.cycle) ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  have hEHorder := I.nonpositive_E_le_H hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
  by_cases hbelow : I.cycle.theta E<I.cycle.theta D
  · have hj : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
      simpa [normalOwners,D] using I.witnesses.allowed D
    have hendpoint : ∃J : HardInput q,
        (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
        J.cycle.theta E=I.cycle.theta D ∧
        AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
        (J.cycle.point E).circle<(I.cycle.point E).circle ∧
        J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
      rcases hj with hj | hj
      · have hDE : I.cycle.Feasible D 2 := by simpa [hj] using I.witnesses.feasible D
        exact I.reduce_nonpositive_below_rotated hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
          hbelow hDE
      · have hDE : I.cycle.Feasible D 3 := by simpa [hj] using I.witnesses.feasible D
        exact I.reduce_nonpositive_below_primary hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
          hbelow hDE
    obtain ⟨J,hfixed,hframe,hnon,hstrict,hcircle,hDE,hEH⟩ := hendpoint
    refine ⟨J,hfixed,?_,hnon,fun _ => hstrict,hDE,hEH⟩
    rw [hframe]
    exact ⟨le_rfl,sub_nonneg.mp hb.span_nonneg⟩
  · have hDEorder : I.cycle.theta D≤I.cycle.theta E := le_of_not_gt hbelow
    have hDE := I.nonpositive_DE_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hDEorder
    have hEH := I.nonpositive_EH_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hEHorder
    exact ⟨I,fun _ _ => ⟨rfl,rfl⟩,⟨hDEorder,hEHorder⟩,
      anchorNonincrease_refl I.cycle,fun h => (hbelow h).elim,hDE,hEH⟩

end SquaresInCircles.Eight.SignedCycle
