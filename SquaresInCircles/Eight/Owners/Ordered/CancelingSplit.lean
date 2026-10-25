module

public import SquaresInCircles.Eight.Owners.Hard.SplitCycle

/-!
# Eight squares: the canceling outer reduction followed by the hard split

The outer construction at the same `q` is followed by the split of the hard cap
(`HardInput.split_with_source_loss`). Strict losses are measured against the original circles of
the anchors, also when a second reduction follows; H, D and E, their frames, and both slacks of the
mixed axes stay.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

/-- The split, improved exactly when the common frame is interior: no anchor circle increases, and
the loss is strict when the frame lies strictly between those of T and G. -/
theorem HardInput.split_with_source_loss {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta G)
    (hright : I.cycle.theta T≤I.cycle.theta A) :
    ∃ J : HardInput q,
      (J.cycle.theta A=J.cycle.theta G ∨ J.cycle.theta A=J.cycle.theta T) ∧
      J.cycle.theta A=J.cycle.theta B ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta A<I.cycle.theta G ∧ I.cycle.theta T<I.cycle.theta A →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧
        J.cycle.theta i=I.cycle.theta i) := by
  by_cases hi : I.cycle.theta A<I.cycle.theta G ∧ I.cycle.theta T<I.cycle.theta A
  · obtain ⟨J,hend,hAB',hnon,hstrict,hA,hB,hfixed⟩ :=
      I.exists_split_strict_loss hq hHG hAB hTD hi.1 hi.2
    exact ⟨J,hend,hAB',hnon,(fun _ => hstrict),hfixed⟩
  · obtain ⟨J,hend,hAB',hcircle,hfixed⟩ :=
      I.exists_split_aligned hq hHG hAB hTD hleft hright
    refine ⟨J,hend,hAB',?_,(fun h => (hi h).elim),hfixed⟩
    intro i _
    exact (hcircle i).le

end SignedCycle
end SquaresInCircles.Eight
