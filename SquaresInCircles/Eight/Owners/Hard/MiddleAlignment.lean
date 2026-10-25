module

public import SquaresInCircles.Eight.Words.Wrong.SignCapture
public import SquaresInCircles.Eight.Words.Middle.Canonicalization

/-!
# Eight squares: aligning the middle of a hard cycle

The frame order of G and T and the bounds `1/10` on their tangents follow from the hard geometry,
and they feed the replacement of A and B. Every hard input has a hard input at the same `q` with
the common middle frame of A and B between those of T and G and `A.y - B.y = 1`; no anchor circle
increases, the loss is strict when the original middle is not canonical, and the other five
vertices keep their points and frames (`HardInput.canonicalize_middle`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

/-- Every hard input has a hard input with the normalized common middle; no sign bound or frame
order of G and T is assumed. -/
theorem HardInput.canonicalize_middle {q : ℝ} (I : HardInput q) (hq : q≤qCap) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta A∈Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta A≠I.cycle.theta B ∨ I.cycle.theta A<I.cycle.theta T ∨
        I.cycle.theta G<I.cycle.theta A ∨ 1<(I.cycle.point A).y-(I.cycle.point B).y) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  have horder := I.intermediate_order hq
  have hsigns := I.small_intermediate_signs hq
  exact I.canonicalize_middle_ordered hq hsigns.1.le hsigns.2.le horder.le

end SignedCycle
end SquaresInCircles.Eight
