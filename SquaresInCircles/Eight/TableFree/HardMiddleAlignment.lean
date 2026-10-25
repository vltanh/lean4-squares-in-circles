module

public import SquaresInCircles.Eight.TableFree.WrongSignCapture
public import SquaresInCircles.Eight.TableFree.MiddleCanonicalization

/-!
# Unconditional middle alignment in the necessary hard class

Uncompiled source draft.  The signed front end now proves the original
G/T frame order and both one-tenth tangent bounds from the actual hard
geometry.  They are immediately used by the concrete A/B replacement.
The result retains separate anchor circle nonincrease, strict source
loss whenever the original middle is noncanonical, and all five
unchanged vertices with their original frames.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace SignedCycle

/-- Every necessary hard input admits the actual normalized common
middle.  No G/T sign bound or frame order is an input. -/
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
end SquaresInCircles.Eight.TableFree
