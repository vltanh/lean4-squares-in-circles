module

public import SquaresInCircles.Eight.TableFree.PairTerminalDescendant
public import SquaresInCircles.Eight.TableFree.BinaryDiagonalExclusion

/-!
# Terminal recovery on the actual paired descendant

Uncompiled source. The complete binary-word exclusions rule out the two
nearest-axis diagonal leaves on the actual same-radius descendant. The
terminal matrix therefore applies without an additional diagonal premise.
The retained source contacts then recover the original cycle and its hard
axes, with the original anchor loss unchanged.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.PairTerminalDescendant
open Set Candidate SignedCycle ExactFamily GeometricModel

theorem hard {q : ℝ} (I : NormalizedBoundaryInput q)
    (hQL : qLow≤q) (hq : q≤qStar) (hcap : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D)) :
    (I.pairDescendant hcap OG OT).cycle.HardOwners := by
  have hmem : q∈Icc (5/2:ℝ) qCap :=
    ⟨le_trans (by norm_num [qLow]) hQL,hcap⟩
  let J := I.pairDescendant hcap OG OT
  exact hard_of_no_diagonal I hQL hq hcap OG OT
    (J.toBoundaryInput.G_negative_not_diagonal hmem)
    (J.toBoundaryInput.T_positive_not_diagonal hmem)

/-- Both original hard axes and all equality data are recovered from the
source-aware paired outputs. No diagonal exclusion is supplied by the
caller; both are proved on the same physical descendant. -/
theorem source_recovery {q : ℝ} (I : NormalizedBoundaryInput q)
    (hQL : qLow≤q) (hq : q≤qStar)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hcap : q≤qCap) :
    I.cycle.HardOwners ∧ (I.pairDescendant hcap SG.output ST.output).cycle=I.cycle ∧
      I.cycle.theta A=I.cycle.theta B ∧ (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hh := hard I hQL hq hcap SG.output ST.output
  exact I.pair_source_recovery hQL hq SG ST hcap hh.1 hh.2

end SquaresInCircles.Eight.TableFree.PairTerminalDescendant
