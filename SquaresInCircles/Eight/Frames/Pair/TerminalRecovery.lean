module

public import SquaresInCircles.Eight.Owners.BinaryDiagonalExclusion
public import SquaresInCircles.Eight.Frames.Pair.TerminalDescendant
public import SquaresInCircles.Eight.Boundary.UniversalSourceRecovery

/-!
# Eight squares: the hard owners after the two pair moves, and the source

The exclusion of the binary words rules out the two diagonal cases on the cycle after the two
pair moves, at the same level (`G_negative_not_diagonal`, `T_positive_not_diagonal`), so the
terminal matrix gives hard owners on that cycle (`hard`). With pair moves that keep track of their
source, the contacts that they keep recover the hard axes on the input itself, which the moves
leave unchanged and which is sharp (`source_recovery`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.PairTerminalDescendant
open Set Candidate SignedCycle Stationary GeometricModel

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

/-- A normalized boundary input at a level in `[qLow, qStar]`, with pair moves that keep track of
their source, has hard owners, is left unchanged by the moves, and is sharp; the diagonal cases
are excluded inside the proof. -/
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

end SquaresInCircles.Eight.PairTerminalDescendant
