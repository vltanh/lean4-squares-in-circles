module

public import SquaresInCircles.Eight.Boundary.Normalization
public import SquaresInCircles.Eight.Owners.Outer.AnchorBridge

/-!
# Eight squares: inputs at the original radius from the global normalization

The continuous frame estimate is applied to the recovered boundary at `sourceLevel q`
(`recoveredFrame`, `recoveredCycle`), with its points, selected weak axes and both signed
variation budgets; the boundary at the larger radius serves only for the frame and the sign of E
(`recovered_E_nonpos`).

Given that every owner is a normal owner, `normalizedInput` is a normalized boundary input: the
four radial anchors, their strict signs and the strict signs of the zero owners are proved on the
recovered cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NormalizationBridge
open Candidate

def recoveredFrame {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) : Candidate.Frame N.recovered :=
  N.frame.pullback N.expansion

def recoveredCycle {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) : SignedCycle :=
  SignedCycle.atFrame (recoveredFrame N)

theorem source_radius_mem {q : ℝ} (hq : q≤Q1) :
    sourceLevel q∈Icc (5/2:ℝ) Q0 := by
  have h := sourceLevel_bounds hq
  exact ⟨h.2.2.1.1,h.2.2.2.trans radius_levels.2.2.1.le⟩

theorem recovered_E_nonpos {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) : ((recoveredCycle N).point E).y≤0 :=
  SignedCycle.E_nonpos_pullback N.frame N.expansion N.eHalf

/-- The normalized boundary input at `sourceLevel q` of a global normalization whose owners are all
normal owners; every other field is proved on the recovered cycle and its selected axes. -/
def normalizedInput {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) (hq : q≤Q1)
    (howners : Candidate.OwnerRestriction N.recovered SignedCycle.normalOwners) :
    SignedCycle.NormalizedBoundaryInput (sourceLevel q) := by
  let F := recoveredFrame N
  let w := SignedCycle.retainedWitnesses F howners
  have hv := FramePhysicalTransport.candidate_variations F (source_radius_mem hq)
  have ha := GlobalOuterAnchor.normal_anchors F (source_radius_mem hq) howners
  have houter := GlobalOuterAnchor.normal_outer F (source_radius_mem hq) howners
  exact {
    cycle := recoveredCycle N
    necessary := SignedCycle.atFrame_necessary F
    ordered := SignedCycle.atFrame_ordered F
    strict_spread := SignedCycle.atFrame_strictSpread F
    positive_variation := hv.1
    negative_variation := hv.2
    radial := SignedCycle.atFrame_boundary F
    anchors_outer := fun i hi => SignedCycle.atFrame_outer_of_kind F i (houter i hi)
    anchors_normal := {
      H_nonneg := (SignedCycle.atFrame_y_nonneg_iff F H).2 ha.1.2.le
      A_nonneg := (SignedCycle.atFrame_y_nonneg_iff F A).2 ha.2.1.2.le
      B_nonpos := (SignedCycle.atFrame_y_nonpos_iff F B).2 ha.2.2.1.2.le
      D_nonpos := (SignedCycle.atFrame_y_nonpos_iff F D).2 ha.2.2.2.2.le }
    witnesses := w
    zero_signs := SignedCycle.atFrame_zero_signs F (source_radius_mem hq) w
    E_nonpos := recovered_E_nonpos N }

end SquaresInCircles.Eight.NormalizationBridge
