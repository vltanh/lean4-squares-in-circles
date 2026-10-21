module

public import SquaresInCircles.Eight.GlobalNormalization
public import SquaresInCircles.Eight.TableFree.FramePhysicalTransport
public import SquaresInCircles.Eight.TableFree.GlobalZeroSignBridge

/-!
# Original-radius inputs from global normalization

The continuous frame estimate is instantiated on the actual recovered
boundary, at `sourceLevel q`.  Its points, selected weak axes and both
signed variation budgets are retained.  The larger-radius boundary is
used only for the already obtained frame and E sign.

The last constructor consumes the precise physical owner/anchor facts
still required from the global classifier.  It does not assume sharpness,
stationarity or feasibility of a newly selected hard primary owner.
The zero-owner strict signs are proved on the original recovered cycle.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NormalizationBridge
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

theorem recovered_data {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) (hq : q≤Q1) :
    (recoveredCycle N).Necessary (sourceLevel q) ∧
      (recoveredCycle N).Ordered ∧
      (recoveredCycle N).StrictSpread ∧
      positiveVariation (recoveredCycle N).theta<frameCap ∧
      negativeVariation (recoveredCycle N).theta<frameCap ∧
      (∀ i,((recoveredCycle N).point i).Boundary (sourceLevel q)) ∧
      (∀ i,(recoveredCycle N).actualSquare i=N.recovered.square i) :=
  FramePhysicalTransport.original_signed_data (recoveredFrame N) (source_radius_mem hq)

theorem recovered_E_nonpos {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) : ((recoveredCycle N).point E).y≤0 :=
  SignedCycle.E_nonpos_pullback N.frame N.expansion N.eHalf

theorem recovered_selected_axis {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) (i : Vertex) :
    N.recovered.selected i=forwardAxis (SignedCycle.retainedOwner (recoveredFrame N) i) :=
  SignedCycle.retainedOwner_axis (recoveredFrame N) i

theorem recovered_selected_feasible {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) (i : Vertex) :
    (recoveredCycle N).Feasible i (SignedCycle.retainedOwner (recoveredFrame N) i) :=
  SignedCycle.retainedOwner_feasible (recoveredFrame N) i

/-- Every weak source separator is represented, including simultaneous
ties.  This equivalence never promotes a separator of an expanded cycle. -/
theorem recovered_all_axes {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) (i : Vertex) (j : Fin 4) :
    (recoveredCycle N).Feasible i j ↔
      (forwardAxis j).Feasible (N.recovered.square i) (N.recovered.square (next i)) :=
  SignedCycle.atFrame_feasible (recoveredFrame N) i j

theorem source_recovered_same_frames {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) (i : Vertex) :
    SameFrame (N.source.square i) (N.recovered.square i) :=
  ⟨(N.source_frames i).1.trans (N.expansion.same_frames i).1,
    (N.source_frames i).2.trans (N.expansion.same_frames i).2⟩

/-- The signed input retains the initial physical normal even though the
original source centers need not equal the recovered boundary centers. -/
theorem original_selected_normal {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q)
    (hselected : N.source.selected=N.recovered.selected) (i : Vertex) :
    (forwardAxis (SignedCycle.retainedOwner (recoveredFrame N) i)).normal
      ((recoveredCycle N).actualSquare i) ((recoveredCycle N).actualSquare (next i))=
        (N.source.selected i).normal (N.source.square i) (N.source.square (next i)) := by
  have h := SignedCycle.retainedOwner_normal (recoveredFrame N) i
  change (forwardAxis (SignedCycle.retainedOwner (recoveredFrame N) i)).normal
    ((recoveredCycle N).actualSquare i) ((recoveredCycle N).actualSquare (next i))=_ at h
  rw [h]
  rw [hselected]
  exact (signed_normal_same_frames (source_recovered_same_frames N i)
    (source_recovered_same_frames N (next i)) (N.recovered.selected i)).symm

/-- The actual finite classifier supplies only owner sets, radial tags and
tangent signs.  All analytic, winding and variation fields are proved on
the original recovered record, with the original selected axes. -/
def normalizedInput {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S q) (hq : q≤Q1)
    (howners : Candidate.OwnerRestriction N.recovered SignedCycle.normalOwners)
    (houter : ∀ i∈({H,A,B,D} : Finset Vertex),N.recovered.kind i=.outer)
    (hH : 0≤N.recovered.tangent H) (hA : 0≤N.recovered.tangent A)
    (hB : N.recovered.tangent B≤0) (hD : N.recovered.tangent D≤0) :
    SignedCycle.NormalizedBoundaryInput (sourceLevel q) := by
  let F := recoveredFrame N
  let w := SignedCycle.retainedWitnesses F howners
  have hv := FramePhysicalTransport.candidate_variations F (source_radius_mem hq)
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
      H_nonneg := (SignedCycle.atFrame_y_nonneg_iff F H).2 hH
      A_nonneg := (SignedCycle.atFrame_y_nonneg_iff F A).2 hA
      B_nonpos := (SignedCycle.atFrame_y_nonpos_iff F B).2 hB
      D_nonpos := (SignedCycle.atFrame_y_nonpos_iff F D).2 hD }
    witnesses := w
    zero_signs := SignedCycle.atFrame_zero_signs F (source_radius_mem hq) w
    E_nonpos := recovered_E_nonpos N }

end SquaresInCircles.Eight.TableFree.NormalizationBridge
