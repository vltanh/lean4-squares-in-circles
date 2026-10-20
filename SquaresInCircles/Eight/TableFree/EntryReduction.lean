module

public import SquaresInCircles.Eight.GeometricModel.SharpAssembly

/-!
# The sharp entry conclusion and its concrete compatibility proof

Uncompiled source draft.

There are three distinct assertions about the formalization:

1. Mathematical conclusion. A fresh recovered boundary at qStar has zero
   mismatch, stationary physical frames, the terminal restriction on every
   weak feasible owner, and actual weak stationary witnesses. Its unchanged
   original source has the same stationary physical frames and the actual
   stationary witnesses, including GA0 and BT2. The initially retained signed
   normals are the stationary normals on both records.
2. Existing proof route. The theorems whose names end in via_capture below
   prove that conclusion concretely using Candidate.capture and conditional
   boundary equality through GeometricModel.SharpAssembly. Their inherited
   generated affine/owner dependencies are intentional and explicit.
3. Alternate hand proof route. The same-radius G/T transports, global
   positive/negative terminal exclusions, and source-aware hard-owner
   recovery in the completed hand proof have not yet been transcribed.
   Replacing capture by those arguments is a dependency replacement for
   these already stated mathematical conclusions. This file does not claim
   that replacement has been completed.

No conclusion-shaped hypothesis, axiom, or admission is used by the public
entry theorems. Their premises are an actual packing and its actual squared
radius bound, or a constructed normalization with the explicitly retained
selection equality. The remaining TableFree.SharpSourceEntry interface in
SharpEntry has the concrete compatibility_source_entry implementation.

The recovered record itself is used throughout. No G/T comparison endpoint
is identified with its ancestor, and no old outer state is relabeled as an
outer state at a new radius.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open ExactFamily Coordinates Candidate GeometricModel

/-- One stationary witness on each edge H,G,A,B,T,D,E. At aligned
edges its other allowed terminal owner has the same physical normal. -/
def stationaryOwner : Vertex → Fin 4 := ![0,0,0,2,0,2,1]

theorem stationaryOwner_mem_terminal (i : Vertex) :
    stationaryOwner i ∈ terminalOwners i := by
  fin_cases i <;> simp [stationaryOwner,terminalOwners]

/-- The stationary axes are genuinely feasible weak witnesses on this same
record. This follows from the retained physical normal, not from choosing a
new comparison packing. -/
theorem stationary_witnesses_admitted {q : ℝ} (C : NeighborCycle q)
    (hf : StationaryFrames sharpData C.square)
    (hn : ∀ i, (C.selected i).normal (C.square i) (C.square (next i)) =
      stationaryNormal sharpData i) :
    ∀ i, (forwardAxis (stationaryOwner i)).Feasible
      (C.square i) (C.square (next i)) := by
  intro i
  have h := C.feasible i
  change SAT.threshold (C.square i) (C.square (next i)) ≤
    dot ((C.selected i).normal (C.square i) (C.square (next i)))
      (sub (C.square (next i)).center (C.square i).center) at h
  change SAT.threshold (C.square i) (C.square (next i)) ≤
    dot ((forwardAxis (stationaryOwner i)).normal
      (C.square i) (C.square (next i)))
      (sub (C.square (next i)).center (C.square i).center)
  rw [terminal_owner_normal hf i (stationaryOwner i)
    (stationaryOwner_mem_terminal i)]
  rwa [hn i] at h

/-- Complete explicit sharp-entry statement, with an actual compatibility
proof. Its source and recovered axes are the initially retained axes. -/
theorem recovered_source_entry_via_capture {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar)
    (hselected : N.source.selected=N.recovered.selected) :
    sourceLevel qStar=qStar ∧
      mismatch (N.frame.pullback N.expansion).theta=0 ∧
      StationaryFrames sharpData N.recovered.square ∧
      StationaryFrames sharpData N.source.square ∧
      OwnerRestriction N.recovered terminalOwners ∧
      (∀ i, (forwardAxis (stationaryOwner i)).Feasible
        (N.recovered.square i) (N.recovered.square (next i))) ∧
      (∀ i, (forwardAxis (stationaryOwner i)).Feasible
        (N.source.square i) (N.source.square (next i))) ∧
      (∀ i, (N.source.selected i).Feasible
        (N.recovered.square i) (N.recovered.square (next i))) ∧
      (∀ i, (N.recovered.selected i).normal (N.recovered.square i)
        (N.recovered.square (next i))=stationaryNormal sharpData i) ∧
      (∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=stationaryNormal sharpData i) := by
  obtain ⟨hS,ht,howners⟩ := compatibility_boundary_equality N
  obtain ⟨hsource,hsourceNormal⟩ := compatibility_source_witnesses N
  have hrecovered : StationaryFrames sharpData N.recovered.square :=
    frames_of_same_frames
      (fun i => ⟨(source_recovered_frames N i).1.symm,
        (source_recovered_frames N i).2.symm⟩) hsource
  have hownersRecovered : OwnerRestriction N.recovered terminalOwners := by
    intro i j h
    exact howners i j
      (N.expansion.preserves_all_axes i (forwardAxis j) h)
  have hrecoveredNormal (i : Vertex) :
      (N.recovered.selected i).normal (N.recovered.square i)
        (N.recovered.square (next i))=stationaryNormal sharpData i :=
    (source_retained_recovered_normal N hselected i).symm.trans
      (hsourceNormal i)
  exact ⟨sharp_source_level,hS,hrecovered,hsource,hownersRecovered,
    stationary_witnesses_admitted N.recovered.toNeighborCycle
      hrecovered hrecoveredNormal,
    stationary_witnesses_admitted N.source hsource hsourceNormal,
    source_selected_feasible_on_recovered N hselected,
    hrecoveredNormal,hsourceNormal⟩

/-- In particular, the two hard primary witnesses already hold on the
unchanged original source. This is an actual feasibility conclusion. -/
theorem original_hard_owners_via_capture {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) :
    (forwardAxis 0).Feasible (N.source.square 1) (N.source.square 2) ∧
      (forwardAxis 2).Feasible (N.source.square 3) (N.source.square 4) := by
  obtain ⟨hf,hn⟩ := compatibility_source_witnesses N
  have h := stationary_witnesses_admitted N.source hf hn
  constructor
  · simpa [stationaryOwner,next] using h (1 : Vertex)
  · simpa [stationaryOwner,next] using h (3 : Vertex)

/-- The unconditional fresh-boundary entry theorem. Original containment is
retained at q, while the new boundary is constructed at qStar. The only
proof-route qualification is the explicitly named capture implementation. -/
theorem fresh_sharp_entry_via_capture {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ qStar) :
    ∃ N : GlobalNormalization S qStar,
      SqPacking N.squares (0,0) q ∧
      N.source.selected=N.recovered.selected ∧
      sourceLevel qStar=qStar ∧
      mismatch (N.frame.pullback N.expansion).theta=0 ∧
      StationaryFrames sharpData N.recovered.square ∧
      StationaryFrames sharpData N.source.square ∧
      OwnerRestriction N.recovered terminalOwners ∧
      (∀ i, (forwardAxis (stationaryOwner i)).Feasible
        (N.recovered.square i) (N.recovered.square (next i))) ∧
      (∀ i, (forwardAxis (stationaryOwner i)).Feasible
        (N.source.square i) (N.source.square (next i))) ∧
      (∀ i, (N.source.selected i).Feasible
        (N.recovered.square i) (N.recovered.square (next i))) ∧
      (∀ i, (N.recovered.selected i).normal (N.recovered.square i)
        (N.recovered.square (next i))=stationaryNormal sharpData i) ∧
      (∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=stationaryNormal sharpData i) := by
  obtain ⟨N,hN,hselected⟩ := fresh_normalization_with_retained_source_exists hp hq
  exact ⟨N,hN,hselected,recovered_source_entry_via_capture N hselected⟩

end SquaresInCircles.Eight.TableFree
