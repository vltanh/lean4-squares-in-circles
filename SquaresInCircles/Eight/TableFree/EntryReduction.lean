module

public import SquaresInCircles.Eight.GeometricModel.SharpAssembly

/-!
# Concrete table-free sharp entry on the unchanged original source

This replaces the old via_capture entry adapter with the unconditional
source theorem proved by the global original-owner / same-q BT2 matrix.
The construction is made at the sharp radius, but the original-packing
radius is retained separately. The source and recovered representatives
keep their initially selected physical normals.

Only implications actually obtained from original source equality are
stated here. In particular there is no hypothetical captured owner set,
no generated \`Candidate.capture\`, no terminal-owner restriction asserted
from an unproved frame comparison, and no claim that moved necessary
cycles are physical packings.

Uncompiled Lean source: do not confuse its closed proof terms with
kernel verification.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open ExactFamily Coordinates Candidate GeometricModel

/-- The stationary physical axis on each edge H,G,A,B,T,D,E. -/
def stationaryOwner : Vertex → Fin 4 := ![0,0,0,2,0,2,1]

theorem stationaryOwner_mem_terminal (i : Vertex) :
    stationaryOwner i∈terminalOwners i := by
  fin_cases i <;> simp [stationaryOwner,terminalOwners]

/-- Real feasibility of the stationary normal on the same physical
record, including all zero weak ties. It is deduced from the originally
selected feasible normal and its proven equality, not asserted. -/
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

/-- Physical frame and originally selected-normal equality on both
unchanged source and recovered boundary, with actual weak stationary
witnesses. No selection of a new G/T endpoint is made in this theorem. -/
theorem recovered_source_entry_table_free {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar)
    (hselected : N.source.selected=N.recovered.selected) :
    sourceLevel qStar=qStar ∧
      StationaryFrames sharpData N.recovered.square ∧
      StationaryFrames sharpData N.source.square ∧
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
  obtain ⟨hsource,hnsource⟩ := table_free_sharp_source_entry N hselected
  have hrecovered : StationaryFrames sharpData N.recovered.square :=
    frames_of_same_frames
      (fun i => ⟨(source_recovered_frames N i).1.symm,
        (source_recovered_frames N i).2.symm⟩) hsource
  have hnrecovered (i : Vertex) :
      (N.recovered.selected i).normal (N.recovered.square i)
        (N.recovered.square (next i))=stationaryNormal sharpData i :=
    (source_retained_recovered_normal N hselected i).symm.trans
      (hnsource i)
  exact ⟨sharp_source_level,hrecovered,hsource,
    stationary_witnesses_admitted N.recovered.toNeighborCycle
      hrecovered hnrecovered,
    stationary_witnesses_admitted N.source hsource hnsource,
    source_selected_feasible_on_recovered N hselected,
    hnrecovered,hnsource⟩

/-- The two original hard edge axes GA0 and BT2 are *genuinely*
feasible on the untouched source at sharp equality. -/
theorem original_hard_owners_table_free {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) :
    (forwardAxis 0).Feasible (N.source.square 1) (N.source.square 2) ∧
      (forwardAxis 2).Feasible (N.source.square 3) (N.source.square 4) := by
  obtain ⟨hf,hn⟩ := table_free_sharp_source_entry N N.source_selected
  have h := stationary_witnesses_admitted N.source hf hn
  constructor
  · simpa [stationaryOwner,next] using h (1 : Vertex)
  · simpa [stationaryOwner,next] using h (3 : Vertex)

/-- Fresh sharp representative retaining the original radius and
initially selected witnesses. Every displayed conclusion is justified
directly by the table-free source entry, with no capture compatibility. -/
theorem fresh_sharp_entry_table_free {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q≤qStar) :
    ∃ N : GlobalNormalization S qStar,
      SqPacking N.squares (0,0) q ∧
      N.source.selected=N.recovered.selected ∧
      sourceLevel qStar=qStar ∧
      StationaryFrames sharpData N.recovered.square ∧
      StationaryFrames sharpData N.source.square ∧
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
  obtain ⟨N,hN,hselected⟩ :=
    fresh_normalization_with_retained_source_exists hp hq
  exact ⟨N,hN,hselected,recovered_source_entry_table_free N hselected⟩

end SquaresInCircles.Eight.TableFree
