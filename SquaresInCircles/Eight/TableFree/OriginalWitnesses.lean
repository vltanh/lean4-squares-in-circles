module

public import SquaresInCircles.Eight.BoundaryReduction
public import SquaresInCircles.Eight.Candidate.Model
public import SquaresInCircles.Eight.ExactFamily.CenterCompletion

/-!
# Stationary physical witnesses on the original centers

Uncompiled source draft.

This is the algebraic interface in Sections 5--6 of
HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md.
It uses actual signed normals and actual vertices. No motion of centers is
inverted, and no preservation of individual center rays is assumed.

The lemmas here do not prove the global primary-owner entry theorem. Their
inputs are explicit frames and retained physical normals. The concrete
compatibility implementation in GeometricModel.SharpAssembly supplies those
inputs using the existing conditional capture theorem; its generated
dependencies are documented there.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open ExactFamily Coordinates

/-- Canonical quarter-turn representatives, in cyclic order H,G,A,B,T,D,E. -/
def canonicalCos (d : Coordinates) : Vertex → ℝ :=
  ![d.s,d.s,1,1,0,0,-1]

def canonicalSin (d : Coordinates) : Vertex → ℝ :=
  ![-d.c,-d.c,0,0,1,1,0]

def StationaryFrames (d : Coordinates) (K : Vertex → UnitSquare) : Prop :=
  ∀ i, (K i).cosine=canonicalCos d i ∧ (K i).sine=canonicalSin d i

/-- The physical forward normal, rather than an owner number in a chart. -/
def stationaryNormal (d : Coordinates) : Vertex → Point :=
  ![d.e,d.e,(0,1),(-1,0),(-1,0),(0,-1),(d.s,-d.c)]

def stationaryWidth (d : Coordinates) (i : Vertex) : ℝ :=
  if i=1 ∨ i=6 then (1+d.c+d.s)/2 else 1

/-- Conversion from the dual's AB,BT,TD,DE,GA,HG,EH order to cycle edges. -/
def dualEdge : Fin 7 → Vertex := ![2,3,4,5,1,0,6]

theorem threshold_of_stationary_frames {d : Coordinates}
    (hw : d.WeightDomain) {K : Vertex → UnitSquare}
    (hf : StationaryFrames d K) (i : Vertex) :
    SAT.threshold (K i) (K (next i))=stationaryWidth d i := by
  have hc (j : Vertex) := (hf j).1
  have hs (j : Vertex) := (hf j).2
  have hu : d.s^2+d.c^2=1 := by linarith [d.unit]
  have hz : d.c*d.s+-(d.s*d.c)=0 := by ring
  fin_cases i <;>
    simp [stationaryWidth,SAT.threshold,relativeC,relativeS,hc,hs,
      canonicalCos,canonicalSin,next,← pow_two,
      abs_of_pos hw.c_pos,abs_of_pos hw.s_pos,abs_neg,hu,hz] <;> ring

/-- Aligned terminal owner alternatives have the same physical signed normal.
The two mixed edges have their single retained stationary owner. -/
theorem terminal_owner_normal {d : Coordinates} {K : Vertex → UnitSquare}
    (hf : StationaryFrames d K) (i : Vertex) (j : Fin 4)
    (hj : j ∈ Candidate.terminalOwners i) :
    (forwardAxis j).normal (K i) (K (next i))=stationaryNormal d i := by
  have hc (k : Vertex) := (hf k).1
  have hs (k : Vertex) := (hf k).2
  fin_cases i <;> fin_cases j <;>
    simp [Candidate.terminalOwners] at hj <;>
    simp [forwardAxis,SignedAxis.normal,AxisOwner.normal,AxisSign.value,
      stationaryNormal,canonicalCos,canonicalSin,next,hc,hs,scale,
      Eight.e,Eight.f,Coordinates.e]

/-- The original dual is exactly the seven physical witness slacks. -/
theorem dual_gap_as_projection (d : Coordinates) (K : Vertex → UnitSquare)
    (e : Fin 7) :
    OriginalDual.gap d (OriginalDual.ofCycle (fun i => (K i).center)) e =
      dot (stationaryNormal d (dualEdge e))
        (sub (K (next (dualEdge e))).center (K (dualEdge e)).center) -
      stationaryWidth d (dualEdge e) := by
  fin_cases e <;>
    simp [OriginalDual.gap,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      dualEdge,stationaryNormal,stationaryWidth,next,Coordinates.e,
      Coordinates.f,dot,sub] <;> ring

theorem gaps_of_retained_normals {d : Coordinates} (hw : d.WeightDomain)
    {K : Vertex → UnitSquare} (hf : StationaryFrames d K)
    (selected : Vertex → SignedAxis)
    (hfeasible : ∀ i, (selected i).Feasible (K i) (K (next i)))
    (hnormal : ∀ i, (selected i).normal (K i) (K (next i)) =
      stationaryNormal d i) :
    ∀ e : Fin 7, 0 ≤
      OriginalDual.gap d (OriginalDual.ofCycle (fun i => (K i).center)) e := by
  intro e
  rw [dual_gap_as_projection]
  have h := hfeasible (dualEdge e)
  change SAT.threshold (K (dualEdge e)) (K (next (dualEdge e))) ≤
    dot ((selected (dualEdge e)).normal
      (K (dualEdge e)) (K (next (dualEdge e))))
      (sub (K (next (dualEdge e))).center (K (dualEdge e)).center) at h
  rw [threshold_of_stationary_frames hw hf,hnormal] at h
  exact sub_nonneg.mpr h

/-- These offsets are vertices of the original squares even when their
centers no longer lie in the signed charts of a boundary representative. -/
theorem anchor_offsets_closed {d : Coordinates} {K : Vertex → UnitSquare}
    (hf : StationaryFrames d K) (i : Fin 5) :
    closedSquare (K (OriginalDual.cycleIndex i.castSucc.castSucc))
      (add (OriginalDual.ofCycle (fun j => (K j).center) i.castSucc.castSucc)
        (d.anchorOffsets i)) := by
  have hc (j : Vertex) := (hf j).1
  have hs (j : Vertex) := (hf j).2
  fin_cases i <;> constructor <;> apply abs_le.mpr <;> constructor <;>
    simp [localX,localY,OriginalDual.ofCycle,
      OriginalDual.cycleIndex,anchorOffsets,inFrame,add,hc,hs,
      canonicalCos,canonicalSin] <;>
    nlinarith [d.unit]

/-- Original containment is evaluated at its original squared ceiling q,
independently of the ceiling used to construct a boundary representative. -/
theorem vertices_at_original_radius {d : Coordinates} {q : ℝ}
    {K : Vertex → UnitSquare} (hf : StationaryFrames d K)
    (hc : ∀ i p, closedSquare (K i) p → normSq p ≤ q) :
    ∀ i : Fin 5,
      normSq (add
        (OriginalDual.ofCycle (fun j => (K j).center) i.castSucc.castSucc)
        (d.anchorOffsets i)) ≤ q :=
  fun i => hc _ _ (anchor_offsets_closed hf i)

/-- The recession construction retains the initially chosen normal before
and after its quarter-turn recoding. This is not a statement about rays. -/
theorem reduction_retains_initial_normal {q : ℝ} {C : NeighborCycle q}
    (R : BoundaryReduction C) (i : Vertex) :
    (R.result.selected i).normal (R.result.square i)
        (R.result.square (next i)) =
      (C.selected i).normal (C.square i) (C.square (next i)) := by
  rw [R.axis_transport,R.raw_selected]
  exact signed_normal_same_frames (R.raw_frames i) (R.raw_frames (next i))
    (C.selected i)

/-- Transfer a known physical normal between equal-frame records. The
centers of those records need not coincide. -/
theorem normals_of_same_frames {d : Coordinates}
    {K L : Vertex → UnitSquare} {a b : Vertex → SignedAxis}
    (hf : ∀ i, SameFrame (K i) (L i)) (ha : a=b)
    (hn : ∀ i, (b i).normal (L i) (L (next i))=stationaryNormal d i) :
    ∀ i, (a i).normal (K i) (K (next i))=stationaryNormal d i := by
  intro i
  rw [ha,signed_normal_same_frames (hf i) (hf (next i))]
  exact hn i

theorem frames_of_same_frames {d : Coordinates} {K L : Vertex → UnitSquare}
    (hKL : ∀ i, SameFrame (K i) (L i))
    (hL : StationaryFrames d L) : StationaryFrames d K :=
  fun i => ⟨(hKL i).1.trans (hL i).1,(hKL i).2.trans (hL i).2⟩

end SquaresInCircles.Eight.TableFree
