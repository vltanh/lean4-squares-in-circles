module

public import SquaresInCircles.Eight.Boundary.Reduction
public import SquaresInCircles.Eight.Boundary.Candidate.Model
public import SquaresInCircles.Eight.Stationary.CenterCompletion

/-!
# Eight squares: the stationary witnesses of seven squares

Seven squares `K` in the order H, G, A, B, T, D, E with the frames of a stationary chain `d`
(`StationaryFrames d K`) have the separation thresholds `stationaryWidth d` on their edges
(`threshold_of_stationary_frames`), and every terminal owner of an edge has the stationary
normal (`terminal_owner_normal`). The gaps of the dual of `OriginalDual` at the centres of `K`
are the slacks of the edges along these normals (`dual_gap_as_projection`); they are nonnegative
when the witnesses have the stationary normals (`gaps_of_retained_normals`). The anchor offsets
of `d` give vertices of the anchor squares, wherever their centres lie
(`anchor_offsets_closed`), and these vertices lie in the disk of squared radius `q` when the
squares do (`vertices_at_original_radius`). Normals and frames pass between two cycles of
squares with the same frames, whatever their centres (`normals_of_same_frames`,
`frames_of_same_frames`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Stationary Coordinates

/-- The cosines of the stationary frames, as quarter-turn representatives, in the order H, G, A,
B, T, D, E; `canonicalSin` gives the sines. -/
def canonicalCos (d : Coordinates) : Vertex → ℝ :=
  ![d.s,d.s,1,1,0,0,-1]

def canonicalSin (d : Coordinates) : Vertex → ℝ :=
  ![-d.c,-d.c,0,0,1,1,0]

def StationaryFrames (d : Coordinates) (K : Vertex → UnitSquare) : Prop :=
  ∀ i, (K i).cosine=canonicalCos d i ∧ (K i).sine=canonicalSin d i

/-- The forward normals of the edges in the stationary configuration, as vectors. -/
def stationaryNormal (d : Coordinates) : Vertex → Point :=
  ![d.e,d.e,(0,1),(-1,0),(-1,0),(0,-1),(d.s,-d.c)]

def stationaryWidth (d : Coordinates) (i : Vertex) : ℝ :=
  if i=1 ∨ i=6 then (1+d.c+d.s)/2 else 1

/-- The edges A–B, B–T, T–D, D–E, G–A, H–G, E–H of the dual, as edges of the cycle. -/
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

/-- With the stationary frames, every terminal owner of an edge has the stationary normal; on
G–A and E–H, between a turned and an axis-parallel square, the terminal owner is unique. -/
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

/-- The gaps of the dual at the centres of `K` are the slacks of the seven edges along the
stationary normals. -/
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

/-- With the stationary frames, the anchor offsets of `d` give vertices of the anchor squares,
wherever their centres lie. -/
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

/-- If the squares lie in the disk of squared radius `q`, so do the anchor vertices. -/
theorem vertices_at_original_radius {d : Coordinates} {q : ℝ}
    {K : Vertex → UnitSquare} (hf : StationaryFrames d K)
    (hc : ∀ i p, closedSquare (K i) p → normSq p ≤ q) :
    ∀ i : Fin 5,
      normSq (add
        (OriginalDual.ofCycle (fun j => (K j).center) i.castSucc.castSucc)
        (d.anchorOffsets i)) ≤ q :=
  fun i => hc _ _ (anchor_offsets_closed hf i)

/-- The stationary normals of the witnesses pass between two cycles of squares with the same
frames; their centres may differ. -/
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

end SquaresInCircles.Eight
