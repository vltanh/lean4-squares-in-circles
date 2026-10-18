module

public import SquaresInCircles.Eight.GlobalNormalization
public import SquaresInCircles.Eight.Candidate.Capture
public import SquaresInCircles.Eight.ExactFamily.CentralParameters
public import SquaresInCircles.Eight.ExactFamily.BoxRigidity
public import SquaresInCircles.Eight.ExactFamily.StatementLink

/-!
# Eight squares: uniqueness

No packing of eight unit squares fits in a disk of radius less than `radius`,
and every packing in the disk of radius `radius` is congruent to one of
`models`: the stationary packings of `ExactFamily/Stationary.lean`, with the
central square and the two sliding squares anywhere in the admissible domain,
and their reflections.

A packing at a squared radius `q ≤ qStar` has a boundary neighbour cycle
(`GlobalNormalization.lean`), which is expanded to the level `max q qMinus`;
its frames are captured near the candidate frames (`Candidate/Capture.lean`),
and the boundary terminal (`Terminal.lean`) forces `q = qStar` with every frame
error zero. The stationary identity, evaluated again at the original centres,
then fixes the five squares with a corner on the circle by its positive circle
weights, and leaves free only the two sliding squares, by its zero slider
forces, and the central square (`ExactFamily/CentralParameters.lean`).

The file ends with `optimum`, the case as an `Optimum`, and with
`full_dimensional_equality_box`: a five-dimensional box of parameters gives
pairwise non-congruent packings, even allowing reflections.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open ExactFamily Coordinates EqualityParameters Candidate

namespace Candidate

theorem Captured.rigid {q : ℝ} {C : BoundaryCycle q} {F : Frame C}
    (K : Captured C F) (hq : q≤qStar) :
    q=qStar ∧ K.z=sharpData.z ∧ mismatch F.theta=0 := by
  exact Terminal.boundary_rigid F hq
    (show K.z∈tiltBox from Set.mem_Icc.mpr ⟨by linarith [K.z_lower],by linarith [K.z_upper]⟩)
    K.tilt_eq ⟨K.tilt_lower.le,K.tilt_upper.le⟩ K.mismatch_lt.le K.owners

theorem Frame.zero_angles {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hS : mismatch F.theta=0) :
    F.theta=![tilt F.theta,tilt F.theta,0,0,0,0,0] := by
  have hz (i : Vertex) (hi : i∈charged) : delta F.theta i=0 := by
    have hh := delta_le_mismatch F.theta hi
    rw [hS] at hh
    exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  have h0 := hz 0 (by decide)
  have h2 := hz 2 (by decide)
  have h3 := hz 3 (by decide)
  have h4 := hz 4 (by decide)
  have h5 := hz 5 (by decide)
  have hA := F.theta_A
  dsimp [delta,next,A] at h0 h2 h3 h4 h5 hA
  funext i
  fin_cases i <;> simp [tilt,G] <;> linarith

def sharpCanonicalCos : Vertex → ℝ := ![sharpData.s,sharpData.s,1,1,0,0,-1]
def sharpCanonicalSin : Vertex → ℝ := ![-sharpData.c,-sharpData.c,0,0,1,1,0]

theorem Frame.zero_frames {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hS : mismatch F.theta=0) (ht : tilt F.theta=2*Real.arctan sharpData.z) :
    ∀ i, (C.square i).cosine=sharpCanonicalCos i ∧
      (C.square i).sine=sharpCanonicalSin i := by
  have hθ := F.zero_angles hS
  have htrig := Perturbation.atan_frame sharpData.z
  have hcos : Real.cos (tilt F.theta)=sharpData.c := by
    simpa [ht,c] using htrig.1
  have hsin : Real.sin (tilt F.theta)=sharpData.s := by
    simpa [ht,s] using htrig.2
  have hframe (i : Vertex) :
      (C.square i).cosine = Real.cos ((![tilt F.theta,tilt F.theta,0,0,0,0,0] : Vertex → ℝ) i +
        ((offsets i : ℤ) : ℝ) * Real.pi / 2) ∧
      (C.square i).sine = Real.sin ((![tilt F.theta,tilt F.theta,0,0,0,0,0] : Vertex → ℝ) i +
        ((offsets i : ℤ) : ℝ) * Real.pi / 2) := by
    have hc := C.frame_cos i
    have hs := C.frame_sin i
    change (C.square i).cosine=Real.cos (C.canonicalAngle i) at hc
    change (C.square i).sine=Real.sin (C.canonicalAngle i) at hs
    rw [F.canonical_eq,hθ] at hc hs
    exact ⟨hc,hs⟩
  -- the seven canonical angles at zero frame error
  have a0 : (![tilt F.theta,tilt F.theta,0,0,0,0,0] : Vertex → ℝ) 0 +
      ((offsets 0 : ℤ) : ℝ) * Real.pi / 2 = tilt F.theta - Real.pi / 2 := by
    simp [offsets]
    ring
  have a1 : (![tilt F.theta,tilt F.theta,0,0,0,0,0] : Vertex → ℝ) 1 +
      ((offsets 1 : ℤ) : ℝ) * Real.pi / 2 = tilt F.theta - Real.pi / 2 := by
    simp [offsets]
    ring
  have a2 : (![tilt F.theta,tilt F.theta,0,0,0,0,0] : Vertex → ℝ) 2 +
      ((offsets 2 : ℤ) : ℝ) * Real.pi / 2 = 0 := by
    simp [offsets]
  have a3 : (![tilt F.theta,tilt F.theta,0,0,0,0,0] : Vertex → ℝ) 3 +
      ((offsets 3 : ℤ) : ℝ) * Real.pi / 2 = 0 := by
    simp [offsets]
  have a4 : (![tilt F.theta,tilt F.theta,0,0,0,0,0] : Vertex → ℝ) 4 +
      ((offsets 4 : ℤ) : ℝ) * Real.pi / 2 = Real.pi / 2 := by
    simp [offsets]
  have a5 : (![tilt F.theta,tilt F.theta,0,0,0,0,0] : Vertex → ℝ) 5 +
      ((offsets 5 : ℤ) : ℝ) * Real.pi / 2 = Real.pi / 2 := by
    simp [offsets]
  have a6 : (![tilt F.theta,tilt F.theta,0,0,0,0,0] : Vertex → ℝ) 6 +
      ((offsets 6 : ℤ) : ℝ) * Real.pi / 2 = Real.pi := by
    simp [offsets]
  have e0 := hframe 0
  rw [a0, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, hsin, hcos] at e0
  have e1 := hframe 1
  rw [a1, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, hsin, hcos] at e1
  have e2 := hframe 2
  rw [a2, Real.cos_zero, Real.sin_zero] at e2
  have e3 := hframe 3
  rw [a3, Real.cos_zero, Real.sin_zero] at e3
  have e4 := hframe 4
  rw [a4, Real.cos_pi_div_two, Real.sin_pi_div_two] at e4
  have e5 := hframe 5
  rw [a5, Real.cos_pi_div_two, Real.sin_pi_div_two] at e5
  have e6 := hframe 6
  rw [a6, Real.cos_pi, Real.sin_pi] at e6
  intro i
  fin_cases i
  exacts [e0, e1, e2, e3, e4, e5, e6]

end Candidate

namespace GlobalNormalization

variable {S : Fin 8 → UnitSquare} {q : ℝ}

def captured (N : GlobalNormalization S q) : Captured N.expanded N.frame :=
  Candidate.capture N.frame N.eHalf

def originalPositions (N : GlobalNormalization S q) : OriginalDual.Positions :=
  OriginalDual.ofCycle (fun i=>(N.source.square i).center)

/-- A contradiction below qStar is obtained at the recovered radius.  No
terminal inequality is applied to the expanded centers at Q1. -/
theorem radius_rigid (N : GlobalNormalization S q) (hq : q≤qStar) :
    sourceLevel q=qStar ∧ N.captured.z=sharpData.z ∧ mismatch N.frame.theta=0 := by
  let K := N.captured.pullback N.expansion
  have hlevel : sourceLevel q≤qStar := by
    exact max_le hq (by simpa [qMinus] using qStar_limits.1.le)
  simpa [K,Candidate.Captured.pullback] using K.rigid hlevel

theorem original_frames (N : GlobalNormalization S q)
    (hS : mismatch N.frame.theta=0) (hz : N.captured.z=sharpData.z) :
    ∀ i, (N.source.square i).cosine=sharpCanonicalCos i ∧
      (N.source.square i).sine=sharpCanonicalSin i := by
  have ht : tilt N.frame.theta=2*Real.arctan sharpData.z := by
    rw [N.captured.tilt_eq,hz]
  intro i
  have hf := N.frame.zero_frames hS ht i
  exact ⟨(N.source_frames i).1.trans hf.1,(N.source_frames i).2.trans hf.2⟩

theorem original_vertices (N : GlobalNormalization S q)
    (hS : mismatch N.frame.theta=0) (hz : N.captured.z=sharpData.z) :
    ∀ i : Fin 5,
      normSq (add (N.originalPositions i.castSucc.castSucc) (sharpData.anchorOffsets i))≤q := by
  intro i
  have hframe := N.original_frames hS hz
  have hunit := sharpData.unit
  have hHc : (N.source.square 0).cosine = sharpData.s := (hframe 0).1
  have hHs : (N.source.square 0).sine = -sharpData.c := (hframe 0).2
  have hAc : (N.source.square 2).cosine = 1 := (hframe 2).1
  have hAs : (N.source.square 2).sine = 0 := (hframe 2).2
  have hBc : (N.source.square 3).cosine = 1 := (hframe 3).1
  have hBs : (N.source.square 3).sine = 0 := (hframe 3).2
  have hDc : (N.source.square 5).cosine = 0 := (hframe 5).1
  have hDs : (N.source.square 5).sine = 1 := (hframe 5).2
  have hEc : (N.source.square 6).cosine = -1 := (hframe 6).1
  have hEs : (N.source.square 6).sine = 0 := (hframe 6).2
  have hclosed : closedSquare (N.source.square (OriginalDual.cycleIndex i.castSucc.castSucc))
      (add (N.originalPositions i.castSucc.castSucc) (sharpData.anchorOffsets i)) := by
    fin_cases i
    · show closedSquare (N.source.square 2) (add (N.source.square 2).center (1/2,-1/2))
      have hx : localX (N.source.square 2) (add (N.source.square 2).center (1/2,-1/2)) = 1/2 := by
        simp only [localX, add, hAc, hAs]; ring
      have hy : localY (N.source.square 2) (add (N.source.square 2).center (1/2,-1/2)) =
          -1/2 := by
        simp only [localY, add, hAc, hAs]; ring
      exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩
    · show closedSquare (N.source.square 3) (add (N.source.square 3).center (1/2,1/2))
      have hx : localX (N.source.square 3) (add (N.source.square 3).center (1/2,1/2)) = 1/2 := by
        simp only [localX, add, hBc, hBs]; ring
      have hy : localY (N.source.square 3) (add (N.source.square 3).center (1/2,1/2)) = 1/2 := by
        simp only [localY, add, hBc, hBs]; ring
      exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩
    · show closedSquare (N.source.square 5) (add (N.source.square 5).center (-1/2,1/2))
      have hx : localX (N.source.square 5) (add (N.source.square 5).center (-1/2,1/2)) = 1/2 := by
        simp only [localX, add, hDc, hDs]; ring
      have hy : localY (N.source.square 5) (add (N.source.square 5).center (-1/2,1/2)) = 1/2 := by
        simp only [localY, add, hDc, hDs]; ring
      exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩
    · show closedSquare (N.source.square 6) (add (N.source.square 6).center (-1/2,-1/2))
      have hx : localX (N.source.square 6) (add (N.source.square 6).center (-1/2,-1/2)) =
          1/2 := by
        simp only [localX, add, hEc, hEs]; ring
      have hy : localY (N.source.square 6) (add (N.source.square 6).center (-1/2,-1/2)) =
          1/2 := by
        simp only [localY, add, hEc, hEs]; ring
      exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩
    · show closedSquare (N.source.square 0)
        (add (N.source.square 0).center (sharpData.inFrame (-1/2) (-1/2)))
      have hx : localX (N.source.square 0)
          (add (N.source.square 0).center (sharpData.inFrame (-1/2) (-1/2))) = 1/2 := by
        simp only [localX, add, inFrame, hHc, hHs]
        linear_combination (1/2 : ℝ) * hunit
      have hy : localY (N.source.square 0)
          (add (N.source.square 0).center (sharpData.inFrame (-1/2) (-1/2))) = -1/2 := by
        simp only [localY, add, inFrame, hHc, hHs]
        linear_combination (-1/2 : ℝ) * hunit
      exact ⟨by rw [hx]; norm_num, by rw [hy]; norm_num⟩
  rw [N.source_square] at hclosed
  have hh := N.packing.2.1 _ _ hclosed
  simpa [sub] using hh

theorem original_gaps (N : GlobalNormalization S q)
    (hS : mismatch N.frame.theta=0) (hz : N.captured.z=sharpData.z) :
    ∀ e : Fin 7,0≤OriginalDual.gap sharpData N.originalPositions e := by
  have hj (i : Vertex) : ∃ j : Fin 4,j∈terminalOwners i ∧
      (forwardAxis j).Feasible (N.source.square i) (N.source.square (next i)) := by
    obtain ⟨j,hj⟩ := N.frame.forward_complete i (N.expanded.selected i) (N.expanded.feasible i)
    have hje : (forwardAxis j).Feasible (N.expanded.square i) (N.expanded.square (next i)) := by
      simpa [← hj] using N.expanded.feasible i
    have hjs : N.source.selected i=forwardAxis j := (congrFun N.source_selected i).trans hj
    exact ⟨j,N.captured.owners i j hje,by simpa [hjs] using N.source.feasible i⟩
  choose j hjmem hjsep using hj
  have hframe := N.original_frames hS hz
  have hHc : (N.source.square 0).cosine = sharpData.s := (hframe 0).1
  have hHs : (N.source.square 0).sine = -sharpData.c := (hframe 0).2
  have hGc : (N.source.square 1).cosine = sharpData.s := (hframe 1).1
  have hGs : (N.source.square 1).sine = -sharpData.c := (hframe 1).2
  have hAc : (N.source.square 2).cosine = 1 := (hframe 2).1
  have hAs : (N.source.square 2).sine = 0 := (hframe 2).2
  have hBc : (N.source.square 3).cosine = 1 := (hframe 3).1
  have hBs : (N.source.square 3).sine = 0 := (hframe 3).2
  have hTc : (N.source.square 4).cosine = 0 := (hframe 4).1
  have hTs : (N.source.square 4).sine = 1 := (hframe 4).2
  have hDc : (N.source.square 5).cosine = 0 := (hframe 5).1
  have hDs : (N.source.square 5).sine = 1 := (hframe 5).2
  have hEc : (N.source.square 6).cosine = -1 := (hframe 6).1
  have hEs : (N.source.square 6).sine = 0 := (hframe 6).2
  have hu := sharpData.unit
  have hw := sharpData_stationary.weightDomain
  -- the owners allowed by the terminal owner sets
  have hown (k : Vertex) (x y : Fin 4) (hk : terminalOwners k = {x, y}) :
      j k = x ∨ j k = y := by
    have hm := hjmem k
    rw [hk] at hm
    simpa using hm
  have j0 : j 0 = 0 ∨ j 0 = 2 := hown 0 0 2 rfl
  have j2 : j 2 = 0 ∨ j 2 = 2 := hown 2 0 2 rfl
  have j3 : j 3 = 2 ∨ j 3 = 3 := hown 3 2 3 rfl
  have j4 : j 4 = 0 ∨ j 4 = 2 := hown 4 0 2 rfl
  have j5 : j 5 = 2 ∨ j 5 = 3 := hown 5 2 3 rfl
  have j1 : j 1 = 0 := by simpa [terminalOwners] using hjmem 1
  have j6 : j 6 = 1 := by simpa [terminalOwners] using hjmem 6
  -- edge A → B, cycle edge 2
  have g0 : 0 ≤ OriginalDual.gap sharpData N.originalPositions 0 := by
    have hsep : SAT.threshold (N.source.square 2) (N.source.square 3) ≤
        (forwardAxis (j 2)).projection (N.source.square 2) (N.source.square 3) := hjsep 2
    have hthr : SAT.threshold (N.source.square 2) (N.source.square 3) = 1 := by
      simp only [SAT.threshold, relativeC, relativeS, hAc, hAs, hBc, hBs]; norm_num
    have hgap : OriginalDual.gap sharpData N.originalPositions 0 =
        (N.source.square 3).center.2 - (N.source.square 2).center.2 - 1 := rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j2 with h | h <;> rw [h] at hsep <;>
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, SquaresInCircles.Eight.f, dot, sub, scale,
        hAc, hAs, hBc, hBs] at hsep <;>
      linarith
  -- edge B → T, cycle edge 3, read from T to B
  have g1 : 0 ≤ OriginalDual.gap sharpData N.originalPositions 1 := by
    have hsep : SAT.threshold (N.source.square 3) (N.source.square 4) ≤
        (forwardAxis (j 3)).projection (N.source.square 3) (N.source.square 4) := hjsep 3
    have hthr : SAT.threshold (N.source.square 3) (N.source.square 4) = 1 := by
      simp only [SAT.threshold, relativeC, relativeS, hBc, hBs, hTc, hTs]; norm_num
    have hgap : OriginalDual.gap sharpData N.originalPositions 1 =
        (N.source.square 3).center.1 - (N.source.square 4).center.1 - 1 := rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j3 with h | h <;> rw [h] at hsep <;>
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, SquaresInCircles.Eight.e, SquaresInCircles.Eight.f, dot, sub, scale,
        hBc, hBs, hTc, hTs] at hsep <;>
      linarith
  -- edge T → D, cycle edge 4, read from D to T
  have g2 : 0 ≤ OriginalDual.gap sharpData N.originalPositions 2 := by
    have hsep : SAT.threshold (N.source.square 4) (N.source.square 5) ≤
        (forwardAxis (j 4)).projection (N.source.square 4) (N.source.square 5) := hjsep 4
    have hthr : SAT.threshold (N.source.square 4) (N.source.square 5) = 1 := by
      simp only [SAT.threshold, relativeC, relativeS, hTc, hTs, hDc, hDs]; norm_num
    have hgap : OriginalDual.gap sharpData N.originalPositions 2 =
        (N.source.square 4).center.1 - (N.source.square 5).center.1 - 1 := rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j4 with h | h <;> rw [h] at hsep <;>
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, SquaresInCircles.Eight.f, dot, sub, scale,
        hTc, hTs, hDc, hDs] at hsep <;>
      linarith
  -- edge D → E, cycle edge 5, read from E to D
  have g3 : 0 ≤ OriginalDual.gap sharpData N.originalPositions 3 := by
    have hsep : SAT.threshold (N.source.square 5) (N.source.square 6) ≤
        (forwardAxis (j 5)).projection (N.source.square 5) (N.source.square 6) := hjsep 5
    have hthr : SAT.threshold (N.source.square 5) (N.source.square 6) = 1 := by
      simp only [SAT.threshold, relativeC, relativeS, hDc, hDs, hEc, hEs]; norm_num
    have hgap : OriginalDual.gap sharpData N.originalPositions 3 =
        (N.source.square 5).center.2 - (N.source.square 6).center.2 - 1 := rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j5 with h | h <;> rw [h] at hsep <;>
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, SquaresInCircles.Eight.e, SquaresInCircles.Eight.f, dot, sub, scale,
        hDc, hDs, hEc, hEs] at hsep <;>
      linarith
  -- edge G → A, cycle edge 1
  have g4 : 0 ≤ OriginalDual.gap sharpData N.originalPositions 4 := by
    have hsep : SAT.threshold (N.source.square 1) (N.source.square 2) ≤
        (forwardAxis (j 1)).projection (N.source.square 1) (N.source.square 2) := hjsep 1
    have hthr : SAT.threshold (N.source.square 1) (N.source.square 2) =
        (1 + sharpData.c + sharpData.s) / 2 := by
      have hc : relativeC (N.source.square 1) (N.source.square 2) = sharpData.s := by
        rw [relativeC, hGc, hGs, hAc, hAs]; ring
      have hs : relativeS (N.source.square 1) (N.source.square 2) = sharpData.c := by
        rw [relativeS, hGc, hGs, hAc, hAs]; ring
      rw [SAT.threshold, hc, hs, abs_of_pos hw.s_pos, abs_of_pos hw.c_pos]; ring
    have hgap : OriginalDual.gap sharpData N.originalPositions 4 =
        sharpData.c * ((N.source.square 2).center.1 - (N.source.square 1).center.1) +
          sharpData.s * ((N.source.square 2).center.2 - (N.source.square 1).center.2) -
          (1 + sharpData.c + sharpData.s) / 2 := rfl
    rw [hthr, j1] at hsep
    rw [hgap]
    simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
      AxisSign.value, SquaresInCircles.Eight.f, dot, sub, scale, hGc, hGs] at hsep
    linarith
  -- edge H → G, cycle edge 0
  have g5 : 0 ≤ OriginalDual.gap sharpData N.originalPositions 5 := by
    have hsep : SAT.threshold (N.source.square 0) (N.source.square 1) ≤
        (forwardAxis (j 0)).projection (N.source.square 0) (N.source.square 1) := hjsep 0
    have hthr : SAT.threshold (N.source.square 0) (N.source.square 1) = 1 := by
      have hc : relativeC (N.source.square 0) (N.source.square 1) = 1 := by
        rw [relativeC, hHc, hHs, hGc, hGs]; linear_combination hu
      have hs : relativeS (N.source.square 0) (N.source.square 1) = 0 := by
        rw [relativeS, hHc, hHs, hGc, hGs]; ring
      rw [SAT.threshold, hc, hs]; norm_num
    have hgap : OriginalDual.gap sharpData N.originalPositions 5 =
        sharpData.c * ((N.source.square 1).center.1 - (N.source.square 0).center.1) +
          sharpData.s * ((N.source.square 1).center.2 - (N.source.square 0).center.2) - 1 := rfl
    rw [hthr] at hsep
    rw [hgap]
    rcases j0 with h | h <;> rw [h] at hsep <;>
      simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisSign.value, SquaresInCircles.Eight.f, dot, sub, scale,
        hHc, hHs, hGc, hGs] at hsep <;>
      linarith
  -- edge E → H, cycle edge 6, read from H to E
  have g6 : 0 ≤ OriginalDual.gap sharpData N.originalPositions 6 := by
    have hsep : SAT.threshold (N.source.square 6) (N.source.square 0) ≤
        (forwardAxis (j 6)).projection (N.source.square 6) (N.source.square 0) := hjsep 6
    have hthr : SAT.threshold (N.source.square 6) (N.source.square 0) =
        (1 + sharpData.c + sharpData.s) / 2 := by
      have hc : relativeC (N.source.square 6) (N.source.square 0) = -sharpData.s := by
        rw [relativeC, hEc, hEs, hHc, hHs]; ring
      have hs : relativeS (N.source.square 6) (N.source.square 0) = sharpData.c := by
        rw [relativeS, hEc, hEs, hHc, hHs]; ring
      rw [SAT.threshold, hc, hs, abs_neg, abs_of_pos hw.s_pos, abs_of_pos hw.c_pos]; ring
    have hgap : OriginalDual.gap sharpData N.originalPositions 6 =
        -sharpData.s * ((N.source.square 6).center.1 - (N.source.square 0).center.1) +
          sharpData.c * ((N.source.square 6).center.2 - (N.source.square 0).center.2) -
          (1 + sharpData.c + sharpData.s) / 2 := rfl
    rw [hthr, j6] at hsep
    rw [hgap]
    simp [forwardAxis, SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
      AxisSign.value, SquaresInCircles.Eight.e, dot, sub, scale, hHc, hHs] at hsep
    linarith
  intro e
  fin_cases e
  exacts [g0, g1, g2, g3, g4, g5, g6]

theorem original_centers (N : GlobalNormalization S qStar)
    (hS : mismatch N.frame.theta=0) (hz : N.captured.z=sharpData.z) :
    (∀ i : Fin 5,N.originalPositions i.castSucc.castSucc=sharpData.anchorCenters i) ∧
    (∀ e : Fin 7,OriginalDual.gap sharpData N.originalPositions e=0) ∧
    ∃ Z η : ℝ,N.originalPositions 5=sharpData.pT Z ∧
      N.originalPositions 6=sharpData.pG η :=
  Terminal.original_pullback (N.original_vertices hS hz) (N.original_gaps hS hz)

theorem source_centers_from_anchors (N : GlobalNormalization S qStar) {Z η : ℝ}
    (ha : ∀ i : Fin 5,N.originalPositions i.castSucc.castSucc=sharpData.anchorCenters i)
    (hT : N.originalPositions 5=sharpData.pT Z)
    (hG : N.originalPositions 6=sharpData.pG η) :
    ∀ i,(N.source.square i).center=sharpData.exteriorCenters Z η i := by
  intro i
  fin_cases i
  · simpa [originalPositions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      anchorCenters,exteriorCenters] using ha 4
  · simpa [originalPositions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      exteriorCenters] using hG
  · simpa [originalPositions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      anchorCenters,exteriorCenters] using ha 0
  · simpa [originalPositions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      anchorCenters,exteriorCenters] using ha 1
  · simpa [originalPositions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      exteriorCenters] using hT
  · simpa [originalPositions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      anchorCenters,exteriorCenters] using ha 2
  · simpa [originalPositions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      anchorCenters,exteriorCenters] using ha 3

theorem source_square_models (N : GlobalNormalization S qStar) {Z η : ℝ}
    (hS : mismatch N.frame.theta=0) (hz : N.captured.z=sharpData.z)
    (hcenters : ∀ i,(N.source.square i).center=sharpData.exteriorCenters Z η i) :
    ∀ i,SameSquare (N.source.square i) (sharpData.exteriorSquares Z η i) := by
  intro i
  apply sameSquare_of_center_physical
  · have hc := hcenters i
    fin_cases i <;> simpa [exteriorSquares,exteriorCenters,axisSquare,tiltedSquare] using hc
  · have hf := N.original_frames hS hz i
    fin_cases i <;>
      simp only [SamePhysicalFrame,exteriorSquares,axisSquare,tiltedSquare,
        Matrix.cons_val_zero,Matrix.cons_val_succ,sharpCanonicalCos,sharpCanonicalSin] at hf ⊢ <;>
      aesop

end GlobalNormalization

/-- The unrestricted squared-radius lower bound at the origin. -/
theorem squared_radius_lower_bound (S : Fin 8 → UnitSquare) {q : ℝ}
    (hp : SqPacking S (0,0) q) : qStar≤q := by
  by_contra! hq
  have hQ : q≤Q1 := hq.le.trans (by simpa [Q1] using qStar_limits.2.1.le)
  obtain ⟨N⟩ := global_normalization_exists hp hQ
  have hr := N.radius_rigid hq.le
  have hstrict : sourceLevel q<qStar :=
    max_lt hq (by simpa [qMinus] using qStar_limits.1)
  rw [hr.1] at hstrict
  exact lt_irrefl _ hstrict

/-- The squared optimum has its originally selected stationary value; the
choice is established in F2, independently of this global lower bound. -/
theorem radius_sq : radius^2=qStar :=
  Real.sq_sqrt (by linarith [qStar_limits.1])

theorem radius_pos : 0<radius := by
  apply Real.sqrt_pos.mpr
  linarith [qStar_limits.1]

theorem origin_equality_classification (S : Fin 8 → UnitSquare)
    (hp : SqPacking S (0,0) qStar) : ∃ M∈models,Congruent S (0,0) M := by
  obtain ⟨N⟩ := global_normalization_exists hp
    (by simpa [Q1] using qStar_limits.2.1.le)
  obtain ⟨hq,hz,hS⟩ := N.radius_rigid le_rfl
  obtain ⟨ha,hg,Z,η,hT,hG⟩ := N.original_centers hS hz
  have hcenters := N.source_centers_from_anchors ha hT hG
  have hsquares := N.source_square_models hS hz hcenters
  have hframes := N.original_frames hS hz
  obtain ⟨hZ,hη⟩ := N.original_slider_sectors hcenters
    (by simpa [sharpCanonicalCos,sharpCanonicalSin] using hframes 4)
    (by simpa [sharpCanonicalCos,sharpCanonicalSin] using hframes 1)
  obtain ⟨p,hcentral,hcentralCenter,hframe,hpz,hpη⟩ :=
    central_parameters_exist (N.squares 0) Z η
  have hmodel (i : Fin 8) : SameSquare (N.squares i) (p.model sharpData i) := by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact ⟨fun x=>(hcentral.1 x).symm,fun x=>(hcentral.2 x).symm⟩
    · have h := hsquares j
      rw [N.source_square] at h
      simpa [model,exteriorSquares,hpz,hpη] using h
  have hpmodel : SqPacking (p.model sharpData) (0,0) qStar := by
    refine ⟨N.packing.1,?_,?_⟩
    · intro i x hx
      exact N.packing.2.1 i x ((hmodel i).2 x |>.mpr hx)
    · intro i j hij x hx
      exact N.packing.2.2 i j hij x
        ⟨(hmodel i).1 x |>.mpr hx.1,(hmodel j).1 x |>.mpr hx.2⟩
  have hpcore : ContainsCore p.centralSquare := by
    intro x hx
    exact (hcentral.1 x).mpr (N.central_core x hx)
  have hpadm : p.Admissible sharpData := admissible_of_original_geometry hpmodel hpcore hframe
    (by simpa [hpz] using hZ) (by simpa [hpη] using hη)
  refine ⟨reflectedModel N.reflected p,⟨N.reflected,p,hpadm,rfl⟩,?_⟩
  obtain ⟨φ,σ,hφ⟩ := N.congruent
  refine ⟨φ,σ,?_⟩
  intro i x
  have hm :
      (openSquare (if N.reflected then reflectDiagonalSquare (N.squares i) else N.squares i) x↔
        openSquare (reflectedModel N.reflected p i) x) ∧
      (closedSquare (if N.reflected then reflectDiagonalSquare (N.squares i) else N.squares i) x↔
        closedSquare (reflectedModel N.reflected p i) x) := by
    cases hb : N.reflected
    · simpa [reflectedModel,hb] using ⟨(hmodel i).1 x,(hmodel i).2 x⟩
    · simpa [reflectedModel,hb,reflectDiagonal_open,reflectDiagonal_closed] using
        ⟨(hmodel i).1 (diagonalPoint x),(hmodel i).2 (diagonalPoint x)⟩
  exact ⟨(hφ i x).1.trans hm.1,(hφ i x).2.trans hm.2⟩

def translatedToOrigin (S : Fin 8 → UnitSquare) (o : Point) : Fin 8 → UnitSquare :=
  fun i=>pullSquare o 0 (S i)

theorem translated_congruent (S : Fin 8 → UnitSquare) (o : Point) :
    Congruent S o (translatedToOrigin S o) := by
  refine ⟨0,Equiv.refl _,?_⟩
  intro i x
  exact ⟨(pullSquare_open o 0 (S i) x).symm,(pullSquare_closed o 0 (S i) x).symm⟩

/-- No restrictions on orientation, contact graph, the containing center,
or which seven squares surround the core are premises of this theorem. -/
theorem lower_bound (S : Fin 8 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : radius≤R := by
  have horigin := packing_pull hp (0 : Direction)
  have hsq := squared_radius_lower_bound (translatedToOrigin S o) (packing_sq horigin)
  have hr := radius_sq
  have hpos := radius_pos
  nlinarith [hp.1]

theorem uniqueness (S : Fin 8 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : ∃ M∈models,Congruent S o M := by
  have horigin := packing_pull hp (0 : Direction)
  have hsq : SqPacking (translatedToOrigin S o) (0,0) qStar := by
    have h := packing_sq horigin
    rw [radius_sq] at h
    exact h
  obtain ⟨M,hM,hcong⟩ := origin_equality_classification (translatedToOrigin S o) hsq
  exact ⟨M,hM,congruent_trans (translated_congruent S o) hcong⟩

/-- Public interface shared with the one- through seven-square cases. -/
def optimum : Optimum 8 where
  radius := Eight.radius
  models := Eight.models
  models_nonempty := Eight.models_nonempty
  model_packing := Eight.model_packing
  model_reaches := Eight.model_reaches
  uniqueness := Eight.uniqueness

theorem isLeast : IsLeast
    {R : ℝ | ∃ (S : Fin 8 → UnitSquare) (o : Point),Packing S o R} radius :=
  optimum.isLeast

theorem packing_iff (S : Fin 8 → UnitSquare) (o : Point) :
    Packing S o radius↔∃ M∈models,Congruent S o M := optimum.packing_iff S o

theorem equality_iff_parameters (S : Fin 8 → UnitSquare) (o : Point) :
    Packing S o radius↔∃ reflected : Bool,∃ p : EqualityParameters,
      p.Admissible sharpData ∧ Congruent S o (reflectedModel reflected p) := by
  rw [packing_iff]
  constructor
  · rintro ⟨M,⟨b,p,hp,rfl⟩,hcong⟩
    exact ⟨b,p,hp,hcong⟩
  · rintro ⟨b,p,hp,hcong⟩
    exact ⟨reflectedModel b p,⟨b,p,hp,rfl⟩,hcong⟩

/-- A five dimensional box of distinct equality classes, even when the
equivalence is allowed to reflect, translate, rotate, and relabel. -/
theorem full_dimensional_equality_box :
    (∀ p : EqualityParameters,p.InBox→ Packing (p.model sharpData) (0,0) radius) ∧
    (∀ p r : EqualityParameters,p.InBox→ r.InBox→
      (BoxRigidity.RigidlyCongruent (p.model sharpData) (r.model sharpData)↔p=r)) :=
  ⟨fun _ hp=>whole_box_packing hp,fun _ _ hp hr=>BoxRigidity.box_rigidlyCongruent_iff hp hr⟩

end SquaresInCircles.Eight
