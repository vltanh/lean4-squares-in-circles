module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighSourceComplete
public import SquaresInCircles.Eight.TableFree.SharpEntry
public import SquaresInCircles.Eight.Terminal
public import SquaresInCircles.Eight.Equality

/-!
# Unrestricted sharp-radius assembly from the table-free original source

The original source-level global primary-owner theorem is now
constructed without generated affine/owner capture:
\`TableFree.table_free_sharp_source_entry\` has an explicit proof body
from the exhaustive high-GA/BT2 exclusion, the complete same-radius
G/T terminal source transport, hard equality, and retained *original*
physical normals. Original q is not replaced by qStar.

The lower bound and equality model use a fresh qStar normalization
only as an auxiliary original-witness vehicle. They never assume
that a moved necessary cycle is an original packing and never use
\`Candidate.capture\`.

This is an uncompiled draft. Source theorem existence is not Lean
kernel certification and does not settle compilation performance.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily Coordinates Candidate

theorem frame_zero_angles {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hS : mismatch F.theta=0) :
    F.theta=![tilt F.theta,tilt F.theta,0,0,0,0,0] := by
  have hz (i : Vertex) (hi : i ∈ charged) : delta F.theta i=0 := by
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

theorem frame_zero_physical_frames {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hS : mismatch F.theta=0)
    (ht : tilt F.theta=2*Real.arctan sharpData.z) :
    TableFree.StationaryFrames sharpData C.square := by
  have hθ := frame_zero_angles F hS
  have htrig := Perturbation.atan_frame sharpData.z
  have hcos : Real.cos (tilt F.theta)=sharpData.c := by
    simpa [ht,c] using htrig.1
  have hsin : Real.sin (tilt F.theta)=sharpData.s := by
    simpa [ht,s] using htrig.2
  intro i
  have hc := C.frame_cos i
  have hs := C.frame_sin i
  change (C.square i).cosine=Real.cos (C.canonicalAngle i) at hc
  change (C.square i).sine=Real.sin (C.canonicalAngle i) at hs
  rw [F.canonical_eq,hθ] at hc hs
  fin_cases i <;>
    simp [TableFree.canonicalCos,TableFree.canonicalSin,offsets,
      Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,hcos,hsin]
      at hc hs ⊢ <;>
    exact ⟨hc,hs⟩

theorem origin_sharp_rigidity {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ qStar) :
    ∃ N : GlobalNormalization S qStar,
      SqPacking N.squares (0,0) q ∧
      q=qStar ∧
      TableFree.StationaryFrames sharpData N.source.square ∧
      (∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=TableFree.stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,
        originalPositions N i.castSucc.castSucc=sharpData.anchorCenters i) ∧
      (∀ e : Fin 7, OriginalDual.gap sharpData (originalPositions N) e=0) ∧
      ∃ Z η : ℝ, originalPositions N 5=sharpData.pT Z ∧
        originalPositions N 6=sharpData.pG η := by
  obtain ⟨N,hN,hselected⟩ := fresh_normalization_with_retained_source_exists hp hq
  exact ⟨N,hN,TableFree.table_free_original_rigidity N hselected hN hq⟩

/-- A concrete unrestricted squared-radius lower bound, proved by the fresh
sharp-ceiling construction and the original-circle dual. -/
theorem origin_sharp_lower_bound {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) : qStar ≤ q := by
  by_cases hq : q ≤ qStar
  · obtain ⟨N,hN,heq,_⟩ := origin_sharp_rigidity hp hq
    exact heq.ge
  · exact (lt_of_not_ge hq).le

theorem sharp_squared_radius_lower_bound {S : Fin 8 → UnitSquare}
    {o : Point} {q : ℝ} (hp : SqPacking S o q) : qStar ≤ q := by
  have hp0 : SqPacking (fun i => pullSquare o 0 (S i)) (0,0) q :=
    (sqPacking_iff_packing _ _ hp.1).2
      (packing_pull ((sqPacking_iff_packing _ _ hp.1).1 hp) 0)
  exact origin_sharp_lower_bound hp0

theorem sharp_radius_sq : Eight.radius^2=qStar := by
  change (Real.sqrt qStar)^2=qStar
  exact Real.sq_sqrt (by linarith [qStar_limits.1])

theorem sharp_radius_lower_bound {S : Fin 8 → UnitSquare}
    {o : Point} {R : ℝ} (hp : Packing S o R) : Eight.radius ≤ R := by
  have hq := sharp_squared_radius_lower_bound (packing_sq hp)
  have hR := hp.1
  have hr : 0 ≤ Eight.radius := Real.sqrt_nonneg _
  nlinarith [sharp_radius_sq]

/-! ## Original positions in the cyclic family order -/

theorem source_centers_of_original_anchors {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) {Z η : ℝ}
    (ha : ∀ i : Fin 5,
      originalPositions N i.castSucc.castSucc=sharpData.anchorCenters i)
    (hT : originalPositions N 5=sharpData.pT Z)
    (hG : originalPositions N 6=sharpData.pG η) :
    ∀ i, (N.source.square i).center=sharpData.exteriorCenters Z η i := by
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

theorem source_squares_of_original_centers {S : Fin 8 → UnitSquare}
    (N : GlobalNormalization S qStar) {Z η : ℝ}
    (hf : TableFree.StationaryFrames sharpData N.source.square)
    (hc : ∀ i, (N.source.square i).center=sharpData.exteriorCenters Z η i) :
    ∀ i, SameSquare (N.source.square i) (sharpData.exteriorSquares Z η i) := by
  intro i
  apply sameSquare_of_physical_center
  · fin_cases i <;>
      simpa [exteriorSquares,exteriorCenters,axisSquare,tiltedSquare] using hc i
  · have h := hf i
    fin_cases i <;>
      simp only [SamePhysicalFrame,exteriorSquares,axisSquare,tiltedSquare,
        Matrix.cons_val_zero,Matrix.cons_val_succ,
        TableFree.canonicalCos,TableFree.canonicalSin] at h ⊢ <;>
      aesop

end SquaresInCircles.Eight.GeometricModel
