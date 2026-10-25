module

public import SquaresInCircles.Eight.Owners.GA.High.SourceComplete
public import SquaresInCircles.Eight.Stationary.FixedEval
public import SquaresInCircles.Eight.Stationary.Family

/-!
# Eight squares: the packings at the stationary radius

A packing in the disk of squared radius `qStar` about the origin is congruent to one of
`stationaryModels` (`origin_sharp_uniqueness`): the five anchored squares and the slider lines
come from `origin_sharp_rigidity`, the slider sectors from the cyclic order
(`original_slider_sectors`), the parameters of the central square, with its quarter-turn
representative, from the square itself (`central_parameters_exist`), and the separation
conditions of the model from the packing (`admissible_of_original_geometry`). Translating the
packing to the origin gives the same for every centre (`sharp_uniqueness`).
-/

section
/-!
## The lower bound

For a packing in the disk of squared radius `q ≤ qStar` about the origin, the boundary cycle at
the stationary level (`stationary_normalization_exists`) has the stationary frames
(`sharp_source_entry`), so the dual at the original centres gives `q = qStar`, the five anchors at
their stationary positions and `T`, `G` on their slider lines (`origin_sharp_rigidity`). Hence
every packing of eight unit squares has squared radius at least `qStar`
(`sharp_squared_radius_lower_bound`) and radius at least `stationaryRadius = √qStar`
(`sharp_radius_lower_bound`). At equality the centres of the exterior squares are those of the
stationary family (`source_centers_of_original_anchors`), and with their frames so are the squares
(`source_squares_of_original_centers`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel
open Stationary Coordinates Candidate

theorem origin_sharp_rigidity {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ qStar) :
    ∃ N : GlobalNormalization S qStar,
      SqPacking N.squares (0,0) q ∧
      q=qStar ∧
      Eight.StationaryFrames sharpData N.source.square ∧
      (∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=Eight.stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,
        originalPositions N i.castSucc.castSucc=sharpData.anchorCenters i) ∧
      (∀ e : Fin 7, OriginalDual.gap sharpData (originalPositions N) e=0) ∧
      ∃ Z η : ℝ, originalPositions N 5=sharpData.pT Z ∧
        originalPositions N 6=sharpData.pG η := by
  obtain ⟨N,hN,hselected⟩ := stationary_normalization_exists hp hq
  exact ⟨N,hN,Eight.sharp_original_rigidity N hselected hN hq⟩

/-- Every packing about the origin has squared radius at least `qStar`. -/
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

theorem sharp_radius_sq : stationaryRadius^2=qStar := by
  change (Real.sqrt qStar)^2=qStar
  exact Real.sq_sqrt (by linarith [qStar_limits.1])

theorem sharp_radius_lower_bound {S : Fin 8 → UnitSquare}
    {o : Point} {R : ℝ} (hp : Packing S o R) : stationaryRadius ≤ R := by
  have hq := sharp_squared_radius_lower_bound (packing_sq hp)
  have hR := hp.1
  have hr : 0 ≤ stationaryRadius := Real.sqrt_nonneg _
  nlinarith [sharp_radius_sq]

/-! ## The exterior squares at equality -/

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
    (hf : Eight.StationaryFrames sharpData N.source.square)
    (hc : ∀ i, (N.source.square i).center=sharpData.exteriorCenters Z η i) :
    ∀ i, SameSquare (N.source.square i) (sharpData.exteriorSquares Z η i) := by
  intro i
  have hci := hc i
  have h := hf i
  apply sameSquare_of_physical_center
  · fin_cases i <;> exact hci
  · fin_cases i <;>
      simp only [Eight.canonicalCos,Eight.canonicalSin] at h <;>
      simp only [SamePhysicalFrame,exteriorSquares,axisSquare,tiltedSquare]
    · exact Or.inr (Or.inr (Or.inr ⟨h.1,by rw [h.2]; rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1,by rw [h.2]; rfl⟩))
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨by rw [h.1]; norm_num,h.2⟩)
    · exact Or.inr (Or.inl ⟨by rw [h.1]; norm_num,h.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1,by rw [h.2]; norm_num⟩))

end SquaresInCircles.Eight.GeometricModel
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel
open Stationary Coordinates EqualityParameters

theorem origin_sharp_uniqueness {S : Fin 8 → UnitSquare}
    (hp : SqPacking S (0,0) qStar) :
    ∃ M ∈ stationaryModels, Congruent S (0,0) M := by
  obtain ⟨N,hN,heq,hframes,hnormal,ha,hg,Z,η,hT,hG⟩ :=
    origin_sharp_rigidity hp le_rfl
  have hcenters := source_centers_of_original_anchors N ha hT hG
  have hsquares := source_squares_of_original_centers N hframes hcenters
  obtain ⟨hZ,hη⟩ := N.original_slider_sectors hcenters
    (by simpa [Eight.canonicalCos,Eight.canonicalSin] using hframes 4)
    (by simpa [Eight.canonicalCos,Eight.canonicalSin] using hframes 1)
  obtain ⟨p,hcentral,hcentralCenter,hframe,hpz,hpη⟩ :=
    central_parameters_exist (N.squares 0) Z η
  have hmodel (i : Fin 8) :
      SameSquare (N.squares i) (p.model sharpData i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨fun x => (hcentral.1 x).symm,fun x => (hcentral.2 x).symm⟩
    · have h := hsquares j
      rw [N.source_square] at h
      simpa [EqualityParameters.model,exteriorSquares,hpz,hpη] using h
  have hpmodel : SqPacking (p.model sharpData) (0,0) qStar := by
    refine ⟨hN.1,?_,?_⟩
    · intro i x hx
      exact hN.2.1 i x ((hmodel i).2 x |>.mpr hx)
    · intro i j hij x hx
      exact hN.2.2 i j hij x
        ⟨(hmodel i).1 x |>.mpr hx.1,(hmodel j).1 x |>.mpr hx.2⟩
  have hpcore : ContainsCore p.centralSquare := by
    intro x hx
    exact (hcentral.1 x).mpr (N.central_core x hx)
  have hpadmissible : p.Admissible sharpData :=
    admissible_of_original_geometry hpmodel hpcore hframe
      (by simpa [hpz] using hZ) (by simpa [hpη] using hη)
  refine ⟨stationaryReflectedModel N.reflected p,
    ⟨N.reflected,p,hpadmissible,rfl⟩,?_⟩
  obtain ⟨φ,σ,hφ⟩ := N.congruent
  refine ⟨φ,σ,?_⟩
  intro i x
  have hm :
      (openSquare
        (if N.reflected then reflectDiagonalSquare (N.squares i) else N.squares i) x ↔
        openSquare (stationaryReflectedModel N.reflected p i) x) ∧
      (closedSquare
        (if N.reflected then reflectDiagonalSquare (N.squares i) else N.squares i) x ↔
        closedSquare (stationaryReflectedModel N.reflected p i) x) := by
    cases hb : N.reflected
    · simpa [stationaryReflectedModel,hb] using ⟨(hmodel i).1 x,(hmodel i).2 x⟩
    · simpa [stationaryReflectedModel,hb,reflectDiagonal_open,reflectDiagonal_closed] using
        ⟨(hmodel i).1 (diagonalPoint x),(hmodel i).2 (diagonalPoint x)⟩
  exact ⟨(hφ i x).1.trans hm.1,(hφ i x).2.trans hm.2⟩

def sharpTranslatedToOrigin (S : Fin 8 → UnitSquare) (o : Point) :
    Fin 8 → UnitSquare :=
  fun i => pullSquare o 0 (S i)

theorem sharp_translated_congruent (S : Fin 8 → UnitSquare) (o : Point) :
    Congruent S o (sharpTranslatedToOrigin S o) := by
  refine ⟨0,Equiv.refl _,?_⟩
  intro i x
  exact ⟨(pullSquare_open o 0 (S i) x).symm,
    (pullSquare_closed o 0 (S i) x).symm⟩

/-- Every packing in the disk of radius `stationaryRadius` is congruent to one of
`stationaryModels`. -/
theorem sharp_uniqueness {S : Fin 8 → UnitSquare} {o : Point}
    (hp : Packing S o stationaryRadius) :
    ∃ M ∈ stationaryModels, Congruent S o M := by
  have hp0 := packing_pull hp (0 : Direction)
  have hsq : SqPacking (sharpTranslatedToOrigin S o) (0,0) qStar := by
    have h := packing_sq hp0
    rw [sharp_radius_sq] at h
    exact h
  obtain ⟨M,hM,hcongruent⟩ := origin_sharp_uniqueness hsq
  exact ⟨M,hM,congruent_trans (sharp_translated_congruent S o) hcongruent⟩

end SquaresInCircles.Eight.GeometricModel
end
end
end
