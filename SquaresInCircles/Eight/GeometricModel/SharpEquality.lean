module

public import SquaresInCircles.Eight.GeometricModel.SharpAssembly
public import SquaresInCircles.Eight.ExactFamily.CentralParameters

/-!
# Equality reconstruction from the fresh sharp boundary

Uncompiled source draft.

This reconstructs the full existing exact equality family from the original
centers returned by SharpAssembly.origin_sharp_rigidity. The original cyclic
order supplies the slider sectors only after anchor recovery. Central
parameters come from the actual central square, including its quarter-turn
representative, and all model separation constraints come from the unchanged
original packing.

No theorem in Eight.Theorem is imported or called. The compatibility capture
dependencies are exactly those disclosed in SharpAssembly; the remaining
parameter reconstruction uses the existing exact-family geometry.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily Coordinates EqualityParameters

theorem origin_sharp_uniqueness {S : Fin 8 → UnitSquare}
    (hp : SqPacking S (0,0) qStar) :
    ∃ M ∈ Eight.models, Congruent S (0,0) M := by
  obtain ⟨N,hN,heq,hframes,hnormal,ha,hg,Z,η,hT,hG⟩ :=
    origin_sharp_rigidity hp le_rfl
  have hcenters := source_centers_of_original_anchors N ha hT hG
  have hsquares := source_squares_of_original_centers N hframes hcenters
  obtain ⟨hZ,hη⟩ := N.original_slider_sectors hcenters
    (by simpa [TableFree.canonicalCos,TableFree.canonicalSin] using hframes 4)
    (by simpa [TableFree.canonicalCos,TableFree.canonicalSin] using hframes 1)
  obtain ⟨p,hcentral,hcentralCenter,hframe,hpz,hpη⟩ :=
    central_parameters_exist (N.squares 0) Z η
  have hmodel (i : Fin 8) :
      SameSquare (N.squares i) (p.model sharpData i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨fun x => (hcentral.1 x).symm,fun x => (hcentral.2 x).symm⟩
    · have h := hsquares j
      rw [N.source_square] at h
      simpa [model,exteriorSquares,hpz,hpη] using h
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
  refine ⟨Eight.reflectedModel N.reflected p,
    ⟨N.reflected,p,hpadmissible,rfl⟩,?_⟩
  obtain ⟨φ,σ,hφ⟩ := N.congruent
  refine ⟨φ,σ,?_⟩
  intro i x
  have hm :
      (openSquare
        (if N.reflected then reflectDiagonalSquare (N.squares i) else N.squares i) x ↔
        openSquare (Eight.reflectedModel N.reflected p i) x) ∧
      (closedSquare
        (if N.reflected then reflectDiagonalSquare (N.squares i) else N.squares i) x ↔
        closedSquare (Eight.reflectedModel N.reflected p i) x) := by
    cases hb : N.reflected
    · simpa [Eight.reflectedModel,hb] using ⟨(hmodel i).1 x,(hmodel i).2 x⟩
    · simpa [Eight.reflectedModel,hb,reflectDiagonal_open,reflectDiagonal_closed] using
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

/-- Fresh-sharp equality classification for arbitrary circle center and
arbitrary original labels and orientations. -/
theorem sharp_uniqueness {S : Fin 8 → UnitSquare} {o : Point}
    (hp : Packing S o Eight.radius) :
    ∃ M ∈ Eight.models, Congruent S o M := by
  have hp0 := packing_pull hp (0 : Direction)
  have hsq : SqPacking (sharpTranslatedToOrigin S o) (0,0) qStar := by
    simpa [sharpTranslatedToOrigin,sharp_radius_sq] using packing_sq hp0
  obtain ⟨M,hM,hcongruent⟩ := origin_sharp_uniqueness hsq
  exact ⟨M,hM,congruent_trans (sharp_translated_congruent S o) hcongruent⟩

theorem sharp_packing_iff_models (S : Fin 8 → UnitSquare) (o : Point) :
    Packing S o Eight.radius ↔ ∃ M ∈ Eight.models, Congruent S o M := by
  constructor
  · exact sharp_uniqueness
  · rintro ⟨M,hM,hcongruent⟩
    exact hcongruent.packing (Eight.model_packing M hM)

end SquaresInCircles.Eight.GeometricModel
