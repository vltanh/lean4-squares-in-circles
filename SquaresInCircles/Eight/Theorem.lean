module

public import SquaresInCircles.Eight.GlobalNormalization
public import SquaresInCircles.Eight.Candidate.Capture
public import SquaresInCircles.Eight.ExactFamily.CentralParameters
public import SquaresInCircles.Eight.ExactFamily.BoxRigidity

/-!
# The unrestricted eight-square theorem

Uncompiled source draft.  The boundary terminal is applied to the recovered
cycle at `max q qMinus`.  Candidate capture is computed at Q1 and pulled back
through the radius expansion.  When equality forces the five frame errors
to vanish, the stationary identity is evaluated a second time on the
untouched original centers.  Its five positive circle weights fix the five
anchors; its zero slider forces leave exactly the two displayed sliders.
Original cyclic order supplies the two slider sectors only at that stage.

The public optimum includes the full weak equality domain and a reflected
branch.  The final box theorem distinguishes parameters even under arbitrary
distance preserving bijections and square relabeling.
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
  apply Terminal.boundary_rigid F hq
    (show K.z∈tiltBox by
      constructor <;> dsimp [tiltBox] <;> linarith [K.z_lower,K.z_upper])
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
  intro i
  have hc := C.frame_cos i
  have hs := C.frame_sin i
  change (C.square i).cosine=Real.cos (C.canonicalAngle i) at hc
  change (C.square i).sine=Real.sin (C.canonicalAngle i) at hs
  rw [F.canonical_eq,hθ] at hc hs
  fin_cases i <;>
    simp [sharpCanonicalCos,sharpCanonicalSin,offsets,Real.cos_add,Real.sin_add,
      Real.cos_sub,Real.sin_sub,hcos,hsin] at hc hs ⊢ <;> exact ⟨hc,hs⟩

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
  have hclosed : closedSquare (N.source.square (OriginalDual.cycleIndex i.castSucc.castSucc))
      (add (N.originalPositions i.castSucc.castSucc) (sharpData.anchorOffsets i)) := by
    have hc (j : Vertex) := (hframe j).1
    have hs (j : Vertex) := (hframe j).2
    fin_cases i <;>
      simp [closedSquare,localX,localY,originalPositions,OriginalDual.ofCycle,
        OriginalDual.cycleIndex,anchorOffsets,inFrame,add,hc,hs,
        sharpCanonicalCos,sharpCanonicalSin] <;>
      nlinarith [sharpData.unit]
  have hh := N.packing.2.1
    (OriginalDual.cycleIndex i.castSucc.castSucc).succ _
    (by simpa [N.source_square] using hclosed)
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
  have hc (i : Vertex) := (hframe i).1
  have hs (i : Vertex) := (hframe i).2
  have hu : sharpData.s*sharpData.s+sharpData.c*sharpData.c=1 := by
    nlinarith [sharpData.unit]
  have hw := sharpData_stationary.weightDomain
  have hthreshold (i : Vertex) :
      SAT.threshold (N.source.square i) (N.source.square (next i))=
        if i=1 ∨ i=6 then (1+sharpData.c+sharpData.s)/2 else 1 := by
    fin_cases i <;>
      simp [SAT.threshold,relativeC,relativeS,hc,hs,sharpCanonicalCos,sharpCanonicalSin,
        next,hu,← pow_two,sharpData.unit,abs_of_pos hw.c_pos,abs_of_pos hw.s_pos,abs_neg]
  have hmem0 := hjmem 0; have hmem1 := hjmem 1; have hmem2 := hjmem 2
  have hmem3 := hjmem 3; have hmem4 := hjmem 4; have hmem5 := hjmem 5; have hmem6 := hjmem 6
  have hsep0 := hjsep 0; have hsep1 := hjsep 1; have hsep2 := hjsep 2
  have hsep3 := hjsep 3; have hsep4 := hjsep 4; have hsep5 := hjsep 5; have hsep6 := hjsep 6
  simp only [terminalOwners,Finset.mem_insert,Finset.mem_singleton,
    Matrix.cons_val_zero,Matrix.cons_val_succ] at hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 hmem6
  simp only [SignedAxis.Feasible,hthreshold] at hsep0 hsep1 hsep2 hsep3 hsep4 hsep5 hsep6
  intro e
  fin_cases e <;> rcases hmem0 with hmem0 | hmem0 <;>
    rcases hmem2 with hmem2 | hmem2 <;> rcases hmem3 with hmem3 | hmem3 <;>
    rcases hmem4 with hmem4 | hmem4 <;> rcases hmem5 with hmem5 | hmem5
  all_goals
    simp [OriginalDual.gap,originalPositions,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      SignedAxis.projection,SignedAxis.normal,AxisOwner.normal,AxisSign.value,forwardAxis,
      e,f,Coordinates.e,Coordinates.f,scale,dot,sub,next,hc,hs,
      sharpCanonicalCos,sharpCanonicalSin,hmem0,hmem1,hmem2,hmem3,hmem4,hmem5,hmem6]
      at hsep0 hsep1 hsep2 hsep3 hsep4 hsep5 hsep6 ⊢
  all_goals linarith

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
    simpa [translatedToOrigin,radius_sq] using packing_sq horigin
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
    (∀ p : EqualityParameters,p.InBox→Packing (p.model sharpData) (0,0) radius) ∧
    (∀ p r : EqualityParameters,p.InBox→r.InBox→
      (BoxRigidity.RigidlyCongruent (p.model sharpData) (r.model sharpData)↔p=r)) :=
  ⟨fun _ hp=>whole_box_packing hp,fun _ _ hp hr=>BoxRigidity.box_rigidlyCongruent_iff hp hr⟩

end SquaresInCircles.Eight
