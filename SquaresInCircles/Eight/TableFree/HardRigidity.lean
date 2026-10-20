module

public import SquaresInCircles.Eight.TableFree.OriginalFiveCorner
public import SquaresInCircles.Eight.TableFree.OriginalWitnesses
public import SquaresInCircles.Eight.GeometricModel.FiveCornerSelection

/-!
# The fully aligned hard endpoint, at its actual containing radius

Uncompiled draft. The input consists of seven actual squares, two physical
frame directions at an arbitrary tilt in the closed quarter interval,
actual containment, and one weak endpoint owner on each neighboring edge.
The tilt and the five centers are not assumed to be stationary.

The five selected original corners satisfy the geometric five-point
problem. Its proved minimum therefore supplies the sharp radius. At that
radius its proved unique minimizer identifies the input's own five anchors,
forces all seven retained contacts to be tight, and leaves precisely the
two slider rails. There is no endpoint-to-ancestor identification here.

This is the endpoint theorem, not the arbitrary-frame `HardInput` reduction.
The latter must still construct this endpoint and track its strict anchor
losses. In particular the hypotheses below must not be advertised as a
consequence of the two hard owners alone.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
namespace AlignedEndpoint
open GeometricModel ExactFamily
open OriginalFiveCorner

/-- Weak tied owners at aligned edges, and the actual hard owner at either
mixed edge. A record stores the chosen physical witness, not just existence
of a nonnegative surrogate projection. -/
structure Witnesses (K : Vertex → UnitSquare) where
  owner : Vertex → Fin 4
  allowed : ∀ i, owner i ∈ Candidate.terminalOwners i
  feasible : ∀ i, (forwardAxis (owner i)).Feasible (K i) (K (next i))

theorem owner_normal {K : Vertex → UnitSquare} {t : ℝ}
    (hf : PhysicalFrames K t) (i : Vertex) (j : Fin 4)
    (hj : j ∈ Candidate.terminalOwners i) :
    (forwardAxis j).normal (K i) (K (next i)) = normal t i := by
  have hc (k : Vertex) := (hf k).1
  have hs (k : Vertex) := (hf k).2
  fin_cases i <;> fin_cases j <;>
    simp [Candidate.terminalOwners] at hj <;>
    simp [forwardAxis,SignedAxis.normal,AxisOwner.normal,AxisSign.value,
      OriginalFiveCorner.normal,OriginalFiveCorner.frameCos,
      OriginalFiveCorner.frameSin,next,hc,hs,scale,Eight.e,Eight.f,
      GeometricModel.e,GeometricModel.f]

theorem actual_threshold {K : Vertex → UnitSquare} {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ Real.pi/4) (hf : PhysicalFrames K t) (i : Vertex) :
    SAT.threshold (K i) (K (next i)) = width t i := by
  obtain ⟨hcpos,hcle,hspos,hsle⟩ := FiveCorner.angle_trig ht
  have hc (k : Vertex) := (hf k).1
  have hs (k : Vertex) := (hf k).2
  have hu : Real.sin t*Real.sin t+Real.cos t*Real.cos t=1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  fin_cases i <;>
    simp [SAT.threshold,relativeC,relativeS,hc,hs,
      OriginalFiveCorner.frameCos,OriginalFiveCorner.frameSin,
      OriginalFiveCorner.width,next,hu,← pow_two,
      Real.sin_sq_add_cos_sq,abs_of_pos hcpos,abs_of_nonneg hspos,abs_neg]

/-- Every selected physical slack is exactly the corresponding original
five-corner gap, including either allowed weak aligned owner. -/
theorem actual_slack {K : Vertex → UnitSquare} {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ Real.pi/4) (hf : PhysicalFrames K t)
    (i : Vertex) (j : Fin 4) (hj : j ∈ Candidate.terminalOwners i) :
    (forwardAxis j).projection (K i) (K (next i)) -
      SAT.threshold (K i) (K (next i)) = gap K t i := by
  rw [SignedAxis.projection,owner_normal hf i j hj,actual_threshold ht hf]
  rfl

theorem retained_separators {K : Vertex → UnitSquare} {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ Real.pi/4) (hf : PhysicalFrames K t)
    (w : Witnesses K) : RetainedSeparators K t := by
  intro i
  rw [← actual_slack ht hf i (w.owner i) (w.allowed i)]
  exact sub_nonneg.mpr (w.feasible i)

theorem coordinate_residuals_zero (d : Coordinates) (i : Fin 5) :
    residual (FiveCorner.ofCoordinates d) i = 0 := by
  obtain ⟨hab,hbd,hde,heh,hah⟩ := FiveCorner.coordinate_contacts d
  obtain ⟨hc,hs⟩ := FiveCornerGeometry.coordinateAngle_frame d
  fin_cases i
  · change (d.anchorPoints 1).2-(d.anchorPoints 0).2-2=0
    linarith
  · change (d.anchorPoints 1).1-(d.anchorPoints 2).1-3=0
    linarith
  · change (d.anchorPoints 2).2-(d.anchorPoints 3).2-2=0
    linarith
  · change projection (GeometricModel.f (FiveCornerGeometry.coordinateAngle d))
        (sub (d.anchorPoints 3) (d.anchorPoints 4)) -
        (1+Real.sin (FiveCornerGeometry.coordinateAngle d))=0
    rw [projection_eq_dot,FiveCorner.coordinate_f,hs,heh]
    ring
  · change projection (GeometricModel.e (FiveCornerGeometry.coordinateAngle d))
        (sub (d.anchorPoints 0) (d.anchorPoints 4)) -
        (2+Real.cos (FiveCornerGeometry.coordinateAngle d))=0
    rw [projection_eq_dot,FiveCorner.coordinate_e,hc,hah]
    ring

theorem selected_residuals_zero (i : Fin 5) :
    residual FiveCorner.selected i=0 := by
  rw [FiveCorner.selected_eq_stationary]
  exact coordinate_residuals_zero sharpData i

theorem coordinate_anchor_centers (d : Coordinates) (i : Fin 5) :
    (FiveCorner.ofCoordinates d).anchorCenter i = d.anchorCenters i := by
  obtain ⟨hc,hs⟩ := FiveCornerGeometry.coordinateAngle_frame d
  fin_cases i <;> ext <;>
    simp [FiveCorner.ofCoordinates,FiveCorner.anchorCenter,Coordinates.anchorPoints,
      Coordinates.anchorCenters,Coordinates.pA,Coordinates.pB,Coordinates.pD,
      Coordinates.pE,Coordinates.pH,Coordinates.inFrame,GeometricModel.e,
      GeometricModel.f,hc,hs] <;> ring

theorem selected_anchor_centers (i : Fin 5) :
    FiveCorner.selected.anchorCenter i=sharpData.anchorCenters i := by
  rw [FiveCorner.selected_eq_stationary]
  exact coordinate_anchor_centers sharpData i

/-- No numerical lower radius cutoff is used: containment of an actual
vertex itself gives the nonnegative squared radius needed for its square root. -/
theorem squared_radius_lower_bound {K : Vertex → UnitSquare} {t q : ℝ}
    (ht : 0 ≤ t ∧ t ≤ Real.pi/4) (hf : PhysicalFrames K t)
    (w : Witnesses K)
    (hcontained : ∀ i p, closedSquare (K i) p → normSq p ≤ q) :
    qStar ≤ q := by
  have hvertex := corner_is_original_vertex hf (0 : Fin 5)
  have hq0 : 0 ≤ q :=
    (normSq_nonneg _).trans (hcontained _ _ hvertex)
  have hs := retained_separators ht hf w
  have hr := OriginalFiveCorner.radius_lower_bound ht (Real.sqrt_nonneg q) hf hs
    (by intro i p hp; simpa [Real.sq_sqrt hq0] using hcontained i p hp)
  have hrad := FiveCorner.radius_nonneg
  have hsqrt := Real.sqrt_nonneg q
  have hsquare := Real.sq_sqrt hq0
  have hsharp := FiveCorner.radius_sq_eq_stationary
  nlinarith

/-- Full endpoint rigidity from geometric input alone. All five anchor
centers and all seven gaps here are those of the input record. -/
theorem sharp_rigidity {K : Vertex → UnitSquare} {t q : ℝ}
    (ht : 0 ≤ t ∧ t ≤ Real.pi/4) (hf : PhysicalFrames K t)
    (w : Witnesses K)
    (hcontained : ∀ i p, closedSquare (K i) p → normSq p ≤ q)
    (hq : q ≤ qStar) :
    q=qStar ∧
      t=FiveCorner.selected.angle ∧
      chain K t=FiveCorner.selected ∧
      (∀ i, (K (anchorIndex i)).center=FiveCorner.selected.anchorCenter i) ∧
      (∀ i, gap K t i=0) ∧
      ∃ z η, (K 4).center=FiveCorner.selected.topCenter z ∧
        (K 1).center=FiveCorner.selected.tiltedCenter η := by
  have hqeq : q=qStar :=
    le_antisymm hq (squared_radius_lower_bound ht hf w hcontained)
  have hs := retained_separators ht hf w
  have hc : ∀ i p, closedSquare (K i) p → normSq p ≤ FiveCorner.radius^2 := by
    intro i p hp
    rw [FiveCorner.radius_sq_eq_stationary]
    exact (hcontained i p hp).trans hq
  have hm : FiveCorner.IsMinimizer (chain K t) :=
    ⟨chain_spans ht hs,chain_fits FiveCorner.radius_nonneg hf hc⟩
  have he : chain K t=FiveCorner.selected :=
    (FiveCorner.minimizer_eq_canonical hm).trans FiveCorner.selected_eq_canonical.symm
  obtain ⟨hangle,hanchors⟩ := original_anchor_centers he
  have hgaps := all_original_contacts_tight hs
    (by intro i; rw [he]; exact selected_residuals_zero i)
  exact ⟨hqeq,hangle,he,hanchors,hgaps,original_sliders he hgaps⟩

theorem stationary_frames_of_selected_angle {K : Vertex → UnitSquare} {t : ℝ}
    (hf : PhysicalFrames K t) (ht : t=FiveCorner.selected.angle) :
    StationaryFrames sharpData K := by
  obtain ⟨hc,hs⟩ := FiveCornerGeometry.coordinateAngle_frame sharpData
  intro i
  obtain ⟨hci,hsi⟩ := hf i
  rw [ht,FiveCorner.selected_angle] at hci hsi
  fin_cases i <;>
    simpa [OriginalFiveCorner.frameCos,OriginalFiveCorner.frameSin,
      canonicalCos,canonicalSin,hc,hs] using And.intro hci hsi

theorem normal_at_selected_angle (i : Vertex) :
    normal FiveCorner.selected.angle i=stationaryNormal sharpData i := by
  obtain ⟨hc,hs⟩ := FiveCornerGeometry.coordinateAngle_frame sharpData
  rw [FiveCorner.selected_angle]
  fin_cases i <;>
    simp [OriginalFiveCorner.normal,stationaryNormal,GeometricModel.e,
      GeometricModel.f,Coordinates.e,hc,hs]

/-- Every retained endpoint owner has the stationary physical direction.
Weak ties on the aligned edges are preserved literally. -/
theorem selected_normals {K : Vertex → UnitSquare} {t q : ℝ}
    (ht : 0 ≤ t ∧ t ≤ Real.pi/4) (hf : PhysicalFrames K t)
    (w : Witnesses K)
    (hcontained : ∀ i p, closedSquare (K i) p → normSq p ≤ q)
    (hq : q ≤ qStar) :
    StationaryFrames sharpData K ∧
      (∀ i, (forwardAxis (w.owner i)).normal (K i) (K (next i)) =
        stationaryNormal sharpData i) ∧
      ∀ i, (forwardAxis (w.owner i)).projection (K i) (K (next i)) -
        SAT.threshold (K i) (K (next i))=0 := by
  have h := sharp_rigidity ht hf w hcontained hq
  refine ⟨stationary_frames_of_selected_angle hf h.2.1,?_,?_⟩
  · intro i
    rw [owner_normal hf i (w.owner i) (w.allowed i),h.2.1]
    exact normal_at_selected_angle i
  · intro i
    rw [actual_slack ht hf i (w.owner i) (w.allowed i)]
    exact h.2.2.2.2.1 i

/-- A strict retained contact is an equality obstruction. It suffices at HG
or TD even though neither free intermediate is required to touch the circle. -/
theorem no_strict_retained_contact {K : Vertex → UnitSquare} {t q : ℝ}
    (ht : 0 ≤ t ∧ t ≤ Real.pi/4) (hf : PhysicalFrames K t)
    (w : Witnesses K)
    (hcontained : ∀ i p, closedSquare (K i) p → normSq p ≤ q)
    (hq : q ≤ qStar) (i : Vertex) :
    ¬ 0 < (forwardAxis (w.owner i)).projection (K i) (K (next i)) -
      SAT.threshold (K i) (K (next i)) := by
  have hzero := (selected_normals ht hf w hcontained hq).2.2 i
  rw [hzero]
  exact lt_irrefl 0

end AlignedEndpoint
end SquaresInCircles.Eight.TableFree
