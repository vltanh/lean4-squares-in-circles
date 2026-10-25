module

public import SquaresInCircles.Eight.Boundary.SourceEquality
public import SquaresInCircles.Eight.Corners.GeometricStationaryExistence
public import SquaresInCircles.Eight.Words.Middle.Canonicalization
public import SquaresInCircles.Eight.Words.Wrong.SignCapture

/-!
# Eight squares: rigidity of the aligned hard endpoint at its containing radius

The input is seven squares in the closed disk of squared radius `q`, with two physical frame
directions at a tilt `t ∈ [0, π/4]` (`PhysicalFrames`) and a weak owner on each edge among the
terminal owners (`Witnesses`); neither the tilt nor the centers are assumed stationary.

The selected slacks are the gaps of the five-corner problem (`actual_slack`), so its minimum gives
`qStar ≤ q` (`squared_radius_lower_bound`). For `q ≤ qStar` its unique minimizer identifies the
five anchors of the input, makes all seven contacts tight and leaves exactly the two slider rails
(`sharp_rigidity`).
-/

section
/-!
## Aligning the middle of a hard cycle

The frame order of G and T and the bounds `1/10` on their tangents follow from the hard geometry,
and they feed the replacement of A and B. Every hard input has a hard input at the same `q` with
the common middle frame of A and B between those of T and G and `A.y - B.y = 1`; no anchor circle
increases, the loss is strict when the original middle is not canonical, and the other five
vertices keep their points and frames (`HardInput.canonicalize_middle`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

/-- Every hard input has a hard input with the normalized common middle; no sign bound or frame
order of G and T is assumed. -/
theorem HardInput.canonicalize_middle {q : ℝ} (I : HardInput q) (hq : q≤qCap) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta A∈Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta A≠I.cycle.theta B ∨ I.cycle.theta A<I.cycle.theta T ∨
        I.cycle.theta G<I.cycle.theta A ∨ 1<(I.cycle.point A).y-(I.cycle.point B).y) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  have horder := I.intermediate_order hq
  have hsigns := I.small_intermediate_signs hq
  exact I.canonicalize_middle_ordered hq hsigns.1.le hsigns.2.le horder.le

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
namespace AlignedEndpoint
open GeometricModel Stationary
open OriginalFiveCorner

/-- A weak owner on each edge among the terminal owners, either tied owner at an aligned edge and
the hard owner at a mixed edge, with its feasible witness. -/
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
    SAT.threshold (K i) (K (next i)) = OriginalFiveCorner.width t i := by
  obtain ⟨hcpos,hcle,hspos,hsle⟩ := FiveCorner.angle_trig ht
  have hc (k : Vertex) := (hf k).1
  have hs (k : Vertex) := (hf k).2
  have h0 : Real.cos t*Real.sin t+-(Real.sin t*Real.cos t)=0 := by ring
  fin_cases i <;>
    simp [SAT.threshold,relativeC,relativeS,hc,hs,
      OriginalFiveCorner.frameCos,OriginalFiveCorner.frameSin,
      OriginalFiveCorner.width,next,← pow_two,
      Real.sin_sq_add_cos_sq,abs_of_pos hcpos,abs_of_nonneg hspos,abs_neg] <;>
    first
    | ring1
    | (rw [h0]; norm_num)

/-- The slack of every terminal owner is the corresponding gap of the five-corner problem, for
either tied owner at an aligned edge. -/
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
      Coordinates.pE,Coordinates.pH,Coordinates.inFrame,
      hc,hs] <;> ring

theorem selected_anchor_centers (i : Fin 5) :
    FiveCorner.selected.anchorCenter i=sharpData.anchorCenters i := by
  rw [FiveCorner.selected_eq_stationary]
  exact coordinate_anchor_centers sharpData i

/-- Containment in the disk of squared radius `q` gives `qStar ≤ q`; the containment of a vertex
makes `q` nonnegative, as its square root needs. -/
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

/-- Rigidity of the endpoint: for `q ≤ qStar`, `q = qStar`, the tilt is the selected angle, the
chain is the selected five-corner configuration with the same anchor centers, all seven gaps
vanish, and the squares `4` and `1` lie on the two slider rails. -/
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
  have hc : ∀ i p, closedSquare (K i) p → normSq p ≤ Eight.radius^2 := by
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

end AlignedEndpoint
end SquaresInCircles.Eight
end
end
end
