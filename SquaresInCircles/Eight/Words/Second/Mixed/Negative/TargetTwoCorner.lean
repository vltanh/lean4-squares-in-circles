module

public import SquaresInCircles.Eight.Words.Second.Mixed.CurvatureChord
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCornerCurvature
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCornerReferences

/-!
# Eight squares: the complete negative-core corner primary owner

The two endpoint curves are bounded by their exact interior references
and a uniform positive angular curvature. Concavity in the core
coordinate handles the whole early corner, and the explicit chord
loss handles the whole late corner. The final comparison uses only
the original weak separator and original physical source.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic

lemma join_mem : (1/2:ℝ)∈MixedCorner.domain :=
  ⟨le_rfl,by linarith [CoreAngleEndpoint.diagonal_bounds.1]⟩
lemma diagonal_mem : dc∈MixedCorner.domain :=
  ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl⟩

theorem diagonal_lower {φ : ℝ} (hφ : φ∈angles) : (3591/4000:ℝ)<f dc φ := by
  have hr : (1049/1000:ℝ)∈angles :=
    ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have ht := curvature_tangent (f := f dc) (d := fAngle dc) (dd := fAngleD dc)
    (κ := (1/20:ℝ)) hφ hr (fun φ _ => f_angle_hasDerivAt dc φ)
    (fun φ _ => fAngle_hasDerivAt dc φ) (fun _ hx => (angle_curvature diagonal_mem hx).le)
  have hd := abs_lt.mp diagonal_reference.2
  have hs : (fAngle dc (1049/1000))^2<(1/1000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((1/20)*(φ-1049/1000)+fAngle dc (1049/1000))
  nlinarith [diagonal_reference.1]

theorem join_lower {φ : ℝ} (hφ : φ∈angles) : (4501/5000:ℝ)<f (1/2) φ := by
  have hr : (29/25:ℝ)∈angles :=
    ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have ht := curvature_tangent (f := f (1/2)) (d := fAngle (1/2)) (dd := fAngleD (1/2))
    (κ := (1/20:ℝ)) hφ hr (fun φ _ => f_angle_hasDerivAt (1/2) φ)
    (fun φ _ => fAngle_hasDerivAt (1/2) φ) (fun _ hx => (angle_curvature join_mem hx).le)
  have hd := abs_lt.mp join_reference.2
  have hs : (fAngle (1/2) (29/25))^2<(1/2500:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((1/20)*(φ-29/25)+fAngle (1/2) (29/25))
  nlinarith [join_reference.1]

theorem diagonal_late {φ : ℝ} (hφ : φ∈lateAngles) : (89849/100000:ℝ)<f dc φ := by
  have hr : (11/10:ℝ)∈angles :=
    ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have ht := curvature_tangent (f := f dc) (d := fAngle dc) (dd := fAngleD dc)
    (κ := (1/20:ℝ)) (late_subset hφ) hr (fun φ _ => f_angle_hasDerivAt dc φ)
    (fun φ _ => fAngle_hasDerivAt dc φ) (fun _ hx => (angle_curvature diagonal_mem hx).le)
  have hp := mul_nonneg late_reference.2.le (sub_nonneg.mpr hφ.1)
  nlinarith [late_reference.1,sq_nonneg (φ-11/10)]

theorem lower {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) : γ<f B φ := by
  by_cases he : φ≤11/10
  · have hc : ConcaveOn ℝ (Icc (1/2) dc) (fun B => f B φ) :=
      concave_of_deriv2 (fun _ hB => f_core_hasDerivAt hB)
        (fun _ hB => fB_hasDerivAt hB) (fun _ hB => (early_curvature hB hφ he).le)
    exact concave_gt_of_endpoints (f := fun B => f B φ) hc hB
      (by dsimp only [γ]; linarith [join_lower hφ]) (by dsimp only [γ]; linarith [diagonal_lower hφ])
  · have hlate : φ∈lateAngles := ⟨by linarith,hφ.2⟩
    have hh := curvature_chord_lower (f := fun B => f B φ) (d := fun B => fB B φ)
      (dd := fun B => fBB B φ) (l := 1/2) (u := dc) (κ := (7/4:ℝ)) (m := (89849/100000:ℝ))
      hB (by norm_num)
      (fun _ hB => f_core_hasDerivAt hB) (fun _ hB => fB_hasDerivAt hB)
      (fun _ hB => (late_curvature hB hlate).le)
      (by linarith [join_lower hφ]) (diagonal_late hlate)
    have hlength : 0≤dc-1/2 ∧ dc-1/2<(59/1000:ℝ) := by
      exact ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],
        by linarith [CoreAngleEndpoint.diagonal_bounds.2]⟩
    have hs : (dc-1/2)^2<(59/1000:ℝ)^2 := by nlinarith
    dsimp only [γ] at hh ⊢
    linarith

theorem original_primary {a b A B φ : ℝ} (hs : OuterState a b)
    (hB : 1/2≤B) (hBA : B≤A) (hcircle : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2)
    (hφ : PositiveThree.Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) :
    γ<value b A B φ := by
  have ht : CoreState A B := Or.inr ⟨hB,hBA,hcircle⟩
  by_cases he : (1191/1000:ℝ)≤φ
  · exact corner_tail hs ht hB he
  · have hangle : φ∈angles := ⟨hφ.1,by linarith⟩
    obtain ⟨hdom,rfl⟩ := MixedCorner.actual hB hBA hcircle
    have hu := u_bounds hdom hangle
    have heq : 1+(MixedCorner.a B+1/2)*Real.cos φ+(1/2-B)*Real.sin φ=u B φ := by
      dsimp [u]
      ring
    have hh := primary_height_lower hs
      (show 1+(MixedCorner.a B+1/2)*Real.cos φ+(1/2-B)*Real.sin φ∈PHeightBounds.heights by
        rw [heq]
        exact ⟨by linarith [hu.1],by linarith [hu.2]⟩) hsep
    rw [heq] at hh
    exact (lower hdom hangle).trans hh

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
