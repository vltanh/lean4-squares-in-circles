import SquaresInCircles.Six.PinAxes
import SquaresInCircles.Six.Normalization.CenterRadius

/-!
# Outward axes do not separate

Every exterior centre lies within `ρ0` of the disk centre, and its coordinate
along its primary axis is at least `aMin = 2 - ρ0`. So the centre of another
square lies less than `ρ0 - aMin < 1/2` further out along that axis, while the
threshold of a pair of squares is at least `1/2`. Hence two exterior squares are
never separated along the outward primary axis of the first, nor along the
inward primary axis of the second.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma frame_primary_le_rho0 (S : UnitSquare) {p : Point}
    (hp : normSq p≤rho0^2) : frameX S p≤rho0 := by
  have hf := frame_norm S p
  have hsq : (frameX S p)^2≤rho0^2 := by
    nlinarith [sq_nonneg (frameY S p)]
  by_contra! h
  have hh := mul_pos (sub_pos.mpr h)
    (show 0<frameX S p+rho0 by linarith [rho0_gt_one])
  nlinarith

lemma pair_threshold_ge_half (S T : UnitSquare) : 1/2≤Seven.SAT.threshold S T := by
  dsimp [Seven.SAT.threshold]
  linarith [abs_nonneg (relativeC S T),abs_nonneg (relativeS S T)]

lemma outward_primary_projection_small {S T : UnitSquare}
    (hS : aMin≤frameX S S.center) (hT : normSq T.center≤rho0^2) :
    dot (normalX S) (sub T.center S.center)<1/2 := by
  have hproj := frame_primary_le_rho0 S hT
  have hid : dot (normalX S) (sub T.center S.center)=frameX S T.center-frameX S S.center := by
    dsimp [dot,normalX,frameX,sub]
    ring
  rw [hid]
  dsimp [aMin] at hS
  linarith [rho0_upper]

lemma inward_destination_projection_small {S T : UnitSquare}
    (hT : aMin≤frameX T T.center) (hS : normSq S.center≤rho0^2) :
    dot (scale (-1) (normalX T)) (sub T.center S.center)<1/2 := by
  have h := outward_primary_projection_small (S := T) (T := S) hT hS
  have hid : dot (scale (-1) (normalX T)) (sub T.center S.center)=
      dot (normalX T) (sub S.center T.center) := by
    dsimp [dot,scale,sub]
    ring
  rwa [hid]

lemma normalized_center_radius {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    normSq (P.square i).center≤rho0^2 := by
  have hphi : phi (alpha (P.square i) (0,0)) (beta (P.square i) (0,0))≤Q0 := by
    rw [P.square_def,orientedSquare_alpha,orientedSquare_beta]
    simpa only [phi,abs_of_nonneg (show 0≤P.radial i by linarith [(P.contained i).half_le])]
      using (P.contained i).containment
  have h := center_radius_sq hphi
  simpa [sub] using h

lemma normalized_primary_lower {R : ℝ} (P : NormalizedPacking R) (i : Fin 5) :
    aMin≤frameX (P.square i) (P.square i).center := by
  have hf := oriented_frame_centerX (P.phase i) (P.radial i) (P.transverse i)
  have he : frameX (P.square i) (P.square i).center=P.radial i := by
    simpa [P.square_def,sub] using hf
  rw [he]
  exact (P.contained i).aMin_le (P.avoidsCore i)

/-- Two exterior squares are not separated along the pair normals `0` and `5`,
the outward primary axis of the first and the inward primary axis of the
second. -/
theorem normalized_outward_axes_excluded {R : ℝ} (P : NormalizedPacking R)
    (i j : Fin 5) (k : Fin 8)
    (hsep : Seven.SAT.threshold (P.square i) (P.square j)≤
      dot (Stress.pairNormal k (P.square i) (P.square j))
        (sub (P.square j).center (P.square i).center)) : k≠0 ∧ k≠5 := by
  have hthreshold := pair_threshold_ge_half (P.square i) (P.square j)
  constructor
  · intro hk
    subst k
    have hsmall := outward_primary_projection_small
      (normalized_primary_lower P i) (normalized_center_radius P j)
    change Seven.SAT.threshold (P.square i) (P.square j)≤
      dot (normalX (P.square i)) (sub (P.square j).center (P.square i).center) at hsep
    linarith
  · intro hk
    subst k
    have hsmall := inward_destination_projection_small
      (normalized_primary_lower P j) (normalized_center_radius P i)
    change Seven.SAT.threshold (P.square i) (P.square j)≤
      dot (scale (-1) (normalX (P.square j)))
        (sub (P.square j).center (P.square i).center) at hsep
    linarith

end SquaresInCircles.Six.Analytic
