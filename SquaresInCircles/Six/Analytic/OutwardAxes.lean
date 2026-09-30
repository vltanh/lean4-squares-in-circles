import SquaresInCircles.Six.PinAxes
import SquaresInCircles.Six.Normalization.CenterRadius

/-!
# A uniform primary-axis exclusion before the D-edge classification

Every exterior center lies in the radius-rho0 disk, while its own primary
coordinate is at least aMin. Therefore another center can advance by at most
rho0-aMin < 1/2 in that outward primary direction. A square-pair threshold is
at least 1/2, so that direction cannot separate the pair. The same argument
excludes the negative primary direction of the destination square.

This applies to every normalized exterior pair. It replaces these elementary
branches without a stress table, any narrower candidate angle domain, or any
assumption about the two surviving diagonal secondary edges.
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

/-- Source 0 is the outward primary of the source square; source 5 is the
negative primary of the destination. Neither is possible for any exterior pair. -/
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

/-- Four genuinely possible directed W/D sources, before the remaining primary
and secondary stress reductions. Nothing asserts yet that only source 2 survives. -/
theorem analytic_DW_four_sources {R : ℝ} (P : NormalizedPacking R) :
    ∃ k : Fin 8,
      Seven.SAT.threshold (P.square 2) (P.square 3)≤
        dot (Stress.pairNormal k (P.square 2) (P.square 3))
          (sub (P.square 3).center (P.square 2).center) ∧
      (k=1 ∨ k=2 ∨ k=4 ∨ k=6) := by
  obtain ⟨k,hk,h3,h7⟩ := P.DW_source
  have he := normalized_outward_axes_excluded P 2 3 k hk
  refine ⟨k,hk,?_⟩
  fin_cases k <;> simp_all

/-- The same four-source reduction for D/S. In particular negative S-primary
requires no stress-table row: it is the universally excluded destination axis. -/
theorem analytic_DS_four_sources {R : ℝ} (P : NormalizedPacking R) :
    ∃ k : Fin 8,
      Seven.SAT.threshold (P.square 3) (P.square 4)≤
        dot (Stress.pairNormal k (P.square 3) (P.square 4))
          (sub (P.square 4).center (P.square 3).center) ∧
      (k=1 ∨ k=2 ∨ k=4 ∨ k=6) := by
  obtain ⟨k,hk,h0,h3,h7⟩ := P.DS_source
  have he := normalized_outward_axes_excluded P 3 4 k hk
  refine ⟨k,hk,?_⟩
  fin_cases k <;> simp_all

end SquaresInCircles.Six.Analytic
