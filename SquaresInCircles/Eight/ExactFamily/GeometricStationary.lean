module

public import SquaresInCircles.Eight.ExactFamily.EnvelopeDifferentiation
public import SquaresInCircles.Eight.ExactFamily.RadiusMonotonicity

/-!
# Global uniqueness of the actual stationary chain

The broad algebraic stationary predicate supplies an interior critical
point of the actual position envelope.  The geometric envelope theorem
makes that point a global minimum over the full tilt interval.  Strict
finite radius decrease first identifies its radius; critical-point
uniqueness then identifies its tilt, and full-domain position convexity
identifies the chain.

No local root box, root subdivision, or assumed global-minimum contract
occurs in the final theorem.  The Lean source remains uncompiled.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

open Set

def coordinateAngle (d : Coordinates) : ℝ := 2*Real.arctan d.z

/-- The rational half-angle coordinates are exactly the sine and cosine
of the selected real angle, for every algebraic chain parameter. -/
theorem coordinateAngle_frame (d : Coordinates) :
    Real.cos (coordinateAngle d)=d.c ∧ Real.sin (coordinateAngle d)=d.s := by
  have hp : 0<1+d.z^2 := halfAngle_den_pos d.z
  have hs : (Real.sqrt (1+d.z^2))^2=1+d.z^2 := Real.sq_sqrt hp.le
  have hzs := congrArg (fun x : ℝ => d.z*x) hs
  have hn : Real.sqrt (1+d.z^2)≠0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  constructor
  · rw [coordinateAngle,Real.cos_two_mul,Real.cos_arctan]
    dsimp [Coordinates.c,halfAngleCos]
    field_simp [hn,ne_of_gt hp]
    nlinarith
  · rw [coordinateAngle,Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
    dsimp [Coordinates.s,halfAngleSin]
    field_simp [hn,ne_of_gt hp]
    nlinarith

theorem stationary_angle_mem {d : Coordinates} (hd : d.IsStationary) :
    coordinateAngle d∈tiltInterval := by
  have hpos : 0<Real.arctan d.z := Real.arctan_pos.mpr hd.z_pos
  have he := Real.two_mul_arctan (by linarith [hd.z_pos] : -1<d.z) hd.z_lt_one
  have hupper := Real.arctan_strictMono hd.tilt_range
  change 0<2*Real.arctan d.z ∧ 2*Real.arctan d.z<Real.arctan (1/5)
  constructor
  · linarith
  · rw [he]
    exact hupper

/-- The position selected by the actual envelope agrees with the
algebraic stationary chain on the entire original radical domain. -/
theorem stationary_minimizingPosition {d : Coordinates} (hd : d.IsStationary) :
    minimizingPosition d.q (coordinateAngle d)= -d.y := by
  have hcritical := stationary_isStripCritical hd
  obtain ⟨hc,hs⟩ := coordinateAngle_frame d
  dsimp only [minimizingPosition]
  rw [hc,hs]
  exact windowMinimizer_eq_of_stationary hd.q_lower hd.q_upper
    hcritical.cosine_pos hcritical.sine_nonneg hcritical.unit hcritical.tilt_upper
    hcritical.strip.bounds.domain hcritical.position_derivative_zero

theorem stationary_envelope_zero {d : Coordinates} (hd : d.IsStationary) :
    positionEnvelope d.q (coordinateAngle d)=0 := by
  rw [positionEnvelope_eq]
  change defect d.q (Real.cos (coordinateAngle d)) (Real.sin (coordinateAngle d))
    (minimizingPosition d.q (coordinateAngle d))=0
  obtain ⟨hc,hs⟩ := coordinateAngle_frame d
  rw [stationary_minimizingPosition hd,hc,hs,coordinate_defect hd.toIsChain]
  exact hd.zero_defect

theorem stationary_envelope_critical {d : Coordinates} (hd : d.IsStationary) :
    deriv (positionEnvelope d.q) (coordinateAngle d)=0 := by
  have hderiv := (positionEnvelope_hasDerivAt hd.q_lower hd.q_upper (stationary_angle_mem hd)).deriv
  obtain ⟨hc,hs⟩ := coordinateAngle_frame d
  rw [stationary_minimizingPosition hd,hc,hs,coordinate_tiltFirst hd.toIsChain] at hderiv
  exact hderiv.trans hd.tilt_stationary

/-- This is global angular minimality for the actual chain, proved from
the geometric Hessian and the intervening-maximum argument. -/
theorem stationary_envelope_nonneg {d : Coordinates} (hd : d.IsStationary)
    {t : ℝ} (ht : t∈Icc 0 (Real.arctan (1/5))) :
    0 ≤ positionEnvelope d.q t := by
  have hm := positionEnvelope_critical_global_minimum hd.q_lower hd.q_upper
    (stationary_angle_mem hd) (stationary_envelope_critical hd) t ht
  rwa [stationary_envelope_zero hd] at hm

/-- Two stationary zeros cannot have distinct radii: evaluate the
larger-radius envelope at the smaller-radius critical tilt. -/
theorem stationary_radius_eq {d e : Coordinates} (hd : d.IsStationary) (he : e.IsStationary) :
    d.q=e.q := by
  have htd := stationary_angle_mem hd
  have hte := stationary_angle_mem he
  obtain ⟨hcd,hsd,_⟩ := tiltInterval_bounds htd
  obtain ⟨hce,hse,_⟩ := tiltInterval_bounds hte
  rcases lt_trichotomy d.q e.q with hlt | hq | hlt
  · have hdecrease := positionEnvelope_radius_decrease hd.q_lower he.q_upper hlt hcd hsd.le
    have hnonneg := stationary_envelope_nonneg he ⟨htd.1.le,htd.2.le⟩
    rw [stationary_envelope_zero hd] at hdecrease
    linarith
  · exact hq
  · have hdecrease := positionEnvelope_radius_decrease he.q_lower hd.q_upper hlt hce hse.le
    have hnonneg := stationary_envelope_nonneg hd ⟨hte.1.le,hte.2.le⟩
    rw [stationary_envelope_zero he] at hdecrease
    linarith

theorem stationary_angle_eq {d e : Coordinates} (hd : d.IsStationary) (he : e.IsStationary) :
    coordinateAngle d=coordinateAngle e := by
  have hq := stationary_radius_eq hd he
  have hdcritical := stationary_envelope_critical hd
  have hecritical := stationary_envelope_critical he
  rw [← hq] at hecritical
  exact positionEnvelope_critical_unique hd.q_lower hd.q_upper
    (stationary_angle_mem hd) (stationary_angle_mem he) hdcritical hecritical

/-- Global uniqueness under the original broad stationary predicate.
All three parameters and all four circle radicals are conclusions. -/
theorem stationary_chain_unique {d e : Coordinates} (hd : d.IsStationary) (he : e.IsStationary) :
    d=e := by
  have hq := stationary_radius_eq hd he
  have ht := stationary_angle_eq hd he
  have hdm := stationary_minimizingPosition hd
  have hem := stationary_minimizingPosition he
  rw [← hq,← ht] at hem
  have hy : d.y=e.y := by linarith
  have hz : d.z=e.z := by
    apply Real.arctan_injective
    dsimp only [coordinateAngle] at ht
    linarith
  exact Coordinates.chain_unique_radicals hd.toIsChain he.toIsChain hq hy hz

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
