module

public import SquaresInCircles.Eight.Owners.Stationary.NominalIdentity

/-!
# Eight squares: the canonical terminal bound with all original radial losses

The source radius may differ from the
reference radius used for the actual position minimizer.  Normalization
of the five masses makes their difference exact.  The quantitative
conclusion retains both center-completion squares and every original
anchor's radial slack.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

theorem terminal_tilt_mem {α : ℝ} (hα : α∈Icc (1/10:ℝ) (4/25)) :
    α∈tiltInterval := by
  obtain ⟨hh,hat⟩ := terminal_tangent hα
  rw [← hat]
  exact arctan_mem_tiltInterval hh

/-- Exact reference-radius transfer plus the proved two-error reserve.
The five weak contacts are the original geometric inequalities. -/
theorem original_quantitative_bound {H A B D E : SignedPoint} {q₀ q α t e : ℝ}
    (hq₀ : q₀∈Icc (19577/5000:ℝ) (9789/2500))
    (hα : α∈Icc (1/10:ℝ) (4/25))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hHA : 1+W (α-t-e)≤H.y+A.a*Real.cos (α-t-e)-A.y*Real.sin (α-t-e))
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    q₀+(minimizingWeights q₀ α).mu 4*positionEnvelope q₀ α+(t+e)/5000+
      centerLoss (minimizingWeights q₀ α) α t (α-t-e) e ![A,B,D,E,H]+
      circleLoss q (minimizingWeights q₀ α) ![A,B,D,E,H]≤q := by
  have hw := minimizingWeights_positive hq₀ hα
  have hm : ∀i,(minimizingWeights q₀ α).mu i≠0 := fun i => (hw.2.2.2.2.2 i).ne'
  have hcontact := original_circle_inequality (q:=q) hw
    hyH hyA hyB hyD hyE hHA hAB hBD hDE hEH
  have hid : CanonicalNegativeStress.defect q (minimizingWeights q₀ α) α t (α-t-e) e=
      (minimizingWeights q₀ α).mu 4*positionEnvelope q₀ α+
        correction (minimizingWeights q₀ α) α t e-(q-q₀) := by
    rw [defect_radius (minimizingWeights q₀ α) q q₀,
      defect_difference hm,minimizing_nominal_defect hq₀ hα,
      minimizingWeights_mass hq₀ hα]
    ring
  rw [hid] at hcontact
  linarith [actual_correction_lower hq₀ hα ht he hr hu]

/-- A zero of the actual envelope at an interior angle is the unique
stationary angle.  Local minimality follows from the proved global
nonnegativity of the original envelope. -/
theorem stationary_zero_angle {d : Stationary.Coordinates}
    (hd : d.IsStationary) {α : ℝ} (hα : α∈tiltInterval)
    (hzero : positionEnvelope d.q α=0) : α=coordinateAngle d := by
  have hmin : IsMinOn (positionEnvelope d.q) (Icc 0 (Real.arctan (1/5))) α := by
    intro x hx
    rw [hzero]
    exact stationary_envelope_nonneg hd hx
  have hloc := hmin.isLocalMin (Icc_mem_nhds hα.1 hα.2)
  have hder := positionEnvelope_hasDerivAt hd.q_lower hd.q_upper hα
  have hderzero := hloc.hasDerivAt_eq_zero hder
  have hz : deriv (positionEnvelope d.q) α=0 := hder.deriv.trans hderzero
  exact positionEnvelope_critical_unique hd.q_lower hd.q_upper hα
    (stationary_angle_mem hd) hz (stationary_envelope_critical hd)

end SquaresInCircles.Eight.StationaryTerminal
