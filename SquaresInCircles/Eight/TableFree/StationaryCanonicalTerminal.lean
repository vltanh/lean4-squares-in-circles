module

public import SquaresInCircles.Eight.TableFree.StationaryNominalIdentity
public import SquaresInCircles.Eight.ExactFamily.GeometricStationary

/-!
# The canonical terminal bound with all original radial losses

Uncompiled reconstruction.  The source radius may differ from the
reference radius used for the actual position minimizer.  Normalization
of the five masses makes their difference exact.  The quantitative
conclusion retains both center-completion squares and every original
anchor's radial slack.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.StationaryTerminal
open ExactFamily.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

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

/-- A genuine stationary circle chain supplies the envelope sign.  Its
global-minimum conclusion is proved in `GeometricStationary`, not a
premise of this terminal theorem. -/
theorem stationary_quantitative_bound {d : ExactFamily.Coordinates}
    (hd : d.IsStationary) (hq₀ : d.q∈Icc (19577/5000:ℝ) (9789/2500))
    {H A B D E : SignedPoint} {q α t e : ℝ}
    (hα : α∈Icc (1/10:ℝ) (4/25))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hHA : 1+W (α-t-e)≤H.y+A.a*Real.cos (α-t-e)-A.y*Real.sin (α-t-e))
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    d.q+(t+e)/5000+
      centerLoss (minimizingWeights d.q α) α t (α-t-e) e ![A,B,D,E,H]+
      circleLoss q (minimizingWeights d.q α) ![A,B,D,E,H]≤q := by
  have hfull := original_quantitative_bound (q:=q) hq₀ hα ht he hr hu
    hyH hyA hyB hyD hyE hHA hAB hBD hDE hEH
  have htilt := terminal_tilt_mem hα
  have henv := stationary_envelope_nonneg hd ⟨htilt.1.le,htilt.2.le⟩
  have hmass := (minimizingWeights_positive hq₀ hα).2.2.2.2.2 4
  have hterm := mul_nonneg hmass.le henv
  linarith

/-- Strict loss on any of the five original circles gives a strict
radius inequality.  No auxiliary G/T circle occurs. -/
theorem stationary_strict_source_bound {d : ExactFamily.Coordinates}
    (hd : d.IsStationary) (hq₀ : d.q∈Icc (19577/5000:ℝ) (9789/2500))
    {H A B D E : SignedPoint} {q α t e : ℝ}
    (hα : α∈Icc (1/10:ℝ) (4/25))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hc : ∀i : Fin 5,(![A,B,D,E,H] i).Contained q)
    (hstrict : ∃i : Fin 5,(![A,B,D,E,H] i).circle<q)
    (hHA : 1+W (α-t-e)≤H.y+A.a*Real.cos (α-t-e)-A.y*Real.sin (α-t-e))
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) : d.q<q := by
  have hb := stationary_quantitative_bound (q:=q) hd hq₀ hα ht he hr hu
    hyH hyA hyB hyD hyE hHA hAB hBD hDE hEH
  have hw := minimizingWeights_positive hq₀ hα
  have hcenter := centerLoss_nonneg hw ![A,B,D,E,H] α t (α-t-e) e
  have hcircle := circleLoss_positive hw hc hstrict
  linarith

/-- A zero of the actual envelope at an interior angle is the unique
stationary angle.  Local minimality follows from the proved global
nonnegativity of the original envelope. -/
theorem stationary_zero_angle {d : ExactFamily.Coordinates}
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

end SquaresInCircles.Eight.TableFree.StationaryTerminal
