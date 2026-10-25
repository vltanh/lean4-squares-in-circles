module

public import SquaresInCircles.Eight.TableFree.StationaryFluxBounds

/-!
# The two-error correction at the actual varying position minimum

Uncompiled reconstruction.  This module discharges every coefficient,
flux, and primitive estimate in the quantitative correction theorem by
the actual nested-circle minimizer.  The only remaining error hypotheses
are the canonical nonnegative angles and their proved geometric sum.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryTerminal
open ExactFamily.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

def minimizingWeights (q t : ℝ) : CanonicalNegativeStress.Parameters :=
  weights q (minimizingPosition q t) (Real.tan t)

theorem minimizingPosition_chart_root {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    positionHalf q (cosine (Real.tan t)) (sine (Real.tan t)) (minimizingPosition q t)=0 := by
  obtain ⟨hh,hat⟩ := terminal_tangent ht
  have hz := minimizingPosition_root (by nlinarith [hq.1] : (79/40:ℝ)^2≤q) hq.2
    (arctan_mem_tiltInterval hh)
  rw [hat] at hz
  dsimp [jointPosition] at hz
  rw [cosine,sine,hat]
  linarith

theorem minimizingWeights_positive {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) : (minimizingWeights q t).Positive := by
  have hu := minimizingPosition_terminal hq ht
  exact positive hq ⟨hu.1.le,hu.2.2.2.le⟩ (terminal_tangent ht).1

theorem minimizingWeights_mass {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) : massSum (minimizingWeights q t)=1 := by
  have hu := minimizingPosition_terminal hq ht
  exact mass_one hq ⟨hu.1.le,hu.2.2.2.le⟩ (terminal_tangent ht).1

theorem actual_correction_lower {q α t e : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hα : α∈Icc (1/10:ℝ) (4/25))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α) :
    (t+e)/5000≤correction (minimizingWeights q α) α t e := by
  obtain ⟨hh,hat⟩ := terminal_tangent hα
  obtain ⟨huL,haL,haU,huU⟩ := minimizingPosition_terminal hq hα
  have hpos : minimizingPosition q α∈Icc (179/200:ℝ) (47/50) := ⟨huL.le,huU.le⟩
  have hz := minimizingPosition_chart_root hq hα
  obtain ⟨homega,hKA,hbeta,hKB,hgamma⟩ := correction_coefficients hq hpos hh hz
  have hflux := flux_pos hq hpos hh
  have hsmall := small_reserve hq hpos hh
  have hsecant := secant_reserve hq hpos hh ⟨haL,haU⟩ hz
  rw [hat] at hflux hsmall hsecant
  exact CanonicalNegativeCorrection.correction_lower hα ht he hr hu
    homega hKA hbeta hKB hgamma hflux.le hsmall.le hsecant.le

end SquaresInCircles.Eight.TableFree.StationaryTerminal
