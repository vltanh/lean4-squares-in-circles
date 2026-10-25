module

public import SquaresInCircles.Eight.Corners.GeometricStationaryExistence
public import SquaresInCircles.Eight.Owners.Positive.EContactExclusion

/-!
# Eight squares: original positive-owner reductions at the geometric stationary radius

The sharp-radius hypotheses of the critical-contact construction are
derived here from the broad stationary equations.  Existence and radius
localization come from compact geometric minima and uniqueness.  The
original common radius, points, owners and contact relation stay explicit.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryOriginalReductions
open Candidate SignedCycle

theorem sharp_interval {d : Stationary.Coordinates} (hd : d.IsStationary) :
    d.q∈Icc qLow qTrial := by
  exact ⟨(GeometricExistence.stationary_radius_strip hd).1,
    (GeometricExistence.stationary_radius_ceiling hd).le⟩

theorem sole_DE_false {d : Stationary.Coordinates} (hd : d.IsStationary)
    {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0<delta C.theta G) (hD : 0≤delta C.theta D)
    (hE : (C.point E).Outer q)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : False :=
  PositiveEContactExclusion.sole_DE_false hd (sharp_interval hd) hQL hq hC hn hvar
    hab hG hD hE hf

end SquaresInCircles.Eight.StationaryOriginalReductions
