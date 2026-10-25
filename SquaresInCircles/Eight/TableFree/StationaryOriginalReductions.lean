module

public import SquaresInCircles.Eight.TableFree.GeometricStationaryExistence
public import SquaresInCircles.Eight.TableFree.PositiveGABT2TD0Reduction

/-!
# Original positive-owner reductions at the geometric stationary radius

The sharp-radius hypotheses of the critical-contact construction are
derived here from the broad stationary equations.  Existence and radius
localization come from compact geometric minima and uniqueness.  The
original common radius, points, owners and contact relation stay explicit.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryOriginalReductions
open Candidate SignedCycle

theorem sharp_interval {d : ExactFamily.Coordinates} (hd : d.IsStationary) :
    d.q∈Icc qLow qTrial := by
  exact ⟨(GeometricExistence.stationary_radius_strip hd).1,
    (GeometricExistence.stationary_radius_ceiling hd).le⟩

theorem contact_G_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hEy : 0≤(C.point E).y) (hcontact : ExceptionalContactStress.Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : delta C.theta G=0 :=
  ExceptionalEComplete.original_G_zero hd (sharp_interval hd) hQL hq hC hn hvar
    hab hG hD hEy hcontact hf

theorem sole_DE_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0<delta C.theta G) (hD : 0≤delta C.theta D)
    (hE : (C.point E).Outer q)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : False :=
  PositiveEContactExclusion.sole_DE_false hd (sharp_interval hd) hQL hq hC hn hvar
    hab hG hD hE hf

theorem positive_pair_diagonal {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : BoundaryInput q) {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hab : ab=0 ∨ ab=2)
    (hG : 0<delta I.cycle.theta G) (hD : 0<delta I.cycle.theta D)
    (hE : 0<delta I.cycle.theta E)
    (hf : ∀ i,I.cycle.Feasible i (CoreEStress.owners ab 2 0 3 1 i)) :
    Nonempty (PositiveGABT2TD0Reduction.DiagonalOutput I) :=
  PositiveGABT2TD0Reduction.positive_pair_diagonal hd (sharp_interval hd) I
    hQL hq hab hG hD hE hf

/-- Every radius bound is now a consequence of `hd`; the remaining
diagonal alternative is the actual transported same-radius cycle. -/
theorem positive_GA_diagonal {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : NormalizedBoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hBT : I.witnesses.owner B=2) (hTD : I.witnesses.owner T=0)
    (hG : 0<delta I.cycle.theta G) :
    Nonempty (PositiveGABT2TD0Reduction.DiagonalOutput I.toBoundaryInput) :=
  PositiveGABT2TD0Reduction.original hd (sharp_interval hd) I hQL hq
    hHG hGA hBT hTD hG

end SquaresInCircles.Eight.TableFree.StationaryOriginalReductions
