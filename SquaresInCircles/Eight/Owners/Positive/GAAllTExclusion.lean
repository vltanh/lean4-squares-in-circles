module

public import SquaresInCircles.Eight.Owners.Positive.EContactAllT
public import SquaresInCircles.Eight.Owners.Stationary.OriginalReductions

/-!
# Eight squares: no positive GA terminal, for every preprocessed T row

The reduction of E gives a sole primary at the same radius, keeping the positive G error and the
selected row of T (`PositiveGAOuterSoleReduction.original`). Both sole directions are excluded,
the sole-DE one through the positive-E contact, for every signed error of T
(`original_boundary_false`, `original_false`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveGAAllTExclusion
open Candidate SignedCycle PositiveGAOuterSoleReduction

theorem original_boundary_false {d : Stationary.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : BoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hT : TRegime I) : False := by
  have hsharp := StationaryOriginalReductions.sharp_interval hd
  have hcap := (hq.trans hsharp.2).trans uniform_radius_order.2.2.1.le
  obtain ⟨O⟩ := PositiveGAOuterSoleReduction.original I hQL hcap hHG hGA hG hT
  rcases O.sole with ⟨hDE,hEH,he⟩ | ⟨hDE,hEH,he⟩
  · exact SoleAllTExclusion.sole_EH_false O.boundary hQL (hq.trans hsharp.2)
      O.HG O.GA O.G_positive.le O.T_regime hDE hEH he.le
  · exact PositiveEContactAllT.sole_DE_false hd hsharp O.boundary hQL hq
      O.HG O.GA O.G_positive he.le O.T_regime O.E_outer hDE hEH

theorem original_false {d : Stationary.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : NormalizedBoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hT : TRegime I.toBoundaryInput) : False :=
  original_boundary_false hd I.toBoundaryInput hQL hq hHG hGA hG hT

end SquaresInCircles.Eight.PositiveGAAllTExclusion
