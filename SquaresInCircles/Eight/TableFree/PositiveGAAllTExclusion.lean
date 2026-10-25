module

public import SquaresInCircles.Eight.TableFree.PositiveEContactAllT
public import SquaresInCircles.Eight.TableFree.StationaryOriginalReductions

/-!
# Every positive GA terminal, with every actual preprocessed T row

Uncompiled source. The original E reduction produces a genuine sole
primary at the same common radius, preserving the positive G error and
the selected T row. Both sole directions are now excluded, including
the positive-E contact successor and all signed T errors.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveGAAllTExclusion
open Candidate SignedCycle PositiveGAOuterSoleReduction

theorem original_boundary_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
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

theorem original_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : NormalizedBoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hT : TRegime I.toBoundaryInput) : False :=
  original_boundary_false hd I.toBoundaryInput hQL hq hHG hGA hG hT

end SquaresInCircles.Eight.TableFree.PositiveGAAllTExclusion
