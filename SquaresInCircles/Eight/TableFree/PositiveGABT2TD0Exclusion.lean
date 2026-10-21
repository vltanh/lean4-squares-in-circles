module

public import SquaresInCircles.Eight.TableFree.StationaryOriginalReductions
public import SquaresInCircles.Eight.TableFree.EDiagonalExclusion

/-!
# Close the original positive-GA, BT2/TD0 reduction

The endpoint transport returns an actual boundary cycle at the unchanged
radius with an E-diagonal point.  Exact nearest-axis recoding now excludes
that actual point.  The stationary radius bounds are derived from the
geometric existence theorem, and no diagonal-exclusion premise remains.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveGABT2TD0Exclusion
open Candidate SignedCycle

theorem radius_eligible {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (hQL : qLow≤q) (hq : q≤d.q) : q∈Icc (5/2:ℝ) qCap :=
  ⟨uniform_radius_order.1.le.trans hQL,
    (hq.trans (StationaryOriginalReductions.sharp_interval hd).2).
      trans uniform_radius_order.2.2.1.le⟩

theorem diagonal_output_false {q : ℝ} {I : BoundaryInput q}
    (O : PositiveGABT2TD0Reduction.DiagonalOutput I)
    (hq : q∈Icc (5/2:ℝ) qCap) : False :=
  O.boundary.E_not_diagonal hq O.diagonal

theorem positive_pair_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : BoundaryInput q) {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hab : ab=0 ∨ ab=2)
    (hG : 0<delta I.cycle.theta G) (hD : 0<delta I.cycle.theta D)
    (hE : 0<delta I.cycle.theta E)
    (hf : ∀ i,I.cycle.Feasible i (CoreEStress.owners ab 2 0 3 1 i)) : False := by
  obtain ⟨O⟩ := StationaryOriginalReductions.positive_pair_diagonal hd I hQL hq hab hG hD hE hf
  exact diagonal_output_false O (radius_eligible hd hQL hq)

theorem original_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : NormalizedBoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hBT : I.witnesses.owner B=2) (hTD : I.witnesses.owner T=0)
    (hG : 0<delta I.cycle.theta G) : False := by
  obtain ⟨O⟩ := StationaryOriginalReductions.positive_GA_diagonal hd I hQL hq hHG hGA hBT hTD hG
  exact diagonal_output_false O (radius_eligible hd hQL hq)

theorem original_G_nonpos {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : NormalizedBoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hBT : I.witnesses.owner B=2) (hTD : I.witnesses.owner T=0) :
    delta I.cycle.theta G≤0 := by
  by_contra h
  exact original_false hd I hQL hq hHG hGA hBT hTD (lt_of_not_ge h)

end SquaresInCircles.Eight.TableFree.PositiveGABT2TD0Exclusion
