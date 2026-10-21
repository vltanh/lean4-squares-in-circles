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

/-- The complete BT2/TD0 row is independent of E's tangent sign and
radial kind. All four E owner pairs and both AB owners are consumed by
the same-radius reduction before the genuine E diagonal is excluded. -/
theorem original_boundary_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : BoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hBT : I.witnesses.owner B=2) (hTD : I.witnesses.owner T=0)
    (hG : 0<delta I.cycle.theta G) : False := by
  obtain ⟨O⟩ := PositiveGABT2TD0Reduction.original_boundary hd
    (StationaryOriginalReductions.sharp_interval hd) I hQL hq hHG hGA hBT hTD hG
  exact diagonal_output_false O (radius_eligible hd hQL hq)

theorem original_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : NormalizedBoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hBT : I.witnesses.owner B=2) (hTD : I.witnesses.owner T=0)
    (hG : 0<delta I.cycle.theta G) : False :=
  original_boundary_false hd I.toBoundaryInput hQL hq hHG hGA hBT hTD hG

theorem original_boundary_G_nonpos {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : BoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hBT : I.witnesses.owner B=2) (hTD : I.witnesses.owner T=0) :
    delta I.cycle.theta G≤0 := by
  by_contra h
  exact original_boundary_false hd I hQL hq hHG hGA hBT hTD (lt_of_not_ge h)

theorem original_G_nonpos {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : NormalizedBoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hBT : I.witnesses.owner B=2) (hTD : I.witnesses.owner T=0) :
    delta I.cycle.theta G≤0 :=
  original_boundary_G_nonpos hd I.toBoundaryInput hQL hq hHG hGA hBT hTD

/-- Reverse the actual physical cycle. Its resulting E sign is left
untouched and is covered by `original_boundary_false`. Thus positive BT
is excluded when the original opposite pair has GA0/HG2. -/
theorem reflected_BT_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : BoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=0)
    (hBT : I.witnesses.owner B=3) (hTD : I.witnesses.owner T=0)
    (hB : 0<delta I.cycle.theta B) : False := by
  let J := I.reflected
  have hHG' : J.witnesses.owner H=2 := by
    simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,
      H,T,reflectedOwner,hTD]
  have hGA' : J.witnesses.owner G=1 := by
    simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,
      G,B,reflectedOwner,hBT]
  have hBT' : J.witnesses.owner B=2 := by
    simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,
      B,G,reflectedOwner,hGA]
  have hTD' : J.witnesses.owner T=0 := by
    simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,
      T,H,reflectedOwner,hHG]
  have hG' : 0<delta J.cycle.theta G := by
    simpa [J,BoundaryInput.reflected,reflected_delta,reflectedIndex,next,G,B] using hB
  exact original_boundary_false hd J hQL hq hHG' hGA' hBT' hTD' hG'

theorem reflected_BT_nonpos {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : BoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=0)
    (hBT : I.witnesses.owner B=3) (hTD : I.witnesses.owner T=0) :
    delta I.cycle.theta B≤0 := by
  by_contra h
  exact reflected_BT_false hd I hQL hq hHG hGA hBT hTD (lt_of_not_ge h)

end SquaresInCircles.Eight.TableFree.PositiveGABT2TD0Exclusion
