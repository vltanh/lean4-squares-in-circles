module

public import SquaresInCircles.Eight.Stationary.Analysis
public import SquaresInCircles.Eight.Equality.Basic
public import SquaresInCircles.Eight.Boundary.SourceAwareBoundaryPreprocessing

/-!
# Eight squares: the hard axes of the source

The pair moves of G and T keep track of their source: if the hard axis GA0 becomes feasible only
after the moves, then `θA - θH > 0` or the contact H–G is strict, and the same for BT2 with
`θD - θB` and the contact T–D. So if both hard axes are feasible after the moves, with
`θA ≤ θH`, `θD ≤ θB` and the contacts H–G and T–D tight, they were already feasible on the input
(`original_hard_of_pair_contacts`). Then the moves leave G and T in place (their field
`fixed_if_hard`), and the cycle after both moves is the input itself
(`pairDescendant_eq_original_of_hard`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate Stationary GeometricModel

namespace SignedCycle.BoundaryInput

/-- If, on the cycle after both moves, GA0 and BT2 are feasible, `θA ≤ θH`, `θD ≤ θB`, and the
contacts H–G and T–D are tight, then GA0 and BT2 are feasible on the input. -/
theorem original_hard_of_pair_contacts {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hGA : (I.pairDescendant hq SG.output ST.output).cycle.Feasible G 0)
    (hBT : (I.pairDescendant hq SG.output ST.output).cycle.Feasible B 2)
    (hGtotal : (I.pairDescendant hq SG.output ST.output).cycle.theta A≤
      (I.pairDescendant hq SG.output ST.output).cycle.theta H)
    (hTtotal : (I.pairDescendant hq SG.output ST.output).cycle.theta D≤
      (I.pairDescendant hq SG.output ST.output).cycle.theta B)
    (hHG : (I.pairDescendant hq SG.output ST.output).cycle.slack H SG.output.hgOwner=0)
    (hTD : (I.pairDescendant hq SG.output ST.output).cycle.slack T ST.output.tdOwner=0) :
    I.cycle.HardOwners := by
  have ha := I.pairDescendant_anchors hq SG.output ST.output
  have hGsource : I.cycle.theta A≤I.cycle.theta H := by
    have h1 := (ha A (by simp [anchorVertices])).2
    have h2 := (ha H (by simp [anchorVertices])).2
    linarith
  have hTsource : I.cycle.theta D≤I.cycle.theta B := by
    have h1 := (ha D (by simp [anchorVertices])).2
    have h2 := (ha B (by simp [anchorVertices])).2
    linarith
  constructor
  · by_contra hnot
    rcases I.pairDescendant_g_source_obstruction hq SG ST hnot hGA with ht | hs
    · exact (not_lt_of_ge (sub_nonpos.mpr hGsource)) ht
    · rw [hHG] at hs
      exact (lt_irrefl 0) hs
  · by_contra hnot
    rcases I.pairDescendant_t_source_obstruction hq SG ST hnot hBT with ht | hs
    · exact (not_lt_of_ge (sub_nonpos.mpr hTsource)) ht
    · rw [hTD] at hs
      exact (lt_irrefl 0) hs

/-- If the input has hard owners, the moves leave G and T in place, and the anchors do not move,
so the cycle after both moves is the input. -/
theorem pairDescendant_eq_original_of_hard {q : ℝ} (I : BoundaryInput q)
    (hq : q≤qCap)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hhard : I.cycle.HardOwners) :
    (I.pairDescendant hq SG.output ST.output).cycle=I.cycle := by
  have ha := I.pairDescendant_anchors hq SG.output ST.output
  have hfixed := I.pairDescendant_fixed_sources hq SG ST
  have hG := hfixed.1 hhard.1
  have hT := hfixed.2 hhard.2
  have hpoint : (I.pairDescendant hq SG.output ST.output).cycle.point=I.cycle.point := by
    funext i
    by_cases hiG : i=G
    · subst i; exact hG.1
    by_cases hiT : i=T
    · subst i; exact hT.1
    have hi : i∈anchorVertices := by
      fin_cases i <;> simp [anchorVertices,H,G,A,B,T,D,E] at hiG hiT ⊢
    exact (ha i hi).1
  have htheta : (I.pairDescendant hq SG.output ST.output).cycle.theta=I.cycle.theta := by
    funext i
    by_cases hiG : i=G
    · subst i; exact hG.2
    by_cases hiT : i=T
    · subst i; exact hT.2
    have hi : i∈anchorVertices := by
      fin_cases i <;> simp [anchorVertices,H,G,A,B,T,D,E] at hiG hiT ⊢
    exact (ha i hi).2
  have hext : ∀ C D : SignedCycle, C.point=D.point → C.theta=D.theta → C=D := by
    rintro ⟨p,t⟩ ⟨p',t'⟩ h1 h2
    simp only at h1 h2
    subst h1 h2
    rfl
  exact hext _ _ hpoint htheta

end SignedCycle.BoundaryInput

namespace SignedCycle.NormalizedBoundaryInput

end SignedCycle.NormalizedBoundaryInput
end SquaresInCircles.Eight
