import SquaresInCircles.Six.Normalization.Input
import SquaresInCircles.Six.Analytic.ForbiddenArcs
import SquaresInCircles.Six.DiagonalReflection
import SquaresInCircles.Six.Construction
import SquaresInCircles.Six.Containing

/-!
# The strong central box

In a packing of six squares in a disk about `(0, 0)` of squared radius at most
`Q0`, let the square containing the disk centre be axis-parallel, with centre
`(cx, cy)` in `[0, 1/2)²`. Then `cx ≤ c0` and `cy ≤ c0`. If `cx > c0` and
`cy ≤ cx`, every other square is separated from it along some axis, and the
forbidden arcs leave no marker in an open arc of length more than `2π/3` on the
east side, against the gaps between the five markers. The case `cy > c0` follows
by the reflection in the diagonal.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Six.Analytic

private theorem bad_east_center_impossible {S : Fin 6 → UnitSquare} {R cx cy : ℝ}
    (hp : Packing S (0,0) R) (hQ : R^2 ≤ Q0)
    (hcentral : ∀ p, openSquare (S 0) p ↔ openSquare (axisSquare (cx,cy)) p)
    (hx : c0 < cx) (hx1 : cx < 1/2) (hy0 : 0 ≤ cy) (hy : cy ≤ cx) : False := by
  have hx0 : 0 ≤ cx := (c0_pos.trans hx).le
  have hy1 : cy < 1/2 := hy.trans_lt hx1
  have hzero : openSquare (S 0) (0,0) := by
    apply (hcentral (0,0)).mpr
    simpa [axisSquare_open,openAxisSquare,abs_neg,abs_of_nonneg hx0,abs_of_nonneg hy0]
      using And.intro hx1 hy1
  obtain ⟨D⟩ := exterior_input_of_ceiling hp hQ
  have hDzero : D.central = 0 := by
    by_contra hne
    exact hp.disjoint D.central 0 hne (0,0) ⟨D.central_inside,hzero⟩
  let t : Fin 5 → ℝ := fun i => (D.chart i).phase.toReal
  have ht (i : Fin 5) : |t i| ≤ Real.pi := by
    apply abs_le.mpr
    exact ⟨(D.chart i).phase.neg_pi_lt_toReal.le,(D.chart i).phase.toReal_le_pi⟩
  have htclass (i : Fin 5) : (t i : Direction) = (D.chart i).phase :=
    Real.Angle.coe_toReal _
  have hc (i : Fin 5) : ContainedChart (D.chart i).a |(D.chart i).signedB| := by
    rw [signedB_abs]
    exact ⟨(D.chart i).exterior (D.sorted i) (D.exterior i),
      (D.chart i).nonneg.2,D.sorted i,D.contained i⟩
  have hmarker (i : Fin 5) :
      (liftedMarker (t i) (D.chart i).a (D.chart i).signedB : Direction) = D.markers i :=
    liftedMarker_eq_chartMarker (D.chart i) (D.admissible i) (htclass i)
  have hs (i : Fin 5) :
      ∃ k, 0 ≤ centralMargin k (t i) (D.chart i).a (D.chart i).signedB cx cy := by
    apply central_separators_complete (hc i).half_le hx0 hy0 hx1.le hy1.le
    intro p hboth
    have hne : (0:Fin 6) ≠ D.central.succAbove i := by
      rw [← hDzero]
      exact (D.central.succAbove_ne i).symm
    have hX := (chart_same_open_oriented (D.chart i) (htclass i) p).mpr hboth.2
    exact hp.disjoint 0 _ hne p ⟨(hcentral p).mpr hboth.1,hX⟩
  by_cases hyc : cy ≤ c0
  · apply D.no_empty_arc small_arc_length
    intro i v hvl hvu he
    have hout := small_core_marker_outside (hc i) hx hx1 hy0 hyc (hs i)
    apply marker_no_representative (hc i) (ht i)
      small_arc_near_east.1 small_arc_near_east.2 hout ⟨hvl,hvu⟩
    exact he.trans (hmarker i).symm
  · apply D.no_empty_arc large_arc_length
    intro i v hvl hvu he
    have hout := large_core_marker_outside (hc i) (lt_of_not_ge hyc) hy hx1 (hs i)
    apply marker_no_representative (hc i) (ht i)
      large_arc_near_east le_rfl hout ⟨hvl,hvu⟩
    exact he.trans (hmarker i).symm

/-- If the square containing the disk centre is axis-parallel, with centre in
`[0, 1/2)²`, then its centre lies in `[0, c0]²`. -/
theorem strong_central_box {S : Fin 6 → UnitSquare} {R cx cy : ℝ}
    (hp : Packing S (0,0) R) (hQ : R^2 ≤ Q0)
    (hcentral : ∀ p, openSquare (S 0) p ↔ openSquare (axisSquare (cx,cy)) p)
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx1 : cx < 1/2) (hy1 : cy < 1/2) :
    cx ≤ c0 ∧ cy ≤ c0 := by
  by_contra! hbad
  rcases le_total cy cx with horder | horder
  · have hx : c0 < cx := by
      by_contra! h
      linarith [hbad h]
    exact bad_east_center_impossible hp hQ hcentral hx hx1 hy0 horder
  · have hy : c0 < cy := by
      by_contra! h
      linarith [hbad (by linarith)]
    have hp' := Six.packing_reflectDiagonal hp
    have hcentral' := Six.reflected_central_axis hcentral
    exact bad_east_center_impossible hp' hQ hcentral' hy hy1 hx0 horder

end SquaresInCircles.Six.Normalization
