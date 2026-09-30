module
public import SquaresInCircles.Six.Normalization.Input
public import SquaresInCircles.Six.Analytic.ForbiddenArcs
public import SquaresInCircles.Six.DiagonalReflection
public import SquaresInCircles.Six.Goals

@[expose] public section

/-!
# Proposition A: the analytic strong central box, before pins and sectors

The forbidden arcs are proved on whole geometric quadrants by algebra,
trigonometric bounds, completed squares and one explicit quartic chord
argument. No central-coordinate subdivision, certificate checker, pin,
sector, or A2 conclusion is used. The existing genuine Seven marker-gap
inequality then contradicts the empty arc.

A temporary diagonal reflection proves the symmetric bound on the ORIGINAL
packing. It imposes no D-angle convention and does not spend the later global
D normalization. Compilation is distinct from this source proof.
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

/-- N23 for an actual packing with an axis-parallel central point set. -/
theorem strong_central_box {S : Fin 6 → UnitSquare} {R cx cy : ℝ}
    (hp : Packing S (0,0) R) (hQ : R^2 ≤ Q0)
    (hcentral : ∀ p, openSquare (S 0) p ↔ openSquare (axisSquare (cx,cy)) p)
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx1 : cx < 1/2) (hy1 : cy < 1/2) :
    cx ≤ c0 ∧ cy ≤ c0 := by
  by_contra! hbad
  rcases le_total cy cx with horder | horder
  · have hx : c0 < cx := by rcases hbad with h | h <;> linarith
    exact bad_east_center_impossible hp hQ hcentral hx hx1 hy0 horder
  · have hy : c0 < cy := by rcases hbad with h | h <;> linarith
    have hp' := Six.packing_reflectDiagonal hp
    have hcentral' := Six.reflected_central_axis hcentral
    exact bad_east_center_impossible hp' hQ hcentral' hy hy1 hx0 horder

/-- Unconditional strong-box endpoint, now through only analytic marker lemmas. -/
theorem strongCentralBox : Six.Goals.StrongCentralBox := by
  intro S c R hp hR haxis hinside hcx hcy
  have hbounds : |c.1| < 1/2 ∧ |c.2| < 1/2 := by
    simpa [haxis,axisSquare_open,openAxisSquare,abs_neg] using hinside
  apply strong_central_box hp (hR.trans Six.qStar_lt_Q0.le)
    (fun p => by rw [haxis]) hcx hcy
  · exact (le_abs_self c.1).trans_lt hbounds.1
  · exact (le_abs_self c.2).trans_lt hbounds.2

/-- N16 follows from the closed strong box, not conversely. -/
theorem coarse_central_box {S : Fin 6 → UnitSquare} {R cx cy : ℝ}
    (hp : Packing S (0,0) R) (hQ : R^2 ≤ Q0)
    (hcentral : ∀ p, openSquare (S 0) p ↔ openSquare (axisSquare (cx,cy)) p)
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx1 : cx < 1/2) (hy1 : cy < 1/2) :
    0 ≤ cx ∧ cx < 23/200 ∧ 0 ≤ cy ∧ cy < 23/200 := by
  have h := strong_central_box hp hQ hcentral hx0 hy0 hx1 hy1
  exact ⟨hx0,h.1.trans_lt c0_lt_23_200,hy0,h.2.trans_lt c0_lt_23_200⟩

end SquaresInCircles.Six.Normalization
