import SquaresInCircles.Six.Normalization.Input
import SquaresInCircles.Six.Normalization.Certificates.CentralGrid
import SquaresInCircles.Six.DiagonalReflection
import SquaresInCircles.Six.Goals

/-!
# Proposition A: the strong central box, before pins and sectors

The proof uses the supplied sufficient rational forbidden arcs. Their finite
arithmetic proofs are kernel reductions in Certificates.Checks, connected to
actual SAT by ConeSemantics. The five-marker contradiction is proved in
MarkerGaps. No pin, sector, A2 conclusion, or strong-box assumption is used.

The temporary diagonal reflection proves the symmetric bound on the original
packing. It does not impose a D-angle convention or consume the later global
D normalization.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

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
  · apply D.no_empty_arc first_arc_long
    intro i v hvl hvu he
    have hred := reducedUpper_of_actual (hc i) hx hy0 (by linarith : cy ≤ cx+1/10)
      ⟨hx.le,hx1.le⟩ ⟨hy0,hyc⟩ (hs i)
    have hout := coneA1_marker (ht i) (hc i) hred
    apply no_marker_lift_in_arc (ht i) (hc i)
      first_arc_near_east.1 first_arc_near_east.2 hout ⟨hvl,hvu⟩
    exact he.trans (hmarker i).symm
  · have hyc' : c0 ≤ cy := (lt_of_not_ge hyc).le
    obtain ⟨i0,j0,hji,hxb,hyb⟩ := triangular_grid_cover ⟨hx.le,hx1.le⟩ ⟨hyc',hy⟩
    apply D.no_empty_arc second_arc_long
    intro i v hvl hvu he
    have hred := reducedUpper_of_actual (hc i) hx hy0 (by linarith : cy ≤ cx+1/10)
      hxb hyb (hs i)
    have hout := coneA2_marker i0 j0 hji (ht i) (hc i) hred
    apply no_marker_lift_in_arc (ht i) (hc i)
      second_arc_near_east.1 second_arc_near_east.2 hout ⟨hvl,hvu⟩
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

/-- The previously uninhabited strong-box goal is now supplied by Proposition A. -/
theorem strongCentralBox : Six.Goals.StrongCentralBox := by
  intro S c R hp hR haxis hinside hcx hcy
  have hbounds : |c.1| < 1/2 ∧ |c.2| < 1/2 := by
    simpa [haxis,axisSquare_open,openAxisSquare,abs_neg] using hinside
  apply strong_central_box hp (hR.trans Six.qStar_lt_Q0.le)
    (fun p => by rw [haxis]) hcx hcy
  · exact (le_abs_self c.1).trans_lt hbounds.1
  · exact (le_abs_self c.2).trans_lt hbounds.2

/-- N16 is a consequence of the closed strong box, not an input to it. -/
theorem coarse_central_box {S : Fin 6 → UnitSquare} {R cx cy : ℝ}
    (hp : Packing S (0,0) R) (hQ : R^2 ≤ Q0)
    (hcentral : ∀ p, openSquare (S 0) p ↔ openSquare (axisSquare (cx,cy)) p)
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx1 : cx < 1/2) (hy1 : cy < 1/2) :
    0 ≤ cx ∧ cx < 23/200 ∧ 0 ≤ cy ∧ cy < 23/200 := by
  have h := strong_central_box hp hQ hcentral hx0 hy0 hx1 hy1
  exact ⟨hx0,h.1.trans_lt c0_lt_23_200,hy0,h.2.trans_lt c0_lt_23_200⟩

end SquaresInCircles.Six.Normalization
