module
public import SquaresInCircles.Six.Normalization.ChartBounds
public import SquaresInCircles.Common.Support

@[expose] public section

/-!
# From the strong central box to actual square-chart bounds

This file connects the scalar Lemma B to the repository's `UnitSquare`,
`closedSquare`, `openSquare`, and `SquareChart` definitions. In particular,
it does not identify disjoint closed squares with disjoint interiors.
The strong central box remains an explicit hypothesis: Proposition A is not
assumed to have been formalized by these lemmas.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

private lemma clipped_distance {x v : ℝ}
    (hv : |v| = min |x| (1 / 2))
    (hprod : x * v = min |x| (1 / 2) * |x|) :
    (v - x) ^ 2 = (max (|x| - 1 / 2) 0) ^ 2 := by
  have hv2 : v ^ 2 = (min |x| (1 / 2)) ^ 2 := by
    rw [← sq_abs v, hv]
  have hx2 := sq_abs x
  rcases le_total |x| (1 / 2) with h | h
  · rw [min_eq_left h] at hv2 hprod
    rw [max_eq_right (by linarith : |x| - 1 / 2 ≤ 0)]
    nlinarith
  · rw [min_eq_right h] at hv2 hprod
    rw [max_eq_left (by linarith : 0 ≤ |x| - 1 / 2)]
    nlinarith

/-- An actual point of a closed square realizes the coordinate-clipping distance.
This statement is valid even when the disk center is on an edge or a corner. -/
lemma exists_clipped_point (S : UnitSquare) (o : Point) :
    ∃ p : Point, closedSquare S p ∧
      normSq (sub p o) = (max (alpha S o - 1 / 2) 0) ^ 2 +
        (max (beta S o - 1 / 2) 0) ^ 2 := by
  obtain ⟨u, hu, hxu⟩ := exists_signed (localX S o)
    (c := min |localX S o| (1 / 2))
    (le_min (abs_nonneg _) (by norm_num))
  obtain ⟨v, hv, hyv⟩ := exists_signed (localY S o)
    (c := min |localY S o| (1 / 2))
    (le_min (abs_nonneg _) (by norm_num))
  refine ⟨add S.center (rotate S (u, v)), ?_, ?_⟩
  · constructor
    · rw [localX_rotated, hu]
      exact min_le_right _ _
    · rw [localY_rotated, hv]
      exact min_le_right _ _
  · rw [← frame_distance S, localX_rotated, localY_rotated,
      clipped_distance hu hxu, clipped_distance hv hyv]
    rfl

lemma chart_exists_clipped_point {S : UnitSquare} {o : Point} (T : SquareChart S o) :
    ∃ p : Point, closedSquare S p ∧
      normSq (sub p o) = (max (T.a - 1 / 2) 0) ^ 2 +
        (max (T.b - 1 / 2) 0) ^ 2 := by
  apply T.transfer
    (fun a b => ∃ p : Point, closedSquare S p ∧
      normSq (sub p o) = (max (a - 1 / 2) 0) ^ 2 + (max (b - 1 / 2) 0) ^ 2)
  · rintro a b ⟨p, hp, hd⟩
    exact ⟨p, hp, by simpa only [add_comm] using hd⟩
  · exact exists_clipped_point S o

/-- The open core of C excludes every point of the closed exterior square.
The mixed closed/open implication is supplied by `closed_open_disjoint`. -/
lemma avoidsCore_of_disjoint {S C : UnitSquare} {o : Point} (T : SquareChart S o)
    (hsort : T.b ≤ T.a) (hout : ¬ openSquare S o)
    (hc : alpha C o ≤ c0 ∧ beta C o ≤ c0)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare C p)) :
    AvoidsCore T.a T.b := by
  obtain ⟨p, hp, hdist⟩ := chart_exists_clipped_point T
  have hn := closed_open_disjoint S C hd hp
  have hcore : coreRadius ^ 2 ≤ normSq (sub p o) := by
    by_contra! ht
    exact hn (inscribed_disk_mem C o coreRadius_pos c0_add_coreRadius hc.1 hc.2 ht)
  have ha : 0 ≤ T.a - 1 / 2 := by linarith [T.exterior hsort hout]
  rw [hdist, max_eq_left ha] at hcore
  exact hcore

lemma containedChart_of_contained {S : UnitSquare} {o : Point} (T : SquareChart S o)
    (hsort : T.b ≤ T.a) (hout : ¬ openSquare S o)
    (hcontain : ∀ p, closedSquare S p → inDisk o R0 p) :
    ContainedChart T.a T.b where
  half_le := T.exterior hsort hout
  u_nonneg := T.nonneg.2
  u_le := hsort
  containment := by
    have h := chart_phi T (phi_le_of_contained S o R0 hcontain)
    rw [R0_sq] at h
    exact h

/-- N17 and axial selection, for the actual chart, conditional only on the
strong central box and the geometric containment/disjointness hypotheses. -/
theorem chart_bounds_and_axial_of_strong_core {S C : UnitSquare} {o : Point}
    (T : SquareChart S o) (hsort : T.b ≤ T.a) (hout : ¬ openSquare S o)
    (hc : alpha C o ≤ c0 ∧ beta C o ≤ c0)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare C p))
    (hcontain : ∀ p, closedSquare S p → inDisk o R0 p) :
    aMin ≤ T.a ∧ T.a ≤ rho0 ∧ T.b ≤ U0 ∧ T.b < 1 / 2 ∧
      (177 / 200 < T.a ∧ T.a < 223 / 200 ∧ T.b < 117 / 250) ∧
      Seven.label T.a T.b = 5 * T.b / 4 := by
  have hs := containedChart_of_contained T hsort hout hcontain
  have hcore := avoidsCore_of_disjoint T hsort hout hc hd
  exact ⟨hs.aMin_le hcore, hs.a_le_rho0, hs.u_le_U0 hcore,
    hs.u_lt_half hcore, hs.bounds hcore, hs.label_eq_axial hcore⟩

end SquaresInCircles.Six.Normalization
