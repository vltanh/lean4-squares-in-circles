import SquaresInCircles.Six.Normalization.ChartBounds
import SquaresInCircles.Common.Support

/-!
# Exterior squares avoid the core disk

Clipping the local coordinates of a point `o` to `[-1/2, 1/2]` gives a point of
the closed square at squared distance `(max (α - 1/2) 0)² + (max (β - 1/2) 0)²`
from `o`, where `α` and `β` are the absolute local coordinates of `o`. If both
are at most `c0` in the frame of C, the open square C contains the disk of
radius `3/2 - ρ0` about `o`, so an exterior square whose interior is disjoint
from that of C has no point in this disk: `AvoidsCore a b` holds for its chart.
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

/-- A point of the closed square at squared distance
`(max (α - 1/2) 0)² + (max (β - 1/2) 0)²` from `o`. -/
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

/-- If the local coordinates of `o` in the frame of C are at most `c0`, an
exterior square whose interior is disjoint from that of C avoids the core
disk. -/
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

end SquaresInCircles.Six.Normalization
