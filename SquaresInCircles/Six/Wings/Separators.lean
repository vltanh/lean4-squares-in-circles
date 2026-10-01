import SquaresInCircles.Six.Wings.WestGap
import SquaresInCircles.Six.Wings.WestSide
import SquaresInCircles.Six.Wings.SouthTurned
import SquaresInCircles.Six.Wings.WestTurned
import SquaresInCircles.Six.Wings.SouthSide
import SquaresInCircles.Six.Wings.WestDiagonal
import SquaresInCircles.Six.Wings.WestRange

/-!
# Six squares: the separators of the turned square

In the model W and D are separated along the secondary axis of W, and D and S
along that of S. If the first separation fails, the west wing is missing: W
and D are separated along the secondary axis of D, and D and S along that of S;
if the second fails, the south wing is missing. Neither happens. Each case of
the separators of W and S from C, along an own axis or a side of C, and, when
both are own, of the order of their angles, is a weighted sum of the separating
inequalities against the supports of the squares. A missing west wing with S on
its own axis is read in the reflection in the diagonal, where it is a missing
south wing with W on its own axis, on the other half `π/4 ≤ d` of the range of
the angle of D.
-/

noncomputable section
namespace SquaresInCircles.Six.Wings
open Normalization

variable {R : ℝ}

/-- No normalized packing has a missing south wing. -/
theorem not_missing_south (P : NormalizedPacking R) : ¬ MissingSouthWing P := by
  intro h
  have hm := missing_south h
  have hd := diagonal_range (P := P)
  have hr : (chart P).d-(chart P).s < Real.pi/4 := by
    have h' := h.phase_wall
    dsimp [chart]
    linarith
  have hs2 := south_upper (P := P)
  match hW : P.ownAxis 2, hS : P.ownAxis 4 with
  | false, false =>
    exact WestSide.SmallSouth.impossible (west_side hW) hm (west_side_angle hW).le
      ⟨hd.1.le,hd.2⟩ (by linarith [(abs_lt.mp (south_side_angle hS)).2]) hr.le
  | false, true =>
    by_cases hs : (chart P).s ≤ 12/25
    · exact WestSide.SmallSouth.impossible (west_side hW) hm (west_side_angle hW).le
        ⟨hd.1.le,hd.2⟩ hs hr.le
    · exact WestSide.LargeSouth.impossible (west_side hW) (south_own hS) hm
        (west_side_angle hW).le ⟨by linarith,hs2.le⟩ ⟨hd.1.le,by linarith [Real.pi_lt_d4]⟩
  | true, false =>
    exact SouthSide.impossible (west_own hW) (south_side hS) hm
      ⟨(west_own_angle hW).le,west_upper.le⟩ (south_side_angle hS).le
      ⟨hd.1.le,by linarith [Real.pi_lt_d4]⟩ hr.le
      (fun h' => absurd h' (by linarith [Real.pi_lt_d4]))
  | true, true =>
    have hsum := own_angle_sum hW hS
    by_cases horder : (chart P).v ≤ (chart P).s
    · exact SouthTurned.impossible (west_own hW) (south_own hS) hm
        (west_own_angle hW).le horder hs2.le hsum.le ⟨hd.1.le,hd.2⟩
    · exact WestTurned.impossible (west_own hW) (south_own hS) hm west_upper.le
        (south_own_angle hS).le (le_of_not_ge horder) hsum.le
        ⟨hd.1.le,by linarith [Real.pi_lt_d4]⟩ (by linarith [south_own_angle hS])

/-- In a missing west wing the phase gap of W and D exceeds one radian. -/
lemma west_gap {P : NormalizedPacking R} (h : MissingWestWing P) :
    1 < (chart P).d+(chart P).v := by
  have h' := westDiagonal_gap_gt_one P h.from_diagonal
  rw [west_phase,diagonal_phase] at h'
  linarith

/-- The range of W and D in a missing west wing with W on its own axis. -/
lemma own_west_range {P : NormalizedPacking R} (h : MissingWestWing P)
    (hW : P.ownAxis 2=true) :
    53/50 < (chart P).d+(chart P).v ∧ (chart P).v < 31/50 ∧ 16/25 < (chart P).d := by
  have hm := (missing_west h).west
  have hgap := west_gap h
  have hd := diagonal_range (P := P)
  have hd35 := WestRange.diagonal_gt_three_fifths (west_own hW) hm west_upper.le hd.1.le
    hgap.le
  have hd' : 3/5 ≤ (chart P).d ∧ (chart P).d ≤ 11/14 :=
    ⟨hd35.le,by linarith [Real.pi_lt_d4]⟩
  have hgap' := WestRange.gap_gt (west_own hW) hm (west_own_angle hW).le hd' hgap.le
  have hv := WestRange.west_lt (west_own hW) hm west_upper.le hd' hgap.le
  exact ⟨hgap',hv,WestRange.diagonal_gt (west_own hW) hm hv.le hd35.le hgap'.le⟩

/-- No normalized packing has a missing west wing. -/
theorem not_missing_west (P : NormalizedPacking R) : ¬ MissingWestWing P := by
  intro h
  have hm := missing_west h
  have hd := diagonal_range (P := P)
  have hwall : Real.pi/4-(chart P).d < (chart P).v := by
    have h' := h.phase_wall
    dsimp [chart]
    linarith
  have hgap := west_gap h
  match hW : P.ownAxis 2, hS : P.ownAxis 4 with
  | false, false =>
    exact WestSide.MissingWest.impossible (west_side hW) (south_side hS) hm
      ⟨by linarith,(abs_lt.mp (west_side_angle hW)).2.le⟩ (south_side_angle hS).le
      ⟨hd.1.le,hd.2⟩
  | false, true =>
    have hv := abs_lt.mp (west_side_angle hW)
    exact SouthSide.impossible (X := (chart P).reflect) (south_own hS).reflect
      (west_side hW).reflect hm.reflect ⟨(south_own_angle hS).le,south_upper.le⟩
      (west_side_angle hW).le
      (by dsimp only [Chart.reflect]; constructor <;> linarith [Real.pi_gt_d4,Real.pi_lt_d4])
      (by dsimp only [Chart.reflect]; linarith)
      (fun _ => by dsimp only [Chart.reflect]; constructor <;> linarith [Real.pi_lt_d4])
  | true, false =>
    obtain ⟨hgap',hv,hd'⟩ := own_west_range h hW
    exact WestDiagonal.SideSouth.impossible (west_own hW) (south_side hS) hm
      (south_side_angle hS).le ⟨hd'.le,by linarith [Real.pi_lt_d4]⟩ ⟨by linarith,hv.le⟩
  | true, true =>
    obtain ⟨hgap',hv,hd'⟩ := own_west_range h hW
    have hsum := own_angle_sum hW hS
    by_cases horder : (chart P).s ≤ (chart P).v
    · exact WestDiagonal.OwnSouth.impossible (west_own hW) (south_own hS) hm
        ⟨(south_own_angle hS).le,by linarith⟩ ⟨hd'.le,by linarith [Real.pi_lt_d4]⟩
        ⟨by linarith,hv.le⟩
    · exact WestTurned.impossible (X := (chart P).reflect) (south_own hS).reflect
        (west_own hW).reflect hm.reflect south_upper.le (west_own_angle hW).le
        (le_of_not_ge horder) (by dsimp only [Chart.reflect]; linarith)
        (by dsimp only [Chart.reflect]; constructor <;> linarith [Real.pi_gt_d4,Real.pi_lt_d4])
        (by dsimp only [Chart.reflect]; linarith)

end SquaresInCircles.Six.Wings

namespace SquaresInCircles.Six
open Normalization

/-- In every normalized packing W and D are separated along the secondary axis
of W, and D and S along the secondary axis of S, as in the model. -/
theorem wing_separators {R : ℝ} (P : NormalizedPacking R) :
    WingSeparators P :=
  ⟨by_contra fun h => Wings.not_missing_west P (missing_west_of_failure P h),
    by_contra fun h => Wings.not_missing_south P (missing_south_of_failure P h)⟩

end SquaresInCircles.Six
