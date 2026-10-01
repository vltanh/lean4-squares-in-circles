import SquaresInCircles.Six.Normalization.CardinalWindows
import SquaresInCircles.Six.Analytic.WestDiagonalOrder

/-!
# The cyclic order of the exterior squares

With D in its half window `phase 3 ≤ 5π/4`, the angles of the five exterior
squares increase in the order E, N, W, D, S, within one turn
(`PinPacking.cyclic_primary_order`), and D has angle `π + d` with
`-2/5 < d ≤ π/4`. Four of the five inequalities follow from the windows of the
pins. The windows of W and D overlap; for them, the pins, the bounds on the
charts and the disjointness of the two squares give `phase 2 < phase 3`
(`Analytic.west_before_diagonal`).
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

/-- The angle of W is less than that of D. -/
theorem PinPacking.west_before_diagonal {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) : P.phase 2 < P.phase 3 := by
  have hw := P.window 2
  have hd := P.window 3
  norm_num [windowLower,windowUpper,phaseCenter] at hw hd
  have bw := (P.contained 2).bounds (P.avoidsCore 2)
  have bd := (P.contained 3).bounds (P.avoidsCore 3)
  have hpW : openSquare (orientedSquare (P.phase 2) (P.radial 2) (P.transverse 2))
      (Analytic.polarPin (9/10) (11*Real.pi/12)) := by
    simpa [fixedPin,Analytic.polarPin,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
      using P.pin 2
  have hpD : openSquare (orientedSquare (P.phase 3) (P.radial 3) (P.transverse 3))
      (Analytic.polarPin (9/10) (5*Real.pi/4)) := by
    simpa [fixedPin,Analytic.polarPin,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
      using P.pin 3
  exact Analytic.west_before_diagonal (P.contained 2) (P.contained 3)
    bw.1.le bd.1.le bw.2.2.le bd.2.2.le
    ⟨by linarith [hw.1],by linarith [hw.2]⟩
    ⟨by linarith [hd.1,Real.pi_gt_d2],hD⟩ hpW hpD
    (P.exterior_disjoint 2 3 (by decide))

/-- In its half window, D has angle `π + d` with `-2/5 < d ≤ π/4`. -/
lemma PinPacking.diagonal_deviation {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    -2/5 < P.phase 3-Real.pi ∧ P.phase 3-Real.pi ≤ Real.pi/4 := by
  have h := P.window 3
  norm_num [windowLower,windowUpper,phaseCenter] at h
  constructor <;> linarith [h.1,h.2,Real.pi_gt_d2]

/-- The angles of E, N, W, D and S increase, within one turn. -/
theorem PinPacking.cyclic_primary_order {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    P.phase 0 < P.phase 1 ∧ P.phase 1 < P.phase 2 ∧
      P.phase 2 < P.phase 3 ∧ P.phase 3 < P.phase 4 ∧ P.phase 4 < P.phase 0+2*Real.pi := by
  have he := P.window 0
  have hn := P.window 1
  have hw := P.window 2
  have hs := P.window 4
  norm_num [windowLower,windowUpper,phaseCenter] at he hn hw hs
  exact ⟨by linarith [he.2,hn.1,Real.pi_gt_d2],
    by linarith [hn.2,hw.1,Real.pi_gt_d2],P.west_before_diagonal hD,
    by linarith [hs.1,Real.pi_gt_d2],by linarith [hs.2,he.1,Real.pi_gt_d2]⟩

end SquaresInCircles.Six.Normalization
