import SquaresInCircles.Six.Normalization.CardinalWindows
import SquaresInCircles.Six.Analytic.WestDiagonalOrder

/-!
# D4 and N18 from analytic pair geometry

The four exact pair-coordinate identities live in Analytic.PairCoordinates.
W/D order now follows from the actual pins, chart bounds and broad windows by
the whole-domain four-axis proof. The six-variable finite-cover application and
its root-membership/reification helpers have been removed from this module.
The earlier construction of PinPacking remains a separate conversion task.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

/-- D4 with no interval certificate: two primary bounds and two pin-oriented
transverse bounds exclude a reversal of the actual primary directions. -/
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

/-- The normalized D window needed by the retained Appendix A and A2. -/
lemma PinPacking.diagonal_deviation {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    -2/5 < P.phase 3-Real.pi ∧ P.phase 3-Real.pi ≤ Real.pi/4 := by
  have h := P.window 3
  norm_num [windowLower,windowUpper,phaseCenter] at h
  constructor <;> linarith [h.1,h.2,Real.pi_gt_d2]

/-- N18: the other four links use only the stated broad windows. -/
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
