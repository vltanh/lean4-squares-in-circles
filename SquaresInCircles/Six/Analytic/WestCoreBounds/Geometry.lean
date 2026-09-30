module
public import SquaresInCircles.Six.Analytic.WestCoreBounds.Support

@[expose] public section

/-!
# A compact actual domain for an OWN-W D-sourced separator

The three-edge analytic profiles first give v<31/50, and then d>16/25
using the previously proved q>53/50. Every inequality is taken from the
original normalized packing. Neither the S bit nor a candidate D-edge graph
is a premise. These are genuine geometric improvements, not checked cells.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestCoreBounds
open Normalization

theorem own_west_domain {R : ℝ} (P : NormalizedPacking R) (hW : P.ownBits 2=true)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    -P.helperAngle 2 < 31/50 ∧ 16/25 < P.diagonalAngle := by
  let v := -P.helperAngle 2
  let d := P.diagonalAngle
  have hv : 0 ≤ v ∧ v ≤ 2/3 := by
    have hneg := canonical_own_west_negative P hW
    dsimp [v]
    constructor <;> linarith [P.helper_windows.2.2.1.1]
  have hd : 3/5 ≤ d ∧ d ≤ 11/14 := by
    have hlo := DW_Dsecondary_diagonal_gt_three_fifths P hsep
    exact ⟨hlo.le,by linarith [P.diagonal_angle_range.2,Real.pi_lt_d4]⟩
  have hgap : 53/50 < v+d := by
    have h := WestGapReserve.own_west_gap P hW hsep
    dsimp [v,d]
    linarith
  have hq : 1 ≤ v+d ∧ v+d ≤ Real.pi/2 := by
    constructor <;> linarith [hgap,hv.2,hd.2,Real.pi_gt_d2]
  have hWphase : P.phase 2=Real.pi-v := by
    rw [P.phase_from_deviation 2]
    dsimp [v]
    ring
  have hDphase : P.phase 3=Real.pi+d := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hCW : 1/2+angularWidth v ≤
      P.radial 2+P.center.1*Real.cos v-P.center.2*Real.sin v := by
    have h := P.own_separator 2 hW
    rw [hWphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCD : 1/2+angularWidth d ≤
      P.radial 3+P.center.1*Real.cos d+P.center.2*Real.sin d := by
    have h := P.own_separator 3 P.diagonal_own
    rw [hDphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (v+d) ≤
      P.radial 2*Real.sin (v+d)-P.transverse 2*Real.cos (v+d)+P.transverse 3 := by
    have h := hsep
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,pair_frameY_right,
      show (Real.pi+d)-(Real.pi-v)=v+d by ring] at h
    nlinarith only [h]
  have hnonpos (large : Bool) : ∃ upper : Bool, value large upper v d ≤ 0 :=
    value_nonpositive large ⟨hv.1,by linarith [hv.2,Real.pi_gt_d2]⟩
      ⟨by linarith [hd.1],by linarith [hd.2,Real.pi_gt_d2]⟩ hq
      (P.contained 2) (P.contained 3)
      (P.box.1.2.trans CandidateWestTail.ceiling_bounds.2.2.2)
      ⟨P.box.2.1,P.box.2.2.trans CandidateWestTail.ceiling_bounds.2.2.2⟩ hCW hCD hWD
  have hvnew : v < 31/50 := by
    by_contra! h
    obtain ⟨upper,hn⟩ := hnonpos true
    have hp := large_positive upper ⟨h,hv.2⟩ hd
    linarith
  have hdnew : 16/25 < d := by
    by_contra! h
    obtain ⟨upper,hn⟩ := hnonpos false
    have hp := low_positive upper ⟨hd.1,h⟩
      (show 53/50-d ≤ v ∧ v ≤ 31/50 by constructor <;> linarith)
    linarith
  exact ⟨hvnew,hdnew⟩

end SquaresInCircles.Six.Analytic.WestCoreBounds

namespace SquaresInCircles.Six.Analytic
open Normalization

lemma MissingWestWing.own_west_domain {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) (hW : P.ownBits 2=true) :
    -P.helperAngle 2 < 31/50 ∧ 16/25 < P.diagonalAngle :=
  WestCoreBounds.own_west_domain P hW h.from_diagonal

end SquaresInCircles.Six.Analytic
