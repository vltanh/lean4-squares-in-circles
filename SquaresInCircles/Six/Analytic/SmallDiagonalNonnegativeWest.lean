import SquaresInCircles.Six.Analytic.SharpFrontProfile
import SquaresInCircles.Six.Analytic.SmallDiagonalSecondary

/-!
# Small diagonal angles with a nonnegative W deviation

The two secondary alternatives are treated independently. For D-secondary,
normalization bounds the W projection and the sharper OWN-D transverse profile
pays for the remaining phase gap. The final scalar is increasing on [0,1/2]
and negative at 1/2 by its displayed Taylor estimate.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private def smallDPositiveW (d : ℝ) : ℝ :=
  (613/1000)*Real.sin d-(37/1000)*Real.cos d-9/250-(47/100)*d

private lemma smallDPositiveW_negative {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    smallDPositiveW d<0 := by
  have hder (x : ℝ) : HasDerivAt smallDPositiveW
      ((613/1000)*Real.cos x+(37/1000)*Real.sin x-47/100) x := by
    convert ((((Real.hasDerivAt_sin x).const_mul (613/1000)).sub
      ((Real.hasDerivAt_cos x).const_mul (37/1000))).sub_const (9/250)).sub
      ((hasDerivAt_id x).const_mul (47/100)) using 1 <;>
      dsimp [smallDPositiveW] <;> ring
  have hmono := Seven.monoOn_of_hasDeriv_nonneg
    (l := 0) (u := (1:ℝ)/2) (f := smallDPositiveW)
    (d := fun x => (613/1000)*Real.cos x+(37/1000)*Real.sin x-47/100)
    (by dsimp [smallDPositiveW]; fun_prop) (fun x _ => hder x) (by
      intro x hx
      have hx0 := hx.1.le
      have hx1 := hx.2.le
      have hsq := mul_nonneg (sub_nonneg.mpr hx1) (show 0≤1/2+x by linarith)
      have hc := Real.one_sub_sq_div_two_le_cos (x := x)
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_gt_d2])
      nlinarith)
  have hupper := hmono hd (show (1:ℝ)/2∈Set.Icc 0 (1/2) by constructor <;> norm_num) hd.2
  have hlast : smallDPositiveW (1/2)<0 := by
    have hs := Seven.sin_upper_five (x := (1:ℝ)/2) (by norm_num)
    have hc := Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/2)
    dsimp [smallDPositiveW]
    nlinarith only [hs,hc]
  exact hupper.trans_lt hlast

lemma small_diagonal_nonnegative_W_D_secondary {w d aw bw bd : ℝ}
    (hd : 0≤d ∧ d≤1/2) (hw : 0≤w ∧ w≤d)
    (haw : aw≤1113/1000) (hbw : -bw≤463/1000)
    (hbd : bd<58/125-(47/100)*d) :
    aw*Real.sin (d-w)-bw*Real.cos (d-w)+bd<1/2+angularWidth (d-w) := by
  let q := d-w
  have hq : 0≤q ∧ q≤d := by dsimp [q]; constructor <;> linarith [hw.1,hw.2]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hq.1 (by linarith [hq.2,hd.2,Real.pi_gt_d2])
  have hc0 : 0≤Real.cos q := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.1,Real.pi_pos],by linarith [hq.2,hd.2,Real.pi_gt_d2]⟩
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤q by linarith [hq.1,Real.pi_pos])
    (show d≤Real.pi/2 by linarith [hd.2,Real.pi_gt_d2]) hq.2
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hq.1
    (show d≤Real.pi by linarith [hd.2,Real.pi_gt_d2]) hq.2
  have hA := mul_le_mul_of_nonneg_right haw hs0
  have hB := mul_le_mul_of_nonneg_right hbw hc0
  have hnegative := smallDPositiveW_negative hd
  change aw*Real.sin q-bw*Real.cos q+bd<1/2+angularWidth q
  rw [angularWidth,abs_of_nonneg hc0,abs_of_nonneg hs0]
  dsimp [smallDPositiveW] at hnegative
  nlinarith only [hA,hB,hbd,hs,hc,hnegative]

/-- Both remaining W/D source axes are impossible on this part of the domain. -/
theorem nonnegative_W_forces_large_diagonal {R : ℝ} (P : NormalizedPacking R)
    (hw : 0≤P.helperAngle 2) : 1/2<P.diagonalAngle := by
  by_contra! hdsmall
  have hd : 0≤P.diagonalAngle ∧ P.diagonalAngle≤1/2 := ⟨P.diagonal_angle_range.1.le,hdsmall⟩
  obtain ⟨k,hsep,hk⟩ := DW_secondary_exists P
  rcases hk with rfl | rfl
  · linarith [W_secondary_forces_large_diagonal P hsep]
  · have hwphase := P.phase_from_deviation 2
    have hdphase : P.phase 3=Real.pi+P.diagonalAngle := by
      dsimp [NormalizedPacking.diagonalAngle]
      ring
    have horder : P.helperAngle 2≤P.diagonalAngle := by
      have hh := P.primary_order.2.2.1
      rw [hwphase,hdphase] at hh
      linarith
    have hown := P.own_separator 3 P.diagonal_own
    rw [hdphase] at hown
    have hbd := own_sharp_front_transverse (P.contained 3) P.box.1.2 P.box.2.2 hd hown
    have hbW := (P.contained 2).u_le_U0 (P.avoidsCore 2)
    have hbound := small_diagonal_nonnegative_W_D_secondary hd ⟨hw,horder⟩
      ((P.contained 2).a_le_rho0.trans rho0_upper.le)
      (by linarith [neg_le_abs (P.transverse 2),normalization_transverse_upper_sharp])
      ((le_abs_self (P.transverse 3)).trans_lt hbd)
    change Seven.SAT.threshold (P.square 2) (P.square 3)≤
      frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
    rw [P.square_def 2,P.square_def 3,pair_frameY_right,oriented_pair_threshold,
      hwphase,hdphase] at hsep
    have hdiff : (Real.pi+P.diagonalAngle)-(Real.pi+P.helperAngle 2)=
        P.diagonalAngle-P.helperAngle 2 := by ring
    rw [hdiff] at hsep
    linarith

end SquaresInCircles.Six.Analytic
