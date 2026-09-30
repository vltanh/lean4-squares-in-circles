module
public import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening
public import SquaresInCircles.Six.Analytic.HighDiagonalAffineTransverse

@[expose] public section

/-!
# One quadratic obstruction on the complete quarter-to-one interval

This lemma combines the OWN-wing transverse profile with the high-D affine
profile. It does not subdivide a domain or evaluate a generated stress table.
The decisive identity is a quadratic completion in the wing deviation; its
three coefficient estimates use elementary Taylor bounds and exact rational
arithmetic. The result will strengthen a genuine D-sourced W/D gap to > 1.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- The only trigonometric enclosure used in the quadratic coefficient proof. -/
lemma quarter_one_trig_bounds {q : ℝ}
    (hq : Real.pi/4 ≤ q ∧ q ≤ 1) :
    (7/10 ≤ Real.sin q ∧ Real.sin q ≤ 421/500) ∧
      (27/50 ≤ Real.cos q ∧ Real.cos q ≤ 71/100) := by
  have hq0 : 0 ≤ q := by linarith [hq.1,Real.pi_pos]
  have hrootlo : (7:ℝ)/10 ≤ Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hroothi : Real.sqrt 2/2 ≤ (71:ℝ)/100 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hslo := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ Real.pi/4 by linarith [Real.pi_pos])
    (show q ≤ Real.pi/2 by linarith [hq.2,Real.pi_gt_d2]) hq.1
  rw [Real.sin_pi_div_four] at hslo
  have hshi := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ q by linarith [Real.pi_pos])
    (show (1:ℝ) ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hq.2
  have hclo := Real.cos_le_cos_of_nonneg_of_le_pi hq0
    (show (1:ℝ) ≤ Real.pi by linarith [Real.pi_gt_d2]) hq.2
  have hchi := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi/4 by linarith [Real.pi_pos])
    (show q ≤ Real.pi by linarith [hq.2,Real.pi_gt_d2]) hq.1
  rw [Real.cos_pi_div_four] at hchi
  exact ⟨⟨hrootlo.trans hslo,by
    nlinarith [Seven.sin_upper_five (show (0:ℝ) ≤ 1 by norm_num)]⟩,
    ⟨by nlinarith [Seven.cos_lower_six (show (0:ℝ) ≤ 1 by norm_num)],
      hchi.trans hroothi⟩⟩

private def gapA (q : ℝ) : ℝ :=
  19/100+(17/100)*q-(10030541/25000000)*Real.sin q+(17/500)*Real.cos q

private def gapB (q : ℝ) : ℝ :=
  (73/100)*Real.cos q-(1093029/2500000)*Real.sin q-17/100

private def gapC (q : ℝ) : ℝ := (31/100)*(73/100)^2*Real.sin q

private lemma gapA_lower {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) : 1/25 < gapA q := by
  let p : ℝ → ℝ := fun x => 19/100+(17/100)*x-
    (10030541/25000000)*(x-x^3/6+x^5/120)+
    (17/500)*(1-x^2/2+x^4/24-x^6/720)
  have hq0 : 0 ≤ q := hq.1
  have hp : p q ≤ gapA q := by
    have hs := Seven.sin_upper_five hq.1
    have hc := Seven.cos_lower_six hq.1
    dsimp [p,gapA]
    nlinarith only [hs,hc]
  have hq1 : 0 ≤ 1-q := sub_nonneg.mpr hq.2
  have hsq : 0 ≤ 1-q^2 := by
    have hh := mul_nonneg hq1 (show 0 ≤ 1+q by linarith [hq.1])
    nlinarith only [hh]
  have hfactor : 0 ≤ (1-q)*
      (634797249+584065837*(1-q^2)+431065837*(1-q)+
        17766623*q^3+30516623*q^4+425000*q^5)/9000000000 := by positivity
  have hid : p q-p 1 = (1-q)*
      (634797249+584065837*(1-q^2)+431065837*(1-q)+
        17766623*q^3+30516623*q^4+425000*q^5)/9000000000 := by
    dsimp [p]
    ring
  have hleft : (1:ℝ)/25 < p 1 := by norm_num [p]
  linarith

private lemma gapB_square {q : ℝ} (hq : Real.pi/4 ≤ q ∧ q ≤ 1) :
    (gapB q)^2 ≤ Real.sin q/40 := by
  obtain ⟨⟨hslo,hshi⟩,⟨hclo,hchi⟩⟩ := quarter_one_trig_bounds hq
  have hs0 : 0 ≤ Real.sin q := by linarith
  have hlo : -(171/1000)*Real.sin q ≤ gapB q := by
    dsimp [gapB]
    nlinarith only [hclo,hshi]
  have hhi : gapB q ≤ 1/20 := by
    dsimp [gapB]
    nlinarith only [hchi,hslo]
  by_cases hnonneg : 0 ≤ gapB q
  · have hp := mul_nonneg (sub_nonneg.mpr hhi)
      (show 0 ≤ (1:ℝ)/20+gapB q by linarith)
    nlinarith only [hp,hslo]
  · have hnegative : gapB q ≤ 0 := (lt_of_not_ge hnonneg).le
    have hp := mul_nonneg (sub_nonneg.mpr hlo)
      (show 0 ≤ (171/1000)*Real.sin q-gapB q by linarith)
    have hsquare := mul_nonneg hs0 (sub_nonneg.mpr hshi)
    nlinarith only [hp,hsquare,hs0]

/-- The completed quadratic is positive for EVERY real wing deviation. The
profile applications, not this algebraic lemma, impose the physical interval. -/
lemma west_gap_quadratic_positive {q : ℝ}
    (hq : Real.pi/4 ≤ q ∧ q ≤ 1) (v : ℝ) :
    0 < gapA q+gapB q*v+gapC q*v^2 := by
  have hq0 : 0 ≤ q := by linarith [hq.1,Real.pi_pos]
  have hA := gapA_lower ⟨hq0,hq.2⟩
  have hB := gapB_square hq
  have hsin := (quarter_one_trig_bounds hq).1.1
  have hspos : 0 < Real.sin q := by linarith
  have hC : 0 < gapC q := by dsimp [gapC]; positivity
  have hCA := mul_nonneg hC.le (show 0 ≤ gapA q-1/25 by linarith)
  have hdisc : 0 < 4*gapC q*gapA q-(gapB q)^2 := by
    dsimp [gapC] at hCA ⊢
    nlinarith only [hCA,hB,hsin]
  have hid : 4*gapC q*(gapA q+gapB q*v+gapC q*v^2) =
      (2*gapC q*v+gapB q)^2+4*gapC q*gapA q-(gapB q)^2 := by ring
  by_contra! hbad
  have hp := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4*gapC q by positivity) hbad
  nlinarith only [hid,hp,hdisc,sq_nonneg (2*gapC q*v+gapB q)]

/-- The universal radial/transverse quadratic and the two affine profiles
exclude a D-sourced edge on the full quarter-to-one phase interval. -/
theorem west_secondary_profile_obstruction {a b z d v q : ℝ}
    (hc : ContainedChart a |b|)
    (hv : 0 ≤ v) (hq : Real.pi/4 ≤ q ∧ q ≤ 1) (hangle : q=d+v)
    (hwing : |b| ≤ 233/500-(73/100)*v)
    (hdiag : z ≤ 31/100-(17/100)*d) :
    a*Real.sin q-b*Real.cos q+z < 1/2+angularWidth q := by
  let B : ℝ := 233/500-(73/100)*v
  have hB : |b| ≤ B := hwing
  have hBlo : 0 ≤ B := (abs_nonneg b).trans hB
  have hBhi : B ≤ 233/500 := by dsimp [B]; linarith
  obtain ⟨⟨hslo,hshi⟩,⟨hclo,hchi⟩⟩ := quarter_one_trig_bounds hq
  have hs0 : 0 ≤ Real.sin q := by linarith
  have hc0 : 0 ≤ Real.cos q := by linarith
  have hrad := radial_transverse_quadratic hc
  rw [← sq_abs b] at hrad
  have hradmul := mul_nonneg hs0
    (show 0 ≤ 1113/1000-a-(31/100)*(|b|+|b|^2) by linarith [rho0_upper])
  have hsign := mul_le_mul_of_nonneg_right (neg_le_abs b) hc0
  have hbracket : 0 ≤ Real.cos q-(31/100)*(1+B+|b|)*Real.sin q := by
    have hcoef : 1+B+|b| ≤ 483/250 := by linarith
    have hp := mul_le_mul hcoef hshi hs0 (by norm_num : (0:ℝ) ≤ 483/250)
    nlinarith only [hp,hclo]
  have hmono := mul_nonneg (sub_nonneg.mpr hB) hbracket
  have hupper : a*Real.sin q-b*Real.cos q+z ≤
      (1113/1000-(31/100)*(B+B^2))*Real.sin q+B*Real.cos q+
        31/100-(17/100)*d := by
    nlinarith only [hradmul,hsign,hmono,hdiag]
  have hpos := west_gap_quadratic_positive hq v
  have hid : 1/2+(Real.sin q+Real.cos q)/2-
      ((1113/1000-(31/100)*(B+B^2))*Real.sin q+B*Real.cos q+
        31/100-(17/100)*d) = gapA q+gapB q*v+gapC q*v^2 := by
    rw [show d=q-v by linarith [hangle]]
    dsimp [B,gapA,gapB,gapC]
    ring
  rw [angularWidth,abs_of_nonneg hc0,abs_of_nonneg hs0]
  linarith

/-- If the transverse coordinate has the opposite sign, even the purely
radial bound leaves a strict reserve throughout the same phase interval. -/
lemma west_secondary_nonnegative_transverse {a b z q : ℝ}
    (ha : a ≤ rho0) (hb : 0 ≤ b) (hz : z ≤ 9/40)
    (hq : Real.pi/4 ≤ q ∧ q ≤ 1) :
    a*Real.sin q-b*Real.cos q+z < 1/2+angularWidth q := by
  obtain ⟨⟨hslo,hshi⟩,⟨hclo,hchi⟩⟩ := quarter_one_trig_bounds hq
  have hs0 : 0 ≤ Real.sin q := by linarith
  have hc0 : 0 ≤ Real.cos q := by linarith
  have hrad := mul_nonneg hs0 (show 0 ≤ 1113/1000-a by linarith [rho0_upper])
  have htrans := mul_nonneg hb hc0
  rw [angularWidth,abs_of_nonneg hc0,abs_of_nonneg hs0]
  nlinarith only [hrad,htrans,hz,hshi,hclo]

end SquaresInCircles.Six.Analytic
