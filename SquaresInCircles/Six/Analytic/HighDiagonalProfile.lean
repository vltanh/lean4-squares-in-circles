module
public import SquaresInCircles.Six.Analytic.DiagonalHalfBound
public import SquaresInCircles.Six.Analytic.LowDiagonalEndpoints

@[expose] public section

/-!
# A small transverse coordinate for high D

Once d>1/2 is proved, the actual OWN separator and containment give
  aD>=128/125, |bD|<23/100.
A secondary projection with phase gap at most 1/2 then cannot separate D
from an exterior square. This uses actual chart bounds and a direct rational
sine/cosine reserve, not an angle-grid certificate.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma high_diagonal_profile {a b cx cy d : ℝ}
    (hc : ContainedChart a |b|) (hx : cx≤c0) (hy : cy≤c0)
    (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    128/125≤a ∧ |b|<23/100 := by
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hsd := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  have hm := cos_add_sin_mono (x := (1:ℝ)/2) (by norm_num) hd.1 hd.2
  have hT : 339/250≤Real.cos d+Real.sin d := by
    linarith [low_half_bracket.1,low_half_bracket.2.2.1]
  have hcx : 387/1000≤1/2-cx := by dsimp [c0] at hx; linarith [rho0_upper]
  have hcy : 387/1000≤1/2-cy := by dsimp [c0] at hy; linarith [rho0_upper]
  have hxprod := mul_le_mul_of_nonneg_right hcx hcd
  have hyprod := mul_le_mul_of_nonneg_right hcy hsd
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
    abs_neg,abs_of_nonneg hcd,abs_of_nonneg hsd] at hown
  have ha : 128/125≤a := by nlinarith only [hown,hxprod,hyprod,hT]
  refine ⟨ha,?_⟩
  by_contra! hb
  have hAsq := mul_nonneg (show 0≤a-128/125 by linarith)
    (show 0≤a+128/125+1 by linarith)
  have hBsq := mul_nonneg (sub_nonneg.mpr hb)
    (show 0≤|b|+23/100+1 by positivity)
  have hcircle := hc.containment
  norm_num [Q0] at hcircle
  nlinarith

lemma NormalizedPacking.high_diagonal_profile {R : ℝ} (P : NormalizedPacking R) :
    128/125≤P.radial 3 ∧ |P.transverse 3|<23/100 := by
  have hphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  exact Analytic.high_diagonal_profile (P.contained 3) P.box.1.2 P.box.2.2
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
    (by simpa only [hphase] using P.own_separator 3 P.diagonal_own)

lemma short_secondary_projection {a b x q : ℝ}
    (ha : a≤rho0) (hb : b≤U0) (hx : x≤23/100)
    (hq : 0≤q ∧ q≤1/2) :
    x+a*Real.sin q+b*Real.cos q<1/2+angularWidth q := by
  have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hq.1
    (by linarith [hq.2,Real.pi_gt_d2])
  have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤q by linarith [hq.1,Real.pi_pos])
    (show (1:ℝ)/2≤Real.pi/2 by linarith [Real.pi_gt_d2]) hq.2
  have hs : Real.sin q≤4795/10000 := hsinmono.trans low_half_bracket.2.2.2
  have hsq := mul_nonneg (sub_nonneg.mpr hq.2) (show 0≤1/2+q by linarith [hq.1])
  have hcos : 7/8≤Real.cos q := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := q)]
  have hcos0 : 0≤Real.cos q := by linarith
  have hA := mul_le_mul_of_nonneg_right (ha.trans rho0_upper.le) hsin0
  have hB := mul_le_mul_of_nonneg_right (hb.trans U0_lt_117_250.le) hcos0
  rw [angularWidth,abs_of_nonneg hcos0,abs_of_nonneg hsin0]
  nlinarith only [hA,hB,hx,hs,hcos]

/-- D-secondary on D/S needs a phase gap strictly greater than 1/2. -/
theorem DS_Dsecondary_gap_gt_half {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) :
    1/2<P.phase 4-P.phase 3 := by
  by_contra! hq
  have hnonneg := P.primary_order.2.2.2.1.le
  have hb := (P.contained 4).u_le_U0 (P.avoidsCore 4)
  have hx := P.high_diagonal_profile.2
  have hbound := short_secondary_projection (P.contained 4).a_le_rho0
    ((le_abs_self _).trans hb) ((neg_le_abs _).trans hx.le)
    ⟨sub_nonneg.mpr hnonneg,hq⟩
  change Seven.SAT.threshold (P.square 3) (P.square 4)≤
    frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at hsep
  rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_left] at hsep
  linarith

/-- The symmetric destination-frame projection gives the same gap bound on W/D. -/
theorem WD_Dsecondary_gap_gt_half {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    1/2<P.phase 3-P.phase 2 := by
  by_contra! hq
  have hnonneg := P.primary_order.2.2.1.le
  have hb := (P.contained 2).u_le_U0 (P.avoidsCore 2)
  have hx := P.high_diagonal_profile.2
  have hbound := short_secondary_projection (P.contained 2).a_le_rho0
    ((neg_le_abs _).trans hb) ((le_abs_self _).trans hx.le)
    ⟨sub_nonneg.mpr hnonneg,hq⟩
  change Seven.SAT.threshold (P.square 2) (P.square 3)≤
    frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
  rw [P.square_def 2,P.square_def 3,oriented_pair_threshold,pair_frameY_right] at hsep
  nlinarith only [hbound,hsep]

end SquaresInCircles.Six.Analytic
