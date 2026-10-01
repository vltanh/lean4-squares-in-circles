import SquaresInCircles.Six.Analytic.DiagonalHalfBound
import SquaresInCircles.Six.Analytic.LowDiagonalEndpoints

/-!
# High D: a small transverse coordinate

For `1/2 ≤ d ≤ π/4`, the separation of D from the central square along its own
axis and the containment of D give `a ≥ 128/125` and `|b| < 23/100`. Then the
secondary axis of D separates D from S only if their phases differ by more than
`1/2`: for a smaller difference the projection stays below the threshold, by
rational bounds on `sin` and `cos`.
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
  have hsd := Real.sin_nonneg_of_nonneg_of_le_pi (x := d)
    (by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  have hm := cos_add_sin_mono (x := (1:ℝ)/2) (by norm_num) hd.1 hd.2
  have hT : 339/250≤Real.cos d+Real.sin d := by
    linarith [low_half_bracket.1,low_half_bracket.2.2.1]
  have hcx : 387/1000≤1/2-cx := by dsimp [c0] at hx; linarith [rho0_upper]
  have hcy : 387/1000≤1/2-cy := by dsimp [c0] at hy; linarith [rho0_upper]
  have hxprod := mul_le_mul_of_nonneg_right hcx hcd
  have hyprod := mul_le_mul_of_nonneg_right hcy hsd
  have hcpi : Real.cos (Real.pi+d)=-Real.cos d := by rw [add_comm]; exact Real.cos_add_pi d
  have hspi : Real.sin (Real.pi+d)=-Real.sin d := by rw [add_comm]; exact Real.sin_add_pi d
  simp only [centralMargin,centralNormal,angularWidth,hcpi,hspi,
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

/-- If D and S are separated along the secondary axis of D, their phases differ
by more than `1/2`. -/
theorem DS_Dsecondary_gap_gt_half {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) :
    1/2<P.phase 4-P.phase 3 := by
  by_contra! hq
  have hnonneg := P.primary_order.2.2.2.1.le
  have hb := (P.contained 4).u_le_U0 (P.avoidsCore 4)
  have hx := (NormalizedPacking.high_diagonal_profile P).2
  have hbound := short_secondary_projection (P.contained 4).a_le_rho0
    ((le_abs_self _).trans hb) ((neg_le_abs _).trans hx.le)
    ⟨sub_nonneg.mpr hnonneg,hq⟩
  change Seven.SAT.threshold (P.square 3) (P.square 4)≤
    frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at hsep
  rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_left] at hsep
  linarith

end SquaresInCircles.Six.Analytic
