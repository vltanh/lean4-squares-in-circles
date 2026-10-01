import SquaresInCircles.Six.Analytic.SoftAxialSupportWide
import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Curvature

/-!
# Own W, cardinal S: the force on S

Let S be separated from C along the south side of C, and from D along the
secondary axis of D. Equal weights on the two edges give S the force with the
components `U = cos s + cos (d-s)` and `V = sin (d-s) - sin s` in its frame,
that is `2 cos (d/2)` times `cos (d/2-s)` and `sin (d/2-s)`. For
`1/2 ≤ d ≤ π/4`, `s ≤ 2/5` and `d - s ≤ π/4` the force lies in the cone
`U ≥ 33/20`, `|V| ≤ 3U/5`: the first bound follows from `cos x ≥ 1 - x²/2` and
`s² + (d-s)² ≤ 137/196`, the second from `|sin x| ≤ (3/5) cos x` for
`|x| ≤ 15/28`. In this cone a contained square has support at most
`rho0 U + (3/25) V²`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestCardinalSouth
open Normalization

def southRadial (s d : ℝ) : ℝ := Real.cos s+Real.cos (d-s)
def southTransverse (s d : ℝ) : ℝ := Real.sin (d-s)-Real.sin s

lemma south_half_angle (s d : ℝ) :
    southRadial s d=2*Real.cos (d/2)*Real.cos (d/2-s) ∧
    southTransverse s d=2*Real.cos (d/2)*Real.sin (d/2-s) := by
  have hc0 := Real.cos_sub (d/2) (d/2-s)
  have hc1 := Real.cos_add (d/2) (d/2-s)
  have hs0 := Real.sin_sub (d/2) (d/2-s)
  have hs1 := Real.sin_add (d/2) (d/2-s)
  rw [show d/2-(d/2-s)=s by ring] at hc0 hs0
  rw [show d/2+(d/2-s)=d-s by ring] at hc1 hs1
  constructor
  · dsimp [southRadial]
    nlinarith only [hc0,hc1]
  · dsimp [southTransverse]
    nlinarith only [hs0,hs1]

private lemma square_sum_bound {s d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) (hs : s ≤ 2/5) (hr : d-s ≤ 11/14) :
    s^2+(d-s)^2 ≤ 137/196 := by
  have hr0 : 0 ≤ d-s := by linarith [hd.1,hs]
  by_cases hs0 : 0 ≤ s
  · have hp := mul_nonneg hs0 hr0
    have hq := mul_nonneg (sub_nonneg.mpr hd.2)
      (show 0 ≤ 11/14+d by linarith [hd.1])
    nlinarith only [hp,hq]
  · have hslo : -(2/7) ≤ s := by linarith [hd.1,hr]
    have hS := mul_nonneg (show 0 ≤ s+2/7 by linarith)
      (show 0 ≤ 2/7-s by linarith)
    have hR := mul_nonneg (show 0 ≤ 11/14-(d-s) by linarith)
      (show 0 ≤ 11/14+(d-s) by linarith)
    nlinarith only [hS,hR]

private lemma half_angle_ratio {x : ℝ} (hx : -(15/28) ≤ x ∧ x ≤ 15/28) :
    |Real.sin x| ≤ (3/5)*Real.cos x := by
  have hsq := mul_nonneg (show 0 ≤ 15/28-x by linarith [hx.2])
    (show 0 ≤ 15/28+x by linarith [hx.1])
  have hc : 1343/1568 ≤ Real.cos x := by
    nlinarith only [hsq,Real.one_sub_sq_div_two_le_cos (x := x)]
  have sine_upper (y : ℝ) (hy : -(15/28) ≤ y ∧ y ≤ 15/28) :
      Real.sin y ≤ 511/1000 := by
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ y by linarith [hy.1,Real.pi_gt_d2])
      (show (15:ℝ)/28 ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hy.2
    have hu := Seven.sin_upper_five (x := (15:ℝ)/28) (by norm_num)
    nlinarith only [hm,hu]
  have hu := sine_upper x hx
  have hl := sine_upper (-x) (by constructor <;> linarith [hx.1,hx.2])
  rw [Real.sin_neg] at hl
  have hsin : |Real.sin x| ≤ 511/1000 := abs_le.mpr ⟨by linarith,hu⟩
  linarith

/-- The force on S lies in the cone `U ≥ 33/20`, `|V| ≤ 3U/5`. -/
lemma south_force_cone {s d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (hs : s ≤ 2/5) (hr : d-s ≤ Real.pi/4) :
    33/20 ≤ southRadial s d ∧ |southTransverse s d| ≤ (3/5)*southRadial s d := by
  have hd' : 1/2 ≤ d ∧ d ≤ 11/14 := ⟨hd.1,by linarith [hd.2,Real.pi_lt_d4]⟩
  have hr' : d-s ≤ 11/14 := by linarith [hr,Real.pi_lt_d4]
  have hsq := square_sum_bound hd' hs hr'
  have hsine := Real.one_sub_sq_div_two_le_cos (x := s)
  have hrine := Real.one_sub_sq_div_two_le_cos (x := d-s)
  have hU : 33/20 ≤ southRadial s d := by
    dsimp [southRadial]
    nlinarith only [hsq,hsine,hrine]
  have hx : -(15/28) ≤ d/2-s ∧ d/2-s ≤ 15/28 := by
    constructor <;> linarith [hd'.1,hs,hr']
  have hratio := half_angle_ratio hx
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hpos : 0 ≤ 2*Real.cos (d/2) := by positivity
  have hp := mul_le_mul_of_nonneg_left hratio hpos
  obtain ⟨hUI,hVI⟩ := south_half_angle s d
  refine ⟨hU,?_⟩
  rw [hUI,hVI,abs_mul,abs_of_nonneg hpos]
  nlinarith only [hp]

/-- The support of S, with `rho0` replaced by its rational bound
`55641/50000`. -/
lemma south_support {a b s d : ℝ} (hc : ContainedChart a |b|)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (hs : s ≤ 2/5) (hr : d-s ≤ Real.pi/4) :
    southRadial s d*a+southTransverse s d*b ≤
      CandidateWestTail.rhoBound*southRadial s d+(3/25)*(southTransverse s d)^2 := by
  have hcone := south_force_cone hd hs hr
  have h := soft_axial_support_wide hc hcone.1 hcone.2
  have hU : 0 ≤ southRadial s d := by linarith [hcone.1]
  have hm := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.2.1 hU
  linarith

end SquaresInCircles.Six.Analytic.OwnWestCardinalSouth
