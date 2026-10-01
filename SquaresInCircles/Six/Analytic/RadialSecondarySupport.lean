import SquaresInCircles.Six.Analytic.CardinalWidthTriangle
import SquaresInCircles.Six.Stress.Support

/-!
# Radial support of the cardinal-plus-D-secondary resultants

The equal-weight W and S resultants have squared lengths 2+2 sin(d) and
2+2 cos(d), independently of the helper angles. Their half-angle formulas
are proved from the unit-circle identities. The sum is at most 4 cos(pi/8),
with cos(pi/8)<231/250 proved by squaring. These are actual center supports,
not an assumption that the force is on a cap branch.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Stress

def westRadialLength (d : ℝ) : ℝ := 2*Real.cos (Real.pi/4-d/2)
def southRadialLength (d : ℝ) : ℝ := 2*Real.cos (d/2)

lemma west_radial_length {d : ℝ} (hd : 1/2≤d ∧ d≤Real.pi/4) :
    Real.sqrt (2+2*Real.sin d)=westRadialLength d := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show Real.pi/4-d/2∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have h := Real.cos_two_mul (Real.pi/4-d/2)
  rw [show 2*(Real.pi/4-d/2)=Real.pi/2-d by ring,Real.cos_pi_div_two_sub] at h
  have he : 2+2*Real.sin d=(2*Real.cos (Real.pi/4-d/2))^2 := by nlinarith
  rw [he,Real.sqrt_sq (by positivity)]
  rfl

lemma south_radial_length {d : ℝ} (hd : 1/2≤d ∧ d≤Real.pi/4) :
    Real.sqrt (2+2*Real.cos d)=southRadialLength d := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d/2∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have h := Real.cos_two_mul (d/2)
  rw [show 2*(d/2)=d by ring] at h
  have he : 2+2*Real.cos d=(2*Real.cos (d/2))^2 := by nlinarith
  rw [he,Real.sqrt_sq (by positivity)]
  rfl

lemma west_cardinal_secondary_norm (w d : ℝ) :
    (Real.cos w+Real.sin (d-w))^2+(-Real.sin w-Real.cos (d-w))^2=2+2*Real.sin d := by
  have hsum : Real.sin w*Real.cos (d-w)+Real.cos w*Real.sin (d-w)=Real.sin d := by
    rw [← Real.sin_add]
    congr 1
    ring
  nlinarith [Real.sin_sq_add_cos_sq w,Real.sin_sq_add_cos_sq (d-w)]

lemma south_cardinal_secondary_norm (s d : ℝ) :
    (Real.cos s+Real.cos (d-s))^2+(-Real.sin s+Real.sin (d-s))^2=2+2*Real.cos d := by
  have hsum : Real.cos s*Real.cos (d-s)-Real.sin s*Real.sin (d-s)=Real.cos d := by
    rw [← Real.cos_add]
    congr 1
    ring
  nlinarith [Real.sin_sq_add_cos_sq s,Real.sin_sq_add_cos_sq (d-s)]

lemma chart_radial_work {a b : ℝ} (hc : ContainedChart a |b|) (g : Point) :
    dot g (a,b)≤(1113/1000)*vectorLength g := by
  have h := dot_le_radius (v := g) (p := (a,b))
    (show 0≤rho0 by linarith [rho0_gt_one]) (chart_center_radius_sq hc)
  have hr := mul_le_mul_of_nonneg_right rho0_upper.le (vectorLength_nonneg g)
  exact h.trans hr

lemma west_cardinal_secondary_work {a b w d : ℝ}
    (hc : ContainedChart a |b|) (hd : 1/2≤d ∧ d≤Real.pi/4) :
    (Real.cos w+Real.sin (d-w))*a+(-Real.sin w-Real.cos (d-w))*b≤
      (1113/1000)*westRadialLength d := by
  have h := chart_radial_work hc (Real.cos w+Real.sin (d-w),-Real.sin w-Real.cos (d-w))
  dsimp [dot,vectorLength,normSq] at h
  rw [west_cardinal_secondary_norm,west_radial_length hd] at h
  exact h

lemma south_cardinal_secondary_work {a b s d : ℝ}
    (hc : ContainedChart a |b|) (hd : 1/2≤d ∧ d≤Real.pi/4) :
    (Real.cos s+Real.sin (Real.pi/2+s-d))*a+
      (-Real.sin s+Real.cos (Real.pi/2+s-d))*b≤(1113/1000)*southRadialLength d := by
  have h := chart_radial_work hc (Real.cos s+Real.cos (d-s),-Real.sin s+Real.sin (d-s))
  dsimp [dot,vectorLength,normSq] at h
  rw [south_cardinal_secondary_norm,south_radial_length hd] at h
  have he : Real.pi/2+s-d=Real.pi/2-(d-s) := by ring
  simpa only [he,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] using h

lemma eighth_cos_upper : Real.cos (Real.pi/8)≤231/250 := by
  have hhalf := Real.cos_two_mul (Real.pi/8)
  rw [show 2*(Real.pi/8)=Real.pi/4 by ring,Real.cos_pi_div_four] at hhalf
  have hroot : Real.sqrt (2:ℝ)/2≤7072/10000 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0<Real.cos (Real.pi/8)+231/250 by linarith)
  nlinarith

lemma radial_length_sum_bound (d : ℝ) :
    westRadialLength d+southRadialLength d≤4*(231/250) := by
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show Real.pi/8∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])
  have hproduct := mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi/8-d/2)) hcos
  have hsum : Real.cos (Real.pi/4-d/2)+Real.cos (d/2)=
      2*Real.cos (Real.pi/8)*Real.cos (Real.pi/8-d/2) := by
    have hA : Real.cos (Real.pi/4-d/2)=Real.cos (Real.pi/8+(Real.pi/8-d/2)) := by
      congr 1; ring
    have hB : Real.cos (d/2)=Real.cos (Real.pi/8-(Real.pi/8-d/2)) := by congr 1; ring
    rw [hA,hB,Real.cos_add (Real.pi/8),Real.cos_sub (Real.pi/8) (Real.pi/8-d/2)]
    ring
  dsimp [westRadialLength,southRadialLength]
  nlinarith only [hproduct,hsum,eighth_cos_upper]

lemma high_diagonal_width_lower {d : ℝ} (hd : 1/2≤d ∧ d≤Real.pi/4) :
    27/20≤Real.cos d+Real.sin d := by
  have hm := cos_add_sin_mono (x := (1:ℝ)/2) (by norm_num) hd.1 hd.2
  linarith [low_half_bracket.1,low_half_bracket.2.2.1]

end SquaresInCircles.Six.Analytic
