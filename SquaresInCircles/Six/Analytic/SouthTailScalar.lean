import SquaresInCircles.Six.Analytic.HighDiagonalSupport
import SquaresInCircles.Six.Analytic.HalfAngleControl

/-!
# A negative angle of S: two reserves

Let `-v` be the angle of S, with `2/25 ≤ v ≤ 5/8`, let `1/2 ≤ d ≤ π/4` be the
angle of D, and let `t = sin v/(1 + cos v)`. Two inequalities in `v` and `d`,
one for each separator of D and S, hold with a positive reserve. Both reserves
increase with `d`, by the monotonicity of `sin` and `cos` in the first quadrant,
so it is enough to take `d = 1/2`. There the first is a positive quadratic in
`1/2 + v` after Taylor bounds, and the second, multiplied by `1 + t²`, is a
cubic in `x = t - 1/25` with coefficients `p₀ > 1/4000`, `p₁ ≥ 1`, `p₂ ≥ -1` and
`p₃ ≥ 0`, positive on `0 ≤ x ≤ 1`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma halfRatio_upper_five_eighths {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 5/8) :
    halfRatio v ≤ (13/25)*v := by
  have hv2 : v^2 ≤ 25/64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) (show 0 ≤ 5/8+v by linarith)]
  have hv4 : v^4 ≤ 625/4096 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv2) (show 0 ≤ 25/64+v^2 by positivity)]
  have hcoef : 0 ≤ 1/25-(7/75)*v^2-v^4/120 := by linarith
  have hp := mul_nonneg hv.1 hcoef
  have hs := Seven.sin_upper_five hv.1
  have hc := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := v))
    (show 0 ≤ (13/25)*v by linarith [hv.1])
  unfold halfRatio
  apply (div_le_iff₀ (halfRatio_den_pos ⟨hv.1,by linarith [hv.2]⟩)).mpr
  nlinarith only [hp,hs,hc]

lemma halfRatio_circle_identities {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 4/5) :
    (1+(halfRatio v)^2)*Real.cos v=1-(halfRatio v)^2 ∧
      (1+(halfRatio v)^2)*Real.sin v=2*halfRatio v := by
  have h := halfRatio_identities hv
  have h1 := congrArg (fun x : ℝ => halfRatio v*x) h.1
  have h2 := congrArg (fun x : ℝ => halfRatio v*x) h.2
  constructor <;> nlinarith only [h.1,h.2,h1,h2]

lemma south_tail_angle_range {v d : ℝ}
    (hv : 2/25 ≤ v ∧ v ≤ 5/8) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    29/50 ≤ d+v ∧ d+v ≤ Real.pi/2 := by
  constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]

lemma south_tail_trig {v d : ℝ}
    (hv : 2/25 ≤ v ∧ v ≤ 5/8) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    137/250 ≤ Real.sin (d+v) ∧ 0 ≤ Real.cos (d+v) := by
  have h := south_tail_angle_range hv hd
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (29:ℝ)/50 by linarith [Real.pi_pos]) h.2 h.1
  have hl := Seven.sin_lower_seven (x := (29:ℝ)/50) (by norm_num)
  exact ⟨by nlinarith only [hs,hl],Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [h.1,Real.pi_pos],h.2⟩⟩

/-- The reserve for the separator of D and S along the secondary axis of S. -/
theorem south_wing_tail_reserve {v d : ℝ}
    (hv : 2/25 ≤ v ∧ v ≤ 5/8) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    coreCeiling+(55641/50000)*halfRatio v+(21/20)*Real.cos (d+v)+
        diagonalBudget d*Real.sin (d+v) <
      (1+Real.cos (d+v)+Real.sin (d+v))/2 := by
  let z := 1/2+v
  have hz : 0 ≤ z ∧ z ≤ 9/8 := by dsimp [z]; constructor <;> linarith [hv.1,hv.2]
  have hrange := south_tail_angle_range hv hd
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ z by linarith [hz.1,Real.pi_pos]) hrange.2
    (show z ≤ d+v by dsimp [z]; linarith [hd.1])
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hz.1
    (show d+v ≤ Real.pi by linarith [hrange.2,Real.pi_pos])
    (show z ≤ d+v by dsimp [z]; linarith [hd.1])
  have hpos := south_tail_trig hv hd
  have hbudget : diagonalBudget d ≤ 1121/5000 := by
    dsimp [diagonalBudget]
    linarith [hd.1]
  have hB := mul_nonneg (sub_nonneg.mpr hbudget) (by linarith [hpos.1] : 0 ≤ Real.sin (d+v))
  have ht := halfRatio_upper_five_eighths ⟨by linarith [hv.1],hv.2⟩
  have hc := Seven.cos_upper_four hz.1
  have hs := Real.sin_ge_sub_cube hz.1
  have hz3 : z^3 ≤ (9/8)*z^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz.2) (sq_nonneg z)]
  have hz2 : z^2 ≤ 81/64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) (show 0 ≤ 9/8+z by linarith [hz.1])]
  have hz4 : z^4 ≤ (81/64)*z^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz2) (sq_nonneg z)]
  have hquad : 0 < 63/500-(303/1000)*z+(97/500)*z^2 := by
    nlinarith [sq_nonneg ((97/250)*z-303/1000)]
  have hbase : 0 < 19359/50000-(11/20)*Real.cos z+
      (1379/5000)*Real.sin z-(55641/50000)*halfRatio v := by
    have hvz : v=z-1/2 := by dsimp [z]; ring
    nlinarith only [ht,hc,hs,hz3,hz4,hquad,hz.1,sq_nonneg z,hvz]
  dsimp [coreCeiling]
  nlinarith only [hbase,hB,hsin,hcos]

/-- The constant of a supporting line `a + (21/50) b = 7009/6250` of the disk of
far corners. -/
def southSupportCeiling : ℝ := 7009/6250

def southDualSlope : ℝ := 21/50

private def aCoeff (t : ℝ) : ℝ := 19359/50000-(39931/50000)*t
private def bCoeff (t : ℝ) : ℝ := -1435139/2500000+(406539/2500000)*t

private def southDGap (v d : ℝ) : ℝ :=
  (477/2500+(17/100)*d)*(1+(21/50)*halfRatio v)+
    aCoeff (halfRatio v)*Real.sin (d+v)+bCoeff (halfRatio v)*Real.cos (d+v)

private lemma southDGap_at_half_positive {v : ℝ} (hv : 2/25 ≤ v ∧ v ≤ 5/8) :
    0 < southDGap v (1/2) := by
  let t := halfRatio v
  let x := t-1/25
  have hvr : 0 ≤ v ∧ v ≤ 4/5 := ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have ht0 : 1/25 ≤ t := by linarith [halfRatio_lower hvr,hv.1]
  have ht1 : t ≤ 11/32 := by linarith [halfRatio_upper hvr,hv.2]
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hcL := Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)
  have hcU := Seven.cos_upper_four (x := (1:ℝ)/2) (by norm_num)
  have hsL := Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
  have hsU := Seven.sin_upper_five (x := (1:ℝ)/2) (by norm_num)
  let p0 : ℝ := -(1314023629/2441406250)*Real.cos (1/2)+
    (19534712/48828125)*Real.sin (1/2)+548597917/1953125000
  let p1 : ℝ := (333726677/390625000)*Real.cos (1/2)+
    (1852073/6250000)*Real.sin (1/2)+2704219/19531250
  let p2 : ℝ := -(32584321/31250000)*Real.cos (1/2)-
    (770721/1250000)*Real.sin (1/2)+1810627/6250000
  let p3 : ℝ := -(406539/2500000)*Real.cos (1/2)+
    (39931/50000)*Real.sin (1/2)+28959/250000
  have hp0 : 1/4000 < p0 := by dsimp [p0]; nlinarith only [hcU,hsL]
  have hp1 : 1 ≤ p1 := by dsimp [p1]; nlinarith only [hcL,hsL]
  have hp2 : -1 ≤ p2 := by dsimp [p2]; nlinarith only [hcU,hsU]
  have hp3 : 0 ≤ p3 := by dsimp [p3]; nlinarith only [hcU,hsL]
  have h1 := mul_nonneg (sub_nonneg.mpr hp1) hx0
  have h2 := mul_nonneg (sub_nonneg.mpr hp2) (sq_nonneg x)
  have h3 := mul_nonneg hp3 (pow_nonneg hx0 3)
  have hx := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have hpoly : 0 < p0+p1*x+p2*x^2+p3*x^3 := by nlinarith
  have htids := halfRatio_circle_identities hvr
  change (1+t^2)*Real.cos v=1-t^2 ∧ (1+t^2)*Real.sin v=2*t at htids
  have hs : (1+t^2)*Real.sin (1/2+v)=
      Real.sin (1/2)*(1-t^2)+2*Real.cos (1/2)*t := by
    rw [Real.sin_add]
    linear_combination Real.sin (1/2)*htids.1 + Real.cos (1/2)*htids.2
  have hc : (1+t^2)*Real.cos (1/2+v)=
      Real.cos (1/2)*(1-t^2)-2*Real.sin (1/2)*t := by
    rw [Real.cos_add]
    linear_combination Real.cos (1/2)*htids.1 - Real.sin (1/2)*htids.2
  have hid : (1+t^2)*southDGap v (1/2)=p0+p1*x+p2*x^2+p3*x^3 := by
    dsimp [southDGap]
    change (1+t^2)*((477/2500+(17/100)*(1/2))*(1+(21/50)*t)+
      aCoeff t*Real.sin (1/2+v)+bCoeff t*Real.cos (1/2+v))=_
    calc
      _ = (1379/5000)*(1+(21/50)*t)*(1+t^2)+
          aCoeff t*((1+t^2)*Real.sin (1/2+v))+
          bCoeff t*((1+t^2)*Real.cos (1/2+v)) := by ring
      _ = _ := by rw [hs,hc]; dsimp [p0,p1,p2,p3,x,aCoeff,bCoeff]; ring
  have hprod : 0 < (1+t^2)*southDGap v (1/2) := by rw [hid]; exact hpoly
  by_contra! hnonpos
  have hn := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 1+t^2) hnonpos
  linarith

private lemma southDGap_positive {v d : ℝ}
    (hv : 2/25 ≤ v ∧ v ≤ 5/8) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) : 0 < southDGap v d := by
  have hvr : 0 ≤ v ∧ v ≤ 4/5 := ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have ht0 := halfRatio_nonnegative hvr
  have ht1 : halfRatio v ≤ 11/32 := by linarith [halfRatio_upper hvr,hv.2]
  have ha : 0 ≤ aCoeff (halfRatio v) := by dsimp [aCoeff]; linarith
  have hb : bCoeff (halfRatio v) ≤ 0 := by dsimp [bCoeff]; linarith
  have hangle := south_tail_angle_range hv hd
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ 1/2+v by linarith [hv.1,Real.pi_pos]) hangle.2
    (show 1/2+v ≤ d+v by linarith [hd.1])
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ 1/2+v by linarith [hv.1])
    (show d+v ≤ Real.pi by linarith [hangle.2,Real.pi_pos])
    (show 1/2+v ≤ d+v by linarith [hd.1])
  have hS := mul_le_mul_of_nonneg_left hs ha
  have hC := mul_le_mul_of_nonpos_left hc hb
  have hL := mul_nonneg (show 0 ≤ d-1/2 by linarith [hd.1])
    (show 0 ≤ 1+(21/50)*halfRatio v by positivity)
  have hbase := southDGap_at_half_positive hv
  dsimp [southDGap] at *
  nlinarith only [hbase,hS,hC,hL]

/-- The reserve for the separator of D and S along the secondary axis of D. -/
theorem south_diagonal_tail_reserve {v d : ℝ}
    (hv : 2/25 ≤ v ∧ v ≤ 5/8) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    southSupportCeiling*(Real.cos (d+v)+halfRatio v*Real.sin (d+v))+
        coreCeiling*(1-halfRatio v)*(Real.sin (d+v)-southDualSlope*Real.cos (d+v))+
        diagonalBudget d*(1+southDualSlope*halfRatio v) <
      ((1+Real.cos (d+v)+Real.sin (d+v))/2)*(1+southDualSlope*halfRatio v) := by
  have h := southDGap_positive hv hd
  dsimp [southDGap,aCoeff,bCoeff,diagonalBudget,coreCeiling,southDualSlope,southSupportCeiling] at *
  nlinarith only [h]

end SquaresInCircles.Six.Analytic
