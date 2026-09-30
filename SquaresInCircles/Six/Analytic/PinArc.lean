import SquaresInCircles.Six.Analytic.PinProjections
import SquaresInCircles.Six.Normalization.ChartBounds

/-!
# Two pins sixty degrees apart cover their primary-direction arc

This replaces the separate numerical normal/transverse tests in the middle
part of the W/D pin-covering argument. The only cases are which of the two
pins can fail its near-face inequality. Missing both pins would force the
far-corner squared radius above Q0, by one displayed completed square.
No subdivision or certificate is used.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma polar_localX (r q t a b : ℝ) :
    localX (orientedSquare t a b) (polarPin r q) = r*Real.cos (q-t)-a := by
  rw [orientedSquare_localX,Real.cos_sub]
  dsimp [polarPin]
  ring

lemma polar_localY (r q t a b : ℝ) :
    localY (orientedSquare t a b) (polarPin r q) = r*Real.sin (q-t)-b := by
  rw [orientedSquare_localY,Real.sin_sub]
  dsimp [polarPin]
  ring

lemma polar_mem_iff (r q t a b : ℝ) :
    openSquare (orientedSquare t a b) (polarPin r q) ↔
      |r*Real.cos (q-t)-a|<1/2 ∧ |r*Real.sin (q-t)-b|<1/2 := by
  simp only [openSquare,polar_localX,polar_localY]

/-- A coarse chord bound sufficient on the entire sixty-degree interval. -/
lemma cos_sixty_chord {v : ℝ} (hv0 : 0≤v) (hv1 : v≤Real.pi/3) :
    1-v/2≤Real.cos v := by
  by_cases hv : v≤1
  · have hp := mul_nonneg hv0 (sub_nonneg.mpr hv)
    nlinarith [Real.one_sub_sq_div_two_le_cos (x:=v)]
  · have hc := Real.cos_le_cos_of_nonneg_of_le_pi hv0
      (show Real.pi/3≤Real.pi by linarith [Real.pi_pos]) hv1
    rw [Real.cos_pi_div_three] at hc
    linarith

lemma sixty_sine_sum (v : ℝ) :
    Real.sin v+Real.sin (Real.pi/3-v)=Real.cos (v-Real.pi/6) := by
  calc
    _ = Real.sin ((v-Real.pi/6)+Real.pi/6)+
        Real.sin (Real.pi/6-(v-Real.pi/6)) := by congr 1 <;> congr 1 <;> ring
    _ = _ := by rw [Real.sin_add,Real.sin_sub,Real.sin_pi_div_six]; ring

/-- The far-corner obstruction is a single positive quadratic on the whole
real line. Its minimum reserve is 304609/2450000. -/
lemma sixty_cross_quadratic (v : ℝ) :
    Q0 < (19/10-(9/20)*v)^2+(2/35+(9/10)*v)^2 := by
  have hid : (19/10-(9/20)*v)^2+(2/35+(9/10)*v)^2-Q0 =
      (81/80)*(v-50/63)^2+304609/2450000 := by norm_num [Q0]; ring
  have h := sq_nonneg (v-50/63)
  nlinarith only [hid,h]

lemma sixty_cross_obstruction {a b v : ℝ} (hc : ContainedChart a |b|)
    (hv0 : 0≤v) (hv1 : v≤Real.pi/3)
    (ha : 1+(9/10)*Real.cos v≤a+1/2)
    (hb : 1-(9/10)*Real.sin (Real.pi/3-v)≤|b|+1/2) : False := by
  have hpi : Real.pi < (22:ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hcoss := cos_sixty_chord hv0 hv1
  have hsins := Real.sin_le (show 0≤Real.pi/3-v by linarith)
  have hA : 19/10-(9/20)*v≤a+1/2 := by nlinarith
  have hB : 2/35+(9/10)*v≤|b|+1/2 := by nlinarith
  have hA0 : 0≤19/10-(9/20)*v := by linarith
  have hB0 : 0≤2/35+(9/10)*v := by linarith
  have hAsq := mul_nonneg (sub_nonneg.mpr hA)
    (show 0≤a+1/2+(19/10-(9/20)*v) by linarith [hc.half_le])
  have hBsq := mul_nonneg (sub_nonneg.mpr hB)
    (show 0≤|b|+1/2+(2/35+(9/10)*v) by linarith [abs_nonneg b])
  nlinarith [hc.containment,sixty_cross_quadratic v]

private lemma near_thirty_cos {v : ℝ} (hv0 : 0≤v) (hv1 : v≤Real.pi/6) :
    41/50≤Real.cos v := by
  have hv : v≤3/5 := by linarith [Real.pi_lt_d2]
  have hp := pow_le_pow_left₀ hv0 hv 2
  nlinarith [Real.one_sub_sq_div_two_le_cos (x:=v)]

/-- At least one near-normal condition holds because a primary axis between
the pins is at most thirty degrees from one of them. -/
lemma sixty_one_normal {a b v : ℝ} (hc : ContainedChart a |b|)
    (hv0 : 0≤v) (hv1 : v≤Real.pi/3) :
    a-1/2<(9/10)*Real.cos v ∨ a-1/2<(9/10)*Real.cos (Real.pi/3-v) := by
  have ha := hc.a_le_rho0
  by_cases hv : v≤Real.pi/6
  · exact Or.inl (by nlinarith [near_thirty_cos hv0 hv,rho0_upper])
  · right
    have hz0 : 0≤Real.pi/3-v := by linarith
    have hz1 : Real.pi/3-v≤Real.pi/6 := by linarith
    nlinarith [near_thirty_cos hz0 hz1,rho0_upper]

/-- Two local pins at offsets -v and pi/3-v: closed disk containment and the
strict transverse bound alone prevent both from being missed. -/
theorem sixty_coordinates_cover {a b v : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (hv0 : 0≤v) (hv1 : v≤Real.pi/3) :
    (|(9/10)*Real.cos v-a|<1/2 ∧ |-(9/10)*Real.sin v-b|<1/2) ∨
    (|(9/10)*Real.cos (Real.pi/3-v)-a|<1/2 ∧
      |(9/10)*Real.sin (Real.pi/3-v)-b|<1/2) := by
  have hbb := abs_lt.mp hb
  have hsinL : 0≤Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv0
    (by linarith [Real.pi_pos])
  have hsinR : 0≤Real.sin (Real.pi/3-v) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hgap : (9/10)*(Real.sin v+Real.sin (Real.pi/3-v))<1 := by
    rw [sixty_sine_sum]
    nlinarith [Real.cos_le_one (v-Real.pi/6)]
  have hupperL : (9/10)*Real.cos v<a+1/2 := by
    nlinarith [Real.cos_le_one v,hc.half_le]
  have hupperR : (9/10)*Real.cos (Real.pi/3-v)<a+1/2 := by
    nlinarith [Real.cos_le_one (Real.pi/3-v),hc.half_le]
  have hnorm := sixty_one_normal hc hv0 hv1
  by_cases hL : a-1/2<(9/10)*Real.cos v
  · by_cases htL : b<1/2-(9/10)*Real.sin v
    · left
      constructor <;> apply abs_lt.mpr <;> constructor <;>
        linarith [hbb.1,hbb.2]
    · right
      have hnR : a-1/2<(9/10)*Real.cos (Real.pi/3-v) := by
        by_contra! hbad
        apply sixty_cross_obstruction hc (v:=Real.pi/3-v)
          (by linarith) (by linarith)
        · linarith
        · have hab := le_abs_self b
          have hid : Real.pi/3-(Real.pi/3-v)=v := by ring
          rw [hid]
          linarith
      constructor <;> apply abs_lt.mpr <;> constructor <;>
        linarith [hbb.1,hbb.2]
  · right
    have hnR : a-1/2<(9/10)*Real.cos (Real.pi/3-v) := hnorm.resolve_left hL
    have htR : (9/10)*Real.sin (Real.pi/3-v)-1/2<b := by
      by_contra! hbad
      apply sixty_cross_obstruction hc hv0 hv1
      · linarith
      · have hab := neg_le_abs b
        linarith
    constructor <;> apply abs_lt.mpr <;> constructor <;>
      linarith [hbb.1,hbb.2]

/-- Geometric form of the sixty-degree lemma, in an arbitrary real phase lift. -/
theorem sixty_pin_cover {t q a b : ℝ} (hc : ContainedChart a |b|)
    (hb : |b|<1/2) (ht : q≤t ∧ t≤q+Real.pi/3) :
    openSquare (orientedSquare t a b) (polarPin (9/10) q) ∨
      openSquare (orientedSquare t a b) (polarPin (9/10) (q+Real.pi/3)) := by
  have hv := sixty_coordinates_cover hc hb (v:=t-q) (by linarith) (by linarith)
  rw [polar_mem_iff,polar_mem_iff]
  have hL : q-t=-(t-q) := by ring
  have hR : q+Real.pi/3-t=Real.pi/3-(t-q) := by ring
  simpa only [hL,hR,Real.cos_neg,Real.sin_neg,mul_neg] using hv

end SquaresInCircles.Six.Analytic
