import SquaresInCircles.Six.Analytic.FixedPairRadicands

/-!
# The negative-cardinal half of the pair domain

For source W-primary and w<=0, the north rotating force never points near the
angle maximizing its whole-circle curvature. Its resultant length is at most
7/6, and the squared length difference is at least 37/50. This improves the
north curvature bound from 457/1000 to 3/10 on the entire negative-cardinal
half, without introducing a tail or a numerical subdivision.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

lemma harmonicCurvature_length_form {R P Q T x D : ℝ}
    (hx : 0<harmonicArg P Q T x) (hD : P^2-Q^2-T^2=D) :
    harmonicCurvature R P Q T x=
      (R/4)*(Real.sqrt (harmonicArg P Q T x)-D/(Real.sqrt (harmonicArg P Q T x))^3) := by
  let z := Q*Real.cos x+T*Real.sin x
  let L := Real.sqrt (harmonicArg P Q T x)
  have harg : harmonicArg P Q T x=P+z := by dsimp [harmonicArg,z]; ring
  have hroot : Real.sqrt (P+z)=L := by rw [← harg]; rfl
  have hL : 0<L := Real.sqrt_pos.mpr hx
  have hsq : L^2=P+z := by simpa only [harg] using Real.sq_sqrt hx.le
  have hn : z^2+2*P*z+Q^2+T^2=L^4-D := by
    calc
      _=(P+z)^2-D := by nlinarith only [hD]
      _=(L^2)^2-D := by rw [hsq]
      _=_ := by ring
  change R*(z^2+2*P*z+Q^2+T^2)/(4*(P+z)*Real.sqrt (P+z))=(R/4)*(L-D/L^3)
  rw [hroot,hn,← hsq]
  field_simp [ne_of_gt hL]
  ring

lemma harmonicCurvature_le_length_ceiling {R P Q T x D D0 B : ℝ}
    (hR : 0≤R) (hx : 0<harmonicArg P Q T x) (hD : P^2-Q^2-T^2=D)
    (hD0 : 0≤D0) (hDD : D0≤D) (hB : 0<B)
    (hL : Real.sqrt (harmonicArg P Q T x)≤B) :
    harmonicCurvature R P Q T x≤(R/4)*(B-D0/B^3) := by
  let L := Real.sqrt (harmonicArg P Q T x)
  have hL0 : 0<L := Real.sqrt_pos.mpr hx
  have hp := pow_le_pow_left₀ hL0.le hL 3
  have hm := mul_le_mul hDD hp (pow_nonneg hL0.le 3) (hD0.trans hDD)
  have hdiv : D0/B^3≤D/L^3 :=
    (div_le_div_iff₀ (pow_pos hB 3) (pow_pos hL0 3)).mpr hm
  have hlin : L-D/L^3≤B-D0/B^3 := by linarith
  rw [harmonicCurvature_length_form hx hD]
  exact mul_le_mul_of_nonneg_left hlin (by positivity)

namespace FixedPair
open Stress Normalization

/-- This estimate uses only the sign wall w=0, not a newly chosen subdivision. -/
theorem negative_cardinal_north_curvature {no : Bool} {n w : ℝ}
    (hd : Domain no false n w) (hw : w≤0) :
    (northWave no 0 1 n w).curvature (northRadius 0) w≤3/10 := by
  let W := northWave no 0 1 n w
  have hr : W.rotor=rStar := by cases no <;> rfl
  have hb : W.baseSq=1 := by cases no <;> rfl
  have hamp := northWave_amplitude no 0 1 n w
  have hparams : W.parameter=rStar^2+1 := by simp only [Wave.parameter,hr,hb]
  have hdisc : W.parameter^2-W.cosine^2-W.sine^2=(1-rStar^2)^2 := by
    have ha : W.cosine^2+W.sine^2=4*rStar^2 := by
      simpa only [W,hr,hb,mul_one] using hamp
    rw [hparams]
    nlinarith
  have hx : 0<W.arg w := by
    apply northWave_positive (wo := false) 0 1
    simpa only [sliceN,sliceW,if_true,if_false] using hd
  have hbounds := domain_bounds hd
  have hz : W.cosine*Real.cos w+W.sine*Real.sin w≤(3/5)*rStar := by
    cases no
    · have hs : Real.sin w≤0 := by
        have hh := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-w by linarith)
          (by linarith [hbounds.2.2.1,Real.pi_gt_d2] : -w≤Real.pi)
        rw [Real.sin_neg] at hh
        linarith
      change 0*Real.cos w+2*rStar*Real.sin w≤(3/5)*rStar
      have hp := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*rStar by positivity) hs
      linarith [rStar_pos]
    · have hq : -3/10≤Real.sin (n-w) := by
        by_cases h : n-w≤0
        · have hs := sin_lower_of_nonpos h
          linarith [hbounds.1]
        · have hs := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_not_ge h)
            (by linarith [hbounds.2.2.2.2.2,Real.pi_gt_d2] : n-w≤Real.pi)
          linarith
      have he : W.cosine*Real.cos w+W.sine*Real.sin w=-2*rStar*Real.sin (n-w) := by
        dsimp [W,northWave]
        rw [Real.sin_sub]
        ring
      rw [he]
      have hp := mul_nonneg (show 0≤2*rStar by positivity) (show 0≤Real.sin (n-w)+3/10 by linarith)
      nlinarith
  have hrsq := pow_le_pow_left₀ rStar_pos.le pair_multiplier_bounds.2.1.le 2
  have hlength : Real.sqrt (W.arg w)≤7/6 := by
    have hs := Real.sq_sqrt hx.le
    have hn := Real.sqrt_nonneg (W.arg w)
    have ha : W.arg w≤(7/6:ℝ)^2 := by
      dsimp [Wave.arg,harmonicArg]
      rw [hparams]
      nlinarith [pair_multiplier_bounds.2.1]
    nlinarith
  have hdelta : (37:ℝ)/50≤(1-rStar^2)^2 := by
    have hl : (863:ℝ)/1000≤1-rStar^2 := by nlinarith
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤863/1000) hl 2
    norm_num at hs
    linarith
  have hh := harmonicCurvature_le_length_ceiling (R := Six.radius) Six.radius_pos.le hx hdisc
    (by norm_num : (0:ℝ)≤37/50) hdelta (by norm_num : (0:ℝ)<7/6) hlength
  change W.curvature Six.radius w≤(Six.radius/4)*((7/6)-(37/50)/(7/6)^3) at hh
  change W.curvature Six.radius w≤3/10
  norm_num at hh
  linarith [candidate_radius_bounds.2]

end FixedPair
end SquaresInCircles.Six.Analytic
