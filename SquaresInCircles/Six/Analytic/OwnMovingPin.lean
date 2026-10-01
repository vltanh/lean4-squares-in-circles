import SquaresInCircles.Six.Analytic.MovingPinPolynomial
import SquaresInCircles.Six.Normalization.CentralSAT

/-!
# The OWN moving pin, without a finite-cover certificate

The normal coordinate follows directly from OWN separation. For the transverse
coordinate use MovingPinPolynomial: failure would put the far corner outside
Q0. The proof works on the larger symmetric interval |t| <= 5/12; no special
subdivision, numerical root or sampled minimum is needed.

The strong central box is an explicit geometric hypothesis of this local
lemma. Its unconditional construction is a separate conversion obligation.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma moving_pin_trig {t : ℝ} (ht : |t| ≤ 5/12) :
    (5/6 ≤ Real.cos t ∧ Real.cos t ≤ 1) ∧
      (0 ≤ |Real.sin t| ∧ |Real.sin t| ≤ 5/12) := by
  have hs : |Real.sin t| ≤ |t| := by
    simpa using Real.abs_sin_sub_sin_le t 0
  have ht2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at ht2
  refine ⟨⟨?_,Real.cos_le_one t⟩,abs_nonneg _,hs.trans ht⟩
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]

/-- OWN supplies the radial lower bound used in the transverse obstruction. -/
lemma own_radial_lower {t a b cx cy : ℝ}
    (hcy0 : 0 ≤ cy) (hcy1 : cy ≤ 23/200) (hc : 0 ≤ Real.cos t)
    (hown : 0 ≤ centralMargin .own t a b cx cy) :
    1+(1/2+cx)*Real.cos t+(77/200)*|Real.sin t| ≤ a+1/2 := by
  have hy := mul_le_mul_of_nonneg_left (neg_le_abs (Real.sin t)) hcy0
  have hgap := mul_nonneg (show 0 ≤ 23/200-cy by linarith) (abs_nonneg (Real.sin t))
  dsimp [centralMargin,centralNormal,angularWidth] at hown
  rw [abs_of_nonneg hc] at hown
  nlinarith only [hy,hgap,hown]

/-- The two moving-pin coordinates are controlled by transparent inequalities.
In particular the transverse conclusion does not assume the old scalar check. -/
theorem own_moving_pin {t a b cx cy : ℝ}
    (ht : |t| ≤ 5/12) (hc : ContainedChart a |b|)
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx : cx ≤ c0) (hy : cy ≤ c0)
    (hown : 0 ≤ centralMargin .own t a b cx cy) :
    openSquare (orientedSquare t a b) (1+cx,0) := by
  have htr := moving_pin_trig ht
  have hcos0 : 0 ≤ Real.cos t := by linarith [htr.1.1]
  have hx1 : cx ≤ 23/200 := hx.trans c0_lt_23_200.le
  have hy1 : cy ≤ 23/200 := hy.trans c0_lt_23_200.le
  have hrad := own_radial_lower hy0 hy1 hcos0 hown
  have hunit : (Real.cos t)^2+|Real.sin t|^2=1 := by
    rw [sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have htrans := own_transverse_obstruction
    (abs_nonneg b) hx0 hx1 htr.1.1 htr.1.2 htr.2.1 htr.2.2 hunit hrad hc.containment
  have htri := abs_add_le ((1+cx)*Real.sin t) b
  rw [abs_mul,abs_of_nonneg (show 0 ≤ 1+cx by linarith)] at htri
  have hY : |(1+cx)*Real.sin t+b| < 1/2 := by linarith
  have hxc := mul_nonneg hx0 hcos0
  have hvs := mul_nonneg (show (0:ℝ) ≤ 77/200 by norm_num) (abs_nonneg (Real.sin t))
  have hX : |(1+cx)*Real.cos t-a| < 1/2 := by
    apply abs_lt.mpr
    constructor
    · have ha := hc.a_le_rho0
      nlinarith [rho0_upper,htr.1.1]
    · nlinarith only [hrad,hvs,htr.1.2]
  unfold openSquare
  rw [orientedSquare_localX,orientedSquare_localY]
  constructor
  · simpa using hX
  · have hid : -(1+cx)*Real.sin t-b = -((1+cx)*Real.sin t+b) := by ring
    simpa only [zero_mul,mul_zero,zero_add,add_zero,hid,abs_neg] using hY

end SquaresInCircles.Six.Analytic
