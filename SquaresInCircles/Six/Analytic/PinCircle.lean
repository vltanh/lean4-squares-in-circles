module
public import SquaresInCircles.Six.Analytic.OwnAngleWindows
public import SquaresInCircles.Six.Normalization.CapPiercing

@[expose] public section

/-!
# Radius-9/10 pins in actual square coordinates

A fixed pin on a cardinal ray is obtained from the analytic moving/piercing
point by interpolation of the transverse coordinate. The normal coordinate is
bounded directly. This replaces the separate fixed-pin scalar certificate.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

 def pinPoint (θ : ℝ) : Point := ((9/10)*Real.cos θ,(9/10)*Real.sin θ)
 def localPin (a b δ : ℝ) : Prop :=
  |(9/10)*Real.cos δ-a| < 1/2 ∧ |(9/10)*Real.sin δ-b| < 1/2

lemma pin_localX (t a b θ : ℝ) :
    localX (orientedSquare t a b) (pinPoint θ)=(9/10)*Real.cos (θ-t)-a := by
  rw [orientedSquare_localX]
  dsimp [pinPoint]
  rw [Real.cos_sub]
  ring

lemma pin_localY (t a b θ : ℝ) :
    localY (orientedSquare t a b) (pinPoint θ)=(9/10)*Real.sin (θ-t)-b := by
  rw [orientedSquare_localY]
  dsimp [pinPoint]
  rw [Real.sin_sub]
  ring

lemma pin_mem_iff (t a b θ : ℝ) :
    openSquare (orientedSquare t a b) (pinPoint θ) ↔ localPin a b (θ-t) := by
  simp only [openSquare,pin_localX,pin_localY,localPin]

lemma localPin_reflect (a b δ : ℝ) : localPin a (-b) (-δ) ↔ localPin a b δ := by
  simp only [localPin,Real.cos_neg,Real.sin_neg]
  have hid : (9/10)*(-Real.sin δ)-(-b)=-((9/10)*Real.sin δ-b) := by ring
  rw [hid,abs_neg]

lemma pin_normal {a u δ : ℝ} (h : ContainedChart a u) (hδ : |δ| ≤ 2/3) :
    |(9/10)*Real.cos δ-a| < 1/2 := by
  have hd2 := pow_le_pow_left₀ (abs_nonneg δ) hδ 2
  rw [sq_abs] at hd2
  have hc : (7:ℝ)/9 ≤ Real.cos δ := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := δ)]
  apply abs_lt.mpr
  constructor <;> linarith [h.a_le_rho0,rho0_upper,h.half_le,Real.cos_le_one δ]

/-- Interpolation along a ray preserves strict transverse membership. -/
lemma ray_transverse {z s b : ℝ} (hz : 9/10 ≤ z) (hb : |b| < 1/2)
    (hfar : |z*s+b| < 1/2) : |(9/10)*s+b| < 1/2 := by
  have hz0 : 0 < z := by linarith
  have hbb := abs_lt.mp hb
  have hff := abs_lt.mp hfar
  have hlo := mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ b+1/2 by linarith)
  have hhi := mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ 1/2-b by linarith)
  apply abs_lt.mpr
  constructor
  · by_contra! hf
    have hp := mul_nonpos_of_nonneg_of_nonpos hz0.le
      (show (9/10)*s+b+1/2 ≤ 0 by linarith)
    nlinarith
  · by_contra! hf
    have hp := mul_nonneg hz0.le
      (show 0 ≤ (9/10)*s+b-1/2 by linarith)
    nlinarith

lemma fixed_pin_from_ray {a b t z : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ 2/3) (hb : |b| < 1/2) (hz : 9/10 ≤ z)
    (hp : openSquare (orientedSquare t a b) (z,0)) :
    openSquare (orientedSquare t a b) (pinPoint 0) := by
  have hY := hp.2
  rw [orientedSquare_localY] at hY
  have hid : -z*Real.sin t+0*Real.cos t-b=-(z*Real.sin t+b) := by ring
  rw [hid,abs_neg] at hY
  have hbnd := ray_transverse hz hb hY
  rw [pin_mem_iff]
  constructor
  · simpa only [zero_sub,Real.cos_neg] using pin_normal h ht
  · have hid : (9/10)*Real.sin (-t)-b=-((9/10)*Real.sin t+b) := by
      rw [Real.sin_neg]
      ring
    simpa only [zero_sub,hid,abs_neg] using hbnd

/-- CE implies the fixed east pin using the already proved cap piercing. -/
theorem east_cap_fixed_pin {a b t H : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hH : 1/2 ≤ H)
    (hm : H+angularWidth t ≤ centerX t a b) :
    openSquare (orientedSquare t a b) (pinPoint 0) := by
  have hdeep : coreRadius ≤ H := half_ge_core.trans hH
  obtain ⟨ht40,_,_,_,_,hb⟩ := signed_cap_bounds ht hdeep (chart_corner h) hm
  have hp := cap_piercing ht hdeep (contained_from_corner (chart_corner h)) (cap_from_margin hm)
  exact fixed_pin_from_ray h (by linarith) hb (by linarith) hp

/-- OWN in the east primary quadrant implies the fixed east pin. -/
theorem east_own_fixed_pin {a b t x y : ℝ} (h : ContainedChart a |b|)
    (hcore : AvoidsCore a |b|) (ht : |t| ≤ Real.pi/4)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ c0) (hy : y ≤ c0)
    (hm : 0 ≤ centralMargin .own t a b x y) :
    openSquare (orientedSquare t a b) (pinPoint 0) := by
  have hwindow := own_east_window h ht hx0 hy0 hy hm
  have ht' : |t| ≤ 5/12 := by
    apply abs_le.mpr
    constructor <;> linarith [hwindow.1,hwindow.2]
  have hp := own_moving_pin ht' h hx0 hy0 hx hy hm
  exact fixed_pin_from_ray h (by linarith) (h.u_lt_half hcore) (by linarith) hp

end SquaresInCircles.Six.Analytic
