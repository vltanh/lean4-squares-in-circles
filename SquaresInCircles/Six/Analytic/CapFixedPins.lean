import SquaresInCircles.Six.Analytic.PinCoordinates
import SquaresInCircles.Six.Analytic.CapChart
import SquaresInCircles.Six.Normalization.CapPiercing

/-!
# Caps contain fixed pins

A square in a deep cap, the half-plane `x ≥ h` with `h ≥ coreRadius`, has a lift
of its primary phase within `2/5` of the cap normal: of the four quadrants of
the phase, the two transverse ones and the opposite one are impossible. If the
cap is at least `1/2` deep, the square contains the east pin and its phase is
within `1/4` of the normal: it contains the point `(h + 1/2, 0)` of the axis,
and with it the pin at distance `9/10`. A square in a deep cap facing east also
contains the pin at angle `-π/12` or the one at `π/4`, which turned by `π` are
the W and D pins: by the sixty-degree lemma, and on the left flank by the
profile of a square separated along its own axis.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma cap_margin_transport {t u a b h:ℝ} (he:(t:Direction)=(u:Direction))
    (hm:h+angularWidth t≤centerX t a b) : h+angularWidth u≤centerX u a b := by
  have hh := margin_phase_eq he .east a b 0 0
  dsimp [centralMargin] at hh
  linarith

lemma opposite_cap_impossible {v a b h:ℝ} (hc:ContainedChart a |b|)
    (hv:|v|≤Real.pi/4) (hh:0<h)
    (hm:h+angularWidth (Real.pi+v)≤centerX (Real.pi+v) a b) : False := by
  have hcos : 0≤Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [(abs_le.mp hv).1,Real.pi_pos],by linarith [(abs_le.mp hv).2,Real.pi_pos]⟩
  have hsin : |Real.sin v|≤Real.cos v := by
    have hs := Seven.sin_le_cos_of_small ⟨abs_nonneg v,hv⟩
    rw [sin_abs_angle (by linarith [Real.pi_pos]),Real.cos_abs] at hs
    exact hs
  have hA := mul_nonneg (sub_nonneg.mpr hc.u_le) hcos
  have hB := mul_nonneg (abs_nonneg b) (sub_nonneg.mpr hsin)
  have hbs : b*Real.sin v≤|b| *|Real.sin v| := by
    simpa only [abs_mul] using le_abs_self (b*Real.sin v)
  have hwidth : 0≤angularWidth v := by dsimp [angularWidth]; positivity
  rw [add_comm Real.pi v] at hm
  simp only [centerX,angularWidth,Real.cos_add_pi,Real.sin_add_pi,abs_neg] at hm
  dsimp [angularWidth] at hwidth
  nlinarith

/-- A square in a deep cap has a lift of its primary phase within `2/5` of the
cap normal. -/
theorem positive_cap_direction {t a b h:ℝ} (hc:ContainedChart a |b|)
    (hh:coreRadius≤h) (hm:h+angularWidth t≤centerX t a b) :
    ∃ v : ℝ, |v|<2/5 ∧ (t:Direction)=(v:Direction) ∧ h+angularWidth v≤centerX v a b := by
  have hbox : (|a|+1/2)^2+(|b|+1/2)^2≤Q0 := by
    simpa only [abs_of_nonneg (show 0≤a by linarith [hc.half_le])] using hc.containment
  rcases four_primary_quadrants t with he | hn | hw | hs
  · obtain ⟨v,hv,hev⟩ := he
    have hm' := cap_margin_transport hev hm
    have hsmall := (signed_cap_bounds hv hh hbox hm').1
    exact ⟨v,hsmall,hev,hm'⟩
  · obtain ⟨v,hv,hev⟩ := hn
    have hm' := cap_margin_transport hev hm
    have hcb : ContainedChart a |-b| := by simpa only [abs_neg] using hc
    have htrans : h+angularWidth v≤a*Real.sin v+(-b)*Real.cos v := by
      simp only [angularWidth,centerX,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub] at hm' ⊢
      linarith
    exact False.elim (transverse_cap_impossible hcb hv hh htrans)
  · obtain ⟨v,hv,hev⟩ := hw
    exact False.elim (opposite_cap_impossible hc hv (coreRadius_pos.trans_le hh)
      (cap_margin_transport hev hm))
  · obtain ⟨v,hv,hev⟩ := hs
    have hm' := cap_margin_transport hev hm
    have hcb : ContainedChart a |-b| := by simpa only [abs_neg] using hc
    have htrans : h+angularWidth v≤-(a*Real.sin v+(-b)*Real.cos v) := by
      have hcos : Real.cos (-Real.pi/2-v) = -Real.sin v := by
        rw [show -Real.pi/2-v = -(Real.pi/2+v) by ring,Real.cos_neg,Real.cos_add,
          Real.cos_pi_div_two,Real.sin_pi_div_two]
        ring
      have hsin : Real.sin (-Real.pi/2-v) = -Real.cos v := by
        rw [show -Real.pi/2-v = -(Real.pi/2+v) by ring,Real.sin_neg,Real.sin_add,
          Real.cos_pi_div_two,Real.sin_pi_div_two]
        ring
      simp only [angularWidth,centerX,hcos,hsin,abs_neg] at hm'
      dsimp [angularWidth]
      nlinarith
    exact False.elim (negative_transverse_cap_impossible hcb hv hh htrans)

/-- A square in a cap at least `1/2` deep contains the east pin, and its phase
is within `1/4` of the cap normal. -/
theorem east_cap_fixed_pin {t a b h:ℝ} (hc:ContainedChart a |b|)
    (hb:|b|<1/2) (hh:1/2≤h) (hm:h+angularWidth t≤centerX t a b) :
    ∃ v : ℝ, |v|<1/4 ∧ (t:Direction)=(v:Direction) ∧
      openSquare (orientedSquare t a b) (polarPin (9/10) 0) := by
  have hcore : coreRadius≤h := by dsimp [coreRadius]; linarith [rho0_gt_one]
  obtain ⟨v,hv,he,hmv⟩ := positive_cap_direction hc hcore hm
  have hvpi : |v|≤Real.pi/4 := by linarith [Real.pi_gt_d2]
  have hbox : (|a|+1/2)^2+(|b|+1/2)^2≤Q0 := by
    simpa only [abs_of_nonneg (show 0≤a by linarith [hc.half_le])] using hc.containment
  have hsupport : h≤capDepth |v| := cap_support_bound_signed hvpi hbox hmv
  have hquarter := cap_angle_lt_quarter hh hsupport hvpi
  have hp := cap_piercing hvpi hcore (contained_from_corner hbox) (cap_from_margin hmv)
  have hfixed := fixed_east_of_axis_point hc hb (by linarith : |v|≤5/12)
    (show 9/10≤h+1/2 by linarith) hp
  exact ⟨v,hquarter,he,(square_phase_open he _).mpr hfixed⟩

lemma west_cap_rotated_identity (t a b cx cy:ℝ) :
    centralMargin .west t a b cx cy =
      centerX (t-Real.pi) a b-angularWidth (t-Real.pi)-(1/2-cx) := by
  simp only [centralMargin,centerX,angularWidth,Real.cos_sub_pi,Real.sin_sub_pi,abs_neg]
  ring

/-- On the left flank, `v ≤ -π/12`, a square in a deep cap contains the pin at
angle `-π/12`. -/
lemma west_cap_left_pin {v a b h:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hh:coreRadius≤h) (hv:|v|<2/5) (hleft:v≤-Real.pi/12)
    (hm:h+angularWidth v≤centerX v a b) :
    openSquare (orientedSquare v a b) (polarPin (9/10) (-Real.pi/12)) := by
  have hvs := abs_lt.mp hv
  have hcos : 0≤Real.cos (-v) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_gt_d2]⟩
  have hsin : 0≤Real.sin (-v) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d2])
  apply (by simpa only [neg_neg] using
    (western_left_pin (v:=-v) hc hb (by linarith) (by linarith)))
  intro hbneg
  have harg : v=-(-v) := by ring
  have hm' := hm
  conv at hm' => lhs; arg 2; arg 1; rw [harg]
  have hmv : h+(Real.cos (-v)+Real.sin (-v))/2≤a*Real.cos (-v)+b*Real.sin (-v) := by
    simp only [Real.cos_neg,Real.sin_neg] at hcos hsin ⊢
    have h1 : |Real.cos v|=Real.cos v := abs_of_nonneg hcos
    have h2 : |Real.sin v|=-Real.sin v := abs_of_nonpos (by linarith)
    simp only [angularWidth,centerX,h1,h2] at hm
    linarith
  have hprod := mul_nonneg (show 0≤a-1/2 by linarith [hc.half_le])
    (show 0≤1-Real.cos (-v) by linarith [Real.cos_le_one (-v)])
  have hbprod := mul_nonpos_of_nonpos_of_nonneg hbneg.le hsin
  have hcore : (77:ℝ)/200<h := coreRadius_gt_77_200.trans_le hh
  have hcprod := mul_nonneg (show 0≤(77:ℝ)/200 by norm_num)
    (show 0≤1-Real.cos (-v) by linarith [Real.cos_le_one (-v)])
  nlinarith

/-- A square in a deep cap contains the pin at angle `-π/12` or the one at
`π/4`; turned by `π`, these are the W and D pins. -/
theorem west_cap_fixed_pins {v a b h:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hh:coreRadius≤h) (hv:|v|<2/5) (hm:h+angularWidth v≤centerX v a b) :
    openSquare (orientedSquare v a b) (polarPin (9/10) (-Real.pi/12)) ∨
      openSquare (orientedSquare v a b) (polarPin (9/10) (Real.pi/4)) := by
  by_cases hl:v≤-Real.pi/12
  · exact Or.inl (west_cap_left_pin hc hb hh hv hl hm)
  · have h := sixty_pin_cover (t:=v) (q:=-Real.pi/12) hc hb
      ⟨by linarith,by linarith [(abs_lt.mp hv).2,Real.pi_gt_d2]⟩
    have hid : -Real.pi/12+Real.pi/3=Real.pi/4 := by ring
    simpa only [hid] using h

end SquaresInCircles.Six.Analytic
