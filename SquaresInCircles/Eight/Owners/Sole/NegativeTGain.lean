module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.GA.Secant.Gain

/-!
# Eight squares: strict gains of the two negative T primaries

Both gains have slope strictly above `21/20`. The TD gain uses the sorted bound `0.9` on the
tangent, and its whole interval `0 < s ≤ 3/10` follows from one positive quadratic once the
positive cosine is cleared (`TD_strict`). The BT gain uses the capture at `9/100`, before any
scalar enlargement to `3/10` (`BT_quadratic`, `BT_strict`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNegativeTGain
open GlobalGA

theorem TD_strict {s : ℝ} (hs : s∈Ioc 0 (3/10:ℝ)) :
    (21/20)*s<(13/12)*Real.tan s-(2/5)*(1/Real.cos s-1) := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcpos : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hsin := Real.sin_ge_sub_cube hs.1.le
  have hcosL := cos_lower_six hs.1.le
  have hcosU := mul_le_mul_of_nonneg_left (cos_upper_four hs.1.le)
    (show 0≤(21/20)*s by linarith [hs.1])
  have hs3 := pow_nonneg hs.1.le 3
  have h4 : s^4≤(3/10)*s^3 := by
    have hh := mul_le_mul_of_nonneg_right hs.2 hs3
    linarith
  have h5 : s^5≤(9/100)*s^3 := by
    have hs2 : s^2≤9/100 := by nlinarith [hs.1,hs.2]
    have hh := mul_le_mul_of_nonneg_right hs2 hs3
    linarith
  have h6 : s^6≤(27/1000)*s^3 := by
    have hs3' : s^3≤27/1000 := by
      have hh := pow_le_pow_left₀ hs.1.le hs.2 3
      norm_num at hh
      exact hh
    have hh := mul_le_mul_of_nonneg_right hs3' hs3
    linarith
  have hpoly : 0<(1/30:ℝ)-s/5+(17/50)*s^2 := by
    have hid : (1/30:ℝ)-s/5+(17/50)*s^2=
        (17/50)*(s-5/17)^2+1/255 := by ring
    rw [hid]
    positivity
  have hprod := mul_pos hs.1 hpoly
  have hs4 := pow_nonneg hs.1.le 4
  have hnum : 0<(13/12)*Real.sin s-(2/5)*(1-Real.cos s)-(21/20)*s*Real.cos s := by
    linarith
  have hid : ((13/12)*Real.tan s-(2/5)*(1/Real.cos s-1)-(21/20)*s)*Real.cos s=
      (13/12)*Real.sin s-(2/5)*(1-Real.cos s)-(21/20)*s*Real.cos s := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hh : 0<((13/12)*Real.tan s-(2/5)*(1/Real.cos s-1)-(21/20)*s)*Real.cos s := by
    rw [hid]
    exact hnum
  have hg := (mul_pos_iff_of_pos_right hcpos).1 hh
  linarith

theorem BT_radius_ratio {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Icc 0 (9/100:ℝ)) :
    Real.sqrt q/Real.sqrt (gainRadicand a s)<214/125 := by
  have hs2 : s^2≤81/10000 := by nlinarith [hs.1,hs.2]
  have hcos : (19919/20000:ℝ)≤Real.cos s := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have hcos2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19919/20000) hcos 2
  have ha2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤117/200) ha 2
  have hprod := mul_le_mul ha2 hcos2 (by positivity) (sq_nonneg a)
  have hrad : 1+(117/200:ℝ)^2*(19919/20000)^2≤gainRadicand a s := by
    dsimp [gainRadicand]
    linarith
  have hQ' : q≤9789/2500 := hQ
  have hreserve : (9789/2500:ℝ)<(214/125:ℝ)^2*(1+(117/200)^2*(19919/20000)^2) := by
    norm_num
  have hh := mul_le_mul_of_nonneg_left hrad (sq_nonneg (214/125:ℝ))
  have hroot := Real.sqrt_pos.mpr (gainRadicand_pos a s)
  apply (div_lt_iff₀ hroot).2
  have h1 : Real.sqrt q<Real.sqrt ((214/125)^2*gainRadicand a s) :=
    Real.sqrt_lt_sqrt hq (by linarith)
  rw [Real.sqrt_mul (by positivity),Real.sqrt_sq (by norm_num)] at h1
  exact h1

theorem BT_derivative {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Icc 0 (9/100:ℝ)) :
    13/12-(89/125)*s≤ secantGainDeriv q a s := by
  have hr := BT_radius_ratio hq hQ ha hs
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  obtain ⟨hc,hcu,hs0,hsu,hsc⟩ := transport_trig hs'
  have hst := Real.sin_le hs.1
  have hm := mul_le_mul_of_nonneg_right hr.le hs0
  have hlo : 0≤(13/12:ℝ)-(89/125)*s := by linarith [hs.2]
  have hc2 : (Real.cos s)^2≤1 := by nlinarith
  have hcpos : 0<Real.cos s := by linarith
  have hp := mul_nonneg hlo (sub_nonneg.mpr hc2)
  dsimp [secantGainDeriv]
  apply (le_div_iff₀ (sq_pos_of_pos hcpos)).2
  have he : Real.sqrt q*Real.sin s/Real.sqrt (gainRadicand a s)=
      (Real.sqrt q/Real.sqrt (gainRadicand a s))*Real.sin s := by ring
  rw [he]
  nlinarith

theorem BT_quadratic {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Icc 0 (9/100:ℝ)) :
    (13/12)*s-(89/250)*s^2≤ secantGain q a s := by
  have hd (x : ℝ) (hx : x∈Icc 0 (9/100:ℝ)) :
      HasDerivAt (fun x => secantGain q a x-(13/12)*x+(89/250)*x^2)
        (secantGainDeriv q a x-13/12+(89/125)*x) x := by
    have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
    have h := ((secantGain_hasDerivAt q a hc.ne').fun_sub
      ((hasDerivAt_id' x).const_mul (13/12:ℝ))).fun_add
        (((hasDerivAt_id' x).fun_pow 2).const_mul (89/250:ℝ))
    convert h using 1
    push_cast
    ring
  have hm : MonotoneOn (fun x => secantGain q a x-(13/12)*x+(89/250)*x^2)
      (Icc 0 (9/100:ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => hd x (Ioo_subset_Icc_self hx)
    · intro x hx
      linarith [BT_derivative hq hQ ha (Ioo_subset_Icc_self hx)]
  have hh := hm (show (0:ℝ)∈Icc 0 (9/100:ℝ) by norm_num) hs hs.1
  simp only [secantGain_zero] at hh
  linarith

theorem BT_strict {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Ioc 0 (9/100:ℝ)) :
    (21/20)*s<secantGain q a s := by
  have hh := BT_quadratic hq hQ ha (Ioc_subset_Icc_self hs)
  have hm := mul_le_mul_of_nonneg_right hs.2 hs.1.le
  nlinarith [hs.1]

end SquaresInCircles.Eight.SoleNegativeTGain
