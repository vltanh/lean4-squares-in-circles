module

public import SquaresInCircles.Eight.TableFree.ShortSecantGain
public import SquaresInCircles.Eight.TableFree.SoleNegativeTScalar

/-!
# Strict gains of the two genuine negative T primaries

Uncompiled source. The TD gain uses the actual sorted tangent bound .9.
Its complete interval is handled by one positive quadratic after clearing
the positive cosine. The BT gain uses its genuine .09 capture before any
later scalar enlargement to .3. Both gains have slope strictly above 1.05.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTGain
open GlobalGA

theorem tangent_bound {q : ℝ} {D : SignedPoint} (hq : q≤qCap)
    (hs : D.Sorted) (hc : D.Contained q) : |D.y|<9/10 := by
  have ha : 0≤D.a := hs.1.le
  have hb := abs_nonneg D.y
  have hprod := mul_nonneg (sub_nonneg.mpr hs.2)
    (show 0≤D.a+|D.y|+1 by linarith)
  have hcircle : (D.a+1/2)^2+(|D.y|+1/2)^2≤qCap := hc.trans hq
  norm_num [qCap] at hcircle
  nlinarith

theorem TD_strict {s : ℝ} (hs : s∈Ioc 0 (3/10:ℝ)) :
    (21/20)*s<(13/12)*Real.tan s-(2/5)*(1/Real.cos s-1) := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcpos : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hsin := Real.sin_ge_sub_cube hs.1.le
  have hcosL := cos_lower_six hs.1.le
  have hcosU := mul_le_mul_of_nonneg_left (cos_upper_four hs.1.le)
    (show 0≤(21/20)*s by positivity)
  have hs2 : s^2≤9/100 := by nlinarith [hs.1,hs.2]
  have hs3 : s^3≤27/1000 := by
    have hh := pow_le_pow_left₀ hs.1.le hs.2 3
    norm_num at hh
    exact hh
  have h5 := mul_le_mul_of_nonneg_right hs2 (pow_nonneg hs.1.le 3)
  have h6 := mul_le_mul_of_nonneg_right hs3 (pow_nonneg hs.1.le 3)
  have hpoly : 0<(1/30:ℝ)-s/5+(17/50)*s^2 := by
    have hid : (1/30:ℝ)-s/5+(17/50)*s^2=
        (17/50)*(s-5/17)^2+1/255 := by ring
    rw [hid]
    positivity
  have hprod := mul_pos hs.1 hpoly
  have hnum : 0<(13/12)*Real.sin s-(2/5)*(1-Real.cos s)-(21/20)*s*Real.cos s := by
    nlinarith [pow_nonneg hs.1.le 4,pow_nonneg hs.1.le 3]
  have hid : ((13/12)*Real.tan s-(2/5)*(1/Real.cos s-1)-(21/20)*s)*Real.cos s=
      (13/12)*Real.sin s-(2/5)*(1-Real.cos s)-(21/20)*s*Real.cos s := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcpos.ne']
    ring
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
    nlinarith [Real.one_sub_sq_div_two_le_cos s]
  have hcos2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19919/20000) hcos 2
  have ha2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤117/200) ha 2
  have hprod := mul_le_mul ha2 hcos2 (by positivity) (sq_nonneg a)
  have hrad : 1+(117/200:ℝ)^2*(19919/20000)^2≤gainRadicand a s := by
    dsimp [gainRadicand]
    linarith
  have hreserve : qCap<(214/125:ℝ)^2*(1+(117/200)^2*(19919/20000)^2) := by
    norm_num [qCap]
  have hh := mul_le_mul_of_nonneg_left hrad (sq_nonneg (214/125:ℝ))
  have hroot := Real.sqrt_pos.mpr (gainRadicand_pos a s)
  have hroot2 := Real.sq_sqrt (gainRadicand_pos a s).le
  have hq2 := Real.sq_sqrt hq
  apply (div_lt_iff₀ hroot).2
  nlinarith [Real.sqrt_nonneg q]

theorem BT_derivative {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Icc 0 (9/100:ℝ)) :
    13/12-(89/125)*s≤secantGainDeriv q a s := by
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
    (13/12)*s-(89/250)*s^2≤secantGain q a s := by
  let f : ℝ → ℝ := fun x => secantGain q a x-(13/12)*x+(89/250)*x^2
  have hd (x : ℝ) (hx : x∈Icc 0 (9/100:ℝ)) :
      HasDerivAt f (secantGainDeriv q a x-13/12+(89/125)*x) x := by
    have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
    convert ((secantGain_hasDerivAt q a hc.ne').sub
      ((hasDerivAt_id x).const_mul (13/12:ℝ))).add
        (((hasDerivAt_id x).pow 2).const_mul (89/250:ℝ)) using 1 <;> ring
  have hm : MonotoneOn f (Icc 0 (9/100:ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => hd x (Ioo_subset_Icc_self hx)
    · intro x hx
      linarith [BT_derivative hq hQ ha (Ioo_subset_Icc_self hx)]
  have hh := hm (show (0:ℝ)∈Icc 0 (9/100:ℝ) by norm_num) hs hs.1
  dsimp [f] at hh
  rw [secantGain_zero] at hh
  nlinarith

theorem BT_strict {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Ioc 0 (9/100:ℝ)) :
    (21/20)*s<secantGain q a s := by
  have hh := BT_quadratic hq hQ ha (Ioc_subset_Icc_self hs)
  have hm := mul_le_mul_of_nonneg_right hs.2 hs.1.le
  nlinarith

theorem sorted_coordinate_gain {b c s : ℝ} (hb : b≤9/10) (hc : 0<c)
    (hs : s∈Ioc 0 (3/10:ℝ)) :
    (21/20)*c*s<c*((1/Real.cos s-1)/2+(13/12)*Real.tan s)-
      c*(1/Real.cos s-1)*b := by
  have hcos : 0<Real.cos s := by
    have hh := transport_trig (show s∈Icc 0 frameCap from
      ⟨hs.1.le,by norm_num [frameCap]; linarith [hs.2]⟩)
    linarith [hh.1]
  have hsec : 0≤1/Real.cos s-1 := by
    have hh : 1≤1/Real.cos s := (le_div_iff₀ hcos).2 (by simpa using Real.cos_le_one s)
    linarith
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg hc.le hsec)
  have hg := mul_lt_mul_of_pos_left (TD_strict hs) hc
  nlinarith

end SquaresInCircles.Eight.TableFree.SoleNegativeTGain
