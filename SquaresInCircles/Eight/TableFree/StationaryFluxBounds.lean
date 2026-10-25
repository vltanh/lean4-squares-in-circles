module

public import SquaresInCircles.Eight.TableFree.StationaryWeightRatios

/-!
# The secant flux reserve on the actual affine position strip

Uncompiled reconstruction.  The two first circle equations express
`r-U` exactly through `1-u`.  The proved affine position bounds then
control the flux ratio by a single cubic inequality on the complete
tangent interval.  This supplies the second strict error reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryTerminal
open ExactFamily.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

theorem circle_ratio_formula {q u : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50)) :
    lowerRight q u/topRight q u=
      1+4*(1-u)/((lowerRight q u+topRight q u)*topRight q u) := by
  have hr := radical_bounds hq hu
  have hd := hr.smoothDomain (by linarith [hq.2]) (by linarith [hu.1])
  have hR : 0<lowerRight q u := by linarith [hr.r_lower]
  have hU : 0<topRight q u := by linarith [hr.U_lower]
  have hsum : 0<lowerRight q u+topRight q u := add_pos hR hU
  have hcR := upper_circle hd.first_radicand
  have hcU := upper_circle hd.second_radicand
  change lowerRight q u^2+u^2=q at hcR
  change topRight q u^2+(2-u)^2=q at hcU
  have hdiff : (lowerRight q u-topRight q u)*(lowerRight q u+topRight q u)=4*(1-u) := by
    nlinarith
  have he : 4*(1-u)/(lowerRight q u+topRight q u)=lowerRight q u-topRight q u :=
    (div_eq_iff hsum.ne').2 hdiff.symm
  calc
    _ = 1+(lowerRight q u-topRight q u)/topRight q u := by field_simp [hU.ne']; ring
    _ = _ := by rw [← he]; simp only [div_eq_mul_inv,mul_inv_rev]; ring

theorem affine_ratio_upper {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (ha : 1-(7/10)*h<u ∧ u<1-(3/5)*h) :
    lowerRight q u/topRight q u<1+(101/200)*h ∧
      u+h*lowerRight q u<1+(233/200)*h := by
  have hr := radical_bounds hq hu
  have hp : 0<h := by linarith [hh.1]
  have hsum : lowerRight q u+topRight q u∈Icc (1691/500:ℝ) (859/250) :=
    ⟨by linarith [hr.r_lower,hr.U_lower],by linarith [hr.r_upper,hr.U_upper]⟩
  have hden := product_bounds hsum hr.U (by norm_num) (by norm_num)
  have hdenp : 0<(lowerRight q u+topRight q u)*topRight q u := by linarith [hden.1]
  have hscaled := mul_le_mul_of_nonneg_left hden.1 (by positivity : 0≤(101/200:ℝ)*h)
  have hquot : 4*(1-u)/((lowerRight q u+topRight q u)*topRight q u)<(101/200)*h := by
    apply (div_lt_iff₀ hdenp).2
    nlinarith [ha.1]
  have hR := mul_lt_mul_of_pos_left hr.r_upper hp
  refine ⟨?_,by linarith [ha.2]⟩
  rw [circle_ratio_formula hq hu]
  linarith

theorem flux_ratio_formula {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    flux (weights q u h) (Real.arctan h)/(weights q u h).beta=
      (2-u)*(lowerRight q u/topRight q u)*(1-h/(u+h*lowerRight q u)) := by
  have hr := radical_bounds hq hu
  have hR : lowerRight q u≠0 := ne_of_gt (by linarith [hr.r_lower])
  have hU : topRight q u≠0 := ne_of_gt (by linarith [hr.U_lower])
  have hL : 2-u≠0 := ne_of_gt (by linarith [hu.2])
  have hC : cosine h≠0 := (cosine_pos h).ne'
  have hO : omega q u h≠0 := ne_of_gt (by linarith [(omega_bounds hq hu hh).1])
  have hN : u+h*lowerRight q u≠0 := ne_of_gt (by
    have hu0 : 0<u := by linarith [hu.1]
    have hh0 : 0<h := by linarith [hh.1]
    have hr0 : 0<lowerRight q u := by linarith [hr.r_lower]
    positivity)
  rw [flux_formula hq hu hh]
  change (omega q u h*(cosine h*u+sine h*(lowerRight q u-1)))/
    (omega q u h*(rawAlpha q u h*topRight q u/(2-u)))=_
  rw [rawAlpha_identity q u h hR,sine_eq]
  field_simp [hR,hU,hL,hC,hO,hN]
  ring

/-- The upper flux ratio is the exact cubic comparison from the hand
proof, on the entire tangent interval. -/
theorem flux_ratio_upper {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (ha : 1-(7/10)*h<u ∧ u<1-(3/5)*h) :
    flux (weights q u h) (Real.arctan h)/(weights q u h).beta<21/20 := by
  have hr := radical_bounds hq hu
  have hp : 0<h := by linarith [hh.1]
  have hu0 : 0<u := by linarith [hu.1]
  have hr0 : 0<lowerRight q u := by linarith [hr.r_lower]
  have hU0 : 0<topRight q u := by linarith [hr.U_lower]
  obtain ⟨hru,hNu⟩ := affine_ratio_upper hq hu hh ha
  have hL : 2-u<1+(7/10)*h := by linarith [ha.1]
  have hN : 0<u+h*lowerRight q u := by positivity
  have hNm : 0<u+h*lowerRight q u-h := by
    have hpR := mul_pos hp (by linarith [hr.r_lower] : 0<lowerRight q u-1)
    nlinarith
  have hD : 0<1+(233/200)*h := by positivity
  have hF : 1-h/(u+h*lowerRight q u)=
      (u+h*lowerRight q u-h)/(u+h*lowerRight q u) := by field_simp [hN.ne']
  have hz0 : 0<1-h/(u+h*lowerRight q u) := by rw [hF]; exact div_pos hNm hN
  have hzU : 1-h/(u+h*lowerRight q u)<(1+(33/200)*h)/(1+(233/200)*h) := by
    rw [hF]
    apply (div_lt_div_iff₀ hN hD).2
    have hs := mul_pos hp (sub_pos.mpr hNu)
    nlinarith
  have hratio0 : 0<lowerRight q u/topRight q u := div_pos hr0 hU0
  have hprod : (2-u)*(lowerRight q u/topRight q u)<
      (1+(7/10)*h)*(1+(101/200)*h) := by
    calc
      _ < (1+(7/10)*h)*(lowerRight q u/topRight q u) := mul_lt_mul_of_pos_right hL hratio0
      _ < _ := mul_lt_mul_of_pos_left hru (by positivity)
  have hprod2 : (2-u)*(lowerRight q u/topRight q u)*(1-h/(u+h*lowerRight q u))<
      (1+(7/10)*h)*(1+(101/200)*h)*((1+(33/200)*h)/(1+(233/200)*h)) := by
    calc
      _ < (1+(7/10)*h)*(1+(101/200)*h)*(1-h/(u+h*lowerRight q u)) :=
        mul_lt_mul_of_pos_right hprod hz0
      _ < _ := mul_lt_mul_of_pos_left hzU (by positivity)
  have hh2 := pow_le_pow_left₀ hp.le hh.2 2
  have hh3 := pow_le_pow_left₀ hp.le hh.2 3
  have hpoly : 0<(1/20:ℝ)-(587/4000)*h-(22093/40000)*h^2-(23331/400000)*h^3 := by
    nlinarith [hh.2]
  have hid : (21/20:ℝ)*(1+(233/200)*h)-
      (1+(7/10)*h)*(1+(101/200)*h)*(1+(33/200)*h)=
      (1/20:ℝ)-(587/4000)*h-(22093/40000)*h^2-(23331/400000)*h^3 := by ring
  have hupper : (1+(7/10)*h)*(1+(101/200)*h)*((1+(33/200)*h)/(1+(233/200)*h))<21/20 := by
    rw [show (1+(7/10)*h)*(1+(101/200)*h)*((1+(33/200)*h)/(1+(233/200)*h))=
      ((1+(7/10)*h)*(1+(101/200)*h)*(1+(33/200)*h))/(1+(233/200)*h) by ring]
    apply (div_lt_iff₀ hD).2
    linarith
  rw [flux_ratio_formula hq hu hh]
  exact hprod2.trans hupper

theorem secant_reserve {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (ha : 1-(7/10)*h<u ∧ u<1-(3/5)*h)
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    23/1000<(weights q u h).beta*(13/12)-flux (weights q u h) (Real.arctan h) := by
  have hb := (beta_bounds hq hu hh hz).1
  have hc := (div_lt_iff₀ (beta_pos hq hu hh)).mp (flux_ratio_upper hq hu hh ha)
  linarith

end SquaresInCircles.Eight.TableFree.StationaryTerminal
