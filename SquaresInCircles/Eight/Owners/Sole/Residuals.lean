module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Positive.AngularEnvelope

/-!
# Eight squares: original-anchor residuals for the fixed-total sole-primary split

These bounds use only the original sorted coordinates
and their common containing circle. The axis tangent and the diagonal
support are proved directly; no contact configuration is substituted for
an original anchor. The estimates hold on the entire signed angle range.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleResiduals
open Candidate SignedStress PositiveAngularEnvelope

theorem contained_bounds {p : SignedPoint} (hs : p.Sorted)
    (hc : p.Contained qCap) :
    p.a<283/200 ∧ |p.y|<9/10 ∧ p.a+|p.y|<8993/5000 := by
  have hb := abs_nonneg p.y
  have ha := hs.1
  have hh : (p.a+1/2)^2+(|p.y|+1/2)^2≤9789/2500 := hc
  have hsort := hs.2
  refine ⟨?_,?_,?_⟩
  · nlinarith [sq_nonneg |p.y|]
  · nlinarith [sq_nonneg (p.a-|p.y|)]
  · nlinarith [sq_nonneg (p.a-|p.y|)]

theorem phi_bounds {x : ℝ} (hx : x∈Icc 0 frameCap) :
    1≤Real.cos x+Real.sin x ∧ Real.cos x+Real.sin x<99/70 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx
  have hid := Real.sin_sq_add_cos_sq x
  constructor
  · nlinarith [mul_nonneg (show 0≤Real.cos x by linarith) hs0]
  · nlinarith [sq_nonneg (Real.cos x-Real.sin x)]

theorem width_ge_one {x : ℝ} (hx : |x|≤frameCap) : 1≤edgeWidth x := by
  have hh : |x|∈Icc 0 frameCap := ⟨abs_nonneg _,hx⟩
  have hp := (phi_bounds hh).1
  have he : edgeWidth x=edgeWidth |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx,edgeWidth_neg]
  rw [he,edgeWidth_positive_formula hh]
  linarith

theorem diagonal_projection {p : SignedPoint} {x : ℝ}
    (hs : p.Sorted) (hc : p.Contained qCap) (hx : x∈Icc 0 frameCap) :
    p.a*Real.sin x+|p.y| *Real.cos x≤
      (8993/10000)*(Real.sin x+Real.cos x) := by
  have hb := contained_bounds hs hc
  obtain ⟨hcos,hcos1,hs0,hs1,hsc⟩ := transport_trig hx
  have hsort := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hsc.le)
  have hsum := mul_le_mul_of_nonneg_right hb.2.2.le
    (show 0≤Real.sin x+Real.cos x by linarith)
  nlinarith

theorem transverse_residual {p : SignedPoint} {x : ℝ}
    (hs : p.Sorted) (hc : p.Contained qCap) (hx : |x|≤frameCap) :
    -(13/200 : ℝ)<edgeWidth x-p.a*Real.sin x-|p.y| *Real.cos x := by
  by_cases hx0 : 0≤x
  · have hx' : x∈Icc 0 frameCap := ⟨hx0,by simpa [abs_of_nonneg hx0] using hx⟩
    have hp := diagonal_projection hs hc hx'
    have hphi := (phi_bounds hx').2
    rw [edgeWidth_positive_formula hx']
    nlinarith
  · have hx0' : x≤0 := (lt_of_not_ge hx0).le
    have hx' : -x∈Icc 0 frameCap := ⟨by linarith,by simpa [abs_of_nonpos hx0'] using hx⟩
    have hsn : Real.sin x≤0 := by
      have hh := (transport_trig hx').2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    have ha := mul_nonpos_of_nonneg_of_nonpos hs.1.le hsn
    have hb := mul_le_mul_of_nonneg_left (Real.cos_le_one x) (abs_nonneg p.y)
    have hwidth := width_ge_one hx
    have hcoord := (contained_bounds hs hc).2.1
    nlinarith

theorem axis_tangent {p : SignedPoint} (_hs : p.Sorted)
    (hc : p.Contained qCap) :
    2*Real.sqrt (qCap-1/4)*(p.a-axisCoordinate qCap)+|p.y|≤0 := by
  have hr : (Real.sqrt (qCap-1/4))^2=qCap-1/4 :=
    Real.sq_sqrt (by norm_num [qCap])
  have hh : (p.a+1/2)^2+(|p.y|+1/2)^2≤qCap := hc
  dsimp [axisCoordinate]
  nlinarith [sq_nonneg (p.a+1/2-Real.sqrt (qCap-1/4)),sq_nonneg |p.y|]

theorem short_axis_projection {p : SignedPoint} {x : ℝ}
    (hs : p.Sorted) (hc : p.Contained qCap) (hx : x∈Icc 0 (1/4 : ℝ)) :
    p.a*Real.cos x+|p.y| *Real.sin x≤axisCoordinate qCap*Real.cos x := by
  let S := Real.sqrt (qCap-1/4)
  have hS0 : 0<S := Real.sqrt_pos.2 (by norm_num [qCap])
  have hS2 : S^2=qCap-1/4 := Real.sq_sqrt (by norm_num [qCap])
  have hSu : S<383/200 := by dsimp [qCap] at hS2; nlinarith
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2]⟩
  obtain ⟨hcos,hcos1,hs0,hs1,hsc⟩ := transport_trig hx'
  have hsx : Real.sin x≤1/4 := (Real.sin_le hx.1).trans hx.2
  have hsq : x^2≤1/16 := by nlinarith [hx.1,hx.2]
  have hcos' : 31/32≤Real.cos x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hcone : 2*S*Real.sin x≤Real.cos x := by
    nlinarith [mul_le_mul_of_nonneg_left hsx hS0.le]
  have ht := axis_tangent hs hc
  have ht' := mul_nonpos_of_nonpos_of_nonneg ht
    (show 0≤Real.cos x by linarith)
  have hb := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hcone) (abs_nonneg p.y)
  change 2*S*(p.a-axisCoordinate qCap)+|p.y|≤0 at ht
  nlinarith

theorem radial_residual {p : SignedPoint} {x : ℝ}
    (hs : p.Sorted) (hc : p.Contained qCap) (hx : |x|≤frameCap) :
    -(83/200 : ℝ)<edgeWidth x-p.a*Real.cos x-|p.y| *Real.sin x := by
  have hb := contained_bounds hs hc
  by_cases hx0 : 0≤x
  · have hx' : x∈Icc 0 frameCap := ⟨hx0,by simpa [abs_of_nonneg hx0] using hx⟩
    obtain ⟨hcos,hcos1,hs0,hs1,hsc⟩ := transport_trig hx'
    by_cases hsmall : x≤1/4
    · have hp := short_axis_projection hs hc ⟨hx0,hsmall⟩
      have hS : axisCoordinate qCap<283/200 := by
        have h : Real.sqrt (qCap-1/4)<383/200 := by
          rw [Real.sqrt_lt' (by norm_num)]
          norm_num [qCap]
        simp only [axisCoordinate]
        linarith
      have ha : 1/2≤axisCoordinate qCap := by
        have h : 1≤Real.sqrt (qCap-1/4) := by
          rw [Real.le_sqrt (by norm_num) (by norm_num [qCap])]
          norm_num [qCap]
        simp only [axisCoordinate]
        linarith
      have hm := mul_le_mul_of_nonneg_left hcos1 (sub_nonneg.mpr ha)
      rw [edgeWidth_positive_formula hx']
      linarith
    · have hlow : 1/4≤x := (lt_of_not_ge hsmall).le
      have hx7 : x≤7/10 := hx'.2
      have hsq : x^2≤(7/10)*x := by
        have h := mul_nonneg hx0 (sub_nonneg.mpr hx7)
        linarith [show x^2=x*x by ring]
      have hcube : x^3≤(49/100)*x := by
        have hmul := mul_le_mul_of_nonneg_left hsq hx0
        have h3 : x^3=x*x^2 := by ring
        linarith [show x*((7/10)*x)=(7/10)*x^2 by ring]
      have hphi : 1+341/600*x≤Real.cos x+Real.sin x := by
        linarith [Real.one_sub_sq_div_two_le_cos (x := x),Real.sin_ge_sub_cube hx0]
      have hR0 := Real.sqrt_nonneg qCap
      have hR2 := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
      have hRu : Real.sqrt qCap<1979/1000 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num [qCap]
      have hnorm : Real.sqrt (Real.cos x^2+Real.sin x^2)=1 := by
        rw [add_comm,Real.sin_sq_add_cos_sq]
        norm_num
      have hcq : normSq (p.a+1/2,|p.y|+1/2)≤(Real.sqrt qCap)^2 := by
        rw [hR2]
        exact hc
      have hp := dot_le_radius (v := (Real.cos x,Real.sin x))
        (p := (p.a+1/2,|p.y|+1/2)) hR0 hcq
      simp only [dot,vectorLength,normSq,hnorm,mul_one] at hp
      rw [edgeWidth_positive_formula hx']
      linarith
  · have hx0' : x≤0 := (lt_of_not_ge hx0).le
    have hx' : -x∈Icc 0 frameCap := ⟨by linarith,by simpa [abs_of_nonpos hx0'] using hx⟩
    have hsn : Real.sin x≤0 := by
      have hh := (transport_trig hx').2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    have ha := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hs.1.le
    have hminor := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg p.y) hsn
    have hw := width_ge_one hx
    linarith [hb.1]

def sigma (R v : ℝ) : ℝ := R*Real.sqrt (1+v^2)-(1+v)/2

theorem tilt_reserve {R v : ℝ} (_hR : 0≤R) (hR2 : R^2≤qCap)
    (hv : v∈Icc (1/4 : ℝ) (7/20)) : sigma R v-1/2<187/200 := by
  have hv2 := mul_nonneg (sub_nonneg.mpr hv.1) (sub_nonneg.mpr hv.2)
  have hs0 := Real.sqrt_nonneg (1+v^2)
  have hs2 := Real.sq_sqrt (show 0≤1+v^2 by positivity)
  have hb := mul_le_mul_of_nonneg_right hR2 (show 0≤1+v^2 by positivity)
  have hmajor : R*Real.sqrt (1+v^2)<387/200+v/2 := by
    have hsq : (R*Real.sqrt (1+v^2))^2≤qCap*(1+v^2) := by
      rw [mul_pow,hs2]
      exact hb
    dsimp [qCap] at hsq
    by_contra hcon
    have hc0 : (0:ℝ)≤387/200+v/2 := by linarith [hv.1]
    have hsq' := pow_le_pow_left₀ hc0 (not_lt.mp hcon) 2
    nlinarith [hv2]
  dsimp [sigma]
  linarith

end SquaresInCircles.Eight.SoleResiduals
