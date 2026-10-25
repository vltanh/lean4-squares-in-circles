module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2InversePower
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves

/-!
# Eight squares: the secant-curvature bounds on the two high-angle cuts

The alternating inverse-power estimates (`baseSecond_inversePower`) are used with fixed ratios.
The late AB estimate keeps its positive-square test on the derivative and a single endpoint
evaluation (`AB_late_base_endpoint`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SecantBounds
open Candidate Secondary SecantCoordinate

theorem tan_GA_cut : Real.tan (1/4:ℝ)<32/125 := by
  have hb := trig_bracket (l:=(1/4:ℝ)) (u:=(1/4:ℝ)) (x:=(1/4:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  have hc : 0<Real.cos (1/4:ℝ) := by norm_num at hb; linarith [hb.2.2.1]
  rw [Real.tan_eq_sin_div_cos,div_lt_iff₀ hc]
  norm_num at hb
  linarith [hb.2.1,hb.2.2.1]

theorem tan_AB_cut : Real.tan (19/50:ℝ)<2/5 := by
  have hb := trig_bracket (l:=(19/50:ℝ)) (u:=(19/50:ℝ)) (x:=(19/50:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  have hc : 0<Real.cos (19/50:ℝ) := by norm_num at hb; linarith [hb.2.2.1]
  rw [Real.tan_eq_sin_div_cos,div_lt_iff₀ hc]
  norm_num at hb
  linarith [hb.2.1,hb.2.2.1]

theorem tan_third : Real.tan (1/3:ℝ)<7/20 := by
  have hb := trig_bracket (l:=(1/3:ℝ)) (u:=(1/3:ℝ)) (x:=(1/3:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  have hc : 0<Real.cos (1/3:ℝ) := by norm_num at hb; linarith [hb.2.2.1]
  rw [Real.tan_eq_sin_div_cos,div_lt_iff₀ hc]
  norm_num at hb
  linarith [hb.2.1,hb.2.2.1]

theorem normalized_radius_bounds {A L U : ℝ} (hA : 0<A)
    (hL : 0≤L) (hU : 0<U)
    (hl : L^2*A<qCap) (hu : qCap<U^2*A) :
    L<R/Real.sqrt A ∧ R/Real.sqrt A<U := by
  have hs := Real.sqrt_pos.mpr hA
  have hs2 := Real.sq_sqrt hA.le
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  constructor
  · apply (lt_div_iff₀ hs).2
    have hp : 0≤L*Real.sqrt A := mul_nonneg hL hs.le
    nlinarith [mul_pow L (Real.sqrt A) 2]
  · apply (div_lt_iff₀ hs).2
    have hp : 0<U*Real.sqrt A := mul_pos hU hs
    nlinarith [mul_pow U (Real.sqrt A) 2]

theorem radical_scale {A x : ℝ} (hA : 0<A) :
    radical A x=Real.sqrt A*InversePower.root (x^2/A) := by
  have hy : 0≤x^2/A := div_nonneg (sq_nonneg x) hA.le
  have hN := radical_positive (x:=x) hA
  have hN2 := radical_square (x:=x) hA
  have hS := Real.sqrt_pos.mpr hA
  have hS2 := Real.sq_sqrt hA.le
  have hW := InversePower.root_positive hy
  have hW2 := InversePower.root_square hy
  have hsq : (Real.sqrt A*InversePower.root (x^2/A))^2=A+x^2 := by
    rw [mul_pow,hS2,hW2]
    field_simp [hA.ne']
  nlinarith [mul_pos hS hW]

theorem baseSecond_inversePower (r x : ℝ) :
    baseSecond r x=InversePower.odd 0 (x^2)-
      (R/Real.sqrt (1+r^2))*InversePower.odd 0 (x^2/(1+r^2)) := by
  have hA : 0<1+r^2 := by positivity
  have hS := Real.sqrt_pos.mpr hA
  have hS2 := Real.sq_sqrt hA.le
  have hW := InversePower.root_positive
    (div_nonneg (sq_nonneg x) hA.le)
  have hsecond : R*(1+r^2)/
      (Real.sqrt (1+r^2)*InversePower.root (x^2/(1+r^2)))^3=
      (R/Real.sqrt (1+r^2))*(1/(InversePower.root (x^2/(1+r^2)))^3) := by
    calc
      R*(1+r^2)/(Real.sqrt (1+r^2)*InversePower.root (x^2/(1+r^2)))^3=
          R*(Real.sqrt (1+r^2))^2/
            ((Real.sqrt (1+r^2))^3*(InversePower.root (x^2/(1+r^2)))^3) := by
        rw [mul_pow,hS2]
      _=(R/Real.sqrt (1+r^2))*(1/(InversePower.root (x^2/(1+r^2)))^3) := by
        field_simp [hS.ne',hW.ne']
  dsimp [baseSecond]
  rw [radical_scale hA,hsecond]
  rfl

/-- The bound `baseSecond r x < -.507` for `r ≤ 17/20`, after a harmless enlargement of the
ratio. -/
theorem GA_base_curvature {r x : ℝ}
    (hr : r∈Icc 0 (17/20:ℝ)) (hx : x∈Icc 0 (32/125:ℝ)) :
    baseSecond r x< -(507/1000:ℝ) := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hm := baseSecond_ratio_mono hr.1 hr.2 (by nlinarith : 2*x^2≤1)
  have hD := normalized_radius_bounds (A:=1+(17/20:ℝ)^2)
    (L:=1507/1000) (U:=377/250) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCap]) (by norm_num [qCap])
  let D : ℝ := R/Real.sqrt (1+(17/20:ℝ)^2)
  have hD0 : 0≤D := by dsimp [D]; positivity
  have hu := InversePower.second_upper (sq_nonneg x)
  have hl := mul_le_mul_of_nonneg_left
    (InversePower.first_lower (div_nonneg (sq_nonneg x) (by norm_num : (0:ℝ)≤1+(17/20:ℝ)^2))) hD0
  have hdy := mul_le_mul_of_nonneg_right hD.2.le (sq_nonneg x)
  have hy := mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)
  have he := baseSecond_inversePower (17/20) x
  have hc : -(3/2:ℝ)+(3/2)*(377/250)/(1+(17/20:ℝ)^2)+
      (15/8)*(32/125:ℝ)^2<0 := by norm_num
  have hcy := mul_nonpos_of_nonpos_of_nonneg hc.le (sq_nonneg x)
  dsimp [D] at hl hD0
  norm_num at hD hl hdy he hc hcy hy
  nlinarith

def ABsquare : ℝ := 1+(129/125:ℝ)^2
def a2 : ℝ := -3/2+(3/2)*(689/500)/ABsquare
def a4 : ℝ := 15/8-(15/8)*(1377/1000)/ABsquare^2
def a6 : ℝ := -35/16+(35/16)*(689/500)/ABsquare^3
def a8 : ℝ := 315/128
def coefficientCubic (y : ℝ) : ℝ := a2+a4*y+a6*y^2+a8*y^3

theorem coefficientCubic_hasDerivAt (y : ℝ) :
    HasDerivAt coefficientCubic (a4+2*a6*y+3*a8*y^2) y := by
  have h1 : HasDerivAt (fun y:ℝ => a4*y) a4 y := by
    simpa using (hasDerivAt_id y).const_mul a4
  have h2 : HasDerivAt (fun y:ℝ => a6*y^2) (a6*(2*y)) y := by
    simpa using ((hasDerivAt_id y).fun_pow 2).const_mul a6
  have h3 : HasDerivAt (fun y:ℝ => a8*y^3) (a8*(3*y^2)) y := by
    simpa using ((hasDerivAt_id y).fun_pow 3).const_mul a8
  exact (((h1.const_add a2).fun_add h2).fun_add h3).congr_deriv (by ring)

theorem coefficientCubic_upper {y : ℝ} (hy : y∈Icc 0 (49/400:ℝ)) :
    coefficientCubic y< -(1833/5000:ℝ) := by
  have hm : MonotoneOn coefficientCubic (Icc (0:ℝ) (49/400)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun y _ => (coefficientCubic_hasDerivAt y).continuousAt.continuousWithinAt)
      (fun y _ => coefficientCubic_hasDerivAt y)
    intro y hy
    have hsign : a6<0 ∧ 0<a8 ∧ 0<a4+2*a6*(49/400:ℝ) := by
      norm_num [a4,a6,a8,ABsquare]
    have hh := mul_le_mul_of_nonpos_left hy.2.le (show 2*a6≤0 by linarith [hsign.1])
    have hp := mul_nonneg (show 0≤3*a8 by linarith [hsign.2.1]) (sq_nonneg y)
    linarith [hsign.2.2]
  have hh := hm hy (show (49/400:ℝ)∈Icc 0 (49/400) by norm_num) hy.2
  have he : coefficientCubic (49/400:ℝ)< -(1833/5000:ℝ) := by
    norm_num [coefficientCubic,a2,a4,a6,a8,ABsquare]
  exact hh.trans_lt he

/-- The comparison of the degree-four and degree-three binomials gives
`baseSecond r x < -47/125 - (7/20) x^2`. -/
theorem AB_early_base_curvature {r x : ℝ}
    (hr : r∈Icc 0 (129/125:ℝ)) (hx : x∈Icc 0 (7/20:ℝ)) :
    baseSecond r x< -(47/125:ℝ)-(7/20)*x^2 := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hm := baseSecond_ratio_mono hr.1 hr.2 (by nlinarith : 2*x^2≤1)
  have hD := normalized_radius_bounds (A:=ABsquare) (L:=1377/1000) (U:=689/500)
    (by norm_num [ABsquare]) (by norm_num) (by norm_num)
    (by norm_num [ABsquare,qCap]) (by norm_num [ABsquare,qCap])
  let D : ℝ := R/Real.sqrt ABsquare
  have hD0 : 0≤D := by dsimp [D]; positivity
  have hA : 0<ABsquare := by norm_num [ABsquare]
  have hu := InversePower.fourth_upper (sq_nonneg x)
  have hl := mul_le_mul_of_nonneg_left
    (InversePower.third_lower (div_nonneg (sq_nonneg x) hA.le)) hD0
  have h2 := mul_le_mul_of_nonneg_right hD.2.le (sq_nonneg x)
  have h4 := mul_le_mul_of_nonneg_right hD.1.le (pow_nonneg hx.1 4)
  have h6 := mul_le_mul_of_nonneg_right hD.2.le (pow_nonneg hx.1 6)
  have he := baseSecond_inversePower (129/125) x
  have hpoly : baseSecond (129/125) x< -(377/1000:ℝ)+x^2*coefficientCubic (x^2) := by
    dsimp [D] at hl hD0
    dsimp [coefficientCubic,a2,a4,a6,a8,ABsquare] at ⊢ hD hl h2 h4 h6
    norm_num at hD hl h2 h4 h6 he
    nlinarith
  have hc := coefficientCubic_upper ⟨sq_nonneg x,by nlinarith only [hx2]⟩
  have hc' := mul_le_mul_of_nonneg_left
    (show coefficientCubic (x^2)≤-(7/20:ℝ) by linarith) (sq_nonneg x)
  linarith

/-- The positive-square test at the endpoint `u` gives `baseThird r x ≤ 0` on `[0, u]`. -/
theorem baseThird_nonpos_of_endpoint {r u x : ℝ} (_hu : 0≤u)
    (hx : x∈Icc 0 u)
    (htest : qCap*(1+r^2)^2*(1+u^2)^5<(1+r^2+u^2)^5) :
    baseThird r x≤0 := by
  obtain ⟨A,hAd⟩ : ∃ A:ℝ,A=1+r^2 := ⟨_,rfl⟩
  rw [←hAd] at htest
  have hA : 0<A := by rw [hAd]; positivity
  have hA1 : 1≤A := by rw [hAd]; nlinarith [sq_nonneg r]
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hcross : (A+u^2)*(1+x^2)≤(A+x^2)*(1+u^2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hx2)]
  have hcross5 := pow_le_pow_left₀ (by positivity : 0≤(A+u^2)*(1+x^2)) hcross 5
  simp only [mul_pow] at hcross5
  have hp := mul_lt_mul_of_pos_right htest (show 0<(1+x^2)^5 by positivity)
  have hpoly : qCap*A^2*(1+x^2)^5<(A+x^2)^5 := by
    have hU : 0<(1+u^2)^5 := by positivity
    refine lt_of_mul_lt_mul_right ?_ hU.le
    calc qCap*A^2*(1+x^2)^5*(1+u^2)^5=qCap*A^2*(1+u^2)^5*(1+x^2)^5 := mul_right_comm _ _ _
      _<(A+u^2)^5*(1+x^2)^5 := hp
      _≤(A+x^2)^5*(1+u^2)^5 := hcross5
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hN := radical_positive (x:=x) hA
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hN2 := radical_square (x:=x) hA
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hW10 : ((radical 1 x)^5)^2=(1+x^2)^5 := by
    rw [← pow_mul,show 5*2=2*5 by norm_num,pow_mul,hW2]
  have hN10 : ((radical A x)^5)^2=(A+x^2)^5 := by
    rw [← pow_mul,show 5*2=2*5 by norm_num,pow_mul,hN2]
  have hsquare : (R*A*(radical 1 x)^5)^2<((radical A x)^5)^2 := by
    calc
      (R*A*(radical 1 x)^5)^2=qCap*A^2*(1+x^2)^5 := by
        rw [mul_pow,mul_pow,hR2,hW10]
      _<(A+x^2)^5 := hpoly
      _=((radical A x)^5)^2 := hN10.symm
  have hroot : R*A*(radical 1 x)^5<(radical A x)^5 :=
    lt_of_pow_lt_pow_left₀ 2 (pow_nonneg hN.le 5) hsquare
  have hquot : R*A/(radical A x)^5≤1/(radical 1 x)^5 := by
    apply (div_le_div_iff₀ (pow_pos hN 5) (pow_pos hW 5)).2
    simpa only [one_mul] using hroot.le
  dsimp only [baseThird]
  rw [←hAd]
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.1]) (sub_nonpos.mpr hquot)

theorem AB_late_base_antitone :
    AntitoneOn (baseSecond (23/25)) (Icc (0:ℝ) (2/5)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (baseSecond_hasDerivAt (23/25) x).continuousAt.continuousWithinAt)
    (fun x _ => baseSecond_hasDerivAt (23/25) x)
  intro x hx
  apply baseThird_nonpos_of_endpoint (u:=(2/5:ℝ)) (by norm_num) (Ioo_subset_Icc_self hx)
  norm_num [qCap]

theorem AB_late_base_endpoint : baseSecond (23/25) (7/20)< -(481/1000:ℝ) := by
  have hW := radical_positive (A:=1) (x:=(7/20:ℝ)) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=(7/20:ℝ)) (by norm_num)
  have hN := radical_positive (A:=1+(23/25:ℝ)^2) (x:=(7/20:ℝ)) (by norm_num)
  have hN2 := radical_square (A:=1+(23/25:ℝ)^2) (x:=(7/20:ℝ)) (by norm_num)
  have hWlo : (5297/5000:ℝ)<radical 1 (7/20) := by norm_num at hW2; nlinarith
  have hNhi : radical (1+(23/25:ℝ)^2) (7/20)<877/625 := by norm_num at hN2; nlinarith
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hR2 : R^2=9789/2500 := Real.sq_sqrt (by norm_num)
  have hRlo : (19787/10000:ℝ)<R := by nlinarith
  have hfirst : 1/(radical 1 (7/20))^3≤1/(5297/5000:ℝ)^3 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact pow_le_pow_left₀ (by norm_num) hWlo.le 3
  have hsecond : ((19787/10000:ℝ)*(1+(23/25:ℝ)^2))/(877/625:ℝ)^3<
      R*(1+(23/25:ℝ)^2)/(radical (1+(23/25:ℝ)^2) (7/20))^3 := by
    apply (div_lt_div_iff₀ (by norm_num) (pow_pos hN 3)).2
    have hpow := pow_le_pow_left₀ hN.le hNhi.le 3
    have hmul := mul_le_mul_of_nonneg_left hpow
      (by norm_num : (0:ℝ)≤(19787/10000)*(1+(23/25:ℝ)^2))
    nlinarith
  have hrat : 1/(5297/5000:ℝ)^3-
      ((19787/10000:ℝ)*(1+(23/25:ℝ)^2))/(877/625:ℝ)^3< -(481/1000:ℝ) := by norm_num
  dsimp [baseSecond]
  linarith

theorem AB_late_base_curvature {r x : ℝ}
    (hr : r∈Icc 0 (23/25:ℝ)) (hx : x∈Icc (7/20:ℝ) (2/5:ℝ)) :
    baseSecond r x< -(481/1000:ℝ) := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hx2 := pow_le_pow_left₀ hx0 hx.2 2
  have hm := baseSecond_ratio_mono hr.1 hr.2 (by nlinarith : 2*x^2≤1)
  have ha := AB_late_base_antitone
    (show (7/20:ℝ)∈Icc 0 (2/5) by norm_num) ⟨hx0,hx.2⟩ hx.1
  exact (hm.trans ha).trans_lt AB_late_base_endpoint

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SecantBounds
