module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighNegativeOuter

/-!
# The negative-primary scalar for an actual flat-core target

All trigonometric comparisons are polynomial inequalities on the whole
half-unit interval.  The small-angle range has positive charge without
the marker correction; the full interval loses less than `23/1000`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

def coreU : ℝ := 183/200
def coreL (z : ℝ) : ℝ := (13*kappa/12-1)*z-kappa*coreU/2*z^2+
  13*kappa/36*z^3-47*kappa*coreU/200*z^4+13*kappa/90*z^5
def coreLDerivative (z : ℝ) : ℝ := 13*kappa/12-1-kappa*coreU*z+
  13*kappa/12*z^2-47*kappa*coreU/50*z^3+13*kappa/18*z^4
def coreLSecond (z : ℝ) : ℝ := -kappa*coreU+13*kappa/6*z-
  141*kappa*coreU/50*z^2+26*kappa/9*z^3
def coreLNormalized (z : ℝ) : ℝ := 13*kappa/12-1-kappa*coreU/2*z+
  13*kappa/36*z^2-47*kappa*coreU/200*z^3+13*kappa/90*z^4
def coreLNormalizedDerivative (z : ℝ) : ℝ := -kappa*coreU/2+
  13*kappa/18*z-141*kappa*coreU/200*z^2+26*kappa/45*z^3

/-- A direct Taylor comparison proves the tangent lower polynomial
after multiplication by the positive cosine. -/
theorem core_tangent_polynomial {z : ℝ} (hz : z∈Icc 0 (1/2:ℝ)) :
    (z+z^3/3+2*z^5/15)*Real.cos z≤Real.sin z := by
  have hT : 0≤z+z^3/3+2*z^5/15 := by
    linarith [hz.1,pow_nonneg hz.1 3,pow_nonneg hz.1 5]
  have hc := mul_le_mul_of_nonneg_left (cos_upper_four hz.1) hT
  have hs := sin_lower_seven hz.1
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  norm_num at h2
  have h7 := pow_nonneg hz.1 7
  have h9 : z^9≤(1/4)*z^7 := by
    have hh := mul_le_mul_of_nonneg_left h2 h7
    nlinarith only [hh]
  nlinarith only [hc,hs,h7,h9]

/-- The secant upper polynomial is likewise kept in a form with no
division by a trigonometric expression. -/
theorem core_secant_polynomial {z : ℝ} (hz : z∈Icc 0 (1/2:ℝ)) :
    1-Real.cos z≤(z^2/2+47*z^4/200)*Real.cos z := by
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have h6 := pow_le_pow_left₀ hz.1 hz.2 6
  norm_num at h2 h6
  have h4 := pow_nonneg hz.1 4
  have hbracket : 0≤(2/75:ℝ)-(353/3600)*z^2+(131/14400)*z^4-(47/144000)*z^6 := by
    nlinarith only [h2,h6,h4]
  have hprod := mul_nonneg h4 hbracket
  have hid : (1+z^2/2+47*z^4/200)*(1-z^2/2+z^4/24-z^6/720)-1=
      z^4*((2/75:ℝ)-(353/3600)*z^2+(131/14400)*z^4-(47/144000)*z^6) := by
    ring
  have hc := mul_le_mul_of_nonneg_left (cos_lower_six hz.1)
    (show 0≤1+z^2/2+47*z^4/200 by positivity)
  nlinarith only [hprod,hid,hc]

theorem coreL_factor (z : ℝ) : coreL z=z*coreLNormalized z := by
  dsimp [coreL,coreLNormalized]
  ring

theorem coreL_derivative (z : ℝ) : HasDerivAt coreL (coreLDerivative z) z := by
  have h := (((((hasDerivAt_id z).const_mul (13*kappa/12-1)).sub
    (((hasDerivAt_id z).pow 2).const_mul (kappa*coreU/2))).add
    (((hasDerivAt_id z).pow 3).const_mul (13*kappa/36))).sub
    (((hasDerivAt_id z).pow 4).const_mul (47*kappa*coreU/200))).add
    (((hasDerivAt_id z).pow 5).const_mul (13*kappa/90))
  convert h using 1
  · funext y
    simp only [coreL,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,id]
  · simp only [coreLDerivative,id]
    push_cast
    ring

theorem coreL_second_derivative (z : ℝ) :
    HasDerivAt coreLDerivative (coreLSecond z) z := by
  have h := ((((hasDerivAt_const z (13*kappa/12-1)).sub
    ((hasDerivAt_id z).const_mul (kappa*coreU))).add
    (((hasDerivAt_id z).pow 2).const_mul (13*kappa/12))).sub
    (((hasDerivAt_id z).pow 3).const_mul (47*kappa*coreU/50))).add
    (((hasDerivAt_id z).pow 4).const_mul (13*kappa/18))
  convert h using 1
  · funext y
    simp only [coreLDerivative,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,id]
  · simp only [coreLSecond,id]
    push_cast
    ring

theorem coreLNormalized_derivative (z : ℝ) :
    HasDerivAt coreLNormalized (coreLNormalizedDerivative z) z := by
  have h := ((((hasDerivAt_const z (13*kappa/12-1)).sub
    ((hasDerivAt_id z).const_mul (kappa*coreU/2))).add
    (((hasDerivAt_id z).pow 2).const_mul (13*kappa/36))).sub
    (((hasDerivAt_id z).pow 3).const_mul (47*kappa*coreU/200))).add
    (((hasDerivAt_id z).pow 4).const_mul (13*kappa/90))
  convert h using 1
  · funext y
    simp only [coreLNormalized,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,id]
  · simp only [coreLNormalizedDerivative,id]
    push_cast
    ring

theorem coreLNormalized_antitone :
    AntitoneOn coreLNormalized (Icc 0 (3/10:ℝ)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun z _ => (coreLNormalized_derivative z).continuousAt.continuousWithinAt
  · exact fun z _ => coreLNormalized_derivative z
  · intro z hz
    have h3 := pow_le_pow_left₀ hz.1.le hz.2.le 3
    norm_num at h3
    dsimp [coreLNormalizedDerivative,kappa,coreU]
    nlinarith [sq_nonneg z,hz.2]

theorem coreL_positive_short {z : ℝ} (hz : z∈Ioc 0 (3/10:ℝ)) : 0<coreL z := by
  have hm := coreLNormalized_antitone (Ioc_subset_Icc_self hz)
    (show (3/10:ℝ)∈Icc 0 (3/10:ℝ) by norm_num) hz.2
  have he : 0<coreLNormalized (3/10) := by
    norm_num [coreLNormalized,kappa,coreU]
  rw [coreL_factor]
  exact mul_pos hz.1 (he.trans_le hm)

theorem coreL_concave : ConcaveOn ℝ (Icc 0 (1/2:ℝ)) coreL := by
  apply concave_of_deriv2 (fun z _ => coreL_derivative z)
    (fun z _ => coreL_second_derivative z)
  intro z hz
  have h3 := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)
  have hsq := sq_nonneg (z-1/2)
  dsimp [coreLSecond,kappa,coreU]
  nlinarith only [h3,hsq,hz.2]

theorem coreL_lower {z : ℝ} (hz : z∈Icc 0 (1/2:ℝ)) : -23/1000<coreL z := by
  apply concave_gt_of_endpoints coreL_concave hz
  · norm_num [coreL,kappa,coreU]
  · norm_num [coreL,kappa,coreU]

open FramePair FrameCircleArc FrameLowArc GlobalOuterAnchor

/-- Multiplication by the actual positive cosine keeps the original
projection intact and avoids a tangent/secant state transformation. -/
theorem core_primary_scaled_transfer (s : State) (hs : s.branch.type≠0)
    {Y z : ℝ} (hz : z∈Icc 0 (1/2:ℝ))
    (hm : GlobalOuterAnchor.width (-z)≤ s.a+(7/12)*Real.sin (-z)-Y*Real.cos (-z)) :
    (coreL z+rho*J s)*Real.cos z≤(quarterCharge s Y (-z)-kappa)*Real.cos z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have tr := transport_trig hz'
  have hchart := state_outer_chart s hs
  have ha := (A_bounds hchart.2).2
  rw [← hchart.1] at ha
  have hU : s.a-1/2≤coreU := by dsimp [coreU]; linarith [a0_bounds.2]
  have hdrop := mul_nonneg (sub_nonneg.mpr hU) (sub_nonneg.mpr tr.2.1)
  have htan := core_tangent_polynomial hz
  have hsec := core_secant_polynomial hz
  simp only [GlobalOuterAnchor.width,Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg tr.2.2.1,mul_neg] at hm
  dsimp [quarterCharge,potential,coreL,kappa,rho,coreU] at hdrop ⊢
  nlinarith only [hm,hdrop,htan,hsec]

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
