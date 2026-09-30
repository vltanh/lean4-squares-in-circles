import SquaresInCircles.Six.Analytic.WestCardinalMixedScalar
import SquaresInCircles.Six.Analytic.WestSecondaryGap
import SquaresInCircles.Six.Stress.Support

/-!
# Exact local supports of the cardinal/cardinal missing-west stress

The W force is on the cap branch for a proved slope reason. D and S use the
universally valid far-vertex support. The variable W angle is eliminated by
Cauchy only after its force formula is identified exactly. No dominance rule
or optimized numerical multiplier is an assumption of these lemmas.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestCardinalMixed
open Normalization

def wU (v d : ℝ) : ℝ := (9/40)*(Real.cos v+Real.sin (d+v))
def wV (v d : ℝ) : ℝ := (9/40)*(Real.sin v-Real.cos (d+v))
def dU (r : ℝ) : ℝ := 3/25+(9/50)*Real.sin r
def dV (r : ℝ) : ℝ := 9/40-(9/50)*Real.cos r
def sU (s : ℝ) : ℝ := (1/4)*Real.cos s
def sV (s : ℝ) : ℝ := 9/50-(1/4)*Real.sin s

lemma small_s_trig {s : ℝ} (hs : |s| ≤ 2/5) :
    23/25 ≤ Real.cos s ∧ |Real.sin s| ≤ 2/5 := by
  have hp := mul_nonneg (sub_nonneg.mpr hs)
    (show 0 ≤ (2:ℝ)/5+|s| by positivity)
  have hc : 23/25 ≤ Real.cos s := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := s),sq_abs s]
  have ht := Real.sin_le (abs_nonneg s)
  rw [sin_abs_angle (by linarith [Real.pi_gt_d2] : |s| ≤ Real.pi)] at ht
  exact ⟨hc,ht.trans hs⟩

lemma forward_west_trig {v d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/5) (hd : d ≤ Real.pi/4) (hq : 1 ≤ d+v) :
    (23/25 ≤ Real.cos v ∧ 0 ≤ Real.sin v ∧ Real.sin v ≤ 2/5) ∧
      (21/25 ≤ Real.sin (d+v) ∧ 0 ≤ Real.cos (d+v) ∧ Real.cos (d+v) ≤ 13/24) := by
  have hc := (small_s_trig (by rw [abs_of_nonneg hv.1]; exact hv.2)).1
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv.1 (by linarith [hv.2,Real.pi_gt_d2])
  have hqpi : d+v ≤ Real.pi/2 := by linarith [hd,hv.2,Real.pi_gt_d2]
  have hsq := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ) by linarith [Real.pi_pos]) hqpi hq
  have hcq := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 1)
    (show d+v ≤ Real.pi by linarith [hqpi,Real.pi_pos]) hq
  have hcq0 := Real.cos_nonneg_of_mem_Icc
    (show d+v∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq,hqpi,Real.pi_pos])
  exact ⟨⟨hc,hs,(Real.sin_le hv.1).trans hv.2⟩,
    ⟨by nlinarith [Seven.sin_lower_seven (show (0:ℝ) ≤ 1 by norm_num)],
      hcq0,by nlinarith [Seven.cos_upper_four (show (0:ℝ) ≤ 1 by norm_num)]⟩⟩

/-- This is the genuine corner-slope condition for the W force. -/
lemma west_force_cap_slope {v d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/5) (hd : d ≤ Real.pi/4) (hq : 1 ≤ d+v) :
    0 ≤ wU v d ∧ (rho0+1/2)*|wV v d| ≤ (1/2)*wU v d := by
  obtain ⟨⟨hcv,hsv0,hsv⟩,⟨hsq,hcq0,hcq⟩⟩ := forward_west_trig hv hd hq
  have hU : (9/40)*(44/25) ≤ wU v d := by dsimp [wU]; linarith
  have hV : |wV v d| ≤ (9/40)*(13/24) := by
    apply abs_le.mpr
    dsimp [wV]
    constructor <;> linarith
  have hm := mul_le_mul (show rho0+1/2 ≤ (1613:ℝ)/1000 by linarith [rho0_upper])
    hV (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1613/1000)
  exact ⟨by linarith,by nlinarith only [hm,hU]⟩

/-- Actual W-center support, not a cap bound selected by coordinate dominance. -/
lemma west_center_support {a b v d : ℝ} (hc : ContainedChart a |b|)
    (hv : 0 ≤ v ∧ v ≤ 2/5) (hd : d ≤ Real.pi/4) (hq : 1 ≤ d+v) :
    a*wU v d+b*wV v d ≤ (1113/1000)*wU v d := by
  obtain ⟨hU,hslope⟩ := west_force_cap_slope hv hd hq
  have hh := disk_corner_support
    (A := a+1/2) (B := |b|+1/2) (a := rho0+1/2) (b := (1:ℝ)/2)
    (c := wU v d) (s := |wV v d|)
    (by linarith [rho0_gt_one]) (by linarith [abs_nonneg b]) hU
    (by nlinarith [rho0_identity]) hc.containment hslope
  have hsigned : b*wV v d ≤ |b|*|wV v d| := by
    simpa only [abs_mul] using le_abs_self (b*wV v d)
  have hupper := mul_nonneg (show 0 ≤ 1113/1000-rho0 by linarith [rho0_upper]) hU
  nlinarith only [hh,hsigned,hupper]

/-- Universal far-vertex support in a side frame. -/
lemma side_vertex_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 0 ≤ U) (hV : 0 ≤ V) :
    a*U+b*V ≤ (1689/1000)*Real.sqrt (U^2+V^2)-(U+V)/2 := by
  have hbox : normSq (a+1/2,|b|+1/2) ≤ R0^2 := by
    simpa only [normSq,R0_sq] using hc.containment
  have hh := Six.Stress.dot_le_radius (v := (U,V)) R0_nonneg hbox
  dsimp [dot,Six.Stress.vectorLength,normSq] at hh
  have hsigned := mul_le_mul_of_nonneg_right (le_abs_self b) hV
  have hupper := mul_nonneg
    (show 0 ≤ 1689/1000-R0 by linarith [R0_lt_1689_1000]) (Real.sqrt_nonneg (U^2+V^2))
  nlinarith only [hh,hsigned,hupper]

lemma diagonal_force_norm (r : ℝ) : (dU r)^2+(dV r)^2=dP+dQ*Real.sin r+dC*Real.cos r := by
  dsimp [dU,dV,dP,dQ,dC]
  linear_combination (81/2500)*(Real.sin_sq_add_cos_sq r)

lemma south_force_norm (s : ℝ) : (sU s)^2+(sV s)^2=sP+sQ*Real.sin s := by
  dsimp [sU,sV,sP,sQ]
  linear_combination (1/16)*(Real.sin_sq_add_cos_sq s)

lemma diagonal_center_support {a b r : ℝ} (hc : ContainedChart a |b|)
    (hr : 0 ≤ r ∧ r ≤ Real.pi/2) :
    a*dU r+b*dV r ≤ (1689/1000)*dRoot r-(dU r+dV r)/2 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hr.1 (by linarith [hr.2,Real.pi_pos])
  have hU : 0 ≤ dU r := by dsimp [dU]; linarith
  have hV : 0 ≤ dV r := by dsimp [dV]; linarith [Real.cos_le_one r]
  have hh := side_vertex_support hc hU hV
  rw [diagonal_force_norm] at hh
  exact hh

lemma south_center_support {a b s : ℝ} (hc : ContainedChart a |b|)
    (hs : |s| ≤ 2/5) :
    a*sU s+b*sV s ≤ (1689/1000)*sRoot s-(sU s+sV s)/2 := by
  obtain ⟨hcos,hsin⟩ := small_s_trig hs
  have hU : 0 ≤ sU s := by dsimp [sU]; linarith
  have hV : 0 ≤ sV s := by
    dsimp [sV]
    linarith [(le_abs_self (Real.sin s)).trans hsin]
  have hh := side_vertex_support hc hU hV
  rw [south_force_norm] at hh
  simpa only [sRoot,harmonicRoot,zero_mul,add_zero] using hh

def westOsc (v d : ℝ) : ℝ := (9/40)*
  (-(613/1000)*Real.cos v+(1/2)*Real.sin v+
    (1/2)*Real.cos (d+v)-(613/1000)*Real.sin (d+v))

/-- Eliminate v analytically, preserving the exact dependence on d. -/
lemma westOsc_lower (v d : ℝ) : -wRoot d ≤ westOsc v d := by
  let A : ℝ := (9/40)*(-(613/1000)+(1/2)*Real.cos d-(613/1000)*Real.sin d)
  let B : ℝ := (9/40)*((1/2)-(1/2)*Real.sin d-(613/1000)*Real.cos d)
  have hid : A^2+B^2=wP+wQ*Real.sin d+wC*Real.cos d := by
    dsimp [A,B,wP,wQ,wC]
    linear_combination (50687289/1600000000)*(Real.sin_sq_add_cos_sq d)
  have ht : westOsc v d=A*Real.cos v+B*Real.sin v := by
    dsimp [westOsc,A,B]
    rw [Real.sin_add,Real.cos_add]
    ring
  have hn : normSq (Real.cos v,Real.sin v) ≤ (1:ℝ)^2 := by
    dsimp [normSq]
    nlinarith [Real.sin_sq_add_cos_sq v]
  have hh := Six.Stress.dot_le_radius (v := (-A,-B)) (by norm_num : (0:ℝ) ≤ 1) hn
  dsimp [dot,Six.Stress.vectorLength,normSq] at hh
  simp only [neg_sq] at hh
  rw [hid] at hh
  change -A*Real.cos v+ -B*Real.sin v ≤ 1*wRoot d at hh
  rw [ht]
  linarith

def thresholdSum (v d s : ℝ) : ℝ :=
  (9/40)*(1/2+angularWidth v)+(3/25)*(1/2+angularWidth d)+
  (1/4)*(1/2+angularWidth s)+(9/40)*(1/2+angularWidth (d+v))+
  (9/50)*(1/2+angularWidth (Real.pi/2+s-d))

def centralUpper (d : ℝ) : ℝ :=
  (113/1000)*(9/40+1/4+(3/25)*(Real.cos d+Real.sin d))

def defect (v d s : ℝ) : ℝ :=
  thresholdSum v d s-centralUpper d-(1113/1000)*wU v d-
    ((1689/1000)*dRoot (Real.pi/2+s-d)-(dU (Real.pi/2+s-d)+dV (Real.pi/2+s-d))/2)-
    ((1689/1000)*sRoot s-(sU s+sV s)/2)

/-- Exact force/threshold algebra on the actual trigonometric sign regions. -/
lemma defect_decomposition {v d s : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/5) (hd : 3/5 ≤ d ∧ d ≤ Real.pi/4)
    (hq : 1 ≤ d+v) (hs : d-Real.pi/4 ≤ s ∧ s ≤ 2/5) :
    defect v d s=reduced (decide (s<0)) d s+westOsc v d+wRoot d := by
  obtain ⟨⟨hcv,hsv0,hsv⟩,⟨hsq,hcq0,hcq⟩⟩ := forward_west_trig hv hd.2 hq
  have hdcos : 0 ≤ Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_pos]⟩
  have hdsin := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hd.1])
    (by linarith [hd.2,Real.pi_pos])
  have habs : |s| ≤ 2/5 := by
    apply abs_le.mpr
    constructor <;> linarith [hs.1,hs.2,hd.1,Real.pi_lt_d2]
  have hsCos : 0 ≤ Real.cos s := by linarith [(small_s_trig habs).1]
  have hr : 0 ≤ Real.pi/2+s-d ∧ Real.pi/2+s-d ≤ Real.pi/2 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,Real.pi_pos]
  have hrSin := Real.sin_nonneg_of_nonneg_of_le_pi hr.1 (by linarith [hr.2,Real.pi_pos])
  have hrCos : 0 ≤ Real.cos (Real.pi/2+s-d) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩
  dsimp [defect,thresholdSum,centralUpper,reduced,westPart,southPart,diagonalPart,
    westOsc,wU,dU,dV,sU,sV,angularWidth]
  rw [abs_of_nonneg (show 0 ≤ Real.cos v by linarith),abs_of_nonneg hsv0,
    abs_of_nonneg hdcos,abs_of_nonneg hdsin,abs_of_nonneg hsCos,
    abs_of_nonneg hcq0,abs_of_nonneg (show 0 ≤ Real.sin (d+v) by linarith),
    abs_of_nonneg hrCos,abs_of_nonneg hrSin]
  by_cases hs0 : s<0
  · have hh : Real.sin s ≤ 0 := by
      have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := -s)
        (by linarith) (by linarith [hs.1,hd.1,Real.pi_pos])
      rw [Real.sin_neg] at h
      linarith
    simp only [hs0,decide_true,if_true,abs_of_nonpos hh]
    ring
  · have hh := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_not_gt hs0)
      (by linarith [hs.2,Real.pi_gt_d2])
    simp only [hs0,decide_false,Bool.false_eq_true,if_false,abs_of_nonneg hh]
    ring

lemma defect_positive {v d s : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/5) (hd : 3/5 ≤ d ∧ d ≤ Real.pi/4)
    (hq : 1 ≤ d+v) (hs : d-Real.pi/4 ≤ s ∧ s ≤ 2/5) : 0 < defect v d s := by
  rw [defect_decomposition hv hd hq hs]
  have h := reduced_positive hd hs
  have hw := westOsc_lower v d
  linarith

end SquaresInCircles.Six.Analytic.WestCardinalMixed
