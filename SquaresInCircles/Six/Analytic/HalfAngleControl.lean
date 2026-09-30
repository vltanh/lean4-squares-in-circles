import SquaresInCircles.Seven.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Whole-interval estimates for the canonical central-margin difference

The ratio sin(t)/(1+cos(t)) is used without an inverse trigonometric function.
On [0,4/5] it lies between t/2 and 11t/20. The lower inequality follows from
two monotonicity arguments; the upper one is an explicit fifth-degree Taylor
inequality with nonnegative remainder. The cosine-difference bound is the
integrated linear sine lower bound, proved by monotonicity of cos(t)+89t²/200.
No interval partition, numerical minimization or certificate is used.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

def halfRatio (t : ℝ) : ℝ := Real.sin t/(1+Real.cos t)

lemma small_polynomial_trig {t : ℝ} (ht : 0≤t ∧ t≤4/5) :
    17/25≤Real.cos t ∧ (89/100)*t≤Real.sin t ∧
      Real.sin t≤t ∧ 1+(12/25)*t≤Real.cos t+Real.sin t := by
  have hsq := mul_nonneg (sub_nonneg.mpr ht.2) (show 0≤4/5+t by linarith [ht.1])
  have ht2 : t^2≤16/25 := by nlinarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hs := Real.sin_ge_sub_cube ht.1
  have hsincoef : 0≤1-89/100-t^2/6 := by linarith
  have hsinprod := mul_nonneg ht.1 hsincoef
  have hsumcoef : 0≤1-12/25-t/2-t^2/6 := by linarith [ht.2]
  have hsumprod := mul_nonneg ht.1 hsumcoef
  exact ⟨by linarith,by nlinarith only [hs,hsinprod],Real.sin_le ht.1,
    by nlinarith only [hs,hc,hsumprod]⟩

lemma halfRatio_den_pos {t : ℝ} (ht : 0≤t ∧ t≤4/5) : 0<1+Real.cos t := by
  linarith [(small_polynomial_trig ht).1]

lemma halfRatio_nonnegative {t : ℝ} (ht : 0≤t ∧ t≤4/5) : 0≤halfRatio t := by
  apply div_nonneg _ (halfRatio_den_pos ht).le
  nlinarith [(small_polynomial_trig ht).2.1,ht.1]

lemma halfRatio_identities {t : ℝ} (ht : 0≤t ∧ t≤4/5) :
    halfRatio t*(1+Real.cos t)=Real.sin t ∧
      halfRatio t*Real.sin t=1-Real.cos t := by
  have hden := ne_of_gt (halfRatio_den_pos ht)
  constructor
  · exact div_mul_cancel₀ _ hden
  · unfold halfRatio
    field_simp [hden]
    nlinarith [Real.sin_sq_add_cos_sq t]

lemma halfRatio_lower {t : ℝ} (ht : 0≤t ∧ t≤4/5) : t/2≤halfRatio t := by
  let H : ℝ→ℝ := fun x => Real.cos x-1+x*Real.sin x
  have hHd (x : ℝ) : HasDerivAt H (x*Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).sub_const 1).add
      ((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)) using 1 <;> dsimp [H] <;> ring
  have hHm : MonotoneOn H (Set.Icc 0 (4/5)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (by dsimp [H]; fun_prop)
      (fun x _ => hHd x)
    intro x hx
    have hc := (small_polynomial_trig ⟨hx.1.le,hx.2.le⟩).1
    exact mul_nonneg hx.1.le (by linarith)
  have hHnonneg {x : ℝ} (hx : 0≤x ∧ x≤4/5) : 0≤H x := by
    have h := hHm (show (0:ℝ)∈Set.Icc 0 (4/5) by constructor <;> norm_num) hx hx.1
    simpa [H] using h
  let F : ℝ→ℝ := fun x => 2*Real.sin x-x*(1+Real.cos x)
  have hFd (x : ℝ) : HasDerivAt F (H x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul 2).sub
      ((hasDerivAt_id x).mul ((Real.hasDerivAt_cos x).const_add 1)) using 1 <;>
      dsimp [F,H] <;> ring
  have hFm : MonotoneOn F (Set.Icc 0 (4/5)) :=
    Seven.monoOn_of_hasDeriv_nonneg (by dsimp [F]; fun_prop)
      (fun x _ => hFd x) (fun x hx => hHnonneg ⟨hx.1.le,hx.2.le⟩)
  have hF := hFm (show (0:ℝ)∈Set.Icc 0 (4/5) by constructor <;> norm_num) ht ht.1
  have hF' : 0≤2*Real.sin t-t*(1+Real.cos t) := by simpa [F] using hF
  unfold halfRatio
  apply (le_div_iff₀ (halfRatio_den_pos ht)).mpr
  nlinarith only [hF']

lemma halfRatio_upper {t : ℝ} (ht : 0≤t ∧ t≤4/5) : halfRatio t≤(11/20)*t := by
  have hsq := mul_nonneg (sub_nonneg.mpr ht.2) (show 0≤4/5+t by linarith [ht.1])
  have ht2 : t^2≤16/25 := by nlinarith
  have hfour := mul_nonneg (sub_nonneg.mpr ht2) (show 0≤16/25+t^2 by positivity)
  have hcoef : 0≤1/10-(13/120)*t^2-t^4/120 := by nlinarith
  have hp := mul_nonneg ht.1 hcoef
  have hs := Seven.sin_upper_five ht.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hcm := mul_le_mul_of_nonneg_left hc (show 0≤(11/20)*t by positivity)
  unfold halfRatio
  apply (div_le_iff₀ (halfRatio_den_pos ht)).mpr
  nlinarith only [hp,hs,hcm]

lemma cosine_difference_lower {q d : ℝ} (hq : 0≤q) (hqd : q≤d) (hd : d≤4/5) :
    (89/200)*(d^2-q^2)≤Real.cos q-Real.cos d := by
  let f : ℝ→ℝ := fun x => Real.cos x+(89/200)*x^2
  have hfd (x : ℝ) : HasDerivAt f (-Real.sin x+(89/100)*x) x := by
    convert (Real.hasDerivAt_cos x).add (((hasDerivAt_id x).pow 2).const_mul (89/200))
      using 1 <;> dsimp [f] <;> ring
  have hanti : AntitoneOn f (Set.Icc 0 (4/5)) := by
    apply Seven.antiOn_of_hasDeriv_nonpos (by dsimp [f]; fun_prop) (fun x _ => hfd x)
    intro x hx
    linarith [(small_polynomial_trig ⟨hx.1.le,hx.2.le⟩).2.1]
  have h := hanti ⟨hq,hqd.trans hd⟩ ⟨hq.trans hqd,hd⟩ hqd
  dsimp [f] at h
  linarith

lemma sine_difference_upper {q d : ℝ} (hqd : q≤d) :
    Real.sin d-Real.sin q≤d-q := by
  have h := (le_abs_self (Real.sin d-Real.sin q)).trans (Real.abs_sin_sub_sin_le d q)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hqd)] using h

lemma halfRatio_shift {w d : ℝ} (hw : 0≤w ∧ w≤4/5) :
    Real.sin (d-w)+halfRatio w*Real.cos (d-w)=Real.sin d-halfRatio w*Real.cos d := by
  have h := halfRatio_identities hw
  rw [Real.sin_sub,Real.cos_sub]
  linear_combination Real.sin d*h.2 + Real.cos d*h.1

end SquaresInCircles.Six.Analytic
