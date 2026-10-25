module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Tangent

/-!
# Exact derivatives for the saturated core-E prefix

The TD multiplier varies with the prefix.  The derivatives below
retain that dependence explicitly.  The only varying endpoint ratio
increases over the complete saturated multiplier strip.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open FrameCircleArc

def prefixRatio (a p : ℝ) : ℝ :=
  (a*weight p*Real.cos p+slope*a*Real.sin p-slope*weight p)/tailNorm a (weight p) p
def firstD (p e : ℝ) : ℝ := -1/5-kappa*Real.sin p+
  R*(prefixRatio kappa p-slope*weight p/tailNorm e (weight p) 0)
def lastD (p e : ℝ) : ℝ := -3/5+slope*Real.cos p-weight p*Real.sin p+
  R*(prefixRatio e p-slope*weight p/tailNorm kappa (weight p) 0)

theorem weight_deriv (p : ℝ) : HasDerivAt weight slope p := by
  have h : HasDerivAt (fun z => 3/5+slope*z) (slope*1) p :=
    ((hasDerivAt_id' p).const_mul slope).const_add (3/5:ℝ)
  rw [mul_one] at h
  exact h

theorem variable_norm_deriv {a p : ℝ} (ha : 0<a) (hp : p∈Icc 0 frameCap) :
    HasDerivAt (fun z => tailNorm a (weight z) z) (-prefixRatio a p) p := by
  have hn := (tailNorm_pos ha (weight_pos hp) hp).ne'
  have hw := weight_deriv p
  have h1 : HasDerivAt (fun z => weight z^2) (((2:ℕ):ℝ)*weight p^(2-1)*slope) p :=
    hw.fun_pow 2
  have h2 : HasDerivAt (fun z => 2*a*(weight z*Real.sin z))
      (2*a*(slope*Real.sin p+weight p*Real.cos p)) p :=
    (hw.fun_mul (Real.hasDerivAt_sin p)).const_mul (2*a)
  have hg : HasDerivAt (fun z => a^2+weight z^2-2*a*weight z*Real.sin z)
      (((2:ℕ):ℝ)*weight p^(2-1)*slope-2*a*(slope*Real.sin p+weight p*Real.cos p)) p := by
    have h3 := (h1.const_add (a^2)).fun_sub h2
    convert h3 using 2 with z
    ring
  have hd := hg.sqrt (tail_energy_positive ha (weight_pos hp) hp).ne'
  refine hd.congr_deriv ?_
  simp only [prefixRatio]
  simp only [tailNorm] at hn ⊢
  field_simp
  push_cast
  ring

theorem variable_zero_norm_deriv {a p : ℝ} (ha : 0<a) (hp : p∈Icc 0 frameCap) :
    HasDerivAt (fun z => tailNorm a (weight z) 0)
      (slope*weight p/tailNorm a (weight p) 0) p := by
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hn := (tailNorm_pos ha (weight_pos hp) hzero).ne'
  have hw := weight_deriv p
  have h1 : HasDerivAt (fun z => weight z^2) (((2:ℕ):ℝ)*weight p^(2-1)*slope) p :=
    hw.fun_pow 2
  have h2 : HasDerivAt (fun z => 2*a*weight z*Real.sin 0) (2*a*slope*Real.sin 0) p :=
    (hw.const_mul (2*a)).mul_const (Real.sin 0)
  have hg : HasDerivAt (fun z => a^2+weight z^2-2*a*weight z*Real.sin 0)
      (((2:ℕ):ℝ)*weight p^(2-1)*slope-2*a*slope*Real.sin 0) p :=
    (h1.const_add (a^2)).fun_sub h2
  have hd := hg.sqrt (tail_energy_positive ha (weight_pos hp) hzero).ne'
  refine hd.congr_deriv ?_
  simp only [tailNorm] at hn ⊢
  field_simp
  simp only [Real.sin_zero]
  push_cast
  ring

theorem first_deriv {p t e : ℝ} (hp : p∈Icc 0 frameCap) (he : 0<e) :
    HasDerivAt (fun z => first z t e) (firstD p e) p := by
  have hk : 0<kappa := by norm_num [kappa]
  have h1 : HasDerivAt (fun z => -z+2*weight z+kappa*Real.cos z)
      (-1+2*slope+kappa*(-Real.sin p)) p :=
    (((hasDerivAt_id' p).fun_neg).fun_add ((weight_deriv p).const_mul 2)).fun_add
      ((Real.hasDerivAt_cos p).const_mul kappa)
  have h2 : HasDerivAt (fun z => tailNorm kappa (weight z) z+tailNorm e (weight z) 0)
      (-prefixRatio kappa p+slope*weight p/tailNorm e (weight p) 0) p :=
    (variable_norm_deriv hk hp).fun_add (variable_zero_norm_deriv he hp)
  have hd := (h1.const_add
    (Real.pi-t+(3/2)*kappa+e+(e/2)*Real.cos t+e*(13/12)*Real.sin t)).fun_sub (h2.const_mul R)
  convert hd using 1
  · funext z
    simp only [first]
    ring
  · simp only [firstD,slope]
    ring

theorem last_deriv {p t e : ℝ} (hp : p∈Icc 0 frameCap) (he : 0<e) :
    HasDerivAt (fun z => last z t e) (lastD p e) p := by
  have hk : 0<kappa := by norm_num [kappa]
  have h1 : HasDerivAt (fun z => -z+weight z+weight z*Real.cos z)
      (-1+slope+(slope*Real.cos p+weight p*(-Real.sin p))) p :=
    (((hasDerivAt_id' p).fun_neg).fun_add (weight_deriv p)).fun_add
      ((weight_deriv p).fun_mul (Real.hasDerivAt_cos p))
  have h2 : HasDerivAt (fun z => tailNorm kappa (weight z) 0+tailNorm e (weight z) z)
      (slope*weight p/tailNorm kappa (weight p) 0+-prefixRatio e p) p :=
    (variable_zero_norm_deriv hk hp).fun_add (variable_norm_deriv he hp)
  have hd := (h1.const_add
    (Real.pi-t+(5/2)*kappa+e+(e/2)*Real.cos t+e*(13/12)*Real.sin t)).fun_sub (h2.const_mul R)
  convert hd using 1
  · funext z
    simp only [last]
    ring
  · simp only [lastD,slope]
    ring

theorem multiplier_norm_deriv {a p : ℝ} (ha : 0<a) (hp : p∈Icc 0 frameCap) :
    HasDerivAt (fun z => tailNorm z (weight p) p)
      ((a-weight p*Real.sin p)/tailNorm a (weight p) p) a := by
  have hn := (tailNorm_pos ha (weight_pos hp) hp).ne'
  have hg : HasDerivAt (fun z => z^2+weight p^2-2*z*weight p*Real.sin p)
      (((2:ℕ):ℝ)*a^(2-1)*1-1*(2*weight p*Real.sin p)) a := by
    have h3 := (((hasDerivAt_id' a).fun_pow 2).add_const (weight p^2)).fun_sub
      ((hasDerivAt_id' a).mul_const (2*weight p*Real.sin p))
    convert h3 using 2 with z
    ring
  have hd := hg.sqrt (tail_energy_positive ha (weight_pos hp) hp).ne'
  refine hd.congr_deriv ?_
  simp only [tailNorm] at hn ⊢
  field_simp
  push_cast
  ring

theorem prefixRatio_deriv {a p : ℝ} (ha : 0<a) (hp : p∈Icc 0 frameCap) :
    HasDerivAt (fun z => prefixRatio z p)
      (weight p*Real.cos p*((weight p)^2+a*(slope*Real.cos p-weight p*Real.sin p))/
        (tailNorm a (weight p) p)^3) a := by
  have hc := weight_pos hp
  have hn := (tailNorm_pos ha hc hp).ne'
  have hnum : HasDerivAt
      (fun z => z*weight p*Real.cos p+slope*z*Real.sin p-slope*weight p)
      (weight p*Real.cos p+slope*Real.sin p) a := by
    have h := ((((hasDerivAt_id' a).mul_const (weight p)).mul_const (Real.cos p)).fun_add
      (((hasDerivAt_id' a).const_mul slope).mul_const (Real.sin p))).sub_const
        (slope*weight p)
    convert h using 1
    ring
  have hd := hnum.fun_div (multiplier_norm_deriv ha hp) hn
  refine hd.congr_deriv ?_
  have hsq := tailNorm_sq ha hc hp
  field_simp
  linear_combination
    (weight p*Real.cos p+slope*Real.sin p)*hsq-
      slope*a*weight p*(Real.sin_sq_add_cos_sq p)

theorem multiplier_curvature_positive {a p : ℝ}
    (ha : a∈Icc m (141/100:ℝ)) (hp : p∈Icc 0 frameCap) :
    0<(weight p)^2+a*(slope*Real.cos p-weight p*Real.sin p) := by
  have hc := weight_bounds hp
  have tr := transport_trig hp
  have hapos : 0≤a := by dsimp [m] at ha; linarith [ha.1]
  have hsin := mul_le_mul_of_nonneg_left (show Real.sin p≤13/20 by linarith [tr.2.2.2.1])
    (weight_pos hp).le
  have hinner : (3/10)-(13/20)*weight p≤ slope*Real.cos p-weight p*Real.sin p := by
    dsimp [slope]
    linarith [tr.1]
  have hneg : (3/10)-(13/20)*weight p≤0 := by linarith [hc.1]
  have hprod := mul_le_mul_of_nonneg_left hinner hapos
  have hupper := mul_le_mul_of_nonpos_right ha.2 hneg
  have hquad := mul_nonneg (show 0≤weight p-3/5 by linarith [hc.1])
    (show 0≤weight p+3/5-1833/2000 by linarith [hc.1])
  nlinarith only [hprod,hupper,hquad]

theorem prefixRatio_monotone {p : ℝ} (hp : p∈Icc 0 frameCap) :
    MonotoneOn (fun a => prefixRatio a p) (Icc m (141/100:ℝ)) := by
  have hpos (a : ℝ) (ha : a∈Icc m (141/100:ℝ)) : 0<a := by
    dsimp [m] at ha
    linarith [ha.1]
  apply monoOn_of_hasDeriv_nonneg
  · exact fun a ha => (prefixRatio_deriv (hpos a ha) hp).continuousAt.continuousWithinAt
  · exact fun a ha => prefixRatio_deriv (hpos a (Ioo_subset_Icc_self ha)) hp
  · intro a ha
    have ha' := Ioo_subset_Icc_self ha
    have hnum : 0≤weight p*Real.cos p*
        ((weight p)^2+a*(slope*Real.cos p-weight p*Real.sin p)) := by
      exact mul_nonneg
        (mul_nonneg (weight_pos hp).le (by linarith [(transport_trig hp).1]))
        (multiplier_curvature_positive ha' hp).le
    exact div_nonneg hnum (pow_nonneg (tailNorm_pos (hpos a ha') (weight_pos hp) hp).le 3)

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
