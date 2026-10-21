module

public import SquaresInCircles.Eight.TableFree.SoleECoefficients
public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeEnvelope

/-!
# Actual coefficient comparisons for the negative norm gain

Uncompiled source. The gain is differentiated in its larger coefficient
on the complete interval between the two actual coefficients. The short
angle estimate follows from a monotone normalized integrand on one
rectangle. Its far-angle counterpart uses the actual negative norm.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SoleNormGain
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope VaryingBFunctions VaryingBComparison

def normGain (R p q s : ℝ) : ℝ := R*(pairNorm p q 0-pairNorm p q (-s))

theorem normGain_hasDerivAt_large {R p q s : ℝ} (hp : 0<p) (hq : 0<q)
    (hs : s∈Icc 0 frameCap) :
    HasDerivAt (fun x => normGain R p x s) (R*gain (p/q) (Real.sin s)) q := by
  have hh := (V_hasDerivAt_q (R := R) hp hq hs).sub
    ((hasDerivAt_id q).mul_const (Real.cos s-1))
  convert hh using 1
  · funext x
    dsimp [normGain,V]
    ring
  · dsimp [D]
    ring

theorem gain_nonneg {r z : ℝ} (hr : r∈Icc 0 1)
    (hz : z∈Icc 0 frameCap) (hzr : z≤r) : 0≤gain r z := by
  have hS := shape_pos r
  have hN := root_pos r hz
  have hS2 := shape_sq r
  have hN2 := root_sq r hz
  have hr2 : r^2≤1 := by nlinarith [sq_nonneg r]
  have hprod : r*z≤1 := by nlinarith [mul_le_mul hr.2 (hzr.trans hr.2) hz.1 (by norm_num : (0:ℝ)≤1)]
  have hnum : 0≤1-r*z := by linarith
  have hinner : 0≤2*r-z*(1+r^2) := by
    have hh := mul_le_mul_of_nonneg_right hzr (show 0≤1+r^2 by positivity)
    have ht := mul_nonneg hr.1 (sub_nonneg.mpr hr2)
    nlinarith
  have hp := mul_nonneg (mul_nonneg (sq_nonneg r) hz.1) hinner
  have hid : (root r z)^2-((1-r*z)*shape r)^2=r^2*z*(2*r-z*(1+r^2)) := by
    rw [mul_pow,hS2,hN2]
    ring
  have hc : (1-r*z)*shape r≤root r z := by
    rw [← hid] at hp
    nlinarith [mul_nonneg hnum hS.le]
  have hd : (1-r*z)/root r z≤1/shape r := by
    apply (div_le_div_iff₀ hN hS).2
    simpa only [one_mul] using hc
  dsimp [gain]
  linarith

theorem normGain_larger_mono {R p a b s : ℝ}
    (hR : 0≤R) (hp : 0<p) (hpa : p≤a) (hab : a≤b)
    (hs : s∈Icc 0 frameCap) (hratio : Real.sin s*b≤p) :
    normGain R p a s≤normGain R p b s := by
  have ha : 0<a := hp.trans_le hpa
  have hsin := (transport_trig hs).2.2.1
  have hz := sin_mem hs
  have hx (x : ℝ) (hx : x∈Icc a b) :
      0<x ∧ p/x∈Icc 0 1 ∧ Real.sin s≤p/x := by
    have hxp : 0<x := ha.trans_le hx.1
    refine ⟨hxp,⟨div_nonneg hp.le hxp.le,(div_le_one hxp).2 (hpa.trans hx.1)⟩,?_⟩
    exact (le_div_iff₀ hxp).2
      ((mul_le_mul_of_nonneg_left hx.2 hsin).trans hratio)
  have hm : MonotoneOn (fun x => normGain R p x s) (Icc a b) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hxx
      exact (normGain_hasDerivAt_large hp (hx x hxx).1 hs).continuousAt.continuousWithinAt
    · intro x hxx
      exact normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs
    · intro x hxx
      have hc := hx x (Ioo_subset_Icc_self hxx)
      exact mul_nonneg hR (gain_nonneg hc.2.1 hz hc.2.2)
  exact hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab

theorem normGain_smaller_mono {R q p p' s : ℝ}
    (hR : 0≤R) (hq : 0<q) (hs : s∈Icc 0 frameCap)
    (hp : p∈Icc (q/2) q) (hp' : p'∈Icc (q/2) q) (hpp : p≤p') :
    normGain R p q s≤normGain R p' q s := by
  have hh := V_monotone_smaller hR hq hs hp hp' hpp
  dsimp [V,normGain] at *
  linarith

theorem integrand_hasDerivAt_r {r z : ℝ} (hz : z∈Icc 0 frameCap) :
    HasDerivAt (fun x => integrand x z)
      (r*(3*r-2*z-2*r^2*z+r*z^2)/(root r z)^5) r := by
  have hn := root_hasDerivAt_r (r := r) hz
  have hN := (root_pos r hz).ne'
  have hnum := ((hasDerivAt_id r).pow 2).mul ((hasDerivAt_id r).sub_const z)
  have hh := hnum.div (hn.pow 3) (pow_ne_zero 3 hN)
  have hp := root_power_reduce r hz
  convert hh using 1
  · rfl
  · field_simp [hN]
    ring_nf
    simp only [hp 0,hp 1,hp 2,hp 3,hp 4,hp 5,hp 6,hp 7,
      hp 8,hp 9,hp 10,pow_zero,pow_one]
    ring

theorem integrand_monotone_ratio {z : ℝ} (hz : z∈Icc 0 (1/5 : ℝ)) :
    MonotoneOn (fun r => integrand r z) (Icc (117/200 : ℝ) (18/25)) := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  apply monoOn_of_hasDeriv_nonneg
  · intro r _
    exact (integrand_hasDerivAt_r hz').continuousAt.continuousWithinAt
  · intro r _
    exact integrand_hasDerivAt_r hz'
  · intro r hr
    have hr0 : 0≤r := by linarith [hr.1]
    have hr2 : r^2≤324/625 := by nlinarith [hr.2,sq_nonneg (r-18/25)]
    have hp := mul_le_mul hr2 hz.2 hz.1 (by norm_num : (0:ℝ)≤324/625)
    have hin : 0≤3*r-2*z-2*r^2*z+r*z^2 := by
      nlinarith [mul_nonneg hr0 (sq_nonneg z),hr.1,hz.2]
    exact div_nonneg (mul_nonneg hr0 hin) (pow_pos (root_pos r hz') 5).le

theorem scaled_integrand_upper {R r z : ℝ}
    (hR : R∈Icc 0 2) (hr : r∈Icc (117/200 : ℝ) (18/25))
    (hz : z∈Icc 0 (1/5 : ℝ)) : R*integrand r z≤11/20 := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hm := mul_le_mul_of_nonneg_left
    (integrand_monotone_ratio hz hr ⟨by norm_num,le_rfl⟩ hr.2) hR.1
  have hN := root_pos (18/25) hz'
  have hN2 := root_sq (18/25) hz'
  have hNlo : 1109/1000≤root (18/25) z := by nlinarith [hz.2]
  have hN3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1109/1000) hNlo 3
  have hnum0 : 0≤(18/25:ℝ)-z := by linarith [hz.2]
  have hnum := mul_le_mul_of_nonneg_right hR.2
    (mul_nonneg (by norm_num : (0:ℝ)≤(18/25)^2) hnum0)
  have hlast : R*integrand (18/25) z≤11/20 := by
    dsimp [integrand]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hN 3)).2
    nlinarith [hz.1]
  exact hm.trans hlast

theorem scaled_gain_short {R r s : ℝ}
    (hR : R∈Icc 0 2) (hr : r∈Icc (117/200 : ℝ) (18/25))
    (hs : s∈Icc 0 (1/5 : ℝ)) : R*gain r (Real.sin s)≤(11/20)*s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hsin : Real.sin s∈Icc 0 (1/5 : ℝ) :=
    ⟨(transport_trig hs').2.2.1,(Real.sin_le hs.1).trans hs.2⟩
  have hmem {z : ℝ} (hz : z∈Icc 0 (1/5 : ℝ)) : z∈Icc 0 frameCap :=
    ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hh := derivative_reserve
    (f := fun z => -R*gain r z) (df := fun z => -R*integrand r z)
    (k := -(11/20 : ℝ))
    (fun z hz => ((gain_hasDerivAt_u r (hmem hz)).const_mul (-R)).continuousAt.continuousWithinAt)
    (fun z hz => (gain_hasDerivAt_u r (hmem (Ioo_subset_Icc_self hz))).const_mul (-R))
    (fun z hz => by linarith [scaled_integrand_upper hR hr (Ioo_subset_Icc_self hz)])
    (show (0:ℝ)∈Icc 0 (1/5:ℝ) by norm_num) hsin hsin.1
  have hz : gain r 0=0 := by simp [gain,root,shape]
  rw [hz] at hh
  nlinarith [Real.sin_le hs.1]

theorem scaled_gain_cap {R r : ℝ} (hR : R∈Icc 0 2)
    (hr : r∈Icc (117/200 : ℝ) (18/25)) : R*gain r (Real.sin frameCap)≤1 := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hz := sin_mem hh
  have hsl := cap_sin_lower
  have hsu := (transport_trig hh).2.2.2.1
  have hN := root_pos r hz
  have hN2 := root_sq r hz
  have hS := shape_pos r
  have hS2 := shape_sq r
  have hr0 : 0≤r := by linarith [hr.1]
  have hN1 : root r (Real.sin frameCap)≤1 := by
    have hp := mul_nonneg hr0 (show 0≤2*Real.sin frameCap-r by linarith [hr.2])
    nlinarith
  have hS1 : 1≤shape r := by nlinarith [sq_nonneg r]
  have hp := mul_le_mul hr.2 hsu.le hz.1 (by norm_num : (0:ℝ)≤18/25)
  have hn0 : 0≤1-r*Real.sin frameCap := by nlinarith
  have hquot : 1-r*Real.sin frameCap≤(1-r*Real.sin frameCap)/root r (Real.sin frameCap) := by
    apply (le_div_iff₀ hN).2
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hN1)]
  have hinv : 1/shape r≤1 := (div_le_one hS).2 hS1
  have hg : gain r (Real.sin frameCap)≤(18/25)*(6443/10000) := by
    dsimp [gain]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hg hR.1
  nlinarith [hR.2]

theorem coefficient_short {R p a b s : ℝ}
    (hR : R∈Icc 0 2) (ha : 0<a) (hab : a≤b)
    (hplo : (117/200)*b≤p) (hphi : p≤(18/25)*a)
    (hs : s∈Icc 0 (1/5 : ℝ)) :
    normGain R p b s-normGain R p a s≤(11/20)*s*(b-a) := by
  have hp : 0<p := by nlinarith
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hx (x : ℝ) (hx : x∈Icc a b) : 0<x ∧ p/x∈Icc (117/200 : ℝ) (18/25) := by
    have hxp : 0<x := ha.trans_le hx.1
    refine ⟨hxp,⟨(le_div_iff₀ hxp).2 ?_,(div_le_iff₀ hxp).2 ?_⟩⟩ <;>
      nlinarith [hx.1,hx.2]
  have hh := derivative_reserve
    (f := fun x => -normGain R p x s)
    (df := fun x => -(R*gain (p/x) (Real.sin s))) (k := -(11/20)*s)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x hxx).1 hs').neg.continuousAt.continuousWithinAt)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs').neg)
    (fun x hxx => by linarith [scaled_gain_short hR (hx x (Ioo_subset_Icc_self hxx)).2 hs])
    (show a∈Icc a b from ⟨le_rfl,hab⟩) (show b∈Icc a b from ⟨hab,le_rfl⟩) hab
  linarith

theorem coefficient_cap {R p a b : ℝ}
    (hR : R∈Icc 0 2) (ha : 0<a) (hab : a≤b)
    (hplo : (117/200)*b≤p) (hphi : p≤(18/25)*a) :
    normGain R p b frameCap-normGain R p a frameCap≤b-a := by
  have hp : 0<p := by nlinarith
  have hs : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hx (x : ℝ) (hx : x∈Icc a b) : 0<x ∧ p/x∈Icc (117/200 : ℝ) (18/25) := by
    have hxp : 0<x := ha.trans_le hx.1
    refine ⟨hxp,⟨(le_div_iff₀ hxp).2 ?_,(div_le_iff₀ hxp).2 ?_⟩⟩ <;>
      nlinarith [hx.1,hx.2]
  have hh := derivative_reserve
    (f := fun x => -normGain R p x frameCap)
    (df := fun x => -(R*gain (p/x) (Real.sin frameCap))) (k := -1)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x hxx).1 hs).neg.continuousAt.continuousWithinAt)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs).neg)
    (fun x hxx => by linarith [scaled_gain_cap hR (hx x (Ioo_subset_Icc_self hxx)).2])
    (show a∈Icc a b from ⟨le_rfl,hab⟩) (show b∈Icc a b from ⟨hab,le_rfl⟩) hab
  linarith

end SquaresInCircles.Eight.TableFree.SoleNormGain
