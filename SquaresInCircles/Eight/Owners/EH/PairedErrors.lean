module

public import SquaresInCircles.Eight.Owners.EH.Support

/-!
# Eight squares: opposed errors use one original intermediate circle

The common state receives both forces before its circle is supported.
The positive residual has the usual full-circle cost; the negative
residual has the primary-lower-bound cost.  This supplies the complete
remaining three-error reserve for either original HG secondary.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalEH

open FramePair ZeroPrimary GlobalZeroSign GlobalOuterAnchor

theorem one_sub_cos_le_half_sin {z : ℝ} (hz : z∈Icc 0 frameCap) :
    1-Real.cos z≤(1/2)*Real.sin z := by
  have hc := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hs := Real.sin_ge_sub_cube hz.1
  have hz2 : z≤7/10 := hz.2
  have h2 : z^2≤(7/10)*z := by
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz2)]
  have h3 : z^3≤(49/100)*z := by
    have hh := mul_le_mul_of_nonneg_left h2 hz.1
    nlinarith
  nlinarith

theorem cosine_sine_residual {z t : ℝ}
    (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) :
    1+Real.sin (t-z)≤Real.cos z+Real.sin t := by
  have tz := transport_trig hz
  have tt := transport_trig ht
  have hsmall := one_sub_cos_le_half_sin hz
  have h1 := mul_nonneg (show 0≤Real.cos t-1/2 by linarith [tt.1]) tz.2.2.1
  have h2 := mul_nonneg (sub_nonneg.mpr tz.2.1) tt.2.2.1
  rw [Real.sin_sub]
  nlinarith

theorem residual_norm {z t : ℝ}
    (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) (hzt : z≤t) :
    Real.sqrt ((Real.sin t-Real.sin z)^2+(Real.cos z-Real.cos t)^2)=
      2*Real.sin ((t-z)/2) := by
  have hh : (t-z)/2∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc] at hz ht ⊢
    constructor <;> linarith [ht.2,hz.1]
  have tr := transport_trig hh
  have hunitT := Real.sin_sq_add_cos_sq t
  have hunitZ := Real.sin_sq_add_cos_sq z
  have hunitH := Real.sin_sq_add_cos_sq ((t-z)/2)
  have hsub := Real.cos_sub t z
  have hdouble : Real.cos (t-z)=2*(Real.cos ((t-z)/2))^2-1 := by
    have hh := Real.cos_two_mul ((t-z)/2)
    rwa [show 2*((t-z)/2)=t-z by ring] at hh
  have hid : (Real.sin t-Real.sin z)^2+(Real.cos z-Real.cos t)^2=
      (2*Real.sin ((t-z)/2))^2 := by
    linear_combination hunitT+hunitZ+2*hsub-2*hdouble-4*hunitH
  have hp : 0≤2*Real.sin ((t-z)/2) := mul_nonneg (by norm_num) tr.2.2.1
  rw [hid,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]

theorem paired_nonnegative (s : State) {z t : ℝ}
    (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) (hzt : z≤t) :
    positiveCost (t-z)≤zeroError s (-z)+primaryError s t := by
  have tz := transport_trig hz
  have tt := transport_trig ht
  have hs := state_support s (Real.sin t-Real.sin z) (Real.cos z-Real.cos t)
  rw [residual_norm hz ht hzt] at hs
  have hangle := cosine_sine_residual hz ht
  dsimp [zeroError,primaryError,positiveCost,GlobalOuterAnchor.width,lam]
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg tz.2.2.1,
    abs_of_nonneg tt.2.2.1]
  nlinarith

def pairedBase (w u : ℝ) : ℝ :=
  ((Real.sin (u+w)+Real.cos (u+w)-1)+(Real.sin u+Real.cos u-1))/2+
    primaryLower*(Real.sin (u+w)-Real.sin u)

def pairedBaseDerivative (w u : ℝ) : ℝ :=
  ((1+2*primaryLower)*Real.cos (u+w)+(1-2*primaryLower)*Real.cos u-
    Real.sin (u+w)-Real.sin u)/2

theorem pairedBase_derivative (w u : ℝ) :
    HasDerivAt (pairedBase w) (pairedBaseDerivative w u) u := by
  have hsin := ((hasDerivAt_id u).add_const w).sin
  have hcos := ((hasDerivAt_id u).add_const w).cos
  convert ((((hsin.add hcos).sub_const 1).add
    (((Real.hasDerivAt_sin u).add (Real.hasDerivAt_cos u)).sub_const 1)).div_const 2).add
      ((hsin.sub (Real.hasDerivAt_sin u)).const_mul primaryLower) using 1
  · rfl
  · dsimp [pairedBaseDerivative]
    ring

theorem pairedBase_at_zero {w t : ℝ} (hw : 0≤w) (ht : 0≤t)
    (hsum : t+w≤frameCap) : pairedBase w 0≤pairedBase w t := by
  have hsum' : t+w≤7/10 := hsum
  have hm : MonotoneOn (pairedBase w) (Icc 0 t) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun u _ => (pairedBase_derivative w u).continuousAt.continuousWithinAt
    · intro u _
      exact pairedBase_derivative w u
    · intro u hu
      have hU : u∈Icc 0 frameCap := ⟨hu.1.le,by simp only [frameCap]; linarith [hu.2]⟩
      have hUW : u+w∈Icc 0 frameCap :=
        ⟨by linarith [hu.1],by simp only [frameCap]; linarith [hu.2]⟩
      have tr := transport_trig hU
      have trw := transport_trig hUW
      have h1 := mul_nonneg
        (show 0≤Real.cos (u+w)-191/250 by linarith [trw.1])
        (show 0≤1+2*primaryLower by norm_num [primaryLower])
      have h2 := mul_nonneg (sub_nonneg.mpr tr.2.1)
        (show 0≤2*primaryLower-1 by norm_num [primaryLower])
      dsimp [pairedBaseDerivative,primaryLower] at *
      linarith [tr.2.2.2.1,trw.2.2.2.1]
  exact hm ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩ ht

theorem paired_nonpositive (s : State) {z t : ℝ}
    (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) (htz : t≤z) :
    negativeCost (z-t)≤zeroError s (-z)+primaryError s t := by
  have tz := transport_trig hz
  have tt := transport_trig ht
  have hsin : Real.sin t≤Real.sin z :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [ht.1,Real.pi_pos])
      (by dsimp [frameCap] at hz; linarith [hz.2,Real.pi_gt_three]) htz
  have hcos : Real.cos z≤Real.cos t :=
    Real.cos_le_cos_of_nonneg_of_le_pi ht.1
      (by dsimp [frameCap] at hz; linarith [hz.2,Real.pi_gt_three]) htz
  have ha := mul_le_mul_of_nonpos_right (primary_lower s).le (sub_nonpos.mpr hsin)
  have hb := mul_nonpos_of_nonneg_of_nonpos s.b_nonneg (sub_nonpos.mpr hcos)
  have hbase := pairedBase_at_zero (show 0≤z-t by linarith) ht.1
    (show t+(z-t)≤frameCap by linarith [hz.2])
  have hid : t+(z-t)=z := by ring
  simp only [pairedBase,zero_add,Real.sin_zero,Real.cos_zero,hid] at hbase
  dsimp [negativeCost,zeroError,primaryError,GlobalOuterAnchor.width,lam]
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg tz.2.2.1,
    abs_of_nonneg tt.2.2.1]
  nlinarith

theorem paired_reserve (s u : State) {r z t : ℝ}
    (hr : r∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap)
    (hspan : |r+t-z|≤frameCap) :
    11/4<pathBase+primaryError u r+zeroError s (-z)+primaryError s t+
      (9/50)*frameCost |r+t-z| := by
  have hrCost := primaryError_positive u hr
  by_cases hzt : z≤t
  · have hs : t-z∈Icc 0 frameCap := by
      simp only [frameCap,mem_Icc] at hz ht ⊢
      constructor <;> linarith [ht.2,hz.1]
    have hp := paired_nonnegative s hz ht hzt
    have hrBound := positiveCost_lower hr
    have hsBound := positiveCost_lower hs
    have htotal : r+t-z∈Icc 0 frameCap :=
      ⟨by linarith [hr.1],(le_abs_self _).trans hspan⟩
    have hh := augmentation_lower htotal
    rw [abs_of_nonneg htotal.1]
    dsimp [pathBase,frameCap] at *
    linarith [htotal.1,htotal.2]
  · have htz : t≤z := le_of_not_ge hzt
    have hw : z-t∈Icc 0 frameCap := by
      simp only [frameCap,mem_Icc] at hz ht ⊢
      constructor <;> linarith [hz.2,ht.1]
    have hp := paired_nonpositive s hz ht htz
    have hh := two_cost_reserve hr hw
    have hid : r-(z-t)=r+t-z := by ring
    rw [hid] at hh
    linarith

def remainingCost (h g : State) (zeroTarget : Bool) (r v t : ℝ) : ℝ :=
  primaryError h r+zeroError (if zeroTarget then h else g) v+primaryError g t

/-- Every surviving primary-error sign and either original zero owner
are covered on their full intrinsic frame domain. -/
theorem remaining_reserve (h g : State) (zeroTarget : Bool) {r v t : ℝ}
    (hr : r∈Icc 0 frameCap) (hv : |v|≤frameCap) (ht : t∈Icc 0 frameCap)
    (hspan : |r+v+t|≤frameCap) :
    11/4<pathBase+remainingCost h g zeroTarget r v t+(9/50)*frameCost |r+v+t| := by
  by_cases hvpos : 0≤v
  · have hvframe : v∈Icc 0 frameCap := ⟨hvpos,(le_abs_self v).trans hv⟩
    have hsum : r+v+t∈Icc 0 frameCap :=
      ⟨by linarith [hr.1,ht.1],(le_abs_self _).trans hspan⟩
    have hH := (positiveCost_lower hr).trans (primaryError_positive h hr)
    have hG := (positiveCost_lower ht).trans (primaryError_positive g ht)
    have hZ := (positiveCost_lower hvframe).trans
      (zeroError_positive (if zeroTarget then h else g) hvframe)
    have hreturn := augmentation_lower hsum
    rw [abs_of_nonneg hsum.1]
    dsimp [remainingCost,pathBase,frameCap] at *
    linarith [hsum.1,hsum.2]
  · have hz : -v∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs v).trans hv⟩
    cases zeroTarget
    · have hid : r+t-(-v)=r+v+t := by ring
      have hh := paired_reserve g h hr hz ht (by simpa only [hid] using hspan)
      rw [hid] at hh
      simp only [remainingCost,neg_neg,Bool.false_eq_true,↓reduceIte] at hh ⊢
      linarith
    · have hid : t+r-(-v)=r+v+t := by ring
      have hh := paired_reserve h g ht hz hr (by simpa only [hid] using hspan)
      rw [hid] at hh
      simp only [neg_neg] at hh
      dsimp [remainingCost]
      linarith

end SquaresInCircles.Eight.GlobalEH
