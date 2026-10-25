module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Words.Second.Outer.LabelCalculus

/-!
# Eight squares: higher derivatives and exact curvature references on the outer circle

The fourth derivative is obtained directly from the physical circle
chart.  A reference for the second derivative is affine in its one
positive radical after multiplication by the cube of that radical.
Only rational square comparisons are required at fixed references.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def ratioDDD (b : ℝ) : ℝ :=
  3*Q0*((U b)^2+5*(W b)^2)/(U b)^7

def RoleLabel.d4 (H : RoleLabel) (b : ℝ) : ℝ :=
  -4*H.s*ratioDD b-(H.p+H.s*b)*ratioDDD b

lemma ratioDD_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt ratioDD (ratioDDD b) b := by
  have hu := U_positive hb
  have hu0 : U b≠0 := hu.ne'
  have hU : HasDerivAt U (-(W b/U b)) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt hb).add_const (1/2)
  have hW : HasDerivAt W 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hU5 : HasDerivAt (fun y => (U y)^5) (((5:ℕ):ℝ)*(U b)^(5-1)*(-(W b/U b))) b := hU.pow 5
  have hd : HasDerivAt (fun y => 3*Q0*W y/(U y)^5)
      ((3*Q0*1*(U b)^5-3*Q0*W b*(((5:ℕ):ℝ)*(U b)^(5-1)*(-(W b/U b))))/((U b)^5)^2) b :=
    (hW.const_mul (3*Q0)).div hU5 (pow_ne_zero 5 hu0)
  refine hd.congr_deriv ?_
  rw [ratioDDD]
  norm_num
  field_simp

lemma RoleLabel.d3_hasDerivAt (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) : HasDerivAt H.d3 (H.d4 b) b := by
  have h1 : HasDerivAt (fun y => -3*H.s*ratioD y) (-3*H.s*ratioDD b) b :=
    (ShortOuterOne.SameContact.ratioD_hasDerivAt hb).const_mul (-3*H.s)
  have h2 : HasDerivAt (fun y => (H.p+H.s*y)*ratioDD y)
      (H.s*1*ratioDD b+(H.p+H.s*b)*ratioDDD b) b :=
    (((hasDerivAt_id' b).const_mul H.s).const_add H.p).mul (ratioDD_hasDerivAt hb)
  refine (h1.sub h2).congr_deriv ?_
  unfold RoleLabel.d4
  ring

lemma RoleLabel.second_numerator (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) :
    H.d2 b*(U b)^3=
      2*H.r*(Q0-(W b)^2)*U b-2*H.s*W b*(Q0-(W b)^2)-
        (H.p+H.s*b)*Q0 := by
  have hu := U_positive hb
  have hu0 : U b≠0 := hu.ne'
  have hc := UW_circle hb
  have hr : ratio b=W b/U b := rfl
  have hD : ratioD b=Q0/(U b)^3 := rfl
  have he : H.d2 b*(U b)^3=
      2*H.r*(U b)^3-2*H.s*W b*(U b)^2-(H.p+H.s*b)*Q0 := by
    rw [RoleLabel.d2,hr,hD]
    field_simp
  rw [he]
  linear_combination (2*H.r*U b-2*H.s*W b)*hc

lemma RoleLabel.fourth_numerator (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) :
    H.d4 b*(U b)^7= -3*Q0*((H.p-H.s/2)*(Q0+4*(W b)^2)+
      5*H.s*Q0*W b) := by
  have hu := U_positive hb
  have hu0 : U b≠0 := hu.ne'
  have hc := UW_circle hb
  have hDD : ratioDD b=3*Q0*(W b)/(U b)^5 := rfl
  have he : H.d4 b*(U b)^7= -3*Q0*(4*H.s*W b*(U b)^2+
      (H.p+H.s*b)*((U b)^2+5*(W b)^2)) := by
    rw [RoleLabel.d4,hDD,ratioDDD]
    field_simp
    ring
  rw [he]
  simp only [W] at hc ⊢
  linear_combination -3*Q0*(H.p-H.s/2+5*H.s*(b+1/2))*hc

lemma RoleLabel.second_chart_reference (H : RoleLabel) {b l u dlo dhi : ℝ}
    (hb : b∈Icc 0 outerAxial)
    (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(W b)^2<Q0) (hhi : Q0<u^2+(W b)^2)
    (hdlo : 0< min ((2*H.r-dlo)*(Q0-(W b)^2)*l)
      ((2*H.r-dlo)*(Q0-(W b)^2)*u)-
        2*H.s*W b*(Q0-(W b)^2)-(H.p+H.s*b)*Q0)
    (hdhi : max ((2*H.r-dhi)*(Q0-(W b)^2)*l)
      ((2*H.r-dhi)*(Q0-(W b)^2)*u)-
        2*H.s*W b*(Q0-(W b)^2)-(H.p+H.s*b)*Q0<0) :
    dlo<H.d2 b ∧ H.d2 b<dhi := by
  have hU := shifted_chart_reference hb hl hu hlo hhi
  have hp := U_positive hb
  have hc := UW_circle hb
  have he := H.second_numerator hb
  have hcube : (U b)^3=(Q0-(W b)^2)*U b := by
    rw [← hc]
    ring
  have hlow := affine_min_le (c := (2*H.r-dlo)*(Q0-(W b)^2))
    ⟨hU.1.le,hU.2.le⟩
  have hhigh := affine_le_max (c := (2*H.r-dhi)*(Q0-(W b)^2))
    ⟨hU.1.le,hU.2.le⟩
  have hp3 := pow_pos hp 3
  constructor
  · have hkey : 0<(H.d2 b-dlo)*(U b)^3 := by
      have hh : (H.d2 b-dlo)*(U b)^3=(2*H.r-dlo)*(Q0-(W b)^2)*U b-
          2*H.s*W b*(Q0-(W b)^2)-(H.p+H.s*b)*Q0 := by
        rw [sub_mul,he,hcube]
        ring
      rw [hh]
      linarith
    linarith [pos_of_mul_pos_left hkey hp3.le]
  · have hkey : 0<(dhi-H.d2 b)*(U b)^3 := by
      have hh : (dhi-H.d2 b)*(U b)^3= -((2*H.r-dhi)*(Q0-(W b)^2)*U b-
          2*H.s*W b*(Q0-(W b)^2)-(H.p+H.s*b)*Q0) := by
        rw [sub_mul,he,hcube]
        ring
      rw [hh]
      linarith
    linarith [pos_of_mul_pos_left hkey hp3.le]

lemma fourth_kernel_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<5*Q0*W b-Q0/2-2*(W b)^2 := by
  have hw := (UW_bounds hb).2.2
  have hsq : (W b)^2<(7/5:ℝ)^2 := by nlinarith
  norm_num [Q0]
  nlinarith

lemma P_fourth_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<PLabel.d4 b := by
  have he := PLabel.fourth_numerator (outer_domain hb)
  have hu := pow_pos (U_positive (outer_domain hb)) 7
  have hk := fourth_kernel_positive hb
  have hQ : (0:ℝ)<Q0 := by norm_num [Q0]
  have hval : -3*Q0*((PLabel.p-PLabel.s/2)*(Q0+4*(W b)^2)+5*PLabel.s*Q0*W b)=
      3*Q0*(11055/100000)*(5*Q0*W b-Q0/2-2*(W b)^2) := by
    simp only [PLabel]
    ring
  have hpos : 0<PLabel.d4 b*(U b)^7 := by
    rw [he,hval]
    exact mul_pos (by positivity) hk
  exact pos_of_mul_pos_left hpos hu.le

lemma T_fourth_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<TLabel.d4 b := by
  have he := TLabel.fourth_numerator (outer_domain hb)
  have hu := pow_pos (U_positive (outer_domain hb)) 7
  have hk := fourth_kernel_positive hb
  have hQ : (0:ℝ)<Q0 := by norm_num [Q0]
  have hval : -3*Q0*((TLabel.p-TLabel.s/2)*(Q0+4*(W b)^2)+5*TLabel.s*Q0*W b)=
      3*Q0*(95769/100000)*(5*Q0*W b-Q0/2-2*(W b)^2) := by
    simp only [TLabel]
    ring
  have hpos : 0<TLabel.d4 b*(U b)^7 := by
    rw [he,hval]
    exact mul_pos (by positivity) hk
  exact pos_of_mul_pos_left hpos hu.le

lemma P_third_monotone : MonotoneOn PLabel.d3 (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (PLabel.d3_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => PLabel.d3_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (P_fourth_positive (Ioo_subset_Icc_self hb)).le)

lemma T_third_monotone : MonotoneOn TLabel.d3 (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (TLabel.d3_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => TLabel.d3_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (T_fourth_positive (Ioo_subset_Icc_self hb)).le)

end SquaresInCircles.Eight.SecondWord
