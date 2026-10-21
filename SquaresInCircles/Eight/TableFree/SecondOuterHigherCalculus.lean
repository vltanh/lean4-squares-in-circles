module

public import SquaresInCircles.Eight.TableFree.SecondOuterLabelBounds

/-!
# Higher derivatives and exact curvature references on the outer circle

The fourth derivative is obtained directly from the physical circle
chart.  A reference for the second derivative is affine in its one
positive radical after multiplication by the cube of that radical.
Only rational square comparisons are required at fixed references.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def ratioDDD (b : ℝ) : ℝ :=
  3*Q0*((U b)^2+5*(W b)^2)/(U b)^7

def RoleLabel.d4 (H : RoleLabel) (b : ℝ) : ℝ :=
  -4*H.s*ratioDD b-(H.p+H.s*b)*ratioDDD b

lemma ratioDD_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt ratioDD (ratioDDD b) b := by
  have hu := U_positive hb
  have hd := (((hasDerivAt_id b).add_const (1/2)).const_mul (3*Q0)).div
    (((ShortOuterOne.SameContact.arc_hasDerivAt hb).add_const (1/2)).pow 5)
      (pow_ne_zero 5 hu.ne')
  convert hd using 1 <;> dsimp [ratioDD,ratioDDD,ratio,U,W] <;>
    field_simp [show arc b+1/2≠0 from hu.ne'] <;> ring

lemma RoleLabel.d3_hasDerivAt (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) : HasDerivAt H.d3 (H.d4 b) b := by
  have hd := ((ShortOuterOne.SameContact.ratioD_hasDerivAt hb).const_mul
    (-3*H.s)).sub
      ((((hasDerivAt_id b).const_mul H.s).const_add H.p).mul
        (ratioDD_hasDerivAt hb))
  convert hd using 1 <;> dsimp [RoleLabel.d3,RoleLabel.d4] <;> ring

lemma RoleLabel.second_numerator (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) :
    H.d2 b*(U b)^3=
      2*H.r*(Q0-(W b)^2)*U b-2*H.s*W b*(Q0-(W b)^2)-
        (H.p+H.s*b)*Q0 := by
  have hu := U_positive hb
  have hc := UW_circle hb
  have he : H.d2 b*(U b)^3=
      2*H.r*(U b)^3-2*H.s*W b*(U b)^2-(H.p+H.s*b)*Q0 := by
    dsimp [RoleLabel.d2,ratio,ratioD,U,W]
    field_simp [show arc b+1/2≠0 from hu.ne']
    ring
  rw [he]
  linear_combination (2*H.r*U b-2*H.s*W b)*hc

lemma RoleLabel.fourth_numerator (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) :
    H.d4 b*(U b)^7= -3*Q0*((H.p-H.s/2)*(Q0+4*(W b)^2)+
      5*H.s*Q0*W b) := by
  have hu := U_positive hb
  have hc := UW_circle hb
  have he : H.d4 b*(U b)^7= -3*Q0*(4*H.s*W b*(U b)^2+
      (H.p+H.s*b)*((U b)^2+5*(W b)^2)) := by
    dsimp [RoleLabel.d4,ratioDD,ratioDDD,U,W]
    field_simp [show arc b+1/2≠0 from hu.ne']
    ring
  rw [he]
  dsimp [W] at hc ⊢
  linear_combination -3*Q0*(H.p-H.s/2+5*H.s*(b+1/2))*hc

lemma RoleLabel.second_chart_reference (H : RoleLabel) {b l u dlo dhi : ℝ}
    (hb : b∈Icc 0 outerAxial)
    (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(W b)^2<Q0) (hhi : Q0<u^2+(W b)^2)
    (hdlo : 0<min ((2*H.r-dlo)*(Q0-(W b)^2)*l)
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
  have hcube : (U b)^3=(Q0-(W b)^2)*U b := by nlinarith
  have hlow := affine_min_le (c := (2*H.r-dlo)*(Q0-(W b)^2))
    ⟨hU.1.le,hU.2.le⟩
  have hhigh := affine_le_max (c := (2*H.r-dhi)*(Q0-(W b)^2))
    ⟨hU.1.le,hU.2.le⟩
  have hp3 := pow_pos hp 3
  constructor <;> nlinarith

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
  norm_num [PLabel,Q0] at he hk
  nlinarith

lemma T_fourth_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<TLabel.d4 b := by
  have he := TLabel.fourth_numerator (outer_domain hb)
  have hu := pow_pos (U_positive (outer_domain hb)) 7
  have hk := fourth_kernel_positive hb
  norm_num [TLabel,Q0] at he hk
  nlinarith

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

end SquaresInCircles.Eight.TableFree.SecondWord
