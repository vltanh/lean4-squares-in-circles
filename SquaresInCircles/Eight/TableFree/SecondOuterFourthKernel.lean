module

public import SquaresInCircles.Eight.TableFree.SecondOuterHigherCalculus

/-!
# The increasing fourth-derivative kernel of the two outer labels

The labels `P` and `T` have the same positive fourth-derivative kernel.
Its derivative has a positive numerator on the full physical outer arc.
This comparison is used on a contact which moves the target coordinate
strictly beyond the source coordinate.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def fourthKernel (b : ℝ) : ℝ :=
  (5*Q0*W b-Q0/2-2*(W b)^2)/(U b)^7

def fourthKernelD (b : ℝ) : ℝ :=
  ((5*Q0-4*W b)*(U b)^2+
    7*W b*(5*Q0*W b-Q0/2-2*(W b)^2))/(U b)^9

lemma fourthKernel_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt fourthKernel (fourthKernelD b) b := by
  have hu := U_positive (outer_domain hb)
  have hu0 : U b≠0 := hu.ne'
  have hU : HasDerivAt U (-(W b/U b)) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hW : HasDerivAt W 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hW2 : HasDerivAt (fun y => (W y)^2) (((2:ℕ):ℝ)*(W b)^(2-1)*1) b := hW.pow 2
  have hU7 : HasDerivAt (fun y => (U y)^7) (((7:ℕ):ℝ)*(U b)^(7-1)*(-(W b/U b))) b := hU.pow 7
  have hnum : HasDerivAt (fun y => 5*Q0*W y-Q0/2-2*(W y)^2)
      (5*Q0*1-2*(((2:ℕ):ℝ)*(W b)^(2-1)*1)) b :=
    ((hW.const_mul (5*Q0)).sub_const (Q0/2)).sub (hW2.const_mul 2)
  have hd : HasDerivAt (fun y => (5*Q0*W y-Q0/2-2*(W y)^2)/(U y)^7)
      (((5*Q0*1-2*(((2:ℕ):ℝ)*(W b)^(2-1)*1))*(U b)^7-
        (5*Q0*W b-Q0/2-2*(W b)^2)*(((7:ℕ):ℝ)*(U b)^(7-1)*(-(W b/U b))))/((U b)^7)^2) b :=
    hnum.div hU7 (pow_ne_zero 7 hu0)
  refine hd.congr_deriv ?_
  rw [fourthKernelD]
  norm_num
  field_simp
  ring

lemma fourthKernelD_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<fourthKernelD b := by
  have hu := U_positive (outer_domain hb)
  have hc := UW_circle (outer_domain hb)
  have hw := (UW_bounds hb).2.2
  have he : (5*Q0-4*W b)*(U b)^2+
      7*W b*(5*Q0*W b-Q0/2-2*(W b)^2)=
      5*Q0*(Q0-(3/2)*W b)+10*(W b)^2*(3*Q0-W b) := by
    linear_combination (5*Q0-4*W b)*hc
  have hfirst : 0<Q0-(3/2)*W b := by norm_num [Q0]; linarith [hw.2]
  have hlast : 0<3*Q0-W b := by norm_num [Q0]; linarith [hw.2]
  have hq : 0<Q0 := by norm_num [Q0]
  dsimp [fourthKernelD]
  rw [he]
  positivity

lemma fourthKernel_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<fourthKernel b :=
  div_pos (fourth_kernel_positive hb) (pow_pos (U_positive (outer_domain hb)) 7)

lemma fourthKernel_monotone : MonotoneOn fourthKernel (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (fourthKernel_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun b hb => fourthKernel_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun b hb => (fourthKernelD_positive (Ioo_subset_Icc_self hb)).le)

lemma P_fourth_kernel {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    PLabel.d4 b=3*Q0*(2211/20000)*fourthKernel b := by
  have hu := U_positive (outer_domain hb)
  have he := PLabel.fourth_numerator (outer_domain hb)
  have hval : -3*Q0*((PLabel.p-PLabel.s/2)*(Q0+4*(W b)^2)+5*PLabel.s*Q0*W b)=
      3*Q0*(2211/20000)*(5*Q0*W b-Q0/2-2*(W b)^2) := by
    simp only [PLabel]
    ring
  rw [hval] at he
  rw [eq_div_of_mul_eq (pow_ne_zero 7 hu.ne') he,fourthKernel]
  ring

lemma T_fourth_kernel {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    TLabel.d4 b=3*Q0*(95769/100000)*fourthKernel b := by
  have hu := U_positive (outer_domain hb)
  have he := TLabel.fourth_numerator (outer_domain hb)
  have hval : -3*Q0*((TLabel.p-TLabel.s/2)*(Q0+4*(W b)^2)+5*TLabel.s*Q0*W b)=
      3*Q0*(95769/100000)*(5*Q0*W b-Q0/2-2*(W b)^2) := by
    simp only [TLabel]
    ring
  rw [hval] at he
  rw [eq_div_of_mul_eq (pow_ne_zero 7 hu.ne') he,fourthKernel]
  ring

theorem target_fourth_dominates {b B : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) (h : b≤B) :
    8*PLabel.d4 b<TLabel.d4 B := by
  have hm := fourthKernel_monotone hb hB h
  have hp := fourthKernel_positive hb
  rw [P_fourth_kernel hb,T_fourth_kernel hB]
  norm_num [Q0]
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord
