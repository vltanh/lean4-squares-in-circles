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
  have hw := (hasDerivAt_id b).add_const (1/2)
  have hd := (((hw.const_mul (5*Q0)).sub_const (Q0/2)).sub
    ((hw.pow 2).const_mul 2)).div
      (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const
        (1/2)).pow 7) (pow_ne_zero 7 hu.ne')
  convert hd using 1 <;> dsimp [fourthKernel,fourthKernelD,U,W,ratio] <;>
    field_simp [show arc b+1/2≠0 from hu.ne'] <;> ring

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
  apply (mul_right_cancel₀ (pow_ne_zero 7 hu.ne'))
  dsimp [fourthKernel]
  field_simp [pow_ne_zero 7 hu.ne']
  norm_num [PLabel] at he
  nlinarith

lemma T_fourth_kernel {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    TLabel.d4 b=3*Q0*(95769/100000)*fourthKernel b := by
  have hu := U_positive (outer_domain hb)
  have he := TLabel.fourth_numerator (outer_domain hb)
  apply (mul_right_cancel₀ (pow_ne_zero 7 hu.ne'))
  dsimp [fourthKernel]
  field_simp [pow_ne_zero 7 hu.ne']
  norm_num [TLabel] at he
  nlinarith

theorem target_fourth_dominates {b B : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) (h : b≤B) :
    8*PLabel.d4 b<TLabel.d4 B := by
  have hm := fourthKernel_monotone hb hB h
  have hp := fourthKernel_positive hb
  rw [P_fourth_kernel hb,T_fourth_kernel hB]
  norm_num [Q0]
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord
