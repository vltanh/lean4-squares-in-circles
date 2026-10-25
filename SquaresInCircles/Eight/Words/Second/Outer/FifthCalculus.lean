module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Words.Second.Outer.HigherCalculus

/-!
# Eight squares: fifth derivatives on the complete original outer circle

The next circle-ratio derivative is positive
on the entire physical arc.  The literal P coefficients therefore make
its fifth derivative positive, giving a continuous convexity argument
for the third derivative without a curvature table.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def ratioDDDD (b : ℝ) : ℝ :=
  15*Q0*W b*(3*(U b)^2+7*(W b)^2)/(U b)^9

def RoleLabel.d5 (H : RoleLabel) (b : ℝ) : ℝ :=
  -5*H.s*ratioDDD b-(H.p+H.s*b)*ratioDDDD b

lemma ratioDDD_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt ratioDDD (ratioDDDD b) b := by
  have hu := U_positive hb
  have hu0 : U b≠0 := hu.ne'
  have hU : HasDerivAt U (-(W b/U b)) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt hb).add_const (1/2)
  have hW : HasDerivAt W 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hU2 : HasDerivAt (fun y => (U y)^2) (((2:ℕ):ℝ)*(U b)^(2-1)*(-(W b/U b))) b := hU.pow 2
  have hW2 : HasDerivAt (fun y => (W y)^2) (((2:ℕ):ℝ)*(W b)^(2-1)*1) b := hW.pow 2
  have hU7 : HasDerivAt (fun y => (U y)^7) (((7:ℕ):ℝ)*(U b)^(7-1)*(-(W b/U b))) b := hU.pow 7
  have hnum : HasDerivAt (fun y => 3*Q0*((U y)^2+5*(W y)^2))
      (3*Q0*(((2:ℕ):ℝ)*(U b)^(2-1)*(-(W b/U b))+5*(((2:ℕ):ℝ)*(W b)^(2-1)*1))) b :=
    (hU2.add (hW2.const_mul 5)).const_mul (3*Q0)
  have hd : HasDerivAt (fun y => 3*Q0*((U y)^2+5*(W y)^2)/(U y)^7)
      ((3*Q0*(((2:ℕ):ℝ)*(U b)^(2-1)*(-(W b/U b))+5*(((2:ℕ):ℝ)*(W b)^(2-1)*1))*(U b)^7-
        3*Q0*((U b)^2+5*(W b)^2)*(((7:ℕ):ℝ)*(U b)^(7-1)*(-(W b/U b))))/((U b)^7)^2) b :=
    hnum.div hU7 (pow_ne_zero 7 hu0)
  refine hd.congr_deriv ?_
  rw [ratioDDDD]
  norm_num
  field_simp
  ring

lemma RoleLabel.d4_hasDerivAt (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) : HasDerivAt H.d4 (H.d5 b) b := by
  have h1 : HasDerivAt (fun y => -4*H.s*ratioDD y) (-4*H.s*ratioDDD b) b :=
    (ratioDD_hasDerivAt hb).const_mul (-4*H.s)
  have h2 : HasDerivAt (fun y => (H.p+H.s*y)*ratioDDD y)
      (H.s*1*ratioDDD b+(H.p+H.s*b)*ratioDDDD b) b :=
    (((hasDerivAt_id' b).const_mul H.s).const_add H.p).mul (ratioDDD_hasDerivAt hb)
  refine (h1.sub h2).congr_deriv ?_
  unfold RoleLabel.d5
  ring

lemma ratioDDD_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<ratioDDD b := by
  have hu := U_positive (outer_domain hb)
  have hu2 := sq_pos_of_pos hu
  dsimp [ratioDDD]
  exact div_pos (mul_pos (by norm_num [Q0])
    (by nlinarith [sq_nonneg (W b)])) (pow_pos hu 7)

lemma ratioDDDD_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<ratioDDDD b := by
  have hu := U_positive (outer_domain hb)
  have hw : 0<W b := by dsimp [W]; linarith [hb.1]
  have hu2 := sq_pos_of_pos hu
  dsimp [ratioDDDD]
  exact div_pos (mul_pos (mul_pos (by norm_num [Q0]) hw)
    (by nlinarith [sq_nonneg (W b)])) (pow_pos hu 9)

lemma P_fifth_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<PLabel.d5 b := by
  have hp := ratioDDD_positive hb
  have hq := mul_nonneg hb.1 (ratioDDDD_positive hb).le
  norm_num [RoleLabel.d5,PLabel]
  nlinarith

end SquaresInCircles.Eight.SecondWord
