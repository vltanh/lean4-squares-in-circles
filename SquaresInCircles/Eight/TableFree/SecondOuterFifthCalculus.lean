module

public import SquaresInCircles.Eight.TableFree.SecondOuterHigherCalculus

/-!
# Fifth derivatives on the complete original outer circle

Uncompiled source draft.  The next circle-ratio derivative is positive
on the entire physical arc.  The literal P coefficients therefore make
its fifth derivative positive, giving a continuous convexity argument
for the third derivative without a curvature table.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def ratioDDDD (b : ℝ) : ℝ :=
  15*Q0*W b*(3*(U b)^2+7*(W b)^2)/(U b)^9

def RoleLabel.d5 (H : RoleLabel) (b : ℝ) : ℝ :=
  -5*H.s*ratioDDD b-(H.p+H.s*b)*ratioDDDD b

lemma ratioDDD_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt ratioDDD (ratioDDDD b) b := by
  have hu := U_positive hb
  have hU := (ShortOuterOne.SameContact.arc_hasDerivAt hb).add_const (1/2)
  have hW := (hasDerivAt_id b).add_const (1/2)
  have hd := (((hU.pow 2).add ((hW.pow 2).const_mul 5)).const_mul
    (3*Q0)).div (hU.pow 7) (pow_ne_zero 7 hu.ne')
  convert hd using 1 <;> dsimp [ratioDDD,ratioDDDD,ratio,U,W] <;>
    field_simp [show arc b+1/2≠0 from hu.ne'] <;> ring

lemma RoleLabel.d4_hasDerivAt (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) : HasDerivAt H.d4 (H.d5 b) b := by
  have hd := ((ratioDD_hasDerivAt hb).const_mul (-4*H.s)).sub
    ((((hasDerivAt_id b).const_mul H.s).const_add H.p).mul
      (ratioDDD_hasDerivAt hb))
  convert hd using 1 <;> dsimp [RoleLabel.d4,RoleLabel.d5] <;> ring

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

lemma P_third_convex : ConvexOn ℝ (Icc 0 outerDiagonal) PLabel.d3 := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal) (fun b => -PLabel.d3 b) :=
    concave_of_deriv2
      (fun b hb => (PLabel.d3_hasDerivAt (outer_domain hb)).neg)
      (fun b hb => (PLabel.d4_hasDerivAt (outer_domain hb)).neg)
      (fun b hb => neg_nonpos.mpr (P_fifth_positive hb).le)
  simpa only [neg_neg] using hc.neg

end SquaresInCircles.Eight.TableFree.SecondWord
