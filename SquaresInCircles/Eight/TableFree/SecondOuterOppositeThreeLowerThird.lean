module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerInverse

/-!
# Exact third derivatives of the lower inverse rotation

The source second derivative is a cubic in the positive speed quotient.
Differentiating that identity gives the five-term expression used on
each complete analytic minimum regime.  No estimate enters these
differential identities.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerInverse
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def factorDD (u : ℝ) : ℝ :=
  2*Q0/((Q0+1)*u^3)+8*(Q0-1)/((Q0+1)*(q u)^3)
def X (y : ℝ) : ℝ := -ratioD y*factorD (U y)+(ratio y)^2*factorDD (U y)
def A1 (y : ℝ) : ℝ :=
  9*ratio y*ratioD y/(q (U y))^2-15*(ratio y)^3/(q (U y))^3-ratioDD y/q (U y)
def A3 (y : ℝ) : ℝ :=
  3*ratio y*ratioD y/(q (U y))^2-10*(ratio y)^3/(q (U y))^3
def quotient (z y : ℝ) : ℝ := z/speed z y
def third (z y : ℝ) : ℝ := X y+A1 y*quotient z y+A3 y*(quotient z y)^3-
  3*(ratio y)^3/(q (U y))^3*(quotient z y)^5

lemma factorD_hasDerivAt {u : ℝ} (hu : u≠0) (hq : q u≠0) :
    HasDerivAt factorD (factorDD u) u := by
  have hnum : HasDerivAt NegativeTwo.Inverse.N (4*Q0-4*u) u := by
    have h := (((hasDerivAt_id' (x := u)).const_mul (4*Q0)).fun_sub
      (((hasDerivAt_id' (x := u)).fun_pow 2).const_mul 2)).sub_const (Q0*(Q0+1))
    refine h.congr_deriv ?_
    push_cast
    ring
  have hqd := NegativeTwo.Inverse.q_hasDerivAt u
  have hq' : NegativeTwo.Inverse.q u≠0 := hq
  have hden := ((hasDerivAt_id' (x := u)).fun_pow 2).fun_mul (hqd.fun_pow 2)
  have hd := hnum.fun_div hden (mul_ne_zero (pow_ne_zero 2 hu) (pow_ne_zero 2 hq'))
  refine hd.congr_deriv ?_
  simp only [factorDD,q,NegativeTwo.Inverse.q,NegativeTwo.Inverse.N] at hq' ⊢
  have hQ1 : Q0+1≠0 := by norm_num [Q0]
  rw [div_add_div _ _ (mul_ne_zero hQ1 (pow_ne_zero 3 hu)) (mul_ne_zero hQ1 (pow_ne_zero 3 hq')),
    div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (pow_ne_zero 2 hu) (pow_ne_zero 2 hq')))
      (mul_ne_zero (mul_ne_zero hQ1 (pow_ne_zero 3 hu)) (mul_ne_zero hQ1 (pow_ne_zero 3 hq')))]
  simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one,mul_one]
  ring

lemma factorDD_positive {u : ℝ} (hu : 0<u) (hq : 0<q u) : 0<factorDD u := by
  have hQ : (0:ℝ)<Q0 ∧ 0<Q0-1 ∧ 0<Q0+1 := by norm_num [Q0]
  have h1 : 0<2*Q0/((Q0+1)*u^3) := div_pos (by linarith [hQ.1]) (mul_pos hQ.2.2 (pow_pos hu 3))
  have h2 : 0<8*(Q0-1)/((Q0+1)*(q u)^3) :=
    div_pos (by linarith [hQ.2.1]) (mul_pos hQ.2.2 (pow_pos hq 3))
  simp only [factorDD]
  linarith

lemma quotient_hasDerivAt {z y : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (quotient z) (-z*ratio y/(speed z y)^3) y := by
  have hv := (OppositeTwo.PrimaryInverse.data hy hz).2.2.1
  convert (hasDerivAt_const y z).div (speed_source_hasDerivAt hy hz) hv.ne' using 1
  · rfl
  · field_simp [hv.ne']
    ring

lemma second_cubic {z y : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    second z y= -ratio y*factorD (U y)+(ratio y)^2/(q (U y))^2*(quotient z y)^3+
      (3*(ratio y)^2/(q (U y))^2-ratioD y/q (U y))*quotient z y := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hu := U_positive (outer_domain hy)
  have hq : q (U y)≠0 := by linarith [NegativeTwo.Inverse.actual_q_positive hy]
  have hn : q (U y)=z^2+(speed z y)^2 := hh.2.2.2.symm
  dsimp [second,quotient,NegativeTwo.Inverse.brace]
  change -ratio y*factorD (U y)-z/(q (U y)*speed z y)*
    (ratioD y-2*(ratio y)^2/q (U y)-(ratio y)^2/(speed z y)^2)=_
  field_simp [hq,hh.2.2.1.ne']
  rw [hn]
  ring

lemma second_source_hasDerivAt {z y : ℝ} (hy : y∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (second z) (third z y) y := by
  have hh := OppositeTwo.PrimaryInverse.data hy hz
  have hu := U_positive (outer_domain hy)
  have hq : q (U y)≠0 := by linarith [NegativeTwo.Inverse.actual_q_positive hy]
  have hv : 0<speed z y := hh.2.2.1
  have hn : q (U y)=z^2+(speed z y)^2 := hh.2.2.2.symm
  have hU : HasDerivAt U (-ratio y) y :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hy)).add_const (1/2)
  have hqD : HasDerivAt (fun t => q (U t)) (2*ratio y) y :=
    ((NegativeTwo.Inverse.q_hasDerivAt (U y)).comp y hU).congr_deriv (by ring)
  have hrD := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hy)
  have hrDD := ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hy)
  have hvD := speed_source_hasDerivAt hy hz
  have hfD : HasDerivAt (fun t => factorD (U t)) (-(factorDD (U y)*ratio y)) y :=
    ((factorD_hasDerivAt hu.ne' hq).comp y hU).congr_deriv (by ring)
  have hr2 : HasDerivAt (fun t => ratio t^2) (2*ratio y*ratioD y) y :=
    (hrD.fun_pow 2).congr_deriv (by push_cast; ring)
  have hv2 : HasDerivAt (fun t => speed z t^2) (2*ratio y) y :=
    (hvD.fun_pow 2).congr_deriv (by have hv' := hv.ne'; field_simp; ring)
  have hbr := (hrDD.fun_sub ((hr2.const_mul 2).fun_div hqD hq)).fun_sub
    (hr2.fun_div hv2 (pow_ne_zero 2 hv.ne'))
  have hweight := (hasDerivAt_const y z).fun_div (hqD.fun_mul hvD) (mul_ne_zero hq hv.ne')
  have hd := (hrD.fun_mul hfD).neg.fun_sub (hweight.fun_mul hbr)
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · simp only [third,X,A1,A3,quotient]
    rw [hn] at hq ⊢
    have hv' := hv.ne'
    field_simp
    ring
  · simp only [second,NegativeTwo.Inverse.brace,Pi.neg_apply]
    rw [show ratioD t=Q0/(U t)^3 from rfl]
    ring

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerInverse
