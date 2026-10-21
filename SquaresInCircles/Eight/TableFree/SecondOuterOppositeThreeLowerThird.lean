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
    convert (((hasDerivAt_id u).const_mul (4*Q0)).sub
      (((hasDerivAt_id u).pow 2).const_mul 2)).sub_const (Q0*(Q0+1))
        using 1 <;> dsimp [NegativeTwo.Inverse.N] <;> ring
  have hd := hnum.div (((hasDerivAt_id u).pow 2).mul
    ((NegativeTwo.Inverse.q_hasDerivAt u).pow 2))
      (mul_ne_zero (pow_ne_zero 2 hu) (pow_ne_zero 2 hq))
  convert hd using 1
  · rfl
  · dsimp [factorDD,NegativeTwo.Inverse.N]
    field_simp [hu,hq,show Q0+1≠0 by norm_num [Q0]]
    dsimp [q,NegativeTwo.Inverse.q]
    ring

lemma factorDD_positive {u : ℝ} (hu : 0<u) (hq : 0<q u) : 0<factorDD u := by
  dsimp [factorDD]
  have hQ : 0<Q0 ∧ 0<Q0-1 ∧ 0<Q0+1 := by norm_num [Q0]
  positivity

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
  have hU := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hy)).add_const (1/2)
  have hqD := (NegativeTwo.Inverse.q_hasDerivAt (U y)).comp y hU
  have hrD := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hy)
  have hrDD := ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hy)
  have hvD := speed_source_hasDerivAt hy hz
  have hfD := (factorD_hasDerivAt hu.ne' hq).comp y hU
  have hbr := ((hrDD.sub
    (((hrD.pow 2).const_mul 2).div hqD hq)).sub
      ((hrD.pow 2).div (hvD.pow 2) (pow_ne_zero 2 hh.2.2.1.ne')))
  have hweight := (hasDerivAt_const y z).div (hqD.mul hvD) (mul_ne_zero hq hh.2.2.1.ne')
  have hd := (hrD.mul hfD).neg.sub (hweight.mul hbr)
  convert hd using 1
  · funext t
    dsimp [second,NegativeTwo.Inverse.brace,ratioD]
    rfl
  · have hn : q (U y)=z^2+(speed z y)^2 := hh.2.2.2.symm
    dsimp [third,X,A1,A3,quotient,NegativeTwo.Inverse.brace]
    field_simp [hq,hh.2.2.1.ne']
    rw [hn]
    ring

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerInverse
