module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJBoundaryReferences

/-!
# The hand proof's whole-domain diagonal polynomial

Uncompiled source draft.  These are precisely polynomials (12)--(13)
of Section 4, on one interval.  The two signs of the centered variable
are used only to replace odd powers by their absolute values.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.Inverse (q N factorD)

def bracePolynomial (u : ℝ) : ℝ :=
  Q0*q u*(q u-4/25)-u*(Q0-u^2)*(3*q u-8/25)
def heightPolynomial (u : ℝ) : ℝ :=
  u^4*(q u)^2*(Q0-u)^2-16*(Q0-u^2)*(N u)^2
def heightMinorant (t : ℝ) : ℝ :=
  8-39*t+t^2*(2407-4605*t-975*t^2-371*t^3-9*t^5)

lemma brace_polynomial_positive {u : ℝ} (hu : u∈Icc (33/20:ℝ) (383/200)) :
    0<bracePolynomial u := by
  let y := u-33/20
  have hy : y∈Icc (0:ℝ) (53/200) := by dsimp [y]; constructor <;> linarith [hu.1,hu.2]
  have hident : bracePolynomial u=
      18541395801/62500000000+(175200237/25000000)*y+
        y^2*(627933/50000-(62933/2500)*y-6*y^2) := by
    dsimp [bracePolynomial,q,NegativeTwo.Inverse.q,Q0,y]
    ring
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hbracket : 0<627933/50000-(62933/2500)*y-6*y^2 := by nlinarith
  rw [hident]
  have hh := mul_nonneg (sq_nonneg y) hbracket.le
  linarith [hy.1]

lemma height_polynomial_minorant (x : ℝ) :
    heightMinorant |x|<heightPolynomial (37/20+x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have h2 := pow_nonneg hx 2
    have h3 := pow_nonneg hx 3
    have h4 := pow_nonneg hx 4
    have h5 := pow_nonneg hx 5
    have h6 := pow_nonneg hx 6
    have h7 := pow_nonneg hx 7
    have h8 := pow_nonneg hx 8
    norm_num [heightMinorant,heightPolynomial,q,NegativeTwo.Inverse.q,N,NegativeTwo.Inverse.N,Q0]
    nlinarith
  · rw [abs_of_nonpos hx]
    have h1 : 0≤-x := neg_nonneg.mpr hx
    have h2 := pow_nonneg h1 2
    have h3 := pow_nonneg h1 3
    have h4 := pow_nonneg h1 4
    have h5 := pow_nonneg h1 5
    have h6 := pow_nonneg h1 6
    have h7 := pow_nonneg h1 7
    have h8 := pow_nonneg h1 8
    norm_num [heightMinorant,heightPolynomial,q,NegativeTwo.Inverse.q,N,NegativeTwo.Inverse.N,Q0]
    nlinarith

lemma height_minorant_positive {t : ℝ} (ht : t∈Icc (0:ℝ) (1/5)) :
    (7:ℝ)<heightMinorant t := by
  have h2 := pow_le_pow_left₀ ht.1 ht.2 2
  have h3 := pow_le_pow_left₀ ht.1 ht.2 3
  have h5 := pow_le_pow_left₀ ht.1 ht.2 5
  have hp : (1444:ℝ)<2407-4605*t-975*t^2-371*t^3-9*t^5 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hp.le (sq_nonneg t)
  have hs := sq_nonneg (t-39/2888)
  dsimp [heightMinorant]
  nlinarith

lemma height_polynomial_positive {u : ℝ} (hu : u∈Icc (33/20:ℝ) (383/200)) :
    (7:ℝ)<heightPolynomial u := by
  have hx : |u-37/20|∈Icc (0:ℝ) (1/5) := by
    refine ⟨abs_nonneg _,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith [hu.1,hu.2]
  have hh := height_polynomial_minorant (u-37/20)
  rw [show 37/20+(u-37/20)=u by ring] at hh
  exact (height_minorant_positive hx).trans hh

lemma inverse_brace_positive {u r z w : ℝ}
    (hu : u∈Icc (33/20:ℝ) (383/200)) (hr : r^2*u^2=Q0-u^2)
    (hz : z∈Icc (0:ℝ) (2/5)) (hw : 0<w) (hn : z^2+w^2=q u) :
    0<NegativeTwo.Inverse.brace u r w := by
  have hu0 : 0<u := by linarith [hu.1]
  have hq : 0<q u := by dsimp [q,NegativeTwo.Inverse.q]; norm_num [Q0]; linarith [hu.2]
  have hz2 : z^2≤(4/25:ℝ) := by nlinarith [hz.1,hz.2]
  have hcoef : 0<Q0*q u-2*u*(Q0-u^2) := by
    let y := u-33/20
    have hy : 0≤y := sub_nonneg.mpr hu.1
    have he : u=33/20+y := by dsimp [y]; ring
    rw [he]
    norm_num [q,NegativeTwo.Inverse.q,Q0]
    nlinarith [sq_nonneg y,pow_nonneg hy 3]
  have hdiff := mul_nonneg (sub_nonneg.mpr hz2) hcoef.le
  have hp := brace_polynomial_positive hu
  have hden : 0<u^3*q u*w^2 := mul_pos (mul_pos (pow_pos hu0 3) hq) (sq_pos_of_pos hw)
  have he : NegativeTwo.Inverse.brace u r w*(u^3*q u*w^2)=
      bracePolynomial u+(4/25-z^2)*(Q0*q u-2*u*(Q0-u^2)) := by
    have e1 : NegativeTwo.Inverse.brace u r w*(u^3*q u*w^2)=
        Q0*q u*w^2-2*r^2*u^3*w^2-r^2*u^3*q u := by
      dsimp [NegativeTwo.Inverse.brace]
      field_simp
    rw [e1]
    dsimp [bracePolynomial]
    linear_combination (-(2*u*w^2+u*q u))*hr+(Q0*q u-2*u*(Q0-u^2))*hn
  have hpos : 0<NegativeTwo.Inverse.brace u r w*(u^3*q u*w^2) := by
    rw [he]
    linarith
  exact pos_of_mul_pos_left hpos hden.le

lemma logarithmic_height_bound {u r : ℝ}
    (hu : u∈Icc (33/20:ℝ) (383/200)) (hr : 0≤r)
    (hc : r^2*u^2=Q0-u^2) :
    r*NegativeTwo.Inverse.factorD u < NegativeTwo.Inverse.factor u/4 := by
  have hu0 : 0<u := by linarith [hu.1]
  have hq : 0<q u := by dsimp [q,NegativeTwo.Inverse.q]; norm_num [Q0]; linarith [hu.2]
  have hQu : 0<Q0-u := by norm_num [Q0]; linarith [hu.2]
  have hN : 0<N u := by
    have hprod := mul_nonneg (sub_nonneg.mpr hu.1)
      (show 0≤4*Q0-2*(u+33/20) by norm_num [Q0]; linarith [hu.2])
    norm_num [N,NegativeTwo.Inverse.N,Q0] at *
    nlinarith
  have hp := height_polynomial_positive hu
  have hleft : 0≤4*r*N u := by positivity
  have hright : 0<u*q u*(Q0-u) := by positivity
  have hsquare : (4*r*N u)^2<(u*q u*(Q0-u))^2 := by
    dsimp [heightPolynomial] at hp
    have hm := mul_nonneg (sq_nonneg (N u)) (show 0≤u^2 by positivity)
    nlinarith [hc,sq_pos_of_pos hu0]
  have hroot : 4*r*N u<u*q u*(Q0-u) := by nlinarith
  dsimp [NegativeTwo.Inverse.factorD,NegativeTwo.Inverse.factor]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<4)).2
  field_simp [hu0.ne',hq.ne']
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ.Diagonal
