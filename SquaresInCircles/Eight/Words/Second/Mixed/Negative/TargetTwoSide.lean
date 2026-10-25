module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCornerCalculus
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy

/-!
# Eight squares: complete original primary-side owner at edge two

The single fourth-derivative sign fixes the derivative shape on all
three analytic ranges. Endpoint minima handle the two outer ranges;
one strong tangent quadratic handles the middle. Positive discriminant
then proves the original side cost for every core coordinate at once.
-/

section
/-!
## One global negative fourth derivative for the side discriminant

The positive double-angle harmonic is concave on the whole interval.
Its two endpoints supply the uniform reserve that dominates every
positive term of the fourth derivative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
open CommonQuarter CorePairGeometry Arithmetic

def pay (x : ℝ) : ℝ := -16*C*Real.cos (2*x)+(3093051/250000)*Real.sin (2*x)
def payD (x : ℝ) : ℝ := 32*C*Real.sin (2*x)+(3093051/125000)*Real.cos (2*x)

lemma pay_hasDerivAt (x : ℝ) : HasDerivAt pay (payD x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert (hc.const_mul (-16*C)).add (hs.const_mul (3093051/250000)) using 1
  · funext y
    simp only [pay,Pi.add_apply,Function.comp_apply]
  · dsimp [payD]
    ring

lemma payD_hasDerivAt (x : ℝ) : HasDerivAt payD (-4*pay x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert (hs.const_mul (32*C)).add (hc.const_mul (3093051/125000)) using 1
  · funext y
    simp only [payD,Pi.add_apply,Function.comp_apply]
  · dsimp [pay]
    ring

lemma double_trig {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : 0≤Real.sin (2*x) ∧ 0≤Real.cos (2*x) :=
  ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx.2,pi_hand_enclosure.1]),
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,pi_hand_enclosure.1]⟩⟩

lemma pay_nonnegative {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : 0≤pay x := by
  have hp := mul_nonneg (show 0≤ -16*C by linarith [C_bounds.2]) (double_trig hx).2
  have hq := mul_nonneg (by norm_num : (0:ℝ)≤3093051/250000) (double_trig hx).1
  dsimp [pay]
  linarith

lemma pay_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : (51/25:ℝ)<pay x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (7/10)) pay :=
    concave_of_deriv2 (fun x _ => pay_hasDerivAt x) (fun x _ => payD_hasDerivAt x)
      (fun x hx => by linarith [pay_nonnegative hx])
  apply concave_gt_of_endpoints hc hx
  · norm_num [pay]
    linarith [C_bounds.2]
  · have hs := HighOrderTaylor.S15_le_sin (x := (7/5:ℝ)) (by norm_num)
    norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7] at hs
    have hp := mul_nonneg (show 0≤ -16*C by linarith [C_bounds.2])
      (double_trig (show (7/10:ℝ)∈Icc (0:ℝ) (7/10) by norm_num)).2
    norm_num [pay]
    norm_num at hp
    linarith

theorem fourth_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : E4 x<0 := by
  have hpay := pay_lower hx
  have ht := positive_trig hx
  have hA := mul_le_mul_of_nonneg_left (Real.cos_le_one x) (show 0≤A by norm_num [A])
  have hB := mul_nonpos_of_nonpos_of_nonneg (show B≤0 by norm_num [B]) ht.2.2.1
  have hlast := mul_nonneg hx.1 (double_trig hx).2
  dsimp [E4,pay,A,B,H,q] at *
  nlinarith

lemma third_antitone : AntitoneOn E3 (Icc (0:ℝ) (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x _ => (E3_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => E3_hasDerivAt x)
    (fun _ hx => (fourth_negative (Ioo_subset_Icc_self hx)).le)

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
end
end
end

section
/-!
## Fixed scalar references for the complete side discriminant

Every trigonometric reference is bounded by exact Taylor polynomials.
The two pi-dependent coefficients have rational cages already proved
from the common pi enclosure.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
open CommonQuarter CorePairGeometry Arithmetic

private lemma shift_product {x y l u : ℝ} (hx : 0≤x) (hl : 0≤l) (hy : l≤y ∧ y≤u) :
    (-(25539083129/200000000000:ℝ)-q*x)*u≤(C-q*x)*y ∧
    (C-q*x)*y≤(-(31923853911/250000000000:ℝ)-q*x)*l := by
  have hy0 := hl.trans hy.1
  have hlo : -(25539083129/200000000000:ℝ)-q*x≤0 := by dsimp [q]; linarith
  have hhi : -(31923853911/250000000000:ℝ)-q*x≤0 := by dsimp [q]; linarith
  constructor
  · exact (mul_le_mul_of_nonpos_left hy.2 hlo).trans
      (mul_le_mul_of_nonneg_right (by linarith [C_bounds.1] :
        -(25539083129/200000000000:ℝ)-q*x≤C-q*x) hy0)
  · exact (mul_le_mul_of_nonneg_right (by linarith [C_bounds.2] :
        C-q*x≤ -(31923853911/250000000000:ℝ)-q*x) hy0).trans
      (mul_le_mul_of_nonpos_left hy.1 hhi)

local macro "discriminant_reference" x:term : tactic => `(tactic|
  (have hsL := HighOrderTaylor.S15_le_sin (x := $x) (by norm_num)
   have hsU := HighOrderTaylor.sin_le_S13 (x := $x) (by norm_num)
   have hcL := HighOrderTaylor.C14_le_cos (x := $x) (by norm_num)
   have hcU := HighOrderTaylor.cos_le_C12 (x := $x) (by norm_num)
   have hs2L := HighOrderTaylor.S15_le_sin (x := 2*$x) (by norm_num)
   have hs2U := HighOrderTaylor.sin_le_S13 (x := 2*$x) (by norm_num)
   have hc2L := HighOrderTaylor.C14_le_cos (x := 2*$x) (by norm_num)
   have hc2U := HighOrderTaylor.cos_le_C12 (x := 2*$x) (by norm_num)
   have hpC := shift_product (x := $x) (by norm_num)
     (show 0≤HighOrderTaylor.C14 (2*$x) by
       norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8]) ⟨hc2L,hc2U⟩
   have hpS := shift_product (x := $x) (by norm_num)
     (show 0≤HighOrderTaylor.S15 (2*$x) by
       norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7]) ⟨hs2L,hs2U⟩
   norm_num [q,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
     HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
     at hsL hsU hcL hcU hs2L hs2U hc2L hc2U hpC hpS
   norm_num [E,E1,E2,E3,A,B,H,J,q]
   repeat' constructor
   all_goals nlinarith [C_bounds.1,C_bounds.2,Z_bounds.1,Z_bounds.2]))

lemma zero_value : (177/1000000:ℝ)<E 0 := by
  norm_num [E,A,B,H,J,q]
  linarith [C_bounds.1,Z_bounds.1]

lemma left_reference : (339/100000:ℝ)<E (3/10) ∧ (7/5:ℝ)<E3 (3/10) ∧
    E1 (3/10)< -(13/1000:ℝ) ∧ (47/1000:ℝ)<E2 (3/10) := by
  discriminant_reference (3/10:ℝ)

lemma right_reference : (279/100000:ℝ)<E (1/2) ∧ E3 (1/2)< -(11/10:ℝ) ∧
    (43/5000:ℝ)<E1 (1/2) ∧ (11/125:ℝ)<E2 (1/2) := by
  discriminant_reference (1/2:ℝ)

lemma terminal_value : (389/100000:ℝ)<E (7/10) := by
  discriminant_reference (7/10:ℝ)

lemma middle_reference : (61/25000:ℝ)<E (213/500) ∧
    -(1/25000:ℝ)<E1 (213/500) ∧ E1 (213/500)<(1/25000:ℝ) := by
  discriminant_reference (213/500:ℝ)

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
open CommonQuarter CorePairGeometry Arithmetic

lemma left_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (3/10)) : 0<E x := by
  have hh := MinimumCalculus.endpoint_minimum hx
    (fun x _ => E_hasDerivAt x) (fun x _ => E1_hasDerivAt x) (fun x _ => E2_hasDerivAt x)
    (fun x hx => by
      have hm := third_antitone
        (show x∈Icc (0:ℝ) (7/10) from ⟨hx.1,by linarith [hx.2]⟩)
        (show (3/10:ℝ)∈Icc (0:ℝ) (7/10) by norm_num) hx.2
      linarith [left_reference.2.1])
    (by linarith [left_reference.2.2.1])
  exact (lt_min (by linarith [zero_value]) (by linarith [left_reference.1])).trans_le hh

lemma right_positive {x : ℝ} (hx : x∈Icc (1/2:ℝ) (7/10)) : 0<E x := by
  have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos hx
    (fun x _ => E_hasDerivAt x) (fun x _ => E1_hasDerivAt x) (fun x _ => E2_hasDerivAt x)
    (fun x hx => by
      have hm := third_antitone (show (1/2:ℝ)∈Icc (0:ℝ) (7/10) by norm_num)
        (show x∈Icc (0:ℝ) (7/10) from ⟨by linarith [hx.1],hx.2⟩) hx.1
      linarith [right_reference.2.1])
    (by linarith [right_reference.2.2.1])
  exact (lt_min (by linarith [right_reference.1]) (by linarith [terminal_value])).trans_le hh

lemma middle_curvature {x : ℝ} (hx : x∈Icc (3/10:ℝ) (1/2)) : (47/1000:ℝ)<E2 x := by
  have hc : ConcaveOn ℝ (Icc (3/10:ℝ) (1/2)) E2 :=
    concave_of_deriv2 (fun x _ => E2_hasDerivAt x) (fun x _ => E3_hasDerivAt x)
      (fun x hx => (fourth_negative ⟨by linarith [hx.1],by linarith [hx.2]⟩).le)
  exact concave_gt_of_endpoints hc hx left_reference.2.2.2 (by linarith [right_reference.2.2.2])

lemma middle_positive {x : ℝ} (hx : x∈Icc (3/10:ℝ) (1/2)) : 0<E x := by
  have hh := curvature_tangent (f := E) (d := E1) (dd := E2) (κ := (47/1000:ℝ)) hx
    (show (213/500:ℝ)∈Icc (3/10:ℝ) (1/2) by norm_num)
    (fun x _ => E_hasDerivAt x) (fun x _ => E1_hasDerivAt x) (fun _ hx => (middle_curvature hx).le)
  have hs : (E1 (213/500))^2<(1/25000:ℝ)^2 := by
    nlinarith [middle_reference.2.1,middle_reference.2.2]
  have hp := sq_nonneg ((47/1000)*(x-213/500)+E1 (213/500))
  nlinarith [middle_reference.1]

theorem positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : 0<E x := by
  by_cases hl : x≤3/10
  · exact left_positive ⟨hx.1,hl⟩
  · by_cases hr : x≤1/2
    · exact middle_positive ⟨by linarith,hr⟩
    · exact right_positive ⟨by linarith,hx.2⟩

lemma quadratic_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) (B : ℝ) :
    0<qa x*B^2+qb x*B+qc x := by
  have ht := positive_trig hx
  have ha : 0<qa x := by
    dsimp [qa,k,PHeightQuadratic.k,z]
    nlinarith [ht.1]
  have he := positive hx
  rw [discriminant_identity] at he
  have hp := sq_nonneg (2*qa x*B+qb x)
  by_contra hn
  have hprod := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤4*qa x)
    (le_of_not_gt hn)
  nlinarith

lemma original_identity (B φ : ℝ) :
    φ+PHeightQuadratic.poly (1+(13/12)*Real.cos φ+(1/2-B)*Real.sin φ)+
      MixedThree.negativeCore (7/12) B-γ=
    qa (Real.pi/2-φ)*B^2+qb (Real.pi/2-φ)*B+qc (Real.pi/2-φ) := by
  simp only [qa,qb,qc,contactD,v0,PHeightQuadratic.poly,Real.sin_sub,Real.cos_sub,
    Real.sin_pi_div_two,Real.cos_pi_div_two,zero_mul,one_mul,sub_zero]
  dsimp [p,k,PHeightQuadratic.p,PHeightQuadratic.k,PHeightQuadratic.c,
    MixedThree.negativeCore,g,z,e,γ]
  ring

theorem original_primary {a b B φ : ℝ} (hs : OuterState a b) (hB : B∈Icc (0:ℝ) (1/2))
    (hφ : PositiveThree.Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-(7/12)*Real.cos φ+B*Real.sin φ) :
    γ<value b (7/12) B φ := by
  have ht := PositiveThree.lower_trig hφ
  have hsin : 0≤Real.sin φ := by linarith [ht.1]
  have hterm := mul_nonneg (show 0≤1/2-B by linarith [hB.2]) hsin
  have hcut : 1+(13/12)*Real.cos φ+(1/2-B)*Real.sin φ≤a+1/2 := by nlinarith
  have hu : 1+(13/12)*Real.cos φ+(1/2-B)*Real.sin φ∈PHeightBounds.heights :=
    ⟨by nlinarith [ht.2.2.1],by
      have ha := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
      linarith⟩
  have hh := PHeightQuadratic.original_lower hs hu hcut
  have hp := quadratic_positive (PositiveThree.lower_deviation hφ) B
  rw [←original_identity B φ] at hp
  dsimp [value]
  linarith

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
end
end
end
