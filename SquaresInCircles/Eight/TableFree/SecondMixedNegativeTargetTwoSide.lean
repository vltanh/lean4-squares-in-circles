module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeTargetTwoSideReferences

/-!
# Complete original primary-side owner at edge two

The single fourth-derivative sign fixes the derivative shape on all
three analytic ranges. Endpoint minima handle the two outer ranges;
one strong tangent quadratic handles the middle. Positive discriminant
then proves the original side cost for every core coordinate at once.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Side
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
    Real.sin_pi_div_two,Real.cos_pi_div_two,zero_mul,one_mul,zero_sub,sub_zero,neg_neg]
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

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Side
