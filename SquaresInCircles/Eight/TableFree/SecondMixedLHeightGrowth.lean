module

public import SquaresInCircles.Eight.TableFree.SecondMixedLHeightReferences

/-!
# Whole-domain growth of the actual L height label

The positive third and fourth derivatives give global slope control.
On the complete zero-source height interval the fourth derivative
exceeds six times the third.  Two increasing derivative differences
then give the single third-derivative estimate needed by the retained
primary contact curve.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.LHeightBounds
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

def heights : Set ℝ := Icc (171/125) (383/200)
def zero : Set ℝ := Icc (159/100) (44/25)

lemma domain {u : ℝ} (hu : u∈heights) : 0<Q0-u^2 := by
  have hs := pow_le_pow_left₀ (by linarith [hu.1] : 0≤u) hu.2 2
  norm_num [Q0]
  nlinarith

lemma zero_subset : zero⊆heights := fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩

lemma numerator_positive {u : ℝ} (hu : u∈heights) : 0<LHeight.w*u-LHeight.k*Q0 := by
  norm_num [LHeight,Q0]
  nlinarith [hu.1]

lemma third_positive {u : ℝ} (hu : u∈heights) : 0<LHeight.d3 u := by
  exact div_pos (mul_pos (by norm_num [Q0] : (0:ℝ)<3*Q0) (numerator_positive hu))
    (pow_pos (root_pos (domain hu)) 5)

lemma fourth_positive {u : ℝ} (hu : u∈heights) : 0<LHeight.d4 u := by
  have hn := numerator_positive hu
  have hr := domain hu
  have hu0 : 0<u := by linarith [hu.1]
  have hw : 0<LHeight.w := by norm_num [LHeight]
  have he : LHeight.w*(Q0+4*u^2)-5*LHeight.k*Q0*u=
      LHeight.w*(Q0-u^2)+5*u*(LHeight.w*u-LHeight.k*Q0) := by ring
  have hp : 0<LHeight.w*(Q0+4*u^2)-5*LHeight.k*Q0*u := by rw [he]; positivity
  exact div_pos (mul_pos (by norm_num [Q0] : (0:ℝ)<3*Q0) hp)
    (pow_pos (root_pos hr) 7)

lemma third_monotone : MonotoneOn LHeight.d3 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (LHeight.d3_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun u hu => LHeight.d3_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun u hu => (fourth_positive (Ioo_subset_Icc_self hu)).le)

lemma second_monotone : MonotoneOn LHeight.d2 heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (LHeight.d2_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun u hu => LHeight.d2_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun u hu => (third_positive (Ioo_subset_Icc_self hu)).le)

lemma third_lower {u : ℝ} (hu : u∈heights) : (47/20:ℝ)<LHeight.d3 u :=
  LHeightReference.initial_third.trans_le
    (third_monotone (by norm_num [heights]) hu hu.1)

lemma first_lower {u : ℝ} (hu : u∈heights) : (19/20:ℝ)<LHeight.d1 u := by
  have ht := curvature_tangent (f := LHeight.d1) (d := LHeight.d2) (dd := LHeight.d3)
    (κ := 2) hu (show (161/100:ℝ)∈heights by norm_num [heights])
    (fun y hy => LHeight.d1_hasDerivAt (domain hy))
    (fun y hy => LHeight.d2_hasDerivAt (domain hy))
    (fun y hy => by linarith [third_lower hy])
  have hd := abs_lt.mp LHeightReference.stationary_reference.2
  have hsq : (LHeight.d2 (161/100))^2<(61/1000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg (u-161/100+LHeight.d2 (161/100)/2)
  nlinarith [LHeightReference.stationary_reference.1]

lemma eval_monotone : MonotoneOn LHeight.eval heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (LHeight.eval_hasDerivAt (domain hu)).continuousAt.continuousWithinAt)
    (fun u hu => LHeight.eval_hasDerivAt (domain (Ioo_subset_Icc_self hu)))
    (fun u hu => by linarith [first_lower (Ioo_subset_Icc_self hu)])

lemma second_negative_below {u : ℝ} (hu : u∈heights) (hcut : u≤8/5) : LHeight.d2 u<0 := by
  have hm := second_monotone hu (by norm_num [heights]) hcut
  linarith [LHeightReference.low_second]

lemma first_antitone_low : AntitoneOn LHeight.d1 (Icc (171/125) (8/5)) :=
  antiOn_of_hasDeriv_nonpos
    (fun u hu => (LHeight.d1_hasDerivAt (domain ⟨hu.1,by linarith [hu.2]⟩)).continuousAt.continuousWithinAt)
    (fun u hu => LHeight.d1_hasDerivAt (domain ⟨hu.1.le,by linarith [hu.2]⟩))
    (fun u hu => (second_negative_below ⟨hu.1.le,by linarith [hu.2]⟩ hu.2.le).le)

lemma first_monotone_high : MonotoneOn LHeight.d1 (Icc (33/20) (383/200)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro u hu
    exact (LHeight.d1_hasDerivAt (domain ⟨by linarith [hu.1],hu.2⟩)).continuousAt.continuousWithinAt
  · intro u hu
    exact LHeight.d1_hasDerivAt (domain ⟨by linarith [hu.1],hu.2.le⟩)
  · intro u hu
    have hm := second_monotone (by norm_num [heights]) ⟨by linarith [hu.1],hu.2.le⟩ hu.1.le
    linarith [LHeightReference.high_second]

lemma second_upper_late {u : ℝ} (hu : u∈Icc (3/2) (81/50)) : LHeight.d2 u<(23/100:ℝ) :=
  (second_monotone ⟨by linarith [hu.1],by linarith [hu.2]⟩
    (by norm_num [heights]) hu.2).trans_lt LHeightReference.late_second

lemma fourth_growth {u : ℝ} (hu : u∈zero) : 6*LHeight.d3 u<LHeight.d4 u := by
  have hd := domain (zero_subset hu)
  have hn := numerator_positive (zero_subset hu)
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤159/100) hu.1 2
  have hdiff : 0<u-(Q0-u^2) := by norm_num [Q0]; nlinarith [hu.1]
  have hcoef : 0<LHeight.w-(LHeight.w*u-LHeight.k*Q0) := by
    norm_num [LHeight,Q0]
    nlinarith [hu.2]
  have hp : 0<3*Q0*((LHeight.w-(LHeight.w*u-LHeight.k*Q0))*(Q0-u^2)+
      5*(LHeight.w*u-LHeight.k*Q0)*(u-(Q0-u^2))) := by
    have hQ : 0<Q0 := by norm_num [Q0]
    positivity
  have he := LHeight.fourth_growth_identity hd 6
  have hrewrite : LHeight.w*(Q0-u^2)+(5*u-6*(Q0-u^2))*(LHeight.w*u-LHeight.k*Q0)=
      (LHeight.w-(LHeight.w*u-LHeight.k*Q0))*(Q0-u^2)+
        5*(LHeight.w*u-LHeight.k*Q0)*(u-(Q0-u^2)) := by ring
  rw [hrewrite] at he
  apply (mul_lt_mul_right (pow_pos (root_pos hd) 7)).mp
  nlinarith

lemma third_above_twice_second {u : ℝ} (hu : u∈zero) : 2*LHeight.d2 u<LHeight.d3 u := by
  have hf {y : ℝ} (hy : y∈zero) : HasDerivAt (fun z => LHeight.d3 z-2*LHeight.d2 z)
      (LHeight.d4 y-2*LHeight.d3 y) y :=
    (LHeight.d3_hasDerivAt (domain (zero_subset hy))).sub
      ((LHeight.d2_hasDerivAt (domain (zero_subset hy))).const_mul 2)
  have hm : MonotoneOn (fun z => LHeight.d3 z-2*LHeight.d2 z) zero :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (hf hy).continuousAt.continuousWithinAt)
      (fun y hy => hf (Ioo_subset_Icc_self hy))
      (fun y hy => by linarith [fourth_growth (Ioo_subset_Icc_self hy),
        third_positive (zero_subset (Ioo_subset_Icc_self hy))])
  have hh := hm (by norm_num [zero]) hu hu.1
  linarith [LHeightReference.zero_initial.2.1,LHeightReference.zero_initial.2.2]

lemma third_dominates {u : ℝ} (hu : u∈zero) :
    2*LHeight.d1 u+5*max (LHeight.d2 u) 0<LHeight.d3 u := by
  have hf {y : ℝ} (hy : y∈zero) : HasDerivAt (fun z => LHeight.d3 z-2*LHeight.d1 z)
      (LHeight.d4 y-2*LHeight.d2 y) y :=
    (LHeight.d3_hasDerivAt (domain (zero_subset hy))).sub
      ((LHeight.d1_hasDerivAt (domain (zero_subset hy))).const_mul 2)
  have hg {y : ℝ} (hy : y∈zero) :
      HasDerivAt (fun z => LHeight.d3 z-2*LHeight.d1 z-5*LHeight.d2 z)
        (LHeight.d4 y-2*LHeight.d2 y-5*LHeight.d3 y) y :=
    (hf hy).sub ((LHeight.d2_hasDerivAt (domain (zero_subset hy))).const_mul 5)
  have hmF : MonotoneOn (fun z => LHeight.d3 z-2*LHeight.d1 z) zero :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (hf hy).continuousAt.continuousWithinAt)
      (fun y hy => hf (Ioo_subset_Icc_self hy))
      (fun y hy => by linarith [fourth_growth (Ioo_subset_Icc_self hy),
        third_above_twice_second (Ioo_subset_Icc_self hy),
        third_positive (zero_subset (Ioo_subset_Icc_self hy))])
  have hmG : MonotoneOn (fun z => LHeight.d3 z-2*LHeight.d1 z-5*LHeight.d2 z) zero :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (hg hy).continuousAt.continuousWithinAt)
      (fun y hy => hg (Ioo_subset_Icc_self hy))
      (fun y hy => by linarith [fourth_growth (Ioo_subset_Icc_self hy),
        third_above_twice_second (Ioo_subset_Icc_self hy)])
  have hF := hmF (by norm_num [zero]) hu hu.1
  have hG := hmG (by norm_num [zero]) hu hu.1
  have href := LHeightReference.zero_initial
  by_cases hsign : 0≤LHeight.d2 u
  · rw [max_eq_left hsign]
    linarith
  · rw [max_eq_right (not_le.mp hsign).le]
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.LHeightBounds
