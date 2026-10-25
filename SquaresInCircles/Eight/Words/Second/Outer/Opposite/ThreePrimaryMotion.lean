module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreePrimaryBounds

/-!
# Eight squares: the original primary contact motions for opposite edge three

Both speed identities retain the actual target circle.  The lower contact
has a source-label speed product above one everywhere; the upper product
is below one whenever the target secondary coordinate is at most `.2`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def lowerPrimarySpeed (B x : ℝ) : ℝ :=
  (arc B+1/2)*Real.cos x-(B+1/2)*Real.sin x

def upperPrimarySpeed (B x : ℝ) : ℝ :=
  (arc B-1/2)*Real.cos x+(B+1/2)*Real.sin x

lemma lowerPrimary_hasDerivAt (B x : ℝ) :
    HasDerivAt (lowerPrimary B) (lowerPrimarySpeed B x) x := by
  have hd := (((Real.hasDerivAt_sin x).const_mul (arc B+1/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (B+1/2))).const_add (1/2)
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · simp only [lowerPrimarySpeed]
    ring
  · simp only [lowerPrimary]
    ring

lemma upperPrimary_hasDerivAt (B x : ℝ) :
    HasDerivAt (upperPrimary B) (-upperPrimarySpeed B x) x := by
  have hd := (((Real.hasDerivAt_cos x).const_mul (B+1/2)).fun_sub
    ((Real.hasDerivAt_sin x).const_mul (arc B-1/2))).const_add (1/2)
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · simp only [upperPrimarySpeed]
    ring
  · simp only [upperPrimary]
    ring

lemma lowerPrimarySpeed_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<lowerPrimarySpeed B x := by
  have hs := ShortOuterOne.SameContact.arc_state hB
  have ht := positive_trig hx
  have hsc : Real.sin x<Real.cos x := by linarith [ht.1,ht.2.2.2.1]
  have hp := mul_pos (show 0<B+1/2 by linarith [hB.1]) (sub_pos.mpr hsc)
  have hn := mul_nonneg (sub_nonneg.mpr hs.2.1) (by linarith [ht.1] : 0≤Real.cos x)
  dsimp [lowerPrimarySpeed]
  nlinarith

lemma upperPrimarySpeed_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<upperPrimarySpeed B x := by
  have hs := NegativeTwo.primary_mem (ShortOuterOne.SameContact.arc_state hB)
  have ht := positive_trig hx
  have hp := mul_pos (show 0<arc B-1/2 by linarith [hs.1,fine_outer_endpoint_bounds.2])
    (show 0<Real.cos x by linarith [ht.1])
  have hn := mul_nonneg (show 0≤B+1/2 by linarith [hB.1]) ht.2.2.1
  dsimp [upperPrimarySpeed]
  linarith

lemma lowerPrimary_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (lowerPrimary B) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun t _ => (lowerPrimary_hasDerivAt B t).continuousAt.continuousWithinAt)
    (fun t _ => lowerPrimary_hasDerivAt B t)
    (fun t ht => (lowerPrimarySpeed_positive hB (Ioo_subset_Icc_self ht)).le)

lemma upperPrimary_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (upperPrimary B) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t _ => (upperPrimary_hasDerivAt B t).continuousAt.continuousWithinAt)
    (fun t _ => upperPrimary_hasDerivAt B t)
    (fun t ht => by linarith [upperPrimarySpeed_positive hB (Ioo_subset_Icc_self ht)])

lemma lowerPrimary_norm {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    (lowerPrimary B x-1/2)^2+(lowerPrimarySpeed B x)^2=Q0 := by
  have hc := (ShortOuterOne.SameContact.arc_state hB).2.2
  have ht := Real.sin_sq_add_cos_sq x
  dsimp [lowerPrimary,lowerPrimarySpeed]
  linear_combination hc+((arc B+1/2)^2+(B+1/2)^2)*ht

lemma upperPrimary_norm {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    (upperPrimary B x-1/2)^2+(upperPrimarySpeed B x)^2=Q0-2*arc B := by
  have hc := (ShortOuterOne.SameContact.arc_state hB).2.2
  have ht := Real.sin_sq_add_cos_sq x
  dsimp [upperPrimary,upperPrimarySpeed]
  linear_combination hc+((arc B-1/2)^2+(B+1/2)^2)*ht

lemma lower_primary_speed_paid {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10))
    (ha : lowerPrimary B x∈Icc outerDiagonal outerAxial) :
    1<TPrimaryLabel.d1 (lowerPrimary B x)*lowerPrimarySpeed B x := by
  have hv := lowerPrimarySpeed_positive hB hx
  have hn := lowerPrimary_norm hB x
  have hm := NegativeThree.primary_first_lower ha
  have hz : 0<lowerPrimary B x-1/2 ∧ lowerPrimary B x-1/2<183/200 := by
    constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]
  have hs : (7/4:ℝ)<lowerPrimarySpeed B x := by
    norm_num [Q0] at hn
    nlinarith
  have hh := mul_lt_mul hm hs.le (by norm_num : (0:ℝ)<7/4)
    (by linarith [hm] : 0≤TPrimaryLabel.d1 (lowerPrimary B x))
  nlinarith

lemma upper_primary_speed_paid {B x : ℝ} (hB : B∈Icc 0 (1/5))
    (hx : x∈Icc 0 (7/10))
    (ha : upperPrimary B x∈Icc outerDiagonal (6/5)) :
    TPrimaryLabel.d1 (upperPrimary B x)*upperPrimarySpeed B x<1 := by
  have hBfull : B∈Icc 0 outerDiagonal := ⟨hB.1,hB.2.trans fifth_mem.2⟩
  have hv := upperPrimarySpeed_positive hBfull hx
  have hn := upperPrimary_norm hBfull x
  have hA := ShortOuterOne.SameContact.arc_antitone
    (outer_domain hBfull) (outer_domain fifth_mem) hB.2
  have hAlo : (135083/100000:ℝ)<arc B := fifth_primary_lower.trans_le hA
  have haFull : upperPrimary B x∈Icc outerDiagonal outerAxial :=
    ⟨ha.1,ha.2.trans primary_six_fifths_mem.2⟩
  have hmlo : 0<TPrimaryLabel.d1 (upperPrimary B x) := by
    linarith [NegativeThree.primary_first_lower haFull]
  by_cases hsmall : upperPrimary B x≤11/10
  · have hM := primary_first_eleven ⟨ha.1,hsmall⟩
    have hz : (399/1000:ℝ)<upperPrimary B x-1/2 := by
      linarith [ha.1,fine_outer_endpoint_bounds.2]
    have hs : upperPrimarySpeed B x<(103/100:ℝ) := by
      norm_num [Q0] at hn
      nlinarith
    have hh := mul_lt_mul hM hs.le hv (by norm_num : (0:ℝ)≤17/20)
    norm_num at hh
    linarith
  · have hM := primary_first_six_fifths ha
    have hz : (3/5:ℝ)≤upperPrimary B x-1/2 := by linarith
    have hs : upperPrimarySpeed B x<(37/40:ℝ) := by
      norm_num [Q0] at hn
      nlinarith
    have hh := mul_lt_mul hM hs.le hv (by norm_num : (0:ℝ)≤1051/1000)
    norm_num at hh
    linarith

end SquaresInCircles.Eight.SecondWord.OppositeThree
