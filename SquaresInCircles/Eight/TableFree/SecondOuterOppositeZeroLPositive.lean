module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroLShape
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroPositiveSpeeds

/-!
# The symmetric outer zero edge at nonnegative angle

Uncompiled transcription of Sections 5--6 of the whole-angle hand proof.
The three written monotonicity regimes reduce to the aligned contact
or to the small positive-angle rectangle. No additional case search
or angle discretization is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma small_rectangle {B x : ℝ} (hd : PlusDomain B x)
    (hB : B≤3/20) (hx : x≤1/4) :
    (903/1000:ℝ)<plusCost LLabel LLabel B x := by
  have tr := positive_trig hd.2.1
  have hA := (outer_bounds (ShortOuterOne.SameContact.arc_state hd.1)).2.1
  have hcoef : arc B-1/2≤(183/200:ℝ) := by
    linarith [outer_endpoint_bounds.2.1]
  have hAprod := mul_le_mul_of_nonneg_right hcoef tr.2.2.1
  have hsin := Real.sin_le hd.2.1.1
  have hcos := cos_lower_two hd.2.1.1
  have hBprod := mul_nonneg hd.1.1 (sub_nonneg.mpr tr.2.1)
  have hquad := mul_nonneg hd.2.1.1 (sub_nonneg.mpr hx)
  have hdeficit : 1-B-plus B x≤(391/400)*x := by
    dsimp [plus]
    nlinarith
  have hangle : charge*(1-B-plus B x)≤x := by
    dsimp [charge]
    linarith
  have htarget := small_chord ⟨hd.1.1,hB⟩
  have hsource := support_lower hd.2.2
  have hzero : LLabel.outer 0=(793/20000:ℝ) := L_zero
  rw [hzero] at htarget
  dsimp [plusCost,charge] at *
  linarith

lemma positive_large_target {B x : ℝ} (hd : PlusDomain B x) (hB : 3/10≤B) :
    0<plusFirst LLabel B x := by
  have hv := PositivePJ.speed_bound hd.1 hd.2.1
    (Asymmetric.rational_outer_mem (by norm_num : (3/10:ℝ)∈Icc 0 (899/1000)))
    hB (by norm_num : (0:ℝ)<21/25) Reference.mass_references.2.2.2
  have hp := L_first_upper hd.2.2
  have hh := mul_lt_mul hp hv (positive_data hd.1 hd.2.1).1
    (by norm_num : (0:ℝ)≤147/125)
  dsimp [plusFirst]
  norm_num at hh
  linarith

lemma middle_source {B x : ℝ} (hd : PlusDomain B x) (hB : B∈Icc (3/20:ℝ) (3/10)) :
    plus B x∈Icc (1/10:ℝ) (17/20) := by
  have hthree : (3/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have ht := plus_target_antitone hd.2.1 hd.1 hthree hB.2
  have ha := plus_angle_antitone hthree hd.2.1 (by norm_num) hd.2.1.2
  have hz := plus_angle_antitone hd.1 (by norm_num) hd.2.1 hd.2.1.1
  norm_num [plus] at hz
  exact ⟨by linarith [Reference.plus_references.2.2.2.1],by linarith [hB.1]⟩

lemma positive_middle_target {B x : ℝ} (hd : PlusDomain B x)
    (hB : B∈Icc (3/20:ℝ) (3/10)) : 0<plusFirst LLabel B x := by
  have hv := PositivePJ.speed_bound hd.1 hd.2.1
    (Asymmetric.rational_outer_mem (by norm_num : (3/20:ℝ)∈Icc 0 (899/1000)))
    hB.1 (by norm_num : (0:ℝ)<47/50) Reference.mass_references.2.2.1
  have hp := first_middle_upper (middle_source hd hB)
  have hh := mul_lt_mul hp hv (positive_data hd.1 hd.2.1).1
    (by norm_num : (0:ℝ)≤51/50)
  dsimp [plusFirst]
  norm_num at hh
  linarith

lemma small_late_source {B x : ℝ} (hB : B∈Icc (0:ℝ) (3/20))
    (hx : x∈Icc (1/4:ℝ) (7/10)) : plus B x∈Icc (1/5:ℝ) (19/25) := by
  have hBi : B∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem
    ⟨hB.1,by linarith [hB.2]⟩
  have hxi : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have hsmall : (3/20:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have ht := plus_target_antitone hxi hBi hsmall hB.2
  have ha := plus_angle_antitone hsmall hxi (by norm_num) hx.2
  have ht0 := plus_target_antitone hxi outer_zero_mem hBi hB.1
  have ha0 := plus_angle_antitone outer_zero_mem (by norm_num) hxi hx.1
  exact ⟨by linarith [Reference.plus_references.2.2.2.2.1],
    by linarith [Reference.plus_references.2.2.2.2.2]⟩

lemma positive_small_late {B x : ℝ} (hd : PlusDomain B x)
    (hB : B≤3/20) (hx : 1/4≤x) : 0<plusFirst LLabel B x := by
  have hp := first_inner_upper (small_late_source ⟨hd.1.1,hB⟩ ⟨hx,hd.2.1.2⟩)
  have hv := PositivePJ.speed_upper hd.1 hd.2.1
  have hh := mul_lt_mul hp hv (positive_data hd.1 hd.2.1).1
    (by norm_num : (0:ℝ)≤17/20)
  dsimp [plusFirst]
  norm_num at hh
  linarith

lemma positive_after_small {B x : ℝ} (hd : PlusDomain B x) (hB : 3/20≤B) :
    0<plusFirst LLabel B x := by
  by_cases hlarge : 3/10≤B
  · exact positive_large_target hd hlarge
  · exact positive_middle_target hd ⟨hB,le_of_not_ge hlarge⟩

lemma positive_aligned_reduction {B x : ℝ} (hd : PlusDomain B x) (hB : 3/20≤B) :
    (89777/100000:ℝ)<plusCost LLabel LLabel B x := by
  have hdom {t : ℝ} (ht : t∈Icc 0 x) : PlusDomain B t := by
    have hti : t∈Icc 0 (7/10) := ⟨ht.1,ht.2.trans hd.2.1.2⟩
    have hlo := plus_angle_antitone hd.1 hti hd.2.1 ht.2
    have hhi := plus_angle_antitone hd.1 (by norm_num) hti ht.1
    norm_num [plus] at hhi
    exact ⟨hd.1,hti,⟨hd.2.2.1.trans hlo,by
      linarith [hB,fine_outer_endpoint_bounds.2]⟩⟩
  have hm : MonotoneOn (plusCost LLabel LLabel B) (Icc 0 x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (plusCost_hasDerivAt LLabel LLabel (hdom ht)).continuousAt.continuousWithinAt)
      (fun t ht => plusCost_hasDerivAt LLabel LLabel (hdom (Ioo_subset_Icc_self ht)))
      (fun t ht => (positive_after_small (hdom (Ioo_subset_Icc_self ht)) hB).le)
  have hz := (hdom ⟨le_rfl,hd.2.1.1⟩).2.2
  have hh := hm ⟨le_rfl,hd.2.1.1⟩ ⟨hd.2.1.1,le_rfl⟩ hd.2.1.1
  norm_num [plus] at hz
  have hl := AlignedL.original hz hd.1 (by ring)
  norm_num [plusCost,plus] at hh
  linarith

lemma positive_small_reduction {B x : ℝ} (hd : PlusDomain B x) (hB : B≤3/20) :
    (17953/20000:ℝ)<plusCost LLabel LLabel B x := by
  by_cases hearly : x≤1/4
  · linarith [small_rectangle hd hB hearly]
  · have hstart : (1/4:ℝ)≤x := le_of_not_ge hearly
    have hdom {t : ℝ} (ht : t∈Icc (1/4:ℝ) x) : PlusDomain B t := by
      have hb := small_late_source ⟨hd.1.1,hB⟩ ⟨ht.1,ht.2.trans hd.2.1.2⟩
      exact ⟨hd.1,⟨by linarith [ht.1],ht.2.trans hd.2.1.2⟩,
        ⟨by linarith [hb.1],by linarith [hb.2,fine_outer_endpoint_bounds.2]⟩⟩
    have hm : MonotoneOn (plusCost LLabel LLabel B) (Icc (1/4:ℝ) x) :=
      monoOn_of_hasDeriv_nonneg
        (fun t ht => (plusCost_hasDerivAt LLabel LLabel (hdom ht)).continuousAt.continuousWithinAt)
        (fun t ht => plusCost_hasDerivAt LLabel LLabel (hdom (Ioo_subset_Icc_self ht)))
        (fun t ht => (positive_small_late (hdom (Ioo_subset_Icc_self ht)) hB ht.1.le).le)
    have hh := hm ⟨le_rfl,hstart⟩ ⟨hstart,le_rfl⟩ hstart
    have hl := small_rectangle (hdom ⟨le_rfl,hstart⟩) hB (le_refl _)
    linarith

/-- The entire nonnegative-angle symmetric physical contact. -/
theorem plus_lower {B x : ℝ} (hd : PlusDomain B x) :
    (17953/20000:ℝ)<plusCost LLabel LLabel B x := by
  by_cases hB : 3/20≤B
  · linarith [positive_aligned_reduction hd hB]
  · exact positive_small_reduction hd (le_of_not_ge hB)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric
