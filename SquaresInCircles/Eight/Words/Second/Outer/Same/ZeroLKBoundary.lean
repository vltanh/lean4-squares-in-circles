module

public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroLKReference
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroLKShape

/-!
# Eight squares: the complete target-zero boundary of the L/K contact

The early part is uniformly strongly convex
at its single actual reference.  Once the source coordinate reaches
.755 the cost is increasing.  The transition point is obtained from
continuity when needed; no location or minimizer is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.LK
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def zeroSecond (x : ℝ) : ℝ :=
  LLabel.d2 (b 0 x)*(v 0 x)^2-LLabel.d1 (b 0 x)*(b 0 x-1/2)

lemma zeroFirst_hasDerivAt {x : ℝ} (hd : Domain 0 x) :
    HasDerivAt (angleFirst LLabel 0) (zeroSecond x) x := by
  have hh := (((LLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp x
    (b_angle_hasDerivAt 0 x)).fun_mul (v_angle_hasDerivAt 0 x)).const_sub 1
  exact hh.congr_deriv (by simp only [Function.comp_apply,zeroSecond]; ring)

lemma zero_curvature {x : ℝ} (hd : Domain 0 x) (hb : 151/200≤b 0 x) :
    (1:ℝ)<zeroSecond x := by
  have href : (151/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hL2 := second_right.trans_le (L_second_monotone href hd.2.2 hb)
  have hL := (L_first_bounds hd.2.2).2
  have hz : (b 0 x-1/2)∈Icc 0 (2/5) := by
    constructor <;> linarith [hd.2.2.2,outer_endpoint_bounds.2.2.2]
  have hn := norm_identity outer_zero_mem x
  norm_num [NegativeTwo.Inverse.q,U,ShortOuterOne.SameContact.arc_zero,Q0] at hn
  have hv2 : (579/625:ℝ)<(v 0 x)^2 := by
    nlinarith [ShortOuterZero.fine_axial_bounds.2,
      pow_le_pow_left₀ hz.1 hz.2 2]
  have hp := mul_lt_mul'' hL2 hv2 (by norm_num : (0:ℝ)≤167/100)
    (by norm_num : (0:ℝ)≤579/625)
  have hq := mul_le_mul hL.le hz.2 hz.1 (by norm_num : (0:ℝ)≤147/125)
  dsimp [zeroSecond]
  linarith

lemma zero_first_late {x : ℝ} (hd : Domain 0 x) (hb : b 0 x≤151/200) :
    0<angleFirst LLabel 0 x := by
  have hL := first_middle ⟨(b_lower outer_zero_mem hd.2.1).le,hb⟩
  have hv := v_upper outer_zero_mem hd.2.1
  have hp := mul_lt_mul hL hv.le (v_positive outer_zero_mem hd.2.1)
    (by norm_num : (0:ℝ)≤817/1000)
  dsimp [angleFirst]
  norm_num at hp
  linarith

lemma zero_early_lower {x : ℝ} (hd : Domain 0 x) (hb : 151/200≤b 0 x) :
    (89777/100000:ℝ)<value LLabel KLabel 0 x := by
  let l := min x reference
  let u := max x reference
  have hx : x∈Icc l u := ⟨min_le_left _ _,le_max_left _ _⟩
  have hr : reference∈Icc l u := ⟨min_le_right _ _,le_max_right _ _⟩
  have hdom : ∀t∈Icc l u,Domain 0 t ∧ 151/200≤b 0 t := by
    intro t ht
    have hti : t∈Icc 0 (7/10) := by
      dsimp [l,u] at ht
      constructor
      · exact (le_min hd.2.1.1 reference_domain.1.2.1.1).trans ht.1
      · exact ht.2.trans (max_le hd.2.1.2 reference_domain.1.2.1.2)
    have hblo : 151/200≤b 0 t := by
      rcases le_total x reference with he | he
      · have htt : t≤reference := by simpa [u,max_eq_right he] using ht.2
        exact reference_domain.2.le.trans
          (b_angle_antitone outer_zero_mem hti reference_domain.1.2.1 htt)
      · have htt : t≤x := by simpa [u,max_eq_left he] using ht.2
        exact hb.trans (b_angle_antitone outer_zero_mem hti hd.2.1 htt)
    have hbhi : b 0 t≤outerDiagonal := by
      rcases le_total x reference with he | he
      · have htt : x≤t := by simpa [l,min_eq_left he] using ht.1
        exact (b_angle_antitone outer_zero_mem hd.2.1 hti htt).trans hd.2.2.2
      · have htt : reference≤t := by simpa [l,min_eq_right he] using ht.1
        exact (b_angle_antitone outer_zero_mem reference_domain.1.2.1 hti htt).trans
          reference_domain.1.2.2.2
    exact ⟨⟨outer_zero_mem,hti,⟨by linarith,hbhi⟩⟩,hblo⟩
  have ht := curvature_tangent (f := value LLabel KLabel 0)
    (d := angleFirst LLabel 0) (dd := zeroSecond) (κ := (1:ℝ)) hx hr
    (fun t ht => value_angle_hasDerivAt LLabel KLabel (hdom t ht).1)
    (fun t ht => zeroFirst_hasDerivAt (hdom t ht).1)
    (fun t ht => (zero_curvature (hdom t ht).1 (hdom t ht).2).le)
  have hslope := abs_lt.mp reference_value.2
  have hs2 : (angleFirst LLabel 0 reference)^2<(3/1000000:ℝ)^2 := by
    nlinarith
  have hs := sq_nonneg (x-reference+angleFirst LLabel 0 reference)
  nlinarith [reference_value.1]

theorem zero_boundary_lower {x : ℝ} (hd : Domain 0 x) :
    (89777/100000:ℝ)<value LLabel KLabel 0 x := by
  by_cases hb : 151/200≤b 0 x
  · exact zero_early_lower hd hb
  have hlow : b 0 x<151/200 := lt_of_not_ge hb
  have horder : reference≤x := by
    by_contra! hn
    have hh := b_angle_antitone outer_zero_mem hd.2.1 reference_domain.1.2.1 hn.le
    linarith [reference_domain.2]
  have hc : Continuous (b 0) :=
    continuous_iff_continuousAt.2 fun t => (b_angle_hasDerivAt 0 t).continuousAt
  obtain ⟨y,hy,he⟩ := intermediate_value_Icc horder hc.neg.continuousOn
    (show -(151/200:ℝ)∈Icc (-b 0 reference) (-b 0 x) by
      constructor <;> linarith [reference_domain.2])
  rw [Pi.neg_apply] at he
  have hby : b 0 y=151/200 := by linarith
  have hyi : y∈Icc 0 (7/10) :=
    ⟨reference_domain.1.2.1.1.trans hy.1,hy.2.trans hd.2.1.2⟩
  have hyd : Domain 0 y := by
    refine ⟨outer_zero_mem,hyi,?_⟩
    rw [hby]
    exact Asymmetric.rational_outer_mem (by norm_num)
  have hdom : ∀t∈Icc y x,Domain 0 t ∧ b 0 t≤151/200 := by
    intro t ht
    have hti : t∈Icc 0 (7/10) := ⟨hyi.1.trans ht.1,ht.2.trans hd.2.1.2⟩
    have hhi := b_angle_antitone outer_zero_mem hyi hti ht.1
    have hlo := b_lower outer_zero_mem hti
    rw [hby] at hhi
    exact ⟨⟨outer_zero_mem,hti,⟨by linarith,by
      linarith [fine_outer_endpoint_bounds.2]⟩⟩,hhi⟩
  have hmono : MonotoneOn (value LLabel KLabel 0) (Icc y x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (value_angle_hasDerivAt LLabel KLabel (hdom t ht).1).continuousAt.continuousWithinAt)
      (fun t ht => value_angle_hasDerivAt LLabel KLabel (hdom t (Ioo_subset_Icc_self ht)).1)
      (fun t ht => (zero_first_late (hdom t (Ioo_subset_Icc_self ht)).1
        (hdom t (Ioo_subset_Icc_self ht)).2).le)
  exact (zero_early_lower hyd hby.ge).trans_le
    (hmono ⟨le_rfl,hy.2⟩ ⟨hy.2,le_rfl⟩ hy.2)

end SquaresInCircles.Eight.SecondWord.SameZero.LK
