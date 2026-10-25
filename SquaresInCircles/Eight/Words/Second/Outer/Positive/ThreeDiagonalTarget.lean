module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeDiagonalReferences

/-!
# Eight squares: the entire original target-diagonal boundary

After the actual diagonal crossing, the source coordinate decreases
to the aligned endpoint.  Its speed is bounded away from zero and
its acceleration is at most `0.4`.  The original source-label
curvature then makes the full cost concave.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalTarget

open CommonQuarter CorePairGeometry Arithmetic
open DiagonalContact (height heightFirst heightSecond)

def Domain (φ : ℝ) : Prop := Lower φ ∧ height φ≤outerDiagonal
def cost (φ : ℝ) : ℝ := value (height φ) outerDiagonal φ
def first (φ : ℝ) : ℝ := 1+VLabel.d1 (height φ)*heightFirst φ
def second (φ : ℝ) : ℝ :=
  VLabel.d2 (height φ)*(heightFirst φ)^2+VLabel.d1 (height φ)*heightSecond φ

lemma height_quarter : height (Real.pi/2)=alignedSource := by
  rw [height,FirstContact.source_at_quarter,ShortOuterOne.SameContact.arc_diagonal]
  rfl

lemma source_data {φ : ℝ} (hφ : Domain φ) : height φ∈Icc (1/10:ℝ) outerDiagonal := by
  have hh := DiagonalContact.height_antitone hφ.1 quarter_lower hφ.1.2
  rw [height_quarter] at hh
  dsimp [alignedSource] at hh
  exact ⟨by linarith [outer_endpoint_bounds.2.2.2],hφ.2⟩

lemma source_mem {φ : ℝ} (hφ : Domain φ) : height φ∈Icc 0 outerDiagonal :=
  ⟨by linarith [(source_data hφ).1],hφ.2⟩

lemma domain_after {φ e : ℝ} (he : e∈Icc (507/500:ℝ) (203/200))
    (hc : height e=outerDiagonal) (hφ : φ∈Icc e (Real.pi/2)) : Domain φ := by
  have hl : Lower φ := ⟨(DiagonalContact.join_lower he).1.trans hφ.1,hφ.2⟩
  have hh := DiagonalContact.height_antitone (DiagonalContact.join_lower he) hl hφ.1
  rw [hc] at hh
  exact ⟨hl,hh⟩

lemma after_end {φ e : ℝ} (hφ : Domain φ)
    (he : e∈Icc (507/500:ℝ) (203/200)) (hc : height e=outerDiagonal) : e≤φ :=
  DiagonalContact.after_join hφ.1 he hc hφ.2

lemma angle_lower {φ : ℝ} (hφ : Domain φ) : (507/500:ℝ)≤φ := by
  obtain ⟨e,he,hc⟩ := DiagonalContact.exists_join
  exact he.1.trans (after_end hφ he hc)

lemma source_speed {φ : ℝ} (hφ : Domain φ) :
    heightFirst φ< -(1399/1000:ℝ)*(106/125) ∧ heightSecond φ≤2/5 := by
  have ht := lower_trig hφ.1
  have href : Lower (507/500:ℝ) := DiagonalContact.join_lower ⟨le_rfl,by norm_num⟩
  have hs := DiagonalContact.lower_join_sine.trans_le
    (lower_sin_monotone href hφ.1 (angle_lower hφ))
  have hleft := mul_nonpos_of_nonpos_of_nonneg
    (show 1/2-outerDiagonal≤0 by linarith [fine_outer_endpoint_bounds.2]) ht.2.2.1
  have hright := mul_lt_mul
    (show (1399/1000:ℝ)<outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    hs.le (by norm_num : (0:ℝ)<106/125)
    (show 0≤outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
  constructor
  · dsimp [heightFirst]
    nlinarith
  · dsimp [heightSecond]
    linarith [(source_data hφ).1]

lemma cost_hasDerivAt {φ : ℝ} (hφ : Domain φ) : HasDerivAt cost (first φ) φ := by
  have hd := ((hasDerivAt_id φ).add
    ((VLabel.outer_hasDerivAt (outer_domain (source_mem hφ))).comp φ
      (DiagonalContact.height_hasDerivAt φ))).sub_const (L outerDiagonal)
  convert hd using 1
  · funext t
    simp only [cost,value,V,Pi.add_apply,Function.comp_apply,id]
  · simp only [first]

lemma first_hasDerivAt {φ : ℝ} (hφ : Domain φ) : HasDerivAt first (second φ) φ := by
  have hd := (((VLabel.d1_hasDerivAt (outer_domain (source_mem hφ))).comp φ
    (DiagonalContact.height_hasDerivAt φ)).mul
      (DiagonalContact.heightFirst_hasDerivAt φ)).const_add 1
  convert hd using 1
  · funext t
    simp only [first,Pi.mul_apply,Function.comp_apply]
  · simp only [second,Function.comp_apply]
    ring

lemma second_negative {φ : ℝ} (hφ : Domain φ) : second φ<0 := by
  have hs := source_speed hφ
  have hV := V_first_bounds (source_mem hφ)
  have hV0 : 0≤VLabel.d1 (height φ) := by linarith [hV.1]
  have hsq : ((1399/1000:ℝ)*(106/125))^2<(heightFirst φ)^2 := by
    nlinarith [hs.1]
  have hsqpos : 0<(heightFirst φ)^2 := by nlinarith
  have hfirst := mul_lt_mul_of_pos_right (V_second_late (source_data hφ)) hsqpos
  have hlast1 := mul_le_mul_of_nonneg_left hs.2 hV0
  have hlast2 := mul_lt_mul_of_pos_right hV.2 (by norm_num : (0:ℝ)<2/5)
  dsimp [second]
  nlinarith

theorem cost_lower {φ : ℝ} (hφ : Domain φ) : (44889/50000:ℝ)<cost φ := by
  obtain ⟨e,he,hc⟩ := DiagonalContact.exists_join
  have hleft : (44889/50000:ℝ)<cost e := by
    dsimp [cost]
    rw [hc]
    exact DiagonalContact.corner_value he
  have hright : (44889/50000:ℝ)<cost (Real.pi/2) := by
    rw [cost,height_quarter]
    exact diagonal_aligned_value
  have hconcave : ConcaveOn ℝ (Icc e (Real.pi/2)) cost :=
    concave_of_deriv2
      (fun t ht => cost_hasDerivAt (domain_after he hc ht))
      (fun t ht => first_hasDerivAt (domain_after he hc ht))
      (fun t ht => (second_negative (domain_after he hc ht)).le)
  exact concave_gt_of_endpoints hconcave ⟨after_end hφ he hc,hφ.1.2⟩ hleft hright

theorem original_contact {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hφ : Lower φ) (hc : FirstContact.source outerDiagonal φ=b) :
    (44889/50000:ℝ)<value b outerDiagonal φ := by
  have hh : height φ=b := hc
  have hd : Domain φ := ⟨hφ,by rw [hh]; exact hb.2⟩
  simpa only [cost,hh] using cost_lower hd

end SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalTarget
