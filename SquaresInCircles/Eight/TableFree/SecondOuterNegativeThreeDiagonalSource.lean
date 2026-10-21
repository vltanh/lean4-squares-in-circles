module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeContactStationarity
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoDiagonalReferences

/-!
# The full original diagonal-source contact boundary

On this boundary the physical angular speed has square greater than
`1.9556`.  The global target-label curvature already makes the cost
strictly concave on the entire feasible arc.  Its actual diagonal-target
end occurs before `.556`, and both endpoint costs exceed `.93`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.DiagonalSource

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig
open NegativeTwo.DiagonalSource (height speed Domain diagonal_mem domain_data domain_before)

def cost (x : ℝ) : ℝ := Contact.cost outerDiagonal x
def first (x : ℝ) : ℝ := Contact.angleFirst outerDiagonal x
def second (x : ℝ) : ℝ := Contact.angleSecond outerDiagonal x

lemma contact_domain {x : ℝ} (hx : Domain x) : NegativeTwo.TargetContact.Domain outerDiagonal x :=
  ⟨diagonal_mem,hx.1,(domain_data hx).1⟩

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x :=
  Contact.cost_angle_hasDerivAt (contact_domain hx)

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x :=
  Contact.angleFirst_hasDerivAt (contact_domain hx)

lemma second_negative {x : ℝ} (hx : Domain x) : second x<0 := by
  have hd := domain_data hx
  have hk := K_first_bounds hd.1
  have hk0 : 0<KLabel.d1 (height x) := by linarith [hk.1]
  have hneg := mul_lt_mul_of_pos_right (K_second_upper hd.1) (pow_pos hd.2.1 2)
  have habs := mul_lt_mul hk.2 hd.2.2.1 (abs_nonneg (height x-1/2))
    (by norm_num : (0:ℝ)≤116/125)
  have hlast : -KLabel.d1 (height x)*(height x-1/2)<(232/625:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (neg_le_abs (height x-1/2)) hk0.le
    nlinarith
  change KLabel.d2 (height x)*(speed x)^2-
    KLabel.d1 (height x)*(height x-1/2)<0
  nlinarith [hd.2.2.2]

lemma end_reference : outerDiagonal<height (139/250) := by
  have hs : Real.sin (139/250:ℝ)∈Icc (sin11 (139/250)) (sin9 (139/250)) :=
    ⟨sin11_le_sin (by norm_num),sin_le_sin9 (by norm_num)⟩
  have hc : Real.cos (139/250:ℝ)∈Icc (cos10 (139/250)) (cos12 (139/250)) :=
    ⟨cos10_le_cos (by norm_num),cos_le_cos12 (by norm_num)⟩
  have hh := NegativeTwo.DiagonalSource.point_cage hs hc
    (by norm_num [sin11,sin9,sin7]) (by norm_num [cos10,cos8])
  norm_num [NegativeTwo.DiagonalSource.dLo,NegativeTwo.DiagonalSource.dHi,
    sin11,sin9,sin7,cos12,cos10,cos8] at hh
  linarith [diagonal_fine.2]

lemma true_endpoint : ∃ e : ℝ, e∈Icc 0 (139/250) ∧ height e=outerDiagonal := by
  have hcont : Continuous height := by
    dsimp [height,NegativeTwo.TargetContact.B]
    fun_prop
  obtain ⟨e,he,hc⟩ := intermediate_value_Icc (show (0:ℝ)≤139/250 by norm_num)
    hcont.continuousOn
    (show outerDiagonal∈Icc (height 0) (height (139/250)) by
      rw [NegativeTwo.DiagonalSource.height_zero]
      exact ⟨by linarith [fine_outer_endpoint_bounds.2],end_reference.le⟩)
  exact ⟨e,he,hc⟩

lemma speed_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) : 1<speed x := by
  have ht := positive_trig hx
  have hp := mul_nonneg
    (show 0≤outerDiagonal-1/2 by linarith [fine_outer_endpoint_bounds.2]) ht.2.2.1
  have hq := mul_nonneg
    (show 0≤outerDiagonal+1/2-1399/1000 by linarith [fine_outer_endpoint_bounds.2])
    (show 0≤Real.cos x by linarith [ht.1])
  dsimp [speed,NegativeTwo.TargetContact.v]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  nlinarith [ht.1]

lemma bounded_by_end {x e : ℝ} (hx : Domain x) (he : e∈Icc 0 (139/250))
    (hc : height e=outerDiagonal) : x≤e := by
  have hef : e∈Icc 0 (7/10) := ⟨he.1,by linarith [he.2]⟩
  have hmono : MonotoneOn (fun t => height t-t) (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t _ => ((NegativeTwo.DiagonalSource.height_hasDerivAt t).sub
        (hasDerivAt_id t)).continuousAt.continuousWithinAt)
      (fun t _ => (NegativeTwo.DiagonalSource.height_hasDerivAt t).sub (hasDerivAt_id t))
      (fun t ht => by linarith [speed_lower (Ioo_subset_Icc_self ht)])
  rcases le_total x e with h | h
  · exact h
  · have hh := hmono hef hx.1 h
    rw [hc] at hh
    linarith [hx.2]

lemma zero_value : (93/100:ℝ)<cost 0 := by
  have hb : 1-outerDiagonal∈Icc 0 outerDiagonal := by
    constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]
  have hk := K_chord hb
  change (93/100:ℝ)<value outerDiagonal (height 0) (Real.pi/2-0)
  rw [NegativeTwo.DiagonalSource.height_zero]
  dsimp [value]
  linarith [pi_hand_enclosure.1,T_diagonal_upper,K_zero_bounds.1,
    outer_endpoint_bounds.2.2.2]

lemma endpoint_value {e : ℝ} (he : e∈Icc 0 (139/250))
    (hc : height e=outerDiagonal) : (93/100:ℝ)<cost e := by
  change (93/100:ℝ)<value outerDiagonal (height e) (Real.pi/2-e)
  rw [hc]
  dsimp [value]
  linarith [pi_hand_enclosure.1,he.2,T_diagonal_upper,K_diagonal_lower]

theorem cost_lower {x : ℝ} (hx : Domain x) : (93/100:ℝ)<cost x := by
  obtain ⟨e,he,hc⟩ := true_endpoint
  have hed : Domain e := ⟨⟨he.1,by linarith [he.2]⟩,by rw [hc]⟩
  have hxe := bounded_by_end hx he hc
  have hconcave : ConcaveOn ℝ (Icc 0 e) cost :=
    concave_of_deriv2
      (fun t ht => cost_hasDerivAt (domain_before hed ht))
      (fun t ht => first_hasDerivAt (domain_before hed ht))
      (fun t ht => (second_negative (domain_before hed ht)).le)
  exact concave_gt_of_endpoints hconcave ⟨hx.1.1,hxe⟩ zero_value (endpoint_value he hc)

theorem original_contact {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B outerDiagonal x=B) :
    (93/100:ℝ)<value outerDiagonal B (Real.pi/2-x) := by
  have hd : Domain x := ⟨hx,by
    change NegativeTwo.TargetContact.B outerDiagonal x≤outerDiagonal
    rw [hc]
    exact hB.2⟩
  simpa only [cost,Contact.cost,NegativeTwo.DiagonalSource.height,hc] using cost_lower hd

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.DiagonalSource
