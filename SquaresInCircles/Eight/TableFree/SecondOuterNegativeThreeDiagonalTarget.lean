module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeCapBound
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeContactStationarity

/-!
# The original diagonal-target contact boundary

At nonnegative shifted target coordinate, the exact inverse-angle
derivative has magnitude greater than `.8`.  Along the actual
diagonal-target arc the source-label derivative is below `.774`.
The fixed-target cost consequently increases with source coordinate,
and its minimum is the already bounded angle-cap endpoint.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.DiagonalTarget

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)

def shift : ℝ := outerDiagonal-1/2
def cost (b : ℝ) : ℝ :=
  Real.pi/2-NegativeTwo.ContactInverse.angle shift b-T b+K outerDiagonal
def first (b : ℝ) : ℝ := -NegativeTwo.ContactInverse.first shift b-TLabel.d1 b

lemma shift_mem : shift∈Icc (-(1/2)) (2/5) := by
  dsimp [shift]
  constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]

lemma shift_nonneg : 0≤ shift := by
  dsimp [shift]
  linarith [fine_outer_endpoint_bounds.2]

lemma cost_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt cost (first b) b := by
  have hh := (((NegativeTwo.ContactInverse.angle_hasDerivAt hb shift_mem).const_sub
    (Real.pi/2)).sub (TLabel.outer_hasDerivAt (outer_domain hb))).add_const (K outerDiagonal)
  exact hh

lemma first_positive {b : ℝ} (hb : b∈Icc (3/5) outerDiagonal) : 0<first b := by
  have hm : b∈Icc 0 outerDiagonal := ⟨by linarith [hb.1],hb.2⟩
  have hd := NegativeTwo.ContactInverse.data hm shift_mem
  have hq : 0<NegativeTwo.Inverse.q (U b) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hm]
  have hf := NegativeTwo.Inverse.factor_lower hd.1 hq
  have hr : 0≤ratio b := (ShortOuterOne.SameContact.ratio_pos (outer_domain hm)).le
  have hp : 0≤ shift*ratio b/(NegativeTwo.Inverse.q (U b)*
      NegativeTwo.ContactInverse.speed shift b) :=
    div_nonneg (mul_nonneg shift_nonneg hr) (mul_nonneg hq.le hd.2.2.2.2.1.le)
  have ht := NegativeTwo.PrimaryDiagonal.target_first_late hb
  dsimp [first,NegativeTwo.ContactInverse.first]
  linarith

lemma cost_monotone : MonotoneOn cost (Icc (3/5) outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (cost_hasDerivAt ⟨by linarith [hb.1],hb.2⟩).continuousAt.continuousWithinAt)
    (fun b hb => cost_hasDerivAt ⟨by linarith [hb.1],hb.2.le⟩)
    (fun b hb => (first_positive (Ioo_subset_Icc_self hb)).le)

lemma endpoint_late {e : ℝ} (he : e∈Icc (2/5) Cap.endpointUpper)
    (hc : NegativeTwo.CapCurve.height e=outerDiagonal) : (3/5:ℝ)<e := by
  have hed := Cap.endpoint_domain he hc
  by_contra hh
  have hle : e≤(3/5:ℝ) := le_of_not_gt hh
  have hm := NegativeTwo.CapCurve.height_monotone hed.1 NegativeTwo.CapCurve.six_mem hle
  rw [hc] at hm
  linarith [NegativeTwo.CapCurve.six_cage.1.2,fine_outer_endpoint_bounds.2]

lemma source_after_cap {b e x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=outerDiagonal)
    (he : e∈Icc (2/5) Cap.endpointUpper)
    (hec : NegativeTwo.CapCurve.height e=outerDiagonal) : e≤b := by
  have hed := Cap.endpoint_domain he hec
  have hcap := NegativeTwo.TargetContact.B_angle_monotone hb hx (by norm_num) hx.2
  rw [hc] at hcap
  have hmono : MonotoneOn (fun t => NegativeTwo.CapCurve.height t-(4/5)*t)
      (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => ((NegativeTwo.CapCurve.height_hasDerivAt ht).sub
        ((hasDerivAt_id t).const_mul (4/5))).continuousAt.continuousWithinAt)
      (fun t ht => (NegativeTwo.CapCurve.height_hasDerivAt (Ioo_subset_Icc_self ht)).sub
        ((hasDerivAt_id t).const_mul (4/5)))
      (fun t ht => by linarith [(NegativeTwo.CapCurve.k_bounds (Ioo_subset_Icc_self ht)).1])
  rcases le_total e b with h | h
  · exact h
  · have hh := hmono hb hed.1 h
    dsimp only at hh
    rw [hec] at hh
    change outerDiagonal≤NegativeTwo.CapCurve.height b at hcap
    linarith

lemma original_value {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=outerDiagonal) :
    cost b=value b outerDiagonal (Real.pi/2-x) := by
  have hd : NegativeTwo.TargetContact.Domain b x :=
    ⟨hb,hx,by rw [hc]; exact ⟨outer_zero_mem.2,le_rfl⟩⟩
  have hi := NegativeTwo.ContactInverse.original_angle hd
  rw [hc] at hi
  change NegativeTwo.ContactInverse.angle shift b=x at hi
  dsimp [cost,value]
  rw [hi]

theorem original_contact {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=outerDiagonal) :
    (44889/50000:ℝ)<value b outerDiagonal (Real.pi/2-x) := by
  obtain ⟨e,he,hec⟩ := Cap.true_endpoint
  have hed := Cap.endpoint_domain he hec
  have hlate := endpoint_late he hec
  have heb := source_after_cap hb hx hc he hec
  have hm := cost_monotone ⟨hlate.le,hed.1.2⟩ ⟨hlate.le.trans heb,hb.2⟩ heb
  have hcap := Cap.endpoint_value he hec
  have hevalue := original_value hed.1 (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hec
  have hbvalue := original_value hb hx hc
  rw [hevalue,hbvalue] at hm
  dsimp [Cap.cost] at hcap
  rw [hec] at hcap
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.DiagonalTarget
