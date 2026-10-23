module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterPositiveAxial

/-!
# The actual lower-half side contact and its axial alternative

Uncompiled transcription of section 2.1. The core corner and the side
join are infeasible. The original separator gives the increasing-source
contact on A=7/12, whose angle lies before the unique axial event.
The upper target endpoint is the source-axis endpoint and has positive
target derivative. Nonnegative H makes the original minimum axial.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

theorem lower_separator (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle false x)) :
    1/2+(A+1/2)*Real.sin x+(B+1/2)*Real.cos x≤a := by
  rw [sourcePrimary,angle_width false hx,angle_cos,angle_sin,targetSign_positive hr.2] at hm
  dsimp [direction] at hm
  linarith

theorem target_side (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) : A=7/12 ∧ 0≤B ∧ B<1/2 := by
  have hsep := lower_separator r hr hx hm
  have tr := positive_trig hx
  have hsum : 1≤Real.sin x+Real.cos x := by
    have hh := one_le_abs_cos_add_abs_sin x
    rw [abs_of_pos (by linarith [tr.1]),abs_of_nonneg tr.2.2.1] at hh
    linarith
  have hnot : B<1/2 := by
    by_contra! hb
    have hA : 1/2≤A := by linarith [(CoreAngleEndpoint.state_bounds ht).1]
    have hp := mul_le_mul_of_nonneg_right (show 1≤A+1/2 by linarith) tr.2.2.1
    have hq := mul_le_mul_of_nonneg_right (show 1≤B+1/2 by linarith) (by linarith [tr.1] : 0≤Real.cos x)
    have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
    linarith
  have hside := core_small_side ht hnot
  exact ⟨hside.1,(CoreAngleEndpoint.state_bounds ht).2.2.1,hnot⟩

theorem lower_contact_bounds (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    x∈angleDomain ∧ U x+B*Real.cos x≤a+1/2 ∧
      U x+B*Real.cos x∈coordinateDomain ∧ a+1/2∈coordinateDomain := by
  have hside := target_side r hr hs ht hx hm
  have hsep := lower_separator r hr hx hm
  rw [hside.1] at hsep
  have he : U x+B*Real.cos x≤a+1/2 := by dsimp [U,c0]; linarith
  have hBcos := mul_nonneg hside.2.1 (by linarith [(positive_trig hx).1] : 0≤Real.cos x)
  have h0 := U_strictMono.monotoneOn (by norm_num : (0:ℝ)∈Icc 0 (7/10)) hx hx.1
  have hU0 : (3/2:ℝ)≤U x := by simpa [U] using h0
  have hxcap : x<cap := by
    by_contra! hbad
    have hc := U_strictMono.monotoneOn (by norm_num [cap] : cap∈Icc 0 (7/10)) hx hbad
    linarith [Reference.cap_height.1,(outer_bounds hs).2.1]
  have haU : a+1/2≤383/200 := by linarith [(outer_bounds hs).2.1,outer_endpoint_bounds.2.1]
  exact ⟨⟨hx.1,hxcap.le⟩,he,⟨by linarith,he.trans haU⟩,⟨by linarith,haU⟩⟩

def contactCost (r : Row) (B x : ℝ) : ℝ := Real.pi/2-x+ocC r+M r (U x+B*Real.cos x)-ocG r*B

theorem original_ge_contact (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    contactCost r B x≤outerCoreCost r a b A B (angle false x) := by
  have hd := lower_contact_bounds r hr hs ht hx hm
  have hmono := M_monotone r hr hd.2.2.1 hd.2.2.2 hd.2.1
  rw [M,actual_source hs] at hmono
  dsimp [contactCost,outerCoreCost,angle,direction,sourceSign,targetSign,WordProblems.sign]
  rw [hr.1,hr.2]
  linarith

theorem upper_source_root : V (outerAxial+1/2)=1/2 := by
  have he : Q0-(outerAxial+1/2)^2=(1/2:ℝ)^2 := by linarith [axial_circle]
  rw [V,he,Real.sqrt_sq (by norm_num : (0:ℝ)≤1/2)]

theorem upper_target_derivative (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈angleDomain) :
    0<Md r (outerAxial+1/2)*Real.cos x-ocG r := by
  have hb := coefficients r hr
  have tr := axial_trig hx
  have hq : 0≤ocQ r := by linarith [hb.2.2.1]
  have ha : (957/500:ℝ)<outerAxial+1/2 := by linarith [ShortOuterZero.fine_axial_bounds.1]
  have hprod := mul_le_mul hb.2.2.1 (show (957/500:ℝ)≤outerAxial+1/2 by linarith)
    (by norm_num) hq
  have hM : (121/50:ℝ)<Md r (outerAxial+1/2) := by
    rw [Md,upper_source_root]
    nlinarith [hb.1]
  have hh := mul_lt_mul hM tr.1 (by norm_num : (0:ℝ)≤903/1000) (by linarith : 0<Md r (outerAxial+1/2))
  linarith [hb.2.2.2.2]

theorem contact_ge_axial (r : Row) (hr : Rows r) {B x : ℝ}
    (hx : x∈angleDomain) (hB : 0≤B) (hu : U x+B*Real.cos x∈coordinateDomain)
    (hH : 0≤H r x) : K r x≤contactCost r B x := by
  have hC : 0≤Real.cos x := by linarith [(axial_trig hx).1]
  have hUle : U x≤U x+B*Real.cos x := by nlinarith
  have hdom : ∀u∈Icc (U x) (U x+B*Real.cos x),u∈coordinateDomain := by
    intro u hu'
    exact ⟨(axial_coordinate hx).1.trans hu'.1,hu'.2.trans hu.2⟩
  have hh := derivative_reserve
    (f:=M r) (df:=Md r) (k:=Md r (U x))
    (fun u hu' => (M_hasDerivAt r (hdom u hu')).continuousAt.continuousWithinAt)
    (fun u hu' => M_hasDerivAt r (hdom u (Ioo_subset_Icc_self hu')))
    (fun u hu' => Md_monotone r hr (axial_coordinate hx)
      (hdom u (Ioo_subset_Icc_self hu')) hu'.1.le)
    (show U x∈Icc (U x) (U x+B*Real.cos x) from ⟨le_rfl,hUle⟩)
    (show U x+B*Real.cos x∈Icc (U x) (U x+B*Real.cos x) from ⟨hUle,le_rfl⟩) hUle
  have hpay := mul_nonneg hB hH
  dsimp [H,K,contactCost] at *
  nlinarith

theorem original_axial (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) (hH : 0≤H r x) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle false x) := by
  have hd := lower_contact_bounds r hr hs ht hx hm
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.1
  exact (axial_lower r hr hd.1).trans_le
    ((contact_ge_axial r hr hd.1 hB hd.2.2.1 hH).trans (original_ge_contact r hr hs ht hx hm))

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
