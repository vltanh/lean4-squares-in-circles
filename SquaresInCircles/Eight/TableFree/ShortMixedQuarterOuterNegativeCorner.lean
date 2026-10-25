module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeRatio

/-!
# Every original lower-half negative-core corner contact

Uncompiled transcription of Section 3. The source-label ratio and the
same corner slope in both derivative terms give strict concavity across
the whole corner. The original primary separator supplies the contact
height. The late portion uses the stated direct diagonal label bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Corner
open CommonQuarter CorePairGeometry Arithmetic

def cost (r : Row) (φ B : ℝ) : ℝ := φ+ocC r+M r (contactPrimary B φ)+ocG r*B
def first (r : Row) (φ B : ℝ) : ℝ := -M1 r (contactPrimary B φ)*contactTangent B φ+ocG r
def second (r : Row) (φ B : ℝ) : ℝ :=
  M2 r (contactPrimary B φ)*(contactTangent B φ)^2-
    M1 r (contactPrimary B φ)*(Real.cos φ/SecondWord.MixedCorner.z B)*(1+(SecondWord.MixedCorner.w B)^2)

theorem cost_hasDerivAt (r : Row) {φ B : ℝ} (hφ : φ∈earlyAngles) (hB : B∈SecondWord.MixedCorner.domain) :
    HasDerivAt (cost r φ) (first r φ B) B := by
  have h := (((M_hasDerivAt r (contact_domain hB hφ)).comp B
    (contactPrimary_hasDerivAt_B hB)).const_add (φ+ocC r)).fun_add
      ((hasDerivAt_id' B).const_mul (ocG r))
  exact h.congr_deriv (by simp only [first]; ring)
theorem first_hasDerivAt (r : Row) {φ B : ℝ} (hφ : φ∈earlyAngles) (hB : B∈SecondWord.MixedCorner.domain) :
    HasDerivAt (first r φ) (second r φ B) B := by
  have h := ((((M1_hasDerivAt r (contact_domain hB hφ)).comp B
    (contactPrimary_hasDerivAt_B hB)).fun_neg).fun_mul (contactTangent_hasDerivAt_B (φ:=φ) hB)).add_const
      (ocG r)
  exact h.congr_deriv (by simp only [second,contactTangent,Function.comp]; ring)

theorem second_negative (r : Row) (hr : Remaining r) {φ B : ℝ}
    (hφ : φ∈earlyAngles) (hB : B∈SecondWord.MixedCorner.domain) : second r φ B<0 := by
  have hM := M1_positive r hr (contact_domain hB hφ)
  have hratio := Ratio.source_ratio r hr (contact_height_range hB hφ)
  have hcos := early_cosine hφ
  have hz := SecondWord.MixedCorner.z_positive hB
  have hzU := (SecondWord.MixedCorner.chart_bounds hB).2.1
  have hnorm : (contactTangent B φ)^2≤1+(SecondWord.MixedCorner.w B)^2 := by
    have he : (contactTangent B φ)^2+(Real.cos φ-SecondWord.MixedCorner.w B*Real.sin φ)^2=
        1+(SecondWord.MixedCorner.w B)^2 := by
      dsimp [contactTangent]
      linear_combination (1+(SecondWord.MixedCorner.w B)^2)*(Real.sin_sq_add_cos_sq φ)
    nlinarith [sq_nonneg (Real.cos φ-SecondWord.MixedCorner.w B*Real.sin φ)]
  have hpay : (14/5:ℝ)<Real.cos φ/SecondWord.MixedCorner.z B :=
    (lt_div_iff₀ hz).2 (by linarith)
  have hfirst := mul_le_mul_of_nonneg_right hratio.le (sq_nonneg (contactTangent B φ))
  have hnext := mul_le_mul_of_nonneg_left hnorm (show 0≤(14/5)*M1 r (contactPrimary B φ) by positivity)
  have hstrict := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hpay hM)
    (show 0<1+(SecondWord.MixedCorner.w B)^2 by positivity)
  dsimp [second]
  nlinarith

theorem lower (r : Row) (hr : Remaining r) {φ B : ℝ}
    (hφ : φ∈earlyAngles) (hB : B∈SecondWord.MixedCorner.domain) : (89809/100000:ℝ)<cost r φ B := by
  have hc : ConcaveOn ℝ SecondWord.MixedCorner.domain (cost r φ) :=
    concave_of_deriv2 (fun B hB => cost_hasDerivAt r hφ hB)
      (fun B hB => first_hasDerivAt r hφ hB)
      (fun B hB => (second_negative r hr hφ hB).le)
  have hj := Endpoint.lower r hr false hφ
  have hd := Endpoint.lower r hr true hφ
  have hjoin : Endpoint.H r false φ=cost r φ (1/2) := by
    rw [Endpoint.H,Endpoint.height_contact]
    simp [cost,Endpoint.bC]
  have hdiag : Endpoint.H r true φ=cost r φ CoreAngleEndpoint.diagonal := by
    rw [Endpoint.H,Endpoint.height_contact]
    simp [cost,Endpoint.bC]
  exact concave_gt_of_endpoints hc hB (hjoin ▸ hj) (hdiag ▸ hd)

theorem original_early (r : Row) (hr : Remaining r) {a b A B φ : ℝ}
    (hs : OuterState a b) (hB : 1/2≤B) (hBA : B≤A)
    (hc : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2) (hφ : φ∈earlyAngles)
    (hm : sourcePrimary r a b A B φ) : (89809/100000:ℝ)<outerCoreCost r a b A B φ := by
  obtain ⟨hdom,hA⟩ := SecondWord.MixedCorner.actual hB hBA hc
  have hheight := actual_height r hr hdom hA hφ hm
  have hM := M_monotone r hr (contact_domain hdom hφ) (actual_source_domain hs) hheight
  have hcost := lower r hr hφ hdom
  have hsid := source_identity r hs
  rw [primary_cost r hr]
  dsimp [cost] at hcost
  linarith

theorem late_reference (r : Row) (hr : Remaining r) :
    (183/200:ℝ)<6/5+ocC r+(ocP r-ocQ r)*outerDiagonal+ocG r/2 := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  rcases (remaining_iff r).1 hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [ocC,ocP,ocQ,ocG] <;> linarith [hd.1,hd.2]

theorem original_late (r : Row) (hr : Remaining r) {a b A B φ : ℝ}
    (hs : OuterState a b) (hB : 1/2≤B) (hφ : (6/5:ℝ)≤φ) :
    (183/200:ℝ)<outerCoreCost r a b A B φ := by
  have hd : SourceDomain outerDiagonal :=
    ⟨by linarith [ShortMixedZero.fine_diagonal_bounds.1],
      by linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]⟩
  have hM := M_monotone r hr hd (actual_source_domain hs) (outer_bounds hs).1
  rw [source_diagonal,source_identity r hs] at hM
  have hg := mul_le_mul_of_nonneg_left hB (coefficients r hr).2.1.le
  rw [primary_cost r hr]
  linarith [late_reference r hr]

theorem original_lower (r : Row) (hr : Remaining r) {a b A B x : ℝ}
    (hs : OuterState a b) (hB : 1/2≤B) (hBA : B≤A)
    (hc : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle false x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle false x) := by
  by_cases hφ : angle false x≤6/5
  · have he : angle false x∈earlyAngles := by
      refine ⟨?_,hφ⟩
      dsimp [angle,direction,lowerAngle]
      linarith [hx.2]
    have hh := original_early r hr hs hB hBA hc he hm
    linarith
  · have hh := original_late (A:=A) r hr hs hB (le_of_not_ge hφ)
    linarith

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Corner
