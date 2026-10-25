module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeSecondaryEndpoints

/-!
# Whole negative-half concavity of the opposite secondary supports

Uncompiled transcription of Section 3 of
`HAND_SHORT_WORD_OPPOSITE_SECONDARY_FAMILIES_WITHOUT_TABLES.md`.
The exact squared-norm difference retains the cosine factor. The two
signs of the fixed coefficient use the stated bounds for 1-cos, giving
N(u) ≤ N(0) cos(u). The circle-norm identity then proves concavity on
the entire original negative angle half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeSecondary.Negative
open CommonQuarter CorePairGeometry Arithmetic

def D (r : Row) : ℝ := if 0≤P r then (P r+weight r)^2+(t r)^2-weight r*P r
  else (P r+weight r)^2+(t r)^2-2*weight r*P r/(441/250)

lemma coefficients (r : Row) : 0<D r ∧ (267/1000:ℝ)<2*weight r*t r-(129/200)*D r := by
  fin_cases r <;> norm_num [D,P,t,weight]

lemma norm_defect (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N r false x)^2-(N r false 0)^2*(Real.cos x)^2=
      (N r false 0)^2*(Real.sin x)^2-2*weight r*P r*(1-Real.cos x)-
        2*weight r*t r*Real.sin x := by
  have hn := norm_sq r false hx
  have h0 := norm_initial r false
  dsimp [Unit.direction] at hn
  linear_combination hn-h0-(N r false 0)^2*(Real.sin_sq_add_cos_sq x)

lemma cos_defect_bounds {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (Real.sin x)^2/2≤1-Real.cos x ∧ 1-Real.cos x≤(Real.sin x)^2/(441/250:ℝ) := by
  have ht := positive_trig hx
  have hc := Real.sin_sq_add_cos_sq x
  have hnonneg : 0≤1-Real.cos x := by linarith [ht.2.1]
  have hp := mul_nonneg hnonneg (show 0≤Real.cos x-191/250 by linarith [ht.1])
  constructor
  · nlinarith [sq_nonneg (1-Real.cos x)]
  · norm_num
    nlinarith

lemma norm_defect_upper (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N r false x)^2-(N r false 0)^2*(Real.cos x)^2≤
      Real.sin x*(D r*Real.sin x-2*weight r*t r) := by
  have hdef := norm_defect r hx
  have hc := cos_defect_bounds hx
  have h0 := norm_initial r false
  have h0s := congrArg (fun z : ℝ => z*(Real.sin x)^2) h0
  by_cases hP : 0≤P r
  · have hcoef : -2*weight r*P r≤0 := by
      have hp := mul_nonneg (coefficient_bounds r).1.le hP
      nlinarith
    have hm := mul_le_mul_of_nonpos_left hc.1 hcoef
    rw [D,if_pos hP]
    nlinarith only [hdef,hm,h0s]
  · have hcoef : 0≤-2*weight r*P r := by
      have hp := mul_nonpos_of_nonneg_of_nonpos (coefficient_bounds r).1.le (le_of_not_ge hP)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hc.2 hcoef
    rw [D,if_neg hP]
    nlinarith only [hdef,hm,h0s]

lemma norm_cos_bound (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    N r false x≤N r false 0*Real.cos x := by
  have ht := positive_trig hx
  have hcoef := coefficients r
  have hsin : Real.sin x≤(129/200:ℝ) := by linarith [ht.2.2.2.1]
  have hDs := mul_le_mul_of_nonneg_left hsin hcoef.1.le
  have hinside : D r*Real.sin x-2*weight r*t r≤0 := by linarith [hcoef.2]
  have hright := mul_nonpos_of_nonneg_of_nonpos ht.2.2.1 hinside
  have hdef := norm_defect_upper r hx
  have hN0 := norm_positive r false (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hN := norm_positive r false hx
  have hrightPos := mul_pos hN0 (show 0<Real.cos x by linarith [ht.1])
  nlinarith

lemma curvature_negative (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) : second r false x<0 := by
  have hcoef : (normB r)^2+(normC r false)^2≤(normA r)^2 := by
    fin_cases r <;> norm_num [normA,normB,normC,P,t,weight,Unit.direction]
  have hn := CircularNorm.curvature_lower (norm_energy_positive r false hx) hcoef
  have hm := mul_le_mul_of_nonneg_left hn RoleFour.radius_positive.le
  have hmul : -radius*N r false x/4≤radius*CircularNorm.d2 (normA r) (normB r) (normC r false) x := by
    have e : N r false x=CircularNorm.norm (normA r) (normB r) (normC r false) x := rfl
    rw [e]
    linarith [hm]
  have hnorm := mul_le_mul_of_nonneg_left (norm_cos_bound r hx) RoleFour.radius_positive.le
  have hreserve := Endpoint.initial_curvature_reserve r
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hnegative := mul_neg_of_pos_of_neg hc
    (show -weight r+radius*N r false 0/4<0 by linarith)
  dsimp [second,Unit.direction]
  nlinarith only [hmul,hnorm,hnegative]

theorem value_concave (r : Row) : ConcaveOn ℝ (Icc 0 (7/10)) (value r false) :=
  concave_of_deriv2 (fun x hx => value_hasDerivAt r false hx)
    (fun x hx => first_hasDerivAt r false hx) (fun x hx => (curvature_negative r hx).le)

theorem value_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) : threshold r<value r false x := by
  apply concave_gt_of_endpoints (value_concave r) hx
  · exact Endpoint.initial_threshold r false
  · have hh := Endpoint.final_value r
    have hth : threshold r≤(497/500:ℝ) := by fin_cases r <;> norm_num [threshold]
    exact hth.trans_lt hh

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeSecondary.Negative
