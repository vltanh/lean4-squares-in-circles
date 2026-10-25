module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetSideGeometry

/-!
# Eight squares: J and L corner concavity and the three geometric endpoints

The L second derivative uses the whole-domain
logarithmic-derivative inequality from §4.3.  The endpoint reduction
retains the closed join, diagonal, and first feasible outer diagonal.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.Corner
open CommonQuarter CorePairGeometry Arithmetic

lemma band {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal) : cornerB x b∈Shape.band := by
  rw [Shape.band,diagonal_zero]
  exact ⟨cornerB_lower hx hb,by linarith [outer_endpoint_bounds.2.2.2]⟩

lemma curvature_positive {b : ℝ} (hb : b∈MixedCorner.domain) : 0<cornerCurvature b :=
  div_pos (by nlinarith [sq_nonneg (MixedCorner.w b)]) (MixedCorner.z_positive hb)

lemma J_second_negative {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal) : corner₂ 0 x b<0 := by
  have hd := band hx hb hf
  have h2 := Shape.J_second_upper hd
  have h1 := (Shape.J_first_bounds hd).1
  have hs := sq_pos_of_pos (cornerSpeed_positive hx hb)
  have hp := mul_neg_of_neg_of_pos (show JLabel.d2 (cornerB x b)<0 by linarith) hs
  have hq := mul_nonneg
    (mul_nonneg (show 0≤JLabel.d1 (cornerB x b) by linarith) (curvature_positive hb).le)
    (positive_trig (angle_subset hx)).2.2.1
  norm_num [corner₂,F]
  linarith

lemma L_second_negative {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal) : corner₂ 2 x b<0 := by
  have hd := Shape.band_domain (band hx hb hf)
  have h1 := Shape.L_first_positive hd
  have hv := sq_pos_of_pos (cornerSpeed_positive hx hb)
  have hs := (positive_trig (angle_subset hx)).2.2.1
  have hk := cornerCurvature_bound hx hb
  have hkp := curvature_positive hb
  have h1p : 0<LLabel.d1 (cornerB x b) := by linarith
  by_cases he : cornerB x b≤1/2
  · have h2 := (Labels.L_second_monotone hd (by norm_num [Labels.domain]) he).trans_lt LabelReferences.L_half.2.1
    have hp := mul_neg_of_neg_of_pos h2 hv
    have hq := mul_nonneg (mul_nonneg h1p.le hkp.le) hs
    norm_num [corner₂,F]
    linarith
  · have hlog := Shape.logarithmic_derivative
      (show cornerB x b∈Icc (1/2:ℝ) (9/10) from ⟨by linarith,hd.2⟩)
    have hbu := cornerB_upper hx hb
    have hm := mul_le_mul_of_nonneg_right
      (show (144/13)*(cornerB x b-1/2)≤12*Real.sin x by linarith) h1p.le
    have h2 : LLabel.d2 (cornerB x b)<12*Real.sin x*LLabel.d1 (cornerB x b) := by linarith
    have hp := mul_lt_mul_of_pos_right h2 hv
    have hq := mul_nonneg (show 0≤cornerCurvature b-12*(cornerSpeed x b)^2 by linarith)
      (mul_nonneg h1p.le hs)
    norm_num [corner₂,F]
    nlinarith

lemma first_coordinate {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (he : cornerB x b=outerDiagonal) : inverse CoreAngleEndpoint.diagonal outerDiagonal x≤b := by
  have ha : CoreAngleEndpoint.diagonal≤MixedCorner.a b := by
    dsimp [MixedCorner.a]
    linarith [(MixedCorner.chart_bounds hb).1]
  have hm := mul_le_mul_of_nonneg_right ha (positive_trig (angle_subset hx)).2.2.1
  apply inverse_le_of_contact hx
  dsimp [cornerB,contact] at he ⊢
  linarith

lemma inverse_monotone : MonotoneOn (inverse CoreAngleEndpoint.diagonal outerDiagonal) angles := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x hx => (inverse_hasDerivAt CoreAngleEndpoint.diagonal outerDiagonal hx).continuousAt.continuousWithinAt
  · exact fun x hx => inverse_hasDerivAt CoreAngleEndpoint.diagonal outerDiagonal
      (Ioo_subset_Icc_self hx)
  · intro x hx
    have ha := Ioo_subset_Icc_self hx
    have tr := positive_trig (angle_subset ha)
    have hp := mul_nonneg (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])
      (show 0≤1-Real.sin x by linarith [Real.sin_le_one x])
    apply div_nonneg _ (sq_nonneg (Real.cos x))
    nlinarith [core_diagonal_bounds.1,outer_endpoint_bounds.2.2.2]

/-- The ordinary concave-function endpoint theorem applied to the
actual terminal feasible corner interval. -/
lemma endpoints (r : Row) {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal)
    (hcurv : ∀ t∈MixedCorner.domain, cornerB x t≤outerDiagonal → corner₂ r x t≤0)
    (hjoin : cornerB x (1/2)≤outerDiagonal → (17953/20000:ℝ)<sideCost r x (1/2))
    (hfirst : ∀ t∈MixedCorner.domain, cornerB x t=outerDiagonal →
      outerDiagonal<cornerB x (1/2) → (17953/20000:ℝ)<cornerCost r x t)
    (hdiag : (17953/20000:ℝ)<H r x) : (17953/20000:ℝ)<cornerCost r x b := by
  obtain ⟨e,he,hef,hekind⟩ := corner_entry hx hb hf
  have hed : e∈MixedCorner.domain := ⟨he.1,he.2.trans hb.2⟩
  have hdom {t : ℝ} (ht : t∈Icc e CoreAngleEndpoint.diagonal) :=
    corner_interval_domain hx hed hef ht
  have hc : ConcaveOn ℝ (Icc e CoreAngleEndpoint.diagonal) (cornerCost r x) :=
    concave_of_deriv2
      (fun t ht => cornerCost_hasDerivAt r x (hdom ht).1 (hdom ht).2.1)
      (fun t ht => corner₁_hasDerivAt r x (hdom ht).1 (hdom ht).2.1)
      (fun t ht => hcurv t (hdom ht).1 (hdom ht).2.2)
  apply concave_gt_of_endpoints hc ⟨he.2,hb.2⟩
  · rcases hekind with hj | ⟨hfirsteq,hbefore⟩
    · subst e
      rw [corner_at_join]
      exact hjoin hef
    · exact hfirst e hed hfirsteq hbefore
  · simpa only [cornerCost_diagonal] using hdiag

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.Corner
