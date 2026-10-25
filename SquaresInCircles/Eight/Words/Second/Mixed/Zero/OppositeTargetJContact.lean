module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetPositive
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetLDiagonal

/-!
# Eight squares: the full J negative target contact

This follows §8: the side minimum is the
first feasible target diagonal, and corner concavity leaves the join,
the first feasible target diagonal, and the core diagonal.
-/

section
/-!
## Original side contacts and the corner entry interval

The side contact is kept in its unchanged
core coordinate.  A corner entry is selected by the intermediate value
theorem only when the closed side join is infeasible.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target
open CommonQuarter CorePairGeometry Arithmetic

def sideCost (r : Row) (x b : ℝ) : ℝ :=
  -x+c r+g r*b+(F r).outer (contact (7/12) b x)
def side₁ (r : Row) (x b : ℝ) : ℝ :=
  g r-(F r).d1 (contact (7/12) b x)*Real.cos x

lemma side_contact_hasDerivAt (x b : ℝ) :
    HasDerivAt (fun b => contact (7/12) b x) (-Real.cos x) b := by
  have h : HasDerivAt (fun b => contact (7/12) b x) _ b :=
    ((((hasDerivAt_id' (x:=b)).const_sub (1/2)).mul_const (Real.cos x)).const_add
      (1/2)).add_const (((7/12:ℝ)+1/2)*Real.sin x)
  exact h.congr_deriv (by ring)

lemma sideCost_hasDerivAt (r : Row) (x b : ℝ)
    (hB : contact (7/12) b x∈Labels.domain) : HasDerivAt (sideCost r x) (side₁ r x b) b := by
  have hD := ((F r).outer_hasDerivAt (Labels.chart_domain hB)).comp b
    (side_contact_hasDerivAt x b)
  have h : HasDerivAt (sideCost r x) _ b :=
    (((hasDerivAt_id' (x:=b)).const_mul (g r)).const_add (-x+c r)).fun_add hD
  exact h.congr_deriv (by simp only [side₁]; ring)

lemma side_contact_antitone {x b t : ℝ} (hx : x∈angles) (hbt : b≤t) :
    contact (7/12) t x≤contact (7/12) b x := by
  have hh := mul_nonneg (sub_nonneg.mpr hbt)
    (show 0≤Real.cos x by linarith [(cosine_bounds hx).1])
  dsimp [contact]
  nlinarith

lemma side_contact_lower {x b : ℝ} (hx : x∈angles) (hb : b∈Icc (0:ℝ) (1/2)) :
    (1/2:ℝ)≤contact (7/12) b x := by
  have hh := contact_lower (show CoreState (7/12) b from Or.inl ⟨rfl,hb⟩) hx
  linarith [hb.2]

lemma side_contact_band {x b : ℝ} (hx : x∈angles) (hb : b∈Icc (0:ℝ) (1/2))
    (hf : contact (7/12) b x≤outerDiagonal) : contact (7/12) b x∈Shape.band := by
  have hz := core_diagonal_bounds.1
  rw [Shape.band,diagonal_zero]
  exact ⟨by linarith [side_contact_lower hx hb],
    by linarith [hf,outer_endpoint_bounds.2.2.2]⟩

lemma contact_inverse (a B : ℝ) {x : ℝ} (hx : x∈angles) :
    contact a (inverse a B x) x=B := by
  have hc : Real.cos x≠0 := (lt_trans (by norm_num) (cosine_bounds hx).1).ne'
  dsimp [contact,inverse]
  field_simp [hc]
  ring

lemma inverse_le_of_contact {a b B x : ℝ} (hx : x∈angles) (hf : contact a b x≤B) :
    inverse a B x≤b := by
  have he := contact_inverse a B hx
  have hc : 0<Real.cos x := by linarith [(cosine_bounds hx).1]
  dsimp [contact] at hf he
  nlinarith

lemma inverse_side_nonnegative {x : ℝ} (hx : x∈angles) :
    0≤ inverse (7/12) outerDiagonal x := by
  have he := contact_inverse (7/12) outerDiagonal hx
  have tr := positive_trig (angle_subset hx)
  have hc := cosine_bounds hx
  have hp := mul_nonneg (show 0≤(7/12:ℝ) by norm_num) tr.2.2.1
  have hpos : 0<1/2+(1/2)*Real.cos x+(13/12)*Real.sin x-outerDiagonal := by
    linarith [tr.2.2.2.2.2,outer_endpoint_bounds.2.2.2]
  dsimp [contact] at he
  nlinarith

lemma side_as_boundary (r : Row) {b x : ℝ} (hx : x∈angles) :
    sideCost r x b=boundary r (7/12) (contact (7/12) b x) x := by
  rw [boundary,inverse_contact hx]
  rfl

lemma side_at_entry (r : Row) {x : ℝ} (hx : x∈angles) :
    sideCost r x (inverse (7/12) outerDiagonal x)=boundary r (7/12) outerDiagonal x := by
  rw [sideCost,contact_inverse (7/12) outerDiagonal hx]
  rfl

lemma corner_at_join (r : Row) (x : ℝ) : cornerCost r x (1/2)=sideCost r x (1/2) := by
  rw [cornerCost,cornerB,MixedCorner.join]
  rfl

lemma corner_entry {x b : ℝ} (_hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal) :
    ∃ e, e∈Icc (1/2) b ∧ cornerB x e≤outerDiagonal ∧
      ((e=1/2) ∨ (cornerB x e=outerDiagonal ∧ outerDiagonal<cornerB x (1/2))) := by
  by_cases hj : cornerB x (1/2)≤outerDiagonal
  · exact ⟨1/2,⟨le_rfl,hb.1⟩,hj,Or.inl rfl⟩
  · have hc : ContinuousOn (fun t => -cornerB x t) (Icc (1/2) b) := by
      intro t ht
      exact ((cornerB_hasDerivAt x ⟨ht.1,ht.2.trans hb.2⟩).neg).continuousAt.continuousWithinAt
    obtain ⟨e,he,heq⟩ := intermediate_value_Icc hb.1 hc
      (show -outerDiagonal∈Icc (-cornerB x (1/2)) (-cornerB x b) from
        ⟨by linarith,by linarith⟩)
    have heq' : cornerB x e=outerDiagonal := by linarith
    exact ⟨e,he,heq'.le,Or.inr ⟨heq',by linarith⟩⟩

lemma corner_interval_domain {x e t : ℝ} (hx : x∈angles) (he : e∈MixedCorner.domain)
    (hf : cornerB x e≤outerDiagonal) (ht : t∈Icc e CoreAngleEndpoint.diagonal) :
    t∈MixedCorner.domain ∧ cornerB x t∈Labels.domain ∧ cornerB x t≤outerDiagonal := by
  have hd : t∈MixedCorner.domain := ⟨he.1.trans ht.1,ht.2⟩
  have hu := (cornerB_antitone hx he hd ht.1).trans hf
  have hl := cornerB_lower hx hd
  exact ⟨hd,⟨by linarith [core_diagonal_bounds.2],
    by linarith [outer_endpoint_bounds.2.2.2]⟩,hu⟩

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target
end
end
end

section
/-!
## J and L corner concavity and the three geometric endpoints

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
end
end
end

section
/-!
## The J diagonal is concave on the written extended angle interval

This is the second-derivative estimate in
§8.2 of the original mixed-zero proof, with its two named endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.JDiagonal
open CommonQuarter CorePairGeometry Arithmetic

lemma second_negative {x : ℝ} (hx : x∈angles) : H₂ 0 x<0 := by
  have hb := Shape.diagonal_band hx
  have h1 := Shape.J_first_bounds hb
  have h2 := Shape.J_second_upper hb
  have hw := speed_bounds hx
  have hv : 1/2-diagonal x≤(59/1000:ℝ) := by linarith [(diagonal_bounds hx).1]
  have hp := mul_le_mul_of_nonneg_right h2.le (sq_nonneg (speed x))
  have hq := mul_le_mul_of_nonneg_left hv (show 0≤JLabel.d1 (diagonal x) by linarith [h1.1])
  norm_num [H₂,F]
  nlinarith [hw.2.2.1,h1.2]

lemma lower {x : ℝ} (hx : x∈angles) : (17953/20000:ℝ)<H 0 x := by
  have hc : ConcaveOn ℝ angles (H 0) :=
    concave_of_deriv2 (fun t ht => H_hasDerivAt 0 ht)
      (fun t ht => H₁_hasDerivAt 0 ht) (fun t ht => (second_negative ht).le)
  exact concave_gt_of_endpoints hc hx
    (by linarith [LabelReferences.initial.2.2.2.2])
    (by linarith [DiagonalReferences.J_cap])

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.JDiagonal
end
end
end

section
/-!
## The whole P diagonal at negative target angle

The curvature decreases on the whole interval (`third_negative`). The cap value, slope and
curvature then give the three successive monotonicity conclusions (`second_antitone`,
`first_monotone`, `cost_antitone`) and the lower bound `lower`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.PDiagonal
open CommonQuarter CorePairGeometry Arithmetic

lemma first_lower {B : ℝ} (hB : B∈Shape.band) : (21/25:ℝ)<PLabel.d1 B :=
  LabelReferences.initial.1.trans_le (Labels.P_first_monotone
    (diagonal_domain (by norm_num [angles,cap])) (Shape.band_domain hB) hB.1)

lemma third_negative {x : ℝ} (hx : x∈angles) : H₃ 1 x<0 := by
  have hb := Shape.diagonal_band hx
  have hd := diagonal_domain hx
  have hw := speed_bounds hx
  have hs := speed_positive (angle_subset hx)
  have hp := Labels.P_second_positive hd
  have ht := Labels.P_third_positive hd
  have hinner : PLabel.d3 (diagonal x)*(speed x)^2+
      3*PLabel.d2 (diagonal x)*(1/2-diagonal x)-PLabel.d1 (diagonal x)<0 := by
    by_cases he : diagonal x≤1/2
    · have hhalf : (1/2:ℝ)∈Labels.domain := by norm_num [Labels.domain]
      have htU := (Labels.P_third_monotone hd hhalf he).trans_lt LabelReferences.P_half.2.2.2
      have hpU := (Labels.P_second_monotone hd hhalf he).trans_lt LabelReferences.P_half.2.2.1
      have hv : (1/2-diagonal x)∈Icc (0:ℝ) (59/1000) :=
        ⟨by linarith,by linarith [(diagonal_bounds hx).1]⟩
      have h3 := mul_le_mul htU.le hw.2.2.2.le (sq_nonneg (speed x)) (by norm_num)
      have h2 := mul_le_mul hpU.le hv.2 hv.1 (by norm_num)
      nlinarith [first_lower hb]
    · have hh : diagonal x∈Icc (1/2:ℝ) (9/10) := ⟨by linarith,hd.2⟩
      have hc := Shape.P_third_chord hh
      have hhalf : (1/2:ℝ)∈Labels.domain := by norm_num [Labels.domain]
      have hpL := LabelReferences.P_half.2.1.trans_le (Labels.P_second_monotone hhalf hd hh.1)
      have h1L := LabelReferences.P_half.1.trans_le (Labels.P_first_monotone hhalf hd hh.1)
      have hch : 0≤(153/500:ℝ)+(297/250)*(diagonal x-1/2) := by linarith [hh.1]
      have h3 := mul_le_mul hc.le hw.2.2.2.le (sq_nonneg (speed x)) hch
      have h2 := mul_nonneg (show 0≤PLabel.d2 (diagonal x)-11/50 by linarith)
        (show 0≤diagonal x-1/2 by linarith [hh.1])
      nlinarith [hh.2]
  simpa [H₃,F] using mul_neg_of_pos_of_neg hs hinner

lemma second_antitone : AntitoneOn (H₂ 1) angles :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hx => (H₂_hasDerivAt 1 hx).continuousAt.continuousWithinAt)
    (fun _ hx => H₂_hasDerivAt 1 (Ioo_subset_Icc_self hx))
    (fun _ hx => (third_negative (Ioo_subset_Icc_self hx)).le)

lemma second_positive {x : ℝ} (hx : x∈angles) : 0<H₂ 1 x := by
  have hh := second_antitone hx (by norm_num [angles,cap]) hx.2
  linarith [DiagonalReferences.P_cap.1]

lemma first_monotone : MonotoneOn (H₁ 1) angles :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hx => (H₁_hasDerivAt 1 hx).continuousAt.continuousWithinAt)
    (fun _ hx => H₁_hasDerivAt 1 (Ioo_subset_Icc_self hx))
    (fun _ hx => (second_positive (Ioo_subset_Icc_self hx)).le)

lemma first_negative {x : ℝ} (hx : x∈angles) : H₁ 1 x<0 := by
  have hh := first_monotone hx (by norm_num [angles,cap]) hx.2
  linarith [DiagonalReferences.P_cap.2.1]

lemma cost_antitone : AntitoneOn (H 1) angles :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hx => (H_hasDerivAt 1 hx).continuousAt.continuousWithinAt)
    (fun _ hx => H_hasDerivAt 1 (Ioo_subset_Icc_self hx))
    (fun _ hx => (first_negative (Ioo_subset_Icc_self hx)).le)

lemma lower {x : ℝ} (hx : x∈angles) : (17953/20000:ℝ)<H 1 x := by
  have hh := cost_antitone hx (by norm_num [angles,cap]) hx.2
  linarith [DiagonalReferences.P_cap.2.2]

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.PDiagonal
end
end
end

section
/-!
## The full P negative target contact

As in §9, the cost decreases in the unchanged
core coordinate on both closed charts.  Their common join transports
the side to the corner, and the core diagonal gives the final bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.PContact
open CommonQuarter CorePairGeometry Arithmetic

lemma corner_first_negative {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal) : corner₁ 1 x b<0 := by
  have hP := PDiagonal.first_lower (Corner.band hx hb hf)
  have hp := mul_nonneg (MixedCorner.w_bounds hb).1 (positive_trig (angle_subset hx)).2.2.1
  have hv : (9/10:ℝ)<cornerSpeed x b := by
    dsimp [cornerSpeed]
    linarith [(cosine_bounds hx).1]
  have hm := mul_lt_mul_of_pos_right hP (show 0<cornerSpeed x b by linarith)
  norm_num [corner₁,F,g]
  nlinarith

lemma corner {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal) : (17953/20000:ℝ)<cornerCost 1 x b := by
  have hdom {t : ℝ} (ht : t∈Icc b CoreAngleEndpoint.diagonal) :=
    corner_interval_domain hx hb hf ht
  have hm : AntitoneOn (cornerCost 1 x) (Icc b CoreAngleEndpoint.diagonal) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (cornerCost_hasDerivAt 1 x (hdom ht).1 (hdom ht).2.1).continuousAt.continuousWithinAt)
      (fun t ht => cornerCost_hasDerivAt 1 x (hdom (Ioo_subset_Icc_self ht)).1
        (hdom (Ioo_subset_Icc_self ht)).2.1)
      (fun t ht => (corner_first_negative hx (hdom (Ioo_subset_Icc_self ht)).1
        (hdom (Ioo_subset_Icc_self ht)).2.2).le)
  have hh := hm ⟨le_rfl,hb.2⟩ ⟨hb.2,le_rfl⟩ hb.2
  rw [cornerCost_diagonal] at hh
  exact (PDiagonal.lower hx).trans_le hh

lemma side_first_negative {x b : ℝ} (hx : x∈angles) (hb : b∈Icc (0:ℝ) (1/2))
    (hf : contact (7/12) b x≤outerDiagonal) : side₁ 1 x b<0 := by
  have hP := PDiagonal.first_lower (side_contact_band hx hb hf)
  have hc := (cosine_bounds hx).1
  have hm := mul_lt_mul_of_pos_right hP (show 0<Real.cos x by linarith)
  norm_num [side₁,F,g]
  nlinarith

lemma side {x b : ℝ} (hx : x∈angles) (hb : b∈Icc (0:ℝ) (1/2))
    (hf : contact (7/12) b x≤outerDiagonal) : (17953/20000:ℝ)<sideCost 1 x b := by
  have hdom {t : ℝ} (ht : t∈Icc b (1/2)) :
      t∈Icc (0:ℝ) (1/2) ∧ contact (7/12) t x≤outerDiagonal :=
    ⟨⟨hb.1.trans ht.1,ht.2⟩,(side_contact_antitone hx ht.1).trans hf⟩
  have hm : AntitoneOn (sideCost 1 x) (Icc b (1/2)) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (sideCost_hasDerivAt 1 x t (Shape.band_domain
        (side_contact_band hx (hdom ht).1 (hdom ht).2))).continuousAt.continuousWithinAt)
      (fun t ht => sideCost_hasDerivAt 1 x t (Shape.band_domain
        (side_contact_band hx (hdom (Ioo_subset_Icc_self ht)).1 (hdom (Ioo_subset_Icc_self ht)).2)))
      (fun t ht => (side_first_negative hx (hdom (Ioo_subset_Icc_self ht)).1
        (hdom (Ioo_subset_Icc_self ht)).2).le)
  have hh := hm ⟨le_rfl,hb.2⟩ ⟨hb.2,le_rfl⟩ hb.2
  have hj : cornerB x (1/2)≤outerDiagonal := by
    rw [cornerB,MixedCorner.join]
    exact (hdom ⟨hb.2,le_rfl⟩).2
  have hl := corner hx
    (show (1/2:ℝ)∈MixedCorner.domain from
      ⟨le_rfl,by linarith [core_diagonal_bounds.1]⟩) hj
  rw [corner_at_join] at hl
  exact hl.trans_le hh

lemma core {a b x : ℝ} (hs : CoreState a b) (hx : x∈angles)
    (hf : contact a b x≤outerDiagonal) :
    (17953/20000:ℝ)< -x+c 1+g 1*b+P (contact a b x) := by
  rcases hs with ⟨rfl,hb0,hb1⟩ | ⟨hb0,hba,hcircle⟩
  · exact side hx ⟨hb0,hb1⟩ hf
  · obtain ⟨hb,rfl⟩ := MixedCorner.actual hb0 hba hcircle
    exact corner hx hb hf

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.PContact
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.JContact
open CommonQuarter CorePairGeometry Arithmetic

lemma boundary_first_positive {x : ℝ} (hx : x∈angles) : boundary₁ 0 (7/12) outerDiagonal x>0 := by
  have hd := outer_endpoint_bounds
  have hsq : (outerDiagonal-1/2)^2<(2/5:ℝ)^2 := by
    nlinarith [hd.2.2.1,hd.2.2.2]
  have hdisc : (13/12)*g 0-1-(g 0)^2*(outerDiagonal-1/2)^2/4>0 := by
    norm_num [g]
    nlinarith
  have hnum : 0<(Real.sin x)^2-g 0*(outerDiagonal-1/2)*Real.sin x+
      g 0*((7/12:ℝ)+1/2)-1 := by
    nlinarith [sq_nonneg (Real.sin x-g 0*(outerDiagonal-1/2)/2)]
  exact div_pos hnum (sq_pos_of_pos (by linarith [(cosine_bounds hx).1]))

lemma boundary_lower {x : ℝ} (hx : x∈angles) : (17953/20000:ℝ)<boundary 0 (7/12) outerDiagonal x := by
  have hm : MonotoneOn (boundary 0 (7/12) outerDiagonal) angles :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (boundary_hasDerivAt 0 (7/12) outerDiagonal ht).continuousAt.continuousWithinAt)
      (fun t ht => boundary_hasDerivAt 0 (7/12) outerDiagonal (Ioo_subset_Icc_self ht))
      (fun t ht => (boundary_first_positive (Ioo_subset_Icc_self ht)).le)
  have hh := hm (by norm_num [angles,cap]) hx hx.1
  rw [boundary_zero] at hh
  linarith [J_aligned (show outerDiagonal∈Icc 0 outerDiagonal from
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩)]

lemma side {x b : ℝ} (hx : x∈angles) (hb : b∈Icc (0:ℝ) (1/2))
    (hf : contact (7/12) b x≤outerDiagonal) : (17953/20000:ℝ)<sideCost 0 x b := by
  let e := inverse (7/12) outerDiagonal x
  have he0 : 0≤e := inverse_side_nonnegative hx
  have heb : e≤b := inverse_le_of_contact hx hf
  have heq : contact (7/12) e x=outerDiagonal := contact_inverse (7/12) outerDiagonal hx
  have hdom {t : ℝ} (ht : t∈Icc e b) : contact (7/12) t x∈Shape.band := by
    apply side_contact_band hx ⟨he0.trans ht.1,ht.2.trans hb.2⟩
    have hm := side_contact_antitone hx ht.1
    rw [heq] at hm
    exact hm
  have hm : MonotoneOn (sideCost 0 x) (Icc e b) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (sideCost_hasDerivAt 0 x t (Shape.band_domain (hdom ht))).continuousAt.continuousWithinAt
    · exact fun t ht => sideCost_hasDerivAt 0 x t (Shape.band_domain (hdom (Ioo_subset_Icc_self ht)))
    · intro t ht
      have h1 := Shape.J_first_bounds (hdom (Ioo_subset_Icc_self ht))
      have hp := mul_le_mul_of_nonneg_left (Real.cos_le_one x)
        (show 0≤JLabel.d1 (contact (7/12) t x) by linarith [h1.1])
      norm_num [side₁,F,g]
      linarith [h1.2]
  have hh := hm ⟨le_rfl,heb⟩ ⟨heb,le_rfl⟩ heb
  change sideCost 0 x (inverse (7/12) outerDiagonal x)≤ sideCost 0 x b at hh
  rw [side_at_entry 0 hx] at hh
  exact (boundary_lower hx).trans_le hh

lemma first_corner {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (he : cornerB x b=outerDiagonal) : (17953/20000:ℝ)<cornerCost 0 x b := by
  have hg := (slope_bounds 0).1
  have hc : cornerCost 0 x b=-x+c 0+g 0*b+J outerDiagonal := by
    rw [cornerCost,he]
    rfl
  rw [hc]
  by_cases hs : x≤41/100
  · have hp := mul_le_mul_of_nonneg_left hb.1 hg.le
    linarith [BoundaryReferences.J_first.1]
  · have hh := Corner.inverse_monotone
      (show (41/100:ℝ)∈angles by norm_num [angles,cap]) hx (by linarith)
    have hbL := Corner.first_coordinate hx hb he
    have hp := mul_le_mul_of_nonneg_left
      (show (5249/10000:ℝ)≤b by linarith [BoundaryReferences.J_first.2.2]) hg.le
    linarith [BoundaryReferences.J_first.2.1,hx.2]

lemma corner {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain)
    (hf : cornerB x b≤outerDiagonal) : (17953/20000:ℝ)<cornerCost 0 x b := by
  apply Corner.endpoints 0 hx hb hf
  · exact fun t ht htf => (Corner.J_second_negative hx ht htf).le
  · intro hj
    have hcontact : contact (7/12) (1/2) x≤outerDiagonal := by
      simpa only [cornerB,MixedCorner.join] using hj
    exact side hx (by norm_num) hcontact
  · exact fun t ht he _ => first_corner hx ht he
  · exact JDiagonal.lower hx

lemma core {a b x : ℝ} (hs : CoreState a b) (hx : x∈angles)
    (hf : contact a b x≤outerDiagonal) :
    (17953/20000:ℝ)< -x+c 0+g 0*b+J (contact a b x) := by
  rcases hs with ⟨rfl,hb0,hb1⟩ | ⟨hb0,hba,hcircle⟩
  · exact side hx ⟨hb0,hb1⟩ hf
  · obtain ⟨hb,rfl⟩ := MixedCorner.actual hb0 hba hcircle
    exact corner hx hb hf

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.JContact
end
end
end
