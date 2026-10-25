module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetShape

/-!
# Eight squares: original side contacts and the corner entry interval

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
