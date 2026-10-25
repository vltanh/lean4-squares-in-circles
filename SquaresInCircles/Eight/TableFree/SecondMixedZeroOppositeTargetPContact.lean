module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetCorner
public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetPDiagonal

/-!
# The full P negative target contact

Uncompiled source draft.  As in §9, the cost decreases in the unchanged
core coordinate on both closed charts.  Their common join transports
the side to the corner, and the core diagonal gives the final bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.PContact
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

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.PContact
