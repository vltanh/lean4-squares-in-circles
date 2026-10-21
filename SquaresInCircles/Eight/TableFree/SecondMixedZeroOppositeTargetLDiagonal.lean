module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetDiagonalReferences

/-!
# The L diagonal from its single strong-convexity reference

Uncompiled source draft.  This follows §10.4: the first part decreases
to `.3`; the remaining interval has curvature greater than `1.1`, and
the one value-and-slope reference at `.3832` bounds its entire minimum.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.LDiagonal
open CommonQuarter CorePairGeometry Arithmetic

lemma first_label_early {B : ℝ} (hB : B∈Icc (diagonal 0) (diagonal (3/10))) :
    LLabel.d1 B<41/50 := by
  have hdom {t : ℝ} (ht : t∈Icc (diagonal 0) (diagonal (3/10))) : t∈Labels.domain := by
    exact ⟨by linarith [ht.1,(diagonal_bounds (by norm_num [angles,cap])).1],
      ht.2.trans (diagonal_domain (by norm_num [angles,cap])).2⟩
  have hc : ConcaveOn ℝ (Icc (diagonal 0) (diagonal (3/10)))
      (fun t => (41/50:ℝ)-LLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (LLabel.d1_hasDerivAt (Labels.chart_domain (hdom ht))).const_sub (41/50))
      (fun t ht => (LLabel.d2_hasDerivAt (Labels.chart_domain (hdom ht))).neg)
      (fun t ht => neg_nonpos.mpr (Labels.L_third_positive (hdom ht)).le)
  have hh := concave_gt_of_endpoints hc hB
    (by linarith [LabelReferences.initial.2.2.2.1])
    (by linarith [DiagonalReferences.L_three.2.1])
  linarith

lemma first_label_upper {B : ℝ} (hB : B∈Shape.band) : LLabel.d1 B<233/200 := by
  have hc : ConcaveOn ℝ Shape.band (fun t => (233/200:ℝ)-LLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (LLabel.d1_hasDerivAt (Labels.chart_domain (Shape.band_domain ht))).const_sub (233/200))
      (fun t ht => (LLabel.d2_hasDerivAt (Labels.chart_domain (Shape.band_domain ht))).neg)
      (fun t ht => neg_nonpos.mpr (Labels.L_third_positive (Shape.band_domain ht)).le)
  have hh := concave_gt_of_endpoints hc hB
    (by linarith [LabelReferences.initial.2.2.2.1])
    (by linarith [LabelReferences.nine.2.2])
  linarith

lemma first_early_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (3/10)) : H₁ 2 x<0 := by
  have ha : x∈angles := ⟨hx.1,by norm_num [cap]; linarith [hx.2]⟩
  have hb : diagonal x∈Icc (diagonal 0) (diagonal (3/10)) :=
    ⟨diagonal_monotone (by norm_num) (angle_subset ha) hx.1,
      diagonal_monotone (angle_subset ha) (by norm_num) hx.2⟩
  have hp := first_label_early hb
  have hw := speed_bounds ha
  have hm := mul_le_mul hp.le hw.2.1.le
    (speed_positive (angle_subset ha)).le (by norm_num)
  norm_num [H₁,F]
  linarith

lemma early {x : ℝ} (hx : x∈Icc (0:ℝ) (3/10)) : (17953/20000:ℝ)<H 2 x := by
  have ha {t : ℝ} (ht : t∈Icc (0:ℝ) (3/10)) : t∈angles :=
    ⟨ht.1,by norm_num [cap]; linarith [ht.2]⟩
  have hm : AntitoneOn (H 2) (Icc (0:ℝ) (3/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (H_hasDerivAt 2 (ha ht)).continuousAt.continuousWithinAt)
      (fun t ht => H_hasDerivAt 2 (ha (Ioo_subset_Icc_self ht)))
      (fun t ht => (first_early_negative (Ioo_subset_Icc_self ht)).le)
  have hh := hm hx (by norm_num) hx.2
  linarith [DiagonalReferences.L_three.1]

lemma second_late_lower {x : ℝ} (hx : x∈Icc (3/10:ℝ) cap) : (11/10:ℝ)<H₂ 2 x := by
  have ha : x∈angles := ⟨by linarith [hx.1],hx.2⟩
  have hb := diagonal_domain ha
  have hthree : (3/10:ℝ)∈angles := by norm_num [angles,cap]
  have hm := diagonal_monotone (angle_subset hthree) (angle_subset ha) hx.1
  have h2 := DiagonalReferences.L_three.2.2.1.trans_le
    (Labels.L_second_monotone (diagonal_domain hthree) hb hm)
  have h1 := Shape.L_first_positive hb
  have h1u := first_label_upper (Shape.diagonal_band ha)
  have hw := speed_bounds ha
  have hp := mul_le_mul h2.le
    hw.2.2.1.le (by norm_num : (0:ℝ)≤24/25) (by linarith : 0≤LLabel.d2 (diagonal x))
  have hq := mul_nonneg (show 0≤LLabel.d1 (diagonal x) by linarith)
    (show 0≤(1/2-diagonal x)+2/5 by linarith [hb.2])
  norm_num [H₂,F]
  nlinarith

lemma late {x : ℝ} (hx : x∈Icc (3/10:ℝ) cap) : (17953/20000:ℝ)<H 2 x := by
  have ha {t : ℝ} (ht : t∈Icc (3/10:ℝ) cap) : t∈angles :=
    ⟨by linarith [ht.1],ht.2⟩
  have ht : (479/1250:ℝ)∈Icc (3/10:ℝ) cap := by norm_num [cap]
  have hh := curvature_tangent (κ := (11/10:ℝ)) hx ht
    (fun t ht => H_hasDerivAt 2 (ha ht))
    (fun t ht => H₁_hasDerivAt 2 (ha ht))
    (fun t ht => (second_late_lower ht).le)
  have hs := abs_lt.mp DiagonalReferences.L_minimum.2
  have hp := mul_pos (show 0<H₁ 2 (479/1250)+1/12500 by linarith [hs.1])
    (show 0<(1/12500:ℝ)-H₁ 2 (479/1250) by linarith [hs.2])
  nlinarith [DiagonalReferences.L_minimum.1,
    sq_nonneg ((11/10)*(x-479/1250)+H₁ 2 (479/1250))]

lemma lower {x : ℝ} (hx : x∈angles) : (17953/20000:ℝ)<H 2 x := by
  by_cases he : x≤3/10
  · exact early ⟨hx.1,he⟩
  · exact late ⟨by linarith,hx.2⟩

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.LDiagonal
