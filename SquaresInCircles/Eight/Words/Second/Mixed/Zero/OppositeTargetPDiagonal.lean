module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetDiagonalReferences
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetShape

/-!
# Eight squares: the whole P diagonal at negative target angle

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
    (fun x hx => (H₂_hasDerivAt 1 hx).continuousAt.continuousWithinAt)
    (fun x hx => H₂_hasDerivAt 1 (Ioo_subset_Icc_self hx))
    (fun x hx => (third_negative (Ioo_subset_Icc_self hx)).le)

lemma second_positive {x : ℝ} (hx : x∈angles) : 0<H₂ 1 x := by
  have hh := second_antitone hx (by norm_num [angles,cap]) hx.2
  linarith [DiagonalReferences.P_cap.1]

lemma first_monotone : MonotoneOn (H₁ 1) angles :=
  monoOn_of_hasDeriv_nonneg
    (fun x hx => (H₁_hasDerivAt 1 hx).continuousAt.continuousWithinAt)
    (fun x hx => H₁_hasDerivAt 1 (Ioo_subset_Icc_self hx))
    (fun x hx => (second_positive (Ioo_subset_Icc_self hx)).le)

lemma first_negative {x : ℝ} (hx : x∈angles) : H₁ 1 x<0 := by
  have hh := first_monotone hx (by norm_num [angles,cap]) hx.2
  linarith [DiagonalReferences.P_cap.2.1]

lemma cost_antitone : AntitoneOn (H 1) angles :=
  antiOn_of_hasDeriv_nonpos
    (fun x hx => (H_hasDerivAt 1 hx).continuousAt.continuousWithinAt)
    (fun x hx => H_hasDerivAt 1 (Ioo_subset_Icc_self hx))
    (fun x hx => (first_negative (Ioo_subset_Icc_self hx)).le)

lemma lower {x : ℝ} (hx : x∈angles) : (17953/20000:ℝ)<H 1 x := by
  have hh := cost_antitone hx (by norm_num [angles,cap]) hx.2
  linarith [DiagonalReferences.P_cap.2.2]

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.PDiagonal
