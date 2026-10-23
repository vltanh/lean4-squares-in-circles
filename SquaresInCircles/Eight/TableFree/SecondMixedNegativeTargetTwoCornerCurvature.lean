module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeTargetTwoCornerCalculus

/-!
# Whole-corner curvature, with one complete early and one late range

The early growth inequality makes the cost concave in the core
coordinate. On the late rectangle its core curvature increases in
angle, and its entire terminal edge lies below 7/4. No coordinate
or angle enclosure table is used. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lower_trig)

lemma early_curvature {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) (he : φ≤11/10) :
    fBB B φ<0 := by
  have hu := early_height hB hφ he
  have hg := PHeightTaylor.early_growth hu
  have hdom : u B φ∈PHeightBounds.heights := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hd := PHeightTaylor.d2_positive hdom
  have hfirst := PHeightTaylor.d1_positive hdom
  have hi : (11/10:ℝ)∈angles := ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have hc := PositiveThree.lower_cos_antitone (lower_mem hφ) (lower_mem hi) he
  have hcos : (9/20:ℝ)<Real.cos φ := by linarith [transition_trig.2.2.1]
  have hprod := mul_lt_mul_of_pos_left hcos hfirst
  have hdelta : 0<PHeightTaylor.d1 (u B φ)*Real.cos φ-h := by dsimp [h]; nlinarith
  have hpay : PHeightTaylor.d2 (u B φ)<12*(PHeightTaylor.d1 (u B φ)*Real.cos φ-h) := by
    dsimp [h]
    nlinarith
  have hLsq : (L B φ)^2≤1+(MixedCorner.w B)^2 := by
    nlinarith [LN_circle B φ,sq_nonneg (N B φ)]
  have hp := mul_le_mul_of_nonneg_left hLsq hd.le
  have hq := mul_le_mul_of_nonneg_left (D_bounds hB).2.1 hdelta.le
  have hr := mul_lt_mul_of_pos_right hpay (by positivity : 0<1+(MixedCorner.w B)^2)
  dsimp [fBB,z]
  nlinarith

lemma late_angle_curvature_positive {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈lateAngles) :
    0<fBBAngle B φ := by
  have hu := PHeightTaylor.late_bounds (late_height hB hφ)
  have hsp := speed_bounds hB (late_subset hφ)
  have hD := D_bounds hB
  have ht := lower_trig (lower_mem (late_subset hφ))
  have hi : (11/10:ℝ)∈angles := ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have hsm := PositiveThree.lower_sin_monotone (lower_mem hi) (lower_mem (late_subset hφ)) hφ.1
  have hsin : (89/100:ℝ)<Real.sin φ := by linarith [transition_trig.1]
  have hmass : 0<1+(MixedCorner.w B)^2 := by positivity
  have hLsq : (L B φ)^2≤1+(MixedCorner.w B)^2 := by
    nlinarith [LN_circle B φ,sq_nonneg (N B φ)]
  have hLN : -(1+(MixedCorner.w B)^2)≤2*L B φ*N B φ := by
    nlinarith [LN_circle B φ,sq_nonneg (L B φ+N B φ)]
  have hc3 : 0≤PHeightTaylor.c3*speed B φ := mul_nonneg (by norm_num [PHeightTaylor.c3]) hsp.1.le
  have hc3u : PHeightTaylor.c3*speed B φ≤(109/50:ℝ) := by
    dsimp [PHeightTaylor.c3]
    linarith [hsp.1,hsp.2]
  have h1 := (mul_le_mul_of_nonneg_left hLsq hc3).trans
    (mul_le_mul_of_nonneg_right hc3u hmass.le)
  have h2 := mul_le_mul_of_nonneg_left hLN hu.2.1.le
  have h2u := mul_le_mul_of_nonneg_right hu.2.2.le hmass.le
  have hsinprod := mul_le_mul hu.1.le hsin.le (by norm_num : (0:ℝ)≤89/100)
    (by linarith [hu.1] : 0≤PHeightTaylor.d1 (u B φ))
  have h3 := mul_le_mul_of_nonneg_left hsinprod hD.1.le
  have h3lo := mul_le_mul_of_nonneg_left hD.2.1 (by norm_num : (0:ℝ)≤(909/1000)*(89/100))
  have hremain := mul_nonneg hD.1.le
    (mul_nonneg (mul_nonneg hu.2.1.le hsp.1.le) ht.2.2.1)
  dsimp [fBBAngle]
  nlinarith

lemma late_curvature_monotone {B : ℝ} (hB : B∈MixedCorner.domain) :
    MonotoneOn (fBB B) lateAngles :=
  monoOn_of_hasDeriv_nonneg
    (fun φ _ => (fBB_angle_hasDerivAt B φ).continuousAt.continuousWithinAt)
    (fun φ _ => fBB_angle_hasDerivAt B φ)
    (fun φ hφ => (late_angle_curvature_positive hB (Ioo_subset_Icc_self hφ)).le)

lemma terminal_curvature {B : ℝ} (hB : B∈MixedCorner.domain) : fBB B (1191/1000)<(7/4:ℝ) := by
  have hu := PHeightTaylor.terminal_bounds (terminal_height hB)
  have hD := D_bounds hB
  have hw := MixedCorner.w_bounds hB
  have hcos : 0≤Real.cos (1191/1000) := by linarith [terminal_trig.2.2.1]
  have hsin : 0≤Real.sin (1191/1000) := by linarith [terminal_trig.1]
  have hwc := mul_le_mul_of_nonneg_right hw.2 hcos
  have hL : 0≤L B (1191/1000) ∧ L B (1191/1000)<(13/10:ℝ) := by
    have hp := mul_nonneg hw.1 hcos
    dsimp [L]
    exact ⟨by linarith,by linarith [terminal_trig.2.1,terminal_trig.2.2.2]⟩
  have hL2 : (L B (1191/1000))^2<(13/10:ℝ)^2 := by nlinarith
  have hd : 0<PHeightTaylor.d2 (u B (1191/1000)) := PHeightTaylor.d2_positive
    ⟨by linarith [(terminal_height hB).1],by linarith [(terminal_height hB).2]⟩
  have hfirst := (mul_le_mul_of_nonneg_left hL2.le hd.le).trans
    (mul_le_mul_of_nonneg_right hu.2.le (by norm_num : (0:ℝ)≤(13/10:ℝ)^2))
  have hdc := mul_le_mul hu.1.le terminal_trig.2.2.1.le
    (by norm_num : (0:ℝ)≤370731/1000000) (by linarith [hu.1] : 0≤PHeightTaylor.d1 (u B (1191/1000)))
  have hdelta : -(27/5000:ℝ)≤PHeightTaylor.d1 (u B (1191/1000))*Real.cos (1191/1000)-h := by
    dsimp [h]
    linarith
  have hp := mul_le_mul_of_nonneg_right hdelta hD.1.le
  dsimp [fBB,z]
  nlinarith [hD.2.2]

theorem late_curvature {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈lateAngles) :
    fBB B φ<(7/4:ℝ) :=
  (late_curvature_monotone hB hφ (show (1191/1000:ℝ)∈lateAngles by norm_num [lateAngles]) hφ.2).trans_lt
    (terminal_curvature hB)

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Corner
