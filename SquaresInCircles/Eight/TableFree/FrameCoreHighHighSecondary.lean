module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighHighSecondaryScalars

/-!
# Every original high-source transverse witness against a core state

The actual weak margin excludes the negative source sign.  Each remaining
multiplier is proved nonnegative and is applied to that unchanged margin.
The negative-angle continuation keeps its exact cosine multiplier.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighHighSecondary
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (b2 g K)
open FrameCoreHighGeometry FrameCoreHighHighSecondaryScalars

theorem negative_core_nonnegative {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : x∈Icc 0 Real.pi)
    (hm : 0≤highCoreSecondary true false b a B x) :
    (8833/10000:ℝ)<highCoreCost true false b a B x := by
  have hsource := FrameHighArc.loss_antitone (lambda := g)
    (by norm_num [u,v,g]) hb ⟨FrameMidArc.b2_mem.2,le_rfl⟩ hb.2
  simp only [H_c0] at hsource
  have hscaled := mul_nonneg (show 0≤g by norm_num [g]) hm
  have hsin := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin x) (show 0≤g by norm_num [g])
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x) (show 0≤g by norm_num [g])
  have htarget := positive_support (r := g*Real.sin x) (z := g*Real.cos x) hc
    (by dsimp [K,g] at *; linarith) (by linarith)
  have hh : negativeCore x≤highCoreCost true false b a B x := by
    dsimp [negativeCore,highCoreCost,highCoreSecondary,sign] at *
    linarith
  exact (lt_trans (by norm_num) (negativeCore_lower hx)).trans_le hh

theorem negative_core_negative {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : x∈Icc (-(203/250:ℝ)) 0)
    (hm : 0≤highCoreSecondary true false b a B x) :
    (8833/10000:ℝ)<highCoreCost true false b a B x := by
  have ht := negative_trig hx
  have hc0 : 0<Real.cos x := by linarith [ht.2]
  obtain ⟨lambda,hl⟩ : ∃ l : ℝ, l=g/Real.cos x := ⟨_,rfl⟩
  have hlam0 : 0≤lambda := hl ▸ div_nonneg (by norm_num [g]) hc0.le
  have hlamL : g≤lambda := hl ▸ (le_div_iff₀ hc0).2
    (mul_le_of_le_one_right (by norm_num [g] : 0≤g) (Real.cos_le_one x))
  have hlamU : lambda<2 := hl ▸ (div_lt_iff₀ hc0).2 (by dsimp [g]; linarith [ht.2])
  have hsource := FrameHighArc.loss_antitone (lambda := lambda)
    (by norm_num [u,v,g] at hlamL ⊢; linarith) hb ⟨FrameMidArc.b2_mem.2,le_rfl⟩ hb.2
  simp only [H_c0] at hsource
  have hscaled := mul_nonneg hlam0 hm
  have hsin := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin x) hlam0
  have hcan : lambda*Real.cos x=g := by rw [hl]; exact div_mul_cancel₀ _ hc0.ne'
  have htarget := positive_support (r := lambda*Real.sin x)
    (z := lambda*Real.cos x) hc (by dsimp [K]; linarith) (by rw [hcan])
  have hsupport : x-(9/50)*periodicFrameCost x+lambda*pairWidth x+
      Real.pi/4-lambda*c0-lambda*(7/12)*Real.sin x≤highCoreCost true false b a B x := by
    dsimp [highCoreCost,highCoreSecondary,sign] at *
    linarith
  have he : x-(9/50)*periodicFrameCost x+lambda*pairWidth x+
      Real.pi/4-lambda*c0-lambda*(7/12)*Real.sin x=negativeAngle (-x) := by
    rw [hl]
    dsimp only [negativeAngle]
    rw [(FrameCoreHighGeometry.negative_width hx).1,
      (FrameCoreHighGeometry.negative_width hx).2,Real.sin_neg,Real.cos_neg]
    field_simp
    ring
  rw [he] at hsupport
  have hscalar := negativeAngle_lower
    (show -x∈Icc (0:ℝ) (203/250) from ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  exact (lt_trans (by norm_num) hscalar).trans_le hsupport

theorem positive_core {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B)
    (hx : x∈Icc (-(203/250:ℝ)) (5/2))
    (hm : 0≤highCoreSecondary true true b a B x) :
    (8833/10000:ℝ)<highCoreCost true true b a B x := by
  have hcut := high_secondary_positive_angle hb hc hx.1 hm
  have hsource := FrameHighArc.loss_antitone (lambda := (1:ℝ))
    (by norm_num [u,v]) hb ⟨FrameMidArc.b2_mem.2,le_rfl⟩ hb.2
  simp only [H_c0] at hsource
  have htarget := negative_support (x := x) hc
  have hh : positiveCore x≤highCoreCost true true b a B x := by
    dsimp [positiveCore,highCoreCost,highCoreSecondary,sign] at *
    linarith
  have hscalar := positiveCore_lower
    (show x∈Icc (9/20:ℝ) Real.pi from
      ⟨hcut.le,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  exact (lt_trans (by norm_num) hscalar).trans_le hh

theorem high_secondary (i j : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B)
    (hx : x∈Icc (-(203/250:ℝ)) (5/2))
    (hm : 0≤highCoreSecondary i j b a B x) :
    (8833/10000:ℝ)<highCoreCost i j b a B x := by
  have hi := high_secondary_source_positive i j hb hc hm
  subst i
  cases j with
  | false =>
      by_cases hn : x≤0
      · exact negative_core_negative hb hc ⟨hx.1,hn⟩ hm
      · exact negative_core_nonnegative hb hc
          ⟨(lt_of_not_ge hn).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm
  | true => exact positive_core hb hc hx hm

end SquaresInCircles.Eight.TableFree.FrameCoreHighHighSecondary
