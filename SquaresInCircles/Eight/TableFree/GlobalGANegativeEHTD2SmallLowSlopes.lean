module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2SmallLowSplit

/-!
# Small-EH low-total ordinary slope comparisons

Uncompiled Section 3 of the small-error companion. The G same-block
term retains its actual two signed masses. The separated H/G terms use
the already derived fixed-coefficient cubic on the whole remaining-angle
interval [.6,.7]. These are derivative comparisons, not angle samples.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryCurvatureBounds OrdinaryNegativeSlope
open NegativeAPositiveTD (Curvature)

theorem G_ratio_constants :
    shapeC0q R (17/25)<259/500 ∧ Curvature.shapeD0q (17/25)<1113/1000 := by
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  constructor
  · unfold shapeC0q
    apply quotient_lt_of_square (pow_pos (shape_pos _) 3) (by norm_num)
    rw [show ((shape (17/25:ℝ))^3)^2=((shape (17/25:ℝ))^2)^3 by ring,shape_sq]
    norm_num [mul_pow,hR2,qCap]
  · unfold Curvature.shapeD0q
    apply quotient_lt_of_square (shape_pos _) (by norm_num)
    norm_num [mul_pow,hR2,shape_sq,qCap]

theorem G_constants {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    curvatureZero R (Explicit.k .small .low θ) (Explicit.l .small .low θ)<
      (259/500)*Explicit.l .small .low θ ∧
    Curvature.slopeZero (Explicit.k .small .low θ) (Explicit.l .small .low θ)<
      (1113/1000)*Explicit.l .small .low θ := by
  have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
  have hk : 0<Explicit.k .small .low θ := by linarith [hr.1]
  have hl : 0<Explicit.l .small .low θ := by linarith [hr.2.2.1]
  have hratio := Explicit.small_low_ratio hθ
  have hquot : Explicit.k .small .low θ/Explicit.l .small .low θ∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg hk.le hl.le,(div_le_one hl).2 (by linarith)⟩
  have hbound := (div_le_iff₀ hl).2 hratio.le
  obtain ⟨_,_,hC,_⟩ := curvature_constants_normalize (R:=R) hk hl
  obtain ⟨_,hD⟩ := Curvature.constants_normalize hk hl
  have hC' := (Curvature.shapeC0q_monotone hquot
    (by norm_num : (17/25:ℝ)∈Icc 0 1) hbound).trans_lt G_ratio_constants.1
  have hD' := (Curvature.shapeD0q_monotone hquot
    (by norm_num : (17/25:ℝ)∈Icc 0 1) hbound).trans_lt G_ratio_constants.2
  rw [hC,hD]
  exact ⟨by simpa [mul_comm] using mul_lt_mul_of_pos_left hC' hl,
    by simpa [mul_comm] using mul_lt_mul_of_pos_left hD' hl⟩

theorem G_same_derivative {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc (0:ℝ) (1/10)) :
    (153/1000:ℝ)<NegativeEH.gD s+NegativeDEPositiveTD.LowSame.ordinaryFirst θ s := by
  have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
  have hk : 0<Explicit.k .small .low θ := by linarith [hr.1]
  have hl : 0<Explicit.l .small .low θ := by linarith [hr.2.2.1]
  have ht : |s-θ|≤frameCap := by
    rw [abs_le]
    norm_num [frameCap]
    constructor <;> linarith [hs.1,hs.2,hθ.1,hθ.2]
  have hn := Curvature.norm_slope_signed_tangent hk hl ht
  have hc := G_constants hθ
  have hC0 : 0≤curvatureZero R (Explicit.k .small .low θ) (Explicit.l .small .low θ) := by
    dsimp [curvatureZero]; positivity
  have hshift := mul_le_mul_of_nonneg_left
    (show -(s-θ)≤1/6 by linarith [hs.1,hθ.2]) hC0
  have hCscaled := mul_le_mul_of_nonneg_right hc.1.le (by norm_num : (0:ℝ)≤1/6)
  have hsin : (141/250:ℝ)<Real.sin (frameCap-s) := by
    have hh := trig_bracket (l:=(3/5:ℝ)) (u:=frameCap) (by norm_num)
      (by norm_num [frameCap]; linarith [Real.pi_gt_three])
      (show frameCap-s∈Icc (3/5:ℝ) frameCap by
        norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2])
    norm_num [frameCap] at hh
    linarith [hh.1]
  have hsinL := mul_lt_mul_of_pos_left hsin hl
  have hg := NegativeEH.small_slope hs
  dsimp [NegativeDEPositiveTD.LowSame.ordinaryFirst]
  change (153/1000:ℝ)<NegativeEH.gD s+
    (Explicit.l .small .low θ*Real.sin (frameCap-s)-
      R*normD1 (Explicit.k .small .low θ) (Explicit.l .small .low θ) (s-θ))
  nlinarith [hr.2.2.2.1]

theorem G_same_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => NegativeEH.g s+NegativeDEPositiveTD.LowSame.ordinary θ s)
      (Icc (0:ℝ) (1/10)) := by
  have hd (s : ℝ) (hs : s∈Icc (0:ℝ) (1/10)) :=
    (NegativeEH.g_hasDerivAt s).add (NegativeDEPositiveTD.LowSame.ordinary_hasDerivAt hθ
      (show s∈Icc 0 frameCap from ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩))
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  linarith [G_same_derivative hθ (Ioo_subset_Icc_self hs)]

theorem late_cubic_bound {d : ℝ} (hd : d∈Icc (3/5:ℝ) frameCap) :
    NegativeDEPositiveTD.LowSeparated.lateCubic d<931/1000 := by
  have hm : AntitoneOn NegativeDEPositiveTD.LowSeparated.lateCubic
      (Icc (3/5:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun d _ => (NegativeDEPositiveTD.LowSeparated.lateCubic_derivative d).continuousAt.continuousWithinAt)
      (fun d _ => NegativeDEPositiveTD.LowSeparated.lateCubic_derivative d)
    intro d hd
    have hd2 := pow_le_pow_left₀ (show 0≤d by linarith [hd.1]) hd.2.le 2
    norm_num [frameCap] at hd2
    nlinarith [hd.1]
  have hh := hm (by norm_num [frameCap]) hd hd.1
  norm_num [NegativeDEPositiveTD.LowSeparated.lateCubic] at hh
  linarith

theorem separated_negative_slope (atH : Bool) {θ s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc (0:ℝ) (1/10)) :
    Vd R (Explicit.k .small .low θ) (NegativeDEPositiveTD.LowSeparated.larger atH θ)
      (frameCap-s)<931/1000 := by
  have hp := NegativeDEPositiveTD.LowSeparated.actual_pair_domain atH hθ
  have hd : frameCap-s∈Icc (3/5:ℝ) frameCap := by
    norm_num [frameCap]
    exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hm := NegativeDEPositiveTD.LowSeparated.quadratic_model hp.1 hp.2.1 hp.2.2
    (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hd.1],hd.2⟩)
  have hA := NegativeDEPositiveTD.LowSeparated.A_late_upper
    (show frameCap-s∈Icc (9/25:ℝ) frameCap from ⟨by linarith [hd.1],hd.2⟩)
  have hproduct := mul_nonpos_of_nonpos_of_nonneg
    (show NegativeDEPositiveTD.LowSeparated.A (frameCap-s)+389/4000≤0 by linarith)
    (sub_nonneg.mpr hp.2.2.1)
  have he (d q : ℝ) : NegativeDEPositiveTD.LowSeparated.B d+
      NegativeDEPositiveTD.LowSeparated.A d*(q-NegativeDEPositiveTD.LowSeparated.q0)-
      (389/2000)*(q-NegativeDEPositiveTD.LowSeparated.q0)^2=
      NegativeDEPositiveTD.LowSeparated.lateCubic d+
        (NegativeDEPositiveTD.LowSeparated.A d+389/4000)*(q-1)-(389/2000)*(q-1)^2 := by
    dsimp [NegativeDEPositiveTD.LowSeparated.A,NegativeDEPositiveTD.LowSeparated.B,
      NegativeDEPositiveTD.LowSeparated.lateCubic,NegativeDEPositiveTD.LowSeparated.q0]
    ring
  rw [he] at hm
  have hc := late_cubic_bound hd
  change Vd R (Explicit.k .small .low θ) _ _<_
  nlinarith [sq_nonneg (NegativeDEPositiveTD.LowSeparated.larger atH θ-1)]

theorem separated_monotone (atH : Bool) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => NegativeEH.g s+
      V R (Explicit.k .small .low θ) (NegativeDEPositiveTD.LowSeparated.larger atH θ) (frameCap-s))
      (Icc (0:ℝ) (1/10)) := by
  have hp := NegativeDEPositiveTD.LowSeparated.actual_pair_domain atH hθ
  have hq : 0<NegativeDEPositiveTD.LowSeparated.larger atH θ := by linarith [hp.2.2.1]
  have hd (s : ℝ) (hs : s∈Icc (0:ℝ) (1/10)) :=
    (NegativeEH.g_hasDerivAt s).add
      ((V_hasDerivAt hp.1 hq (show frameCap-s∈Icc 0 frameCap by
        norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2])).comp s
          ((hasDerivAt_id s).const_sub frameCap))
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  have hg := NegativeEH.small_slope (Ioo_subset_Icc_self hs)
  have hv := separated_negative_slope atH hθ (Ioo_subset_Icc_self hs)
  norm_num only [mul_neg_one]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallLow
