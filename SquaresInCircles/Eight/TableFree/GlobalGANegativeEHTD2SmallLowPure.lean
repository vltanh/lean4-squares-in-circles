module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2SmallLowSlopes

/-!
# Both pure-surplus signs in the small-EH low family

Uncompiled Section 3 of the small-error companion. Positive surplus
increases from s=theta. Negative surplus is reduced to the H pair and
then to s=0 or s=min(theta,.1) by concavity. The original split is fixed
through both reductions, and the closed zero-surplus endpoint is shared.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryAngleConcentration
open NegativeAPositiveTD.PositiveSlope

theorem ordinary_positive_monotone {θ z : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    MonotoneOn (fun s => NegativeEH.g s+Explicit.U .small .low θ z i (s-θ))
      (Icc θ (1/10:ℝ)) := by
  have hp := NegativeDEPositiveTD.LowRanges.pairs hθ hz i
  have hq := hp.1.trans_le hp.2.1
  have hd (s : ℝ) (hs : s∈Icc θ (1/10:ℝ)) :=
    (NegativeEH.g_hasDerivAt s).add
      ((U_hasDerivAt hp.1 hq
        (show s-θ∈Icc 0 frameCap from ⟨by linarith [hs.1],by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩)).comp s
          ((hasDerivAt_id s).sub_const θ))
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  have hg := NegativeEH.small_slope
    (show s∈Icc (0:ℝ) (1/10) from ⟨by linarith [hs.1,hθ.1],hs.2.le⟩)
  have hu := NegativeEH.Slopes.small_positive hp.1 hp.2.1 hp.2.2.1
    (show s-θ∈Icc (0:ℝ) (1/10) from ⟨by linarith [hs.1],by linarith [hs.2,hθ.1]⟩)
  norm_num only [mul_one]
  nlinarith [hp.2.2.2.2]

theorem positive_comparison {θ z t : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    ∃j : Fin 3,Explicit.U .small .low θ z j t≤Blocks.positive .small .low θ z t i := by
  have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
  fin_cases i
  · exact ⟨0,by simp [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,
      Blocks.p,Blocks.q,Explicit.U,Explicit.p,Explicit.q,Explicit.errorCharge]⟩
  · exact ⟨1,by simp [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,
      Blocks.p,Blocks.q,Explicit.U,Explicit.p,Explicit.q,Explicit.errorCharge]⟩
  · exact ⟨2,by simp [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,
      Blocks.p,Blocks.q,Explicit.U,Explicit.p,Explicit.q,Explicit.errorCharge]⟩
  · refine ⟨0,?_⟩
    have hh := NegativeEH.PositiveD.H_le_D (ε:=0)
      (show Explicit.k .small .low θ∈Icc (3/5:ℝ) (4/5) from
        ⟨by linarith [hr.1],by linarith [hr.2.1]⟩) ht
    simpa [Blocks.positive_D,Blocks.dCost,Explicit.U,Explicit.p,Explicit.q,
      Explicit.errorCharge] using hh

theorem pure_positive_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (a+z) (1/10:ℝ)) (i : Fin 4) :
    0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.positive .small .low (a+z) z (s-(a+z)) i := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hθv : a+z∈Icc (0:ℝ) (1/10) := ⟨hθ.1,hs.1.trans hs.2⟩
  obtain ⟨j,hj⟩ := positive_comparison hθ hzd
    (show s-(a+z)∈Icc 0 frameCap from
      ⟨by linarith [hs.1],by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩) i
  have hm := ordinary_positive_monotone hθ hzd j ⟨le_rfl,hθv.2⟩ hs hs.1
  simp only [sub_self,Explicit.U,U_zero,add_zero] at hm
  have he := equal_positive hθv ha hz
  linarith

theorem H_negative_concave {θ z : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) :
    ConcaveOn ℝ (Icc 0 (min θ (1/10)))
      (fun s => NegativeEH.g s+V R (Explicit.k .small .low θ) 1 (θ-s)) := by
  have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
  have hU : min θ (1/10:ℝ)≤frameCap := by norm_num [frameCap]; linarith [min_le_right θ (1/10:ℝ)]
  have hg := NegativeEH.g_concave.subset (Icc_subset_Icc le_rfl hU)
    (convex_Icc 0 (min θ (1/10)))
  have hv := concave_affine_argument
    (V_concave (R:=R) (p:=Explicit.k .small .low θ) (q:=1) (Real.sqrt_nonneg qCap) radius_sq.le
      (by linarith [hr.1]) (by linarith [hr.2.1]) (by linarith [hr.1]))
    (a:=-1) (b:=θ) (l:=0) (u:=min θ (1/10))
    (fun s hs => ⟨by linarith [hs.2,min_le_left θ (1/10:ℝ)],by norm_num [frameCap]; linarith [hs.1,hθ.2]⟩)
  simpa only [neg_one_mul,neg_add_eq_sub] using hg.add hv

theorem pure_negative_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (horder : s≤a+z) (i : Fin 4) :
    0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.negative .small .low (a+z) z (a+z-s) i := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hc := TwoPositive.Split.add_constant (H_negative_concave hθ hzd)
    (Explicit.baseline .small .low a z)
  have h0 : 0<Explicit.baseline .small .low a z+NegativeEH.g 0+
      V R (Explicit.k .small .low (a+z)) 1 (a+z-0) := by
    simpa [NegativeEH.g,sub_zero] using zero_H_positive hθ ha hz
  have h1 : 0<Explicit.baseline .small .low a z+NegativeEH.g (min (a+z) (1/10))+
      V R (Explicit.k .small .low (a+z)) 1 (a+z-min (a+z) (1/10)) := by
    by_cases hv : a+z≤1/10
    · simpa [min_eq_left hv] using equal_positive ⟨hθ.1,hv⟩ ha hz
    · simpa [min_eq_right (lt_of_not_ge hv).le] using
        negative_at_v_positive ⟨(lt_of_not_ge hv).le,hθ.2⟩ ha hz
  have hpositive : 0<Explicit.baseline .small .low a z+NegativeEH.g s+
      V R (Explicit.k .small .low (a+z)) 1 (a+z-s) := by
    have hh := concave_gt_of_endpoints hc ⟨hs.1,le_min horder hs.2⟩
      (by linarith only [h0]) (by linarith only [h1])
    linarith only [hh]
  have hb := NegativeDEPositiveTD.LowNegative.pure_comparison hθ hzd
    (show a+z-s∈Icc 0 (a+z) from ⟨by linarith,by linarith [hs.1]⟩) (Blocks.ordinaryIndex i)
  rw [Blocks.negative_to_ordinary]
  change 0<Explicit.baseline .small .low a z+NegativeEH.g s+
    NegativeDEPositiveTD.Explicit.V .low (a+z) z (Blocks.ordinaryIndex i) (a+z-s)
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallLow
