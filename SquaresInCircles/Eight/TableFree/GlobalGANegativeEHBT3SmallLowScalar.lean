module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3SmallLowSlopes

/-!
# Complete small-EH, low-total BT3 scalar exclusion

Uncompiled Section 4. Both surplus signs and every same/separated
allocation are included. The D positive penalty and H negative minorant
remain paired in the distinguished block. The original A/BT split is
held fixed during the EH-magnitude comparisons.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma pure_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) (1/10:ℝ)) (i : Fin 4) :
    0<baseline .smallLow (a+z) a z+gain s+positive (a+z) (s-(a+z)) i := by
  have ht : a+z∈Icc (0:ℝ) (1/10) := ⟨hθ.1,hs.1.trans hs.2⟩
  have hh := positive_monotone hθ i (show a+z∈Icc (a+z) (1/10:ℝ) from ⟨le_rfl,ht.2⟩)
    hs hs.1
  simp only [sub_self,positive,PositiveTD.Hybrid.positive_zero,add_zero] at hh
  linarith [equal_positive ht ha hz]

lemma pure_negative {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (0:ℝ) (1/10))
    (horder : s≤a+z) (i : Fin 4) :
    0<baseline .smallLow (a+z) a z+gain s+negative (a+z) (a+z-s) i := by
  have hk := low_k_range hθ
  have hg := NegativeEH.g_concave.subset
    (Icc_subset_Icc le_rfl
      (show min (a+z) (1/10:ℝ)≤frameCap by norm_num [frameCap]; linarith [min_le_right (a+z) (1/10:ℝ)]))
    (convex_Icc 0 (min (a+z) (1/10:ℝ)))
  have hv := concave_affine_argument
    (V_concave (R:=R) (p:=k (a+z)) (q:=1) (Real.sqrt_nonneg qCap) radius_sq.le
      (by linarith [hk.1]) (by linarith [hk.2]) (by linarith [hk.1]))
    (a:=-1) (b:=a+z) (l:=0) (u:=min (a+z) (1/10))
    (fun t ht => ⟨by linarith [ht.2,min_le_left (a+z) (1/10:ℝ)],
      by norm_num [frameCap]; linarith [ht.1,hθ.2]⟩)
  have hc := TwoPositive.Split.add_constant (hg.add hv) (baseline .smallLow (a+z) a z)
  have h0 : 0<baseline .smallLow (a+z) a z+gain 0+V R (k (a+z)) 1 (a+z-0) := by
    simpa [gain] using zero_positive hθ ha hz
  have h1 : 0<baseline .smallLow (a+z) a z+gain (min (a+z) (1/10))+
      V R (k (a+z)) 1 (a+z-min (a+z) (1/10)) := by
    by_cases ht : a+z≤1/10
    · simpa [min_eq_left ht] using equal_positive ⟨hθ.1,ht⟩ ha hz
    · simpa [min_eq_right (lt_of_not_ge ht).le] using
        negative_at_v_positive ⟨(lt_of_not_ge ht).le,hθ.2⟩ ha hz
  have hh := concave_gt_of_endpoints hc ⟨hs.1,le_min horder hs.2⟩
    (by simpa [neg_one_mul,neg_add_eq_sub,add_comm,add_left_comm,add_assoc] using h0)
    (by simpa [neg_one_mul,neg_add_eq_sub,add_comm,add_left_comm,add_assoc] using h1)
  have hH : 0<baseline .smallLow (a+z) a z+gain s+V R (k (a+z)) 1 (a+z-s) := by
    simpa [neg_one_mul,neg_add_eq_sub,add_comm,add_left_comm,add_assoc] using hh
  have hcmp := H_le_negative hθ
    (show a+z-s∈Icc 0 frameCap from ⟨by linarith,
      by norm_num [frameCap]; linarith [hs.1,hθ.2]⟩) i
  linarith

lemma separated_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (0:ℝ) (1/10)) (i j : Fin 4) :
    0<baseline .smallLow (a+z) a z+gain s+
      positive (a+z) (frameCap-(a+z)) i+negative (a+z) (frameCap-s) j := by
  have hm := separated_monotone hθ (show (0:ℝ)∈Icc 0 (1/10:ℝ) by norm_num) hs hs.1
  simp only [gain,Real.sin_zero,Real.cos_zero,mul_zero,sub_self,sub_zero,zero_add] at hm
  have hcmp := H_le_negative hθ
    (show frameCap-s∈Icc 0 frameCap by
      norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2]) j
  have hzero := zero_separated_lower hθ i 0
  change V R (k (a+z)) 1 (a+z)≤
    positive (a+z) (frameCap-(a+z)) i+V R (k (a+z)) 1 frameCap at hzero
  have hp := zero_positive hθ ha hz
  linarith

lemma same_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 4) :
    0<baseline .smallLow (a+z) a z+gain s+
      block (a+z) (frameCap-(a+z)) (frameCap-s) i := by
  have hP : frameCap-(a+z)∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap := by
    norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2]
  fin_cases i
  · have hm := HG_same_monotone hθ (show (0:ℝ)∈Icc 0 (1/10:ℝ) by norm_num) hs hs.1
    have hzero := zero_same_lower hθ 0
    have hp := zero_positive hθ ha hz
    simp only [HG_same,gain,Real.sin_zero,Real.cos_zero,mul_zero,sub_self,sub_zero,zero_add] at hm
    change V R (k (a+z)) 1 (a+z)≤mixedBlock R (k (a+z)) 1 (frameCap-(a+z)) frameCap at hzero
    change 0<baseline .smallLow (a+z) a z+gain s+
      mixedBlock R (k (a+z)) 1 (frameCap-(a+z)) (frameCap-s)
    linarith
  · have hm := HG_same_monotone hθ (show (0:ℝ)∈Icc 0 (1/10:ℝ) by norm_num) hs hs.1
    have hzero := zero_same_lower hθ 1
    have hp := zero_positive hθ ha hz
    simp only [HG_same,gain,Real.sin_zero,Real.cos_zero,mul_zero,sub_self,sub_zero,zero_add] at hm
    change V R (k (a+z)) 1 (a+z)≤mixedBlock R (k (a+z)) 1 (frameCap-(a+z)) frameCap at hzero
    change 0<baseline .smallLow (a+z) a z+gain s+
      mixedBlock R (k (a+z)) 1 (frameCap-(a+z)) (frameCap-s)
    linarith
  · have hc := coefficients hθ 2
    have hmq : m (a+z)≤5821/5000 := hc.2.2.2
    have hm : 0≤m (a+z) := by change 0≤q (a+z) 2; exact (hc.1.trans_le hc.2.1).le
    by_cases horder : s≤a+z
    · have hsin := mul_le_mul_of_nonneg_left (transport_trig hN).2.2.2.1.le hm
      have hcmp := NegativeAPositiveTD.SameBlock.negative_surplus
        (by norm_num : (0:ℝ)≤1)
        (show frameCap-(a+z)∈Icc 0 (frameCap-s) from ⟨hP.1,by linarith⟩) hN
        (show m (a+z)*Real.sin (frameCap-s)≤1 by
          nlinarith [hmq])
      have hp := pure_negative hθ ha hz hs horder 2
      simpa only [block,PositiveTD.Hybrid.block,show (2:Fin 4)≠3 by decide,if_false,
        p,q,PositiveBT3.LowEnvelope.p,PositiveBT3.LowEnvelope.q,
        Matrix.cons_val_succ,Matrix.cons_val_zero] using
        (show 0<baseline .smallLow (a+z) a z+gain s+
          mixedBlock R 1 (m (a+z)) (frameCap-(a+z)) (frameCap-s) by
            change 0<baseline .smallLow (a+z) a z+gain s+V R 1 (m (a+z)) (a+z-s) at hp
            rw [show frameCap-s-(frameCap-(a+z))=a+z-s by ring] at hcmp
            linarith)
    · have hcmp := NegativeAPositiveTD.SameBlock.positive_surplus
        (by norm_num : (0:ℝ)≤1)
        (show m (a+z)≤(17/10)*1 by linarith [hmq]) hP
        (show frameCap-s∈Icc 0 (frameCap-(a+z)) from ⟨hN.1,by linarith⟩)
      have hp := pure_positive hθ ha hz ⟨(lt_of_not_ge horder).le,hs.2⟩ 2
      change 0<baseline .smallLow (a+z) a z+gain s+U R 1 (m (a+z)) (s-(a+z)) at hp
      change 0<baseline .smallLow (a+z) a z+gain s+
        mixedBlock R 1 (m (a+z)) (frameCap-(a+z)) (frameCap-s)
      rw [show frameCap-(a+z)-(frameCap-s)=s-(a+z) by ring] at hcmp
      linarith
  · simpa [block,positive,negative,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive,
      add_assoc] using separated_positive hθ ha hz hs 3 3

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<baseline .smallLow (a+z) a z+charge .smallLow s+
      ∑i,block (a+z) (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := concentrate P N hθ hs hP hN hPb hNb hbalance
  have hp : 0<baseline .smallLow (a+z) a z+gain s+pure (a+z) s i j := by
    by_cases horder : s≤a+z
    · simpa [pure,ChargedHybridConcentration.pure,horder,negative] using
        pure_negative hθ ha hz hs horder j
    · simpa [pure,ChargedHybridConcentration.pure,horder,
        ChargedHybridConcentration.positive,positive] using
        pure_positive hθ ha hz ⟨(lt_of_not_ge horder).le,hs.2⟩ i
  have ht : 0<baseline .smallLow (a+z) a z+gain s+saturated (a+z) s i j := by
    by_cases he : i=j
    · subst j
      simpa [saturated,ChargedHybridConcentration.saturated,ChargedHybridConcentration.block,block] using
        same_positive hθ ha hz hs i
    · simpa [saturated,ChargedHybridConcentration.saturated,ChargedHybridConcentration.positive,
        positive,negative,he,add_assoc] using separated_positive hθ ha hz hs i j
  have hm : -(baseline .smallLow (a+z) a z+gain s)<
      min (pure (a+z) s i j) (saturated (a+z) s i j) := lt_min (by linarith) (by linarith)
  simp only [charge,far,Bool.false_eq_true,if_false]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.SmallLow
