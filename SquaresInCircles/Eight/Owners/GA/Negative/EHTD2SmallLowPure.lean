module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Source
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSeparated
public import SquaresInCircles.Eight.Owners.GA.Negative.EHSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSlopes

/-!
# Eight squares: both pure-surplus signs in the small-EH low family

Positive surplus
increases from s=theta. Negative surplus is reduced to the H pair and
then to s=0 or s=min(theta,.1) by concavity. The original split is fixed
through both reductions, and the closed zero-surplus endpoint is shared.
-/

section
/-!
## Small-EH low-total intrinsic endpoints at the original split

The s=0 endpoints are
exactly the already proved negative-DE low endpoints. The two new EH
endpoints keep their original coefficients and reduce only in the scalar
A/TD split. The D positive singleton is compared with the exact H U term,
so no concavity of a linearly weakened split expression is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem baseline_identity (a z : ℝ) :
    Explicit.baseline .small .low a z=NegativeDEPositiveTD.Explicit.baseline .low a z 0 := by
  simp only [Explicit.baseline,Explicit.sortedD,↓reduceIte,Explicit.k,Explicit.l,Explicit.c,Explicit.m,
    Explicit.eta,Explicit.sigma,NegativeDEPositiveTD.Explicit.baseline,NegativeDEPositiveTD.Explicit.m,
    NegativeDEPositiveTD.Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,
    sub_self,mul_zero,add_zero]
  ring

theorem zero_split_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => Explicit.baseline .small .low a (θ-a)) := by
  have he : (fun a => Explicit.baseline .small .low a (θ-a))=
      NegativeDEPositiveTD.LowSplit.zeroScalar θ := by
    funext a
    rw [baseline_identity]
    rfl
  rw [he]
  exact NegativeDEPositiveTD.LowSplit.zero_concave hθ

theorem equal_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/10)) (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .small .low a z+NegativeEH.g (a+z) := by
  have hlow : a+z∈Icc (0:ℝ) (1/6) := ⟨hθ.1,by linarith [hθ.2]⟩
  have hc := TwoPositive.Split.add_constant (zero_split_concave hlow) (NegativeEH.g (a+z))
  have h0 : 0<Explicit.baseline .small .low 0 (a+z-0)+NegativeEH.g (a+z) := by
    simpa only [NegativeDEPositiveTD.Explicit.splitA,NegativeDEPositiveTD.Explicit.splitT,
      sub_zero] using Certificate.small_low_equal_positive .atT hθ
  have h1 : 0<Explicit.baseline .small .low (a+z) (a+z-(a+z))+NegativeEH.g (a+z) := by
    simpa only [NegativeDEPositiveTD.Explicit.splitA,NegativeDEPositiveTD.Explicit.splitT,
      sub_self] using Certificate.small_low_equal_positive .atA hθ
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩) h0 h1
  simpa only [show a+z-a=z by ring] using hh

theorem negative_at_v_positive {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .small .low a z+NegativeEH.g (1/10)+
      V R (Explicit.k .small .low (a+z)) 1 (a+z-1/10) := by
  have hlow : a+z∈Icc (0:ℝ) (1/6) := ⟨by linarith [hθ.1],hθ.2⟩
  have hc := TwoPositive.Split.add_constant
    (TwoPositive.Split.add_constant (zero_split_concave hlow) (NegativeEH.g (1/10)))
      (V R (Explicit.k .small .low (a+z)) 1 (a+z-1/10))
  have h0 : 0<Explicit.baseline .small .low 0 (a+z-0)+NegativeEH.g (1/10)+
      V R (Explicit.k .small .low (a+z)) 1 (a+z-1/10) := by
    simpa only [NegativeDEPositiveTD.Explicit.splitA,NegativeDEPositiveTD.Explicit.splitT,
      sub_zero] using Certificate.small_low_negative_positive .atT hθ
  have h1 : 0<Explicit.baseline .small .low (a+z) (a+z-(a+z))+NegativeEH.g (1/10)+
      V R (Explicit.k .small .low (a+z)) 1 (a+z-1/10) := by
    simpa only [NegativeDEPositiveTD.Explicit.splitA,NegativeDEPositiveTD.Explicit.splitT,
      sub_self] using Certificate.small_low_negative_positive .atA hθ
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩) h0 h1
  simpa only [show a+z-a=z by ring] using hh

theorem zero_H_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .small .low a z+V R (Explicit.k .small .low (a+z)) 1 (a+z) := by
  rw [baseline_identity]
  exact (NegativeDEPositiveTD.LowSplit.original_endpoints hθ ha hz).1

theorem zero_G_same_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .small .low a z+mixedBlock R
      (Explicit.k .small .low (a+z)) (Explicit.l .small .low (a+z)) (frameCap-(a+z)) frameCap := by
  have hh := NegativeDEPositiveTD.Low.same_positive hθ ha hz
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) (1:Fin 3)
  rw [sub_zero] at hh
  rw [baseline_identity]
  exact hh

theorem zero_separated_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 4) (atH : Bool) :
    0<Explicit.baseline .small .low a z+Blocks.positive .small .low (a+z) z (frameCap-(a+z)) i+
      V R (Explicit.k .small .low (a+z))
        (NegativeDEPositiveTD.LowSeparated.larger atH (a+z)) frameCap := by
  have he := (NegativeDEPositiveTD.LowSplit.original_endpoints hθ ha hz).2.2.2
  by_cases hi : i=3
  · subst hi
    have hp := he 0 atH
    have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
    have hP : frameCap-(a+z)∈Icc 0 frameCap :=
      ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
    have hD := NegativeEH.PositiveD.H_le_D (ε:=0)
      (k:=NegativeDEPositiveTD.Explicit.k .low (a+z)) ⟨by linarith [hr.1],by linarith [hr.2.1]⟩ hP
    simp only [NegativeDEPositiveTD.Explicit.U,NegativeDEPositiveTD.Explicit.p,
      NegativeDEPositiveTD.Explicit.q,Matrix.cons_val_zero] at hp
    rw [baseline_identity,Blocks.positive_D]
    simp only [Explicit.errorCharge,Explicit.k,add_zero,zero_mul,sub_zero] at hD ⊢
    dsimp [Blocks.dCost]
    linarith
  · have hi3 : i.val<3 := by
      have h4 := i.isLt
      have h3 : i.val≠3 := fun h => hi (Fin.ext h)
      omega
    obtain ⟨j,hj⟩ : ∃j : Fin 3,j.castSucc=i := ⟨⟨i.val,hi3⟩,Fin.ext rfl⟩
    subst hj
    have hh := he j atH
    rw [baseline_identity,Blocks.positive_ordinary]
    simp only [Explicit.errorCharge,zero_mul,sub_zero]
    exact hh

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallLow
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallLow
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
  have hq2 : NegativeDEPositiveTD.Explicit.q .low θ z i≤233/125 := hp.2.2.2.2
  rw [mul_one]
  linarith

theorem positive_comparison {θ z t : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (_hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) (i : Fin 4) :
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
      (k:=NegativeDEPositiveTD.Explicit.k .low θ) ⟨by linarith [hr.1],by linarith [hr.2.1]⟩ ht
    simpa [Blocks.positive_D,Blocks.dCost,Explicit.U,Explicit.p,Explicit.q,Explicit.k,
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
  simp only [sub_self,Explicit.U,U_zero,add_zero] at hm hj
  have he := equal_positive hθv ha hz
  linarith

theorem H_negative_concave {θ z : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (_hz : z∈Icc 0 θ) :
    ConcaveOn ℝ (Icc 0 (min θ (1/10)))
      (fun s => NegativeEH.g s+V R (Explicit.k .small .low θ) 1 (θ-s)) := by
  have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
  have hU : min θ (1/10:ℝ)≤frameCap := by
    simp only [frameCap]; linarith [min_le_right θ (1/10:ℝ)]
  have hg := NegativeEH.g_concave.subset (Icc_subset_Icc le_rfl hU)
    (convex_Icc 0 (min θ (1/10)))
  have hv := concave_affine_argument
    (V_concave (R:=R) (p:=NegativeDEPositiveTD.Explicit.k .low θ) (q:=1) (Real.sqrt_nonneg qCap) radius_sq.le
      (by linarith [hr.1]) (by linarith [hr.2.1]) (by linarith [hr.1]))
    (a:=-1) (b:=θ) (l:=0) (u:=min θ (1/10))
    (fun s hs => ⟨by linarith [hs.2,min_le_left θ (1/10:ℝ)],by simp only [frameCap]; linarith [hs.1,hθ.2]⟩)
  have he : (fun s => NegativeEH.g s+V R (Explicit.k .small .low θ) 1 (θ-s))=
      NegativeEH.g+(fun x => V R (NegativeDEPositiveTD.Explicit.k .low θ) 1 (-1*x+θ)) := by
    funext s
    simp only [Pi.add_apply]
    rw [show -1*s+θ=θ-s by ring]
    rfl
  rw [he]
  exact hg.add hv

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
    rw [show NegativeEH.g 0=0 by simp [NegativeEH.g],sub_zero,add_zero]
    exact zero_H_positive hθ ha hz
  have h1 : 0<Explicit.baseline .small .low a z+NegativeEH.g (min (a+z) (1/10))+
      V R (Explicit.k .small .low (a+z)) 1 (a+z-min (a+z) (1/10)) := by
    by_cases hv : a+z≤1/10
    · rw [min_eq_left hv,sub_self,V_zero,add_zero]
      exact equal_positive ⟨hθ.1,hv⟩ ha hz
    · rw [min_eq_right (lt_of_not_ge hv).le]
      exact negative_at_v_positive ⟨(lt_of_not_ge hv).le,hθ.2⟩ ha hz
  have hpositive : 0<Explicit.baseline .small .low a z+NegativeEH.g s+
      V R (Explicit.k .small .low (a+z)) 1 (a+z-s) := by
    have hl : 0<NegativeEH.g 0+V R (Explicit.k .small .low (a+z)) 1 (a+z-0)+
        Explicit.baseline .small .low a z := by linarith only [h0]
    have hu : 0<NegativeEH.g (min (a+z) (1/10))+
        V R (Explicit.k .small .low (a+z)) 1 (a+z-min (a+z) (1/10))+
        Explicit.baseline .small .low a z := by linarith only [h1]
    have hh := concave_gt_of_endpoints (c:=0) hc ⟨hs.1,le_min horder hs.2⟩ hl hu
    linarith only [hh]
  have hb := NegativeDEPositiveTD.LowNegative.pure_comparison hθ hzd
    (show a+z-s∈Icc 0 (a+z) from ⟨by linarith,by linarith [hs.1]⟩) (Blocks.ordinaryIndex i)
  have hb' : V R (Explicit.k .small .low (a+z)) 1 (a+z-s)≤
      NegativeDEPositiveTD.Explicit.V .low (a+z) z (Blocks.ordinaryIndex i) (a+z-s) := hb
  rw [Blocks.negative_to_ordinary]
  change 0<Explicit.baseline .small .low a z+NegativeEH.g s+
    NegativeDEPositiveTD.Explicit.V .low (a+z) z (Blocks.ordinaryIndex i) (a+z-s)
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallLow
end
end
end
