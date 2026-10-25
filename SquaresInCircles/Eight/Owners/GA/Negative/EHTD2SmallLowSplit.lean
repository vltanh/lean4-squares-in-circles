module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Low
public import SquaresInCircles.Eight.Owners.GA.Negative.EHPositiveD
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2Blocks
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SmallEndpoints

/-!
# Eight squares: small-EH low-total intrinsic endpoints at the original split

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
