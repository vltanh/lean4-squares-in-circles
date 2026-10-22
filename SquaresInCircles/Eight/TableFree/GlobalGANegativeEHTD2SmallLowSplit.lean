module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHPositiveD

/-!
# Small-EH low-total intrinsic endpoints at the original split

Uncompiled Section 3 of the small-EH companion. The s=0 endpoints are
exactly the already proved negative-DE low endpoints. The two new EH
endpoints keep their original coefficients and reduce only in the scalar
A/TD split. The D positive singleton is compared with the exact H U term,
so no concavity of a linearly weakened split expression is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem baseline_identity (a z : ℝ) :
    Explicit.baseline .small .low a z=NegativeDEPositiveTD.Explicit.baseline .low a z 0 := by
  simp only [Explicit.baseline,Explicit.sortedD,if_true,Explicit.k,Explicit.l,Explicit.c,Explicit.m,
    Explicit.eta,Explicit.sigma,NegativeDEPositiveTD.Explicit.baseline,
    NegativeDEPositiveTD.Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,
    sub_self,mul_zero,add_zero,sub_zero]
  ring

theorem zero_split_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => Explicit.baseline .small .low a (θ-a)) := by
  simpa only [baseline_identity,NegativeDEPositiveTD.LowSplit.zeroScalar] using
    NegativeDEPositiveTD.LowSplit.zero_concave hθ

theorem equal_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/10)) (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .small .low a z+NegativeEH.g (a+z) := by
  let θ := a+z
  have hlow : θ∈Icc (0:ℝ) (1/6) := ⟨hθ.1,by linarith [hθ.2]⟩
  have hc := TwoPositive.Split.add_constant (zero_split_concave hlow) (NegativeEH.g θ)
  have h0 : 0<Explicit.baseline .small .low 0 (θ-0)+NegativeEH.g θ := by
    simpa only [Explicit.splitA,Explicit.splitT,sub_zero] using
      Certificate.small_low_equal_positive .atT hθ
  have h1 : 0<Explicit.baseline .small .low θ (θ-θ)+NegativeEH.g θ := by
    simpa only [Explicit.splitA,Explicit.splitT,sub_self] using
      Certificate.small_low_equal_positive .atA hθ
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩) h0 h1
  simpa only [θ,show a+z-a=z by ring] using hh

theorem negative_at_v_positive {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .small .low a z+NegativeEH.g (1/10)+
      V R (Explicit.k .small .low (a+z)) 1 (a+z-1/10) := by
  let θ := a+z
  have hlow : θ∈Icc (0:ℝ) (1/6) := ⟨by linarith [hθ.1],hθ.2⟩
  have hc := TwoPositive.Split.add_constant
    (TwoPositive.Split.add_constant (zero_split_concave hlow) (NegativeEH.g (1/10)))
      (V R (Explicit.k .small .low θ) 1 (θ-1/10))
  have h0 : 0<Explicit.baseline .small .low 0 (θ-0)+NegativeEH.g (1/10)+
      V R (Explicit.k .small .low θ) 1 (θ-1/10) := by
    simpa only [Explicit.splitA,Explicit.splitT,sub_zero] using
      Certificate.small_low_negative_positive .atT hθ
  have h1 : 0<Explicit.baseline .small .low θ (θ-θ)+NegativeEH.g (1/10)+
      V R (Explicit.k .small .low θ) 1 (θ-1/10) := by
    simpa only [Explicit.splitA,Explicit.splitT,sub_self] using
      Certificate.small_low_negative_positive .atA hθ
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩) h0 h1
  simpa only [θ,show a+z-a=z by ring] using hh

theorem zero_H_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .small .low a z+V R (Explicit.k .small .low (a+z)) 1 (a+z) := by
  rw [baseline_identity]
  exact (NegativeDEPositiveTD.LowSplit.original_endpoints hθ ha hz).1

theorem zero_G_same_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .small .low a z+mixedBlock R
      (Explicit.k .small .low (a+z)) (Explicit.l .small .low (a+z)) (frameCap-(a+z)) frameCap := by
  have hh := NegativeDEPositiveTD.Low.same_positive hθ ha hz
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) (1:Fin 3)
  simpa only [baseline_identity,Explicit.k,Explicit.l,NegativeDEPositiveTD.Explicit.p,
    NegativeDEPositiveTD.Explicit.q,Matrix.cons_val_succ,Matrix.cons_val_zero,sub_zero] using hh

theorem zero_separated_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 4) (atH : Bool) :
    0<Explicit.baseline .small .low a z+Blocks.positive .small .low (a+z) z (frameCap-(a+z)) i+
      V R (Explicit.k .small .low (a+z))
        (NegativeDEPositiveTD.LowSeparated.larger atH (a+z)) frameCap := by
  have he := (NegativeDEPositiveTD.LowSplit.original_endpoints hθ ha hz).2.2.2
  by_cases hi : i=3
  · subst i
    have hp := he 0 atH
    have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
    have hP : frameCap-(a+z)∈Icc 0 frameCap :=
      ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
    have hD := NegativeEH.PositiveD.H_le_D (ε:=0)
      (show Explicit.k .small .low (a+z)∈Icc (3/5:ℝ) (4/5) from
        ⟨by linarith [hr.1],by linarith [hr.2.1]⟩) hP
    simp only [NegativeDEPositiveTD.Explicit.U,NegativeDEPositiveTD.Explicit.p,
      NegativeDEPositiveTD.Explicit.q,Matrix.cons_val_zero] at hp
    rw [baseline_identity,Blocks.positive_D]
    simp only [Explicit.errorCharge,add_zero,zero_mul,sub_zero] at hD ⊢
    dsimp [Blocks.dCost]
    linarith
  · obtain ⟨j,hj⟩ : ∃j : Fin 3,j.castSucc=i := by
      fin_cases i <;> simp_all
    subst i
    have hh := he j atH
    simpa only [baseline_identity,Blocks.positive_ordinary,Explicit.errorCharge,zero_mul,sub_zero,
      Explicit.U,Explicit.p,Explicit.q,Explicit.k,Explicit.l,Explicit.m] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallLow
