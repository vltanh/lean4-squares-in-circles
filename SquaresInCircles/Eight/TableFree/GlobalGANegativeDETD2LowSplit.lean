module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowSeparated
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveScalar

/-!
# The five low negative-DE endpoints at the original A/TD split

Uncompiled endpoint join of the complete scalar companion. Coefficients
are frozen at theta while a ranges over [0,theta]. The separated terms
retain their exact U contribution during split concavity; its linear
allowance is used only at the two certified split endpoints. No concavity
of an unreduced saturated two-angle term is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def zeroScalar (θ a : ℝ) : ℝ := Explicit.baseline .low a (θ-a) 0
def HScalar (θ a : ℝ) : ℝ := zeroScalar θ a+V R (Explicit.k .low θ) 1 θ
def GScalar (θ a : ℝ) : ℝ := HScalar θ a+
  Explicit.k .low θ*(phi (frameCap-θ)-1)+Explicit.l .low θ*(Real.cos frameCap-Real.cos θ)
def equalScalar (θ a : ℝ) : ℝ := Explicit.baseline .low a (θ-a) θ
def separatedScalar (θ : ℝ) (i : Fin 3) (atH : Bool) (a : ℝ) : ℝ :=
  zeroScalar θ a+Explicit.U .low θ (θ-a) i (frameCap-θ)+
    V R (Explicit.k .low θ) (LowSeparated.larger atH θ) frameCap

theorem zero_identity (θ a : ℝ) :
    zeroScalar θ a=TwoPositive.splitBase (Explicit.k .low θ) (Explicit.l .low θ)
      (Explicit.c .low θ) θ a := by
  simp only [zeroScalar,Explicit.baseline,show a+(θ-a)=θ by ring,
    Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,add_zero,sub_zero,
    TwoPositive.splitBase,PositiveTD.baseline]
  dsimp [Explicit.m,Explicit.eta,Explicit.sigma,PositiveTD.tilted,PositiveTD.eta,PositiveTD.sigma]
  ring

theorem equal_identity {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (a : ℝ) :
    equalScalar θ a=zeroScalar θ a+LowD.diagonalCorrection θ := by
  have hh := LowD.diagonal_baseline (a:=a) (z:=θ-a) (s:=θ)
    (by simpa only [show a+(θ-a)=θ by ring] using hθ)
    (by simpa only [show a+(θ-a)=θ by ring] using And.intro hθ.1 (le_rfl : θ≤θ))
  exact hh

theorem split_ranges {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<Explicit.c .low θ ∧ 0<Explicit.l .low θ ∧
      Explicit.c .low θ≤(3/2)*Explicit.l .low θ ∧
      (∀a∈Icc 0 θ,PositiveTD.tilted (Explicit.c .low θ) (θ-a)≤(3/2)*Explicit.l .low θ) := by
  have hr := Explicit.low_ranges hθ
  have hc : 0<Explicit.c .low θ := by linarith [hr.2.2.2.2.1]
  have hl : 0<Explicit.l .low θ := by linarith [hr.2.2.1]
  have hm := Explicit.low_tilted hθ (show (0:ℝ)∈Icc 0 θ from ⟨le_rfl,hθ.1⟩)
  refine ⟨hc,hl,by nlinarith [hm.1,hm.2],?_⟩
  intro a ha
  have hz : θ-a∈Icc 0 θ := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  have hh := (Explicit.low_tilted hθ hz).2
  change Explicit.m .low θ (θ-a)≤(3/2)*Explicit.l .low θ
  nlinarith

theorem zero_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    ConcaveOn ℝ (Icc 0 θ) (zeroScalar θ) := by
  have hr := split_ranges hθ
  apply TwoPositive.Split.congr_on
    (TwoPositive.low_base_concave (k:=Explicit.k .low θ) hr.1 hr.2.1 hr.2.2.1 hθ hr.2.2.2)
  intro a _
  exact (zero_identity θ a).symm

theorem H_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    ConcaveOn ℝ (Icc 0 θ) (HScalar θ) :=
  TwoPositive.Split.add_constant (zero_concave hθ) (V R (Explicit.k .low θ) 1 θ)

theorem G_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    ConcaveOn ℝ (Icc 0 θ) (GScalar θ) :=
  TwoPositive.Split.add_constant
    (TwoPositive.Split.add_constant (H_concave hθ) (Explicit.k .low θ*(phi (frameCap-θ)-1)))
    (Explicit.l .low θ*(Real.cos frameCap-Real.cos θ))

theorem equal_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    ConcaveOn ℝ (Icc 0 θ) (equalScalar θ) := by
  apply TwoPositive.Split.congr_on
    (TwoPositive.Split.add_constant (zero_concave hθ) (LowD.diagonalCorrection θ))
  intro a _
  exact (equal_identity hθ a).symm

theorem positive_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (i : Fin 3) :
    ConcaveOn ℝ (Icc 0 θ)
      (fun a => zeroScalar θ a+Explicit.U .low θ (θ-a) i (frameCap-θ)) := by
  have hr := split_ranges hθ
  have hP : frameCap-θ∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  fin_cases i
  · simpa only [Explicit.U,Explicit.p,Explicit.q,Matrix.cons_val_zero] using
      TwoPositive.Split.add_constant (zero_concave hθ) (U R (Explicit.k .low θ) 1 (frameCap-θ))
  · simpa only [Explicit.U,Explicit.p,Explicit.q,Matrix.cons_val_succ,Matrix.cons_val_zero] using
      TwoPositive.Split.add_constant (zero_concave hθ)
        (U R (Explicit.k .low θ) (Explicit.l .low θ) (frameCap-θ))
  · have hh := TwoPositive.Split.low_increment_concave
      (k:=Explicit.k .low θ) (s:=frameCap-θ) (g:=phi (frameCap-θ)-1) (e:=0)
      hr.1 hr.2.1 hr.2.2.1 hθ
      (by rw [abs_of_nonneg hP.1]; exact hP.2)
      (sub_nonneg.mpr (TwoPositive.Split.phi_ge_one hP)) le_rfl
      (by linarith [Real.cos_le_one frameCap]) (by simp) hr.2.2.2
    apply TwoPositive.Split.congr_on hh
    intro a _
    rw [TwoPositive.Split.increment_U,←zero_identity]
    rfl

theorem separated_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (i : Fin 3) (atH : Bool) : ConcaveOn ℝ (Icc 0 θ) (separatedScalar θ i atH) :=
  TwoPositive.Split.add_constant (positive_concave hθ i)
    (V R (Explicit.k .low θ) (LowSeparated.larger atH θ) frameCap)

theorem H_positive {θ a : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (ha : a∈Icc 0 θ) :
    0<HScalar θ a := by
  have h0 : 0<HScalar θ 0 := by
    simpa only [HScalar,zeroScalar,Certificate.lowBase,Explicit.splitA,Explicit.splitT,sub_zero]
      using Certificate.low_H_positive .atT hθ
  have h1 : 0<HScalar θ θ := by
    simpa only [HScalar,zeroScalar,Certificate.lowBase,Explicit.splitA,Explicit.splitT,sub_self]
      using Certificate.low_H_positive .atA hθ
  exact concave_gt_of_endpoints (H_concave hθ) ha h0 h1

theorem G_positive {θ a : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (ha : a∈Icc 0 θ) :
    0<GScalar θ a := by
  have h0 : 0<GScalar θ 0 := by
    simpa only [GScalar,HScalar,zeroScalar,Certificate.lowBase,Explicit.splitA,Explicit.splitT,sub_zero]
      using Certificate.low_M_positive .atT hθ
  have h1 : 0<GScalar θ θ := by
    simpa only [GScalar,HScalar,zeroScalar,Certificate.lowBase,Explicit.splitA,Explicit.splitT,sub_self]
      using Certificate.low_M_positive .atA hθ
  exact concave_gt_of_endpoints (G_concave hθ) ha h0 h1

theorem equal_positive {θ a : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (ha : a∈Icc 0 θ) :
    0<equalScalar θ a := by
  have h0 : 0<equalScalar θ 0 := by
    simpa only [equalScalar,Certificate.lowBase,Explicit.splitA,Explicit.splitT,sub_zero]
      using Certificate.low_Z_positive .atT hθ
  have h1 : 0<equalScalar θ θ := by
    simpa only [equalScalar,Certificate.lowBase,Explicit.splitA,Explicit.splitT,sub_self]
      using Certificate.low_Z_positive .atA hθ
  exact concave_gt_of_endpoints (equal_concave hθ) ha h0 h1

theorem separated_endpoint (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (i : Fin 3) (atH : Bool) :
    0<Explicit.baseline .low (Explicit.splitA e θ) (Explicit.splitT e θ) 0+
      Explicit.U .low θ (Explicit.splitT e θ) i (frameCap-θ)+
        V R (Explicit.k .low θ) (LowSeparated.larger atH θ) frameCap := by
  have hf : θ∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hu := LowSeparated.positive_allowance hθ (Certificate.split_angles e hf).2.1 i
  cases atH
  · have hh := Certificate.low_SG_positive e hθ
    simp only [Certificate.lowBase,Explicit.splitM,LowSeparated.larger,Bool.false_eq_true,if_false] at hh ⊢
    linarith
  · have hh := Certificate.low_SH_positive e hθ
    simp only [Certificate.lowBase,Explicit.splitM,LowSeparated.larger,if_true] at hh ⊢
    linarith

theorem separated_positive {θ a : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ha : a∈Icc 0 θ) (i : Fin 3) (atH : Bool) : 0<separatedScalar θ i atH a := by
  have h0 : 0<separatedScalar θ i atH 0 := by
    simpa only [separatedScalar,zeroScalar,Explicit.splitA,Explicit.splitT,sub_zero]
      using separated_endpoint .atT hθ i atH
  have h1 : 0<separatedScalar θ i atH θ := by
    simpa only [separatedScalar,zeroScalar,Explicit.splitA,Explicit.splitT,sub_self]
      using separated_endpoint .atA hθ i atH
  exact concave_gt_of_endpoints (separated_concave hθ i atH) ha h0 h1

/-- All five intrinsic expressions are positive at the unchanged
original split, rather than only at its two scalar comparison endpoints. -/
theorem original_endpoints {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) 1 (a+z) ∧
    0<LowSame.zeroEnvelope a z ∧ 0<Explicit.baseline .low a z (a+z) ∧
    (∀i : Fin 3,∀atH : Bool,
      0<Explicit.baseline .low a z 0+Explicit.U .low (a+z) z i (frameCap-(a+z))+
        V R (Explicit.k .low (a+z)) (LowSeparated.larger atH (a+z)) frameCap) := by
  have ha' : a∈Icc 0 (a+z) := ⟨ha,by linarith⟩
  have hH := H_positive hθ ha'
  have hG := G_positive hθ ha'
  have hZ := equal_positive hθ ha'
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [HScalar,zeroScalar,show a+z-a=z by ring] using hH
  · simpa only [GScalar,HScalar,zeroScalar,LowSame.zeroEnvelope,show a+z-a=z by ring] using hG
  · simpa only [equalScalar,show a+z-a=z by ring] using hZ
  · intro i atH
    simpa only [separatedScalar,zeroScalar,show a+z-a=z by ring]
      using separated_positive hθ ha' i atH

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSplit
