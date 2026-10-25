module

public import SquaresInCircles.Eight.Frames.Ordinary.SignedBudgetConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2High
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Low
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowSeparated
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress

/-!
# Eight squares: the complete original negative-DE3 / positive-TD2 source exclusion

The low and high total ranges meet at the exact intrinsic value 1/6.
Both HG owners, all four original A-owner choices, arbitrary individual
A signs with nonnegative selected total, and all weak contacts remain
in the statement. No scalar positivity hypothesis remains.
-/

section
/-!
## The contradiction in the high-total negative-DE branch

The seven separator witnesses of the cycle give a nonpositive weighted stress, whereas the scalar
theorem `High.scalar_positive` is positive for their signed budgets (`high_original`). Both HG
owners, all four A owner choices, every sign of the single A errors and weak contacts are covered.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

theorem high_original {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12) (hlarge : (1/6:ℝ)≤total C ga ab)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  let k := Explicit.k .high (total C ga ab)
  let l := Explicit.l .high (total C ga ab)
  let c := Explicit.c .high (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hθ : total C ga ab∈Icc (1/6:ℝ) (7/10) := ⟨hlarge,hb.total_domain.2⟩
  have hn := scalar_nonpositive hg ga ab .high hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hz hs hflat hθ hfeasible
  have hp := High.scalar_positive
    (a:=aTotal C ga ab) (z:=delta C.theta T) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l c i).P)
    (fun i => (blocks C hg ga ab k l c i).N) hθ ha hz hb.de_domain
    (fun i => (blocks C hg ga ab k l c i).P_nonneg)
    (fun i => (blocks C hg ga ab k l c i).N_nonneg)
    hb.positive_bound hb.negative_bound hb.balance
  have hbase := fullBaseline_le .high (aTotal C ga ab) (delta C.theta T) (magnitude C)
  change 0<Explicit.fullBaseline .high (aTotal C ga ab) (delta C.theta T) (magnitude C)+
    ∑i,mixedBlock R (Explicit.p .high (total C ga ab) (delta C.theta T) i)
      (Explicit.q .high (total C ga ab) (delta C.theta T) i)
      (blocks C hg ga ab k l c i).P (blocks C hg ga ab k l c i).N at hp
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
end
end
end

section
/-!
## The five low negative-DE endpoints at the original A/TD split

Coefficients
are frozen at theta while a ranges over [0,theta]. The separated terms
retain their exact U contribution during split concavity; its linear
allowance is used only at the two certified split endpoints. No concavity
of an unreduced saturated two-angle term is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def zeroScalar (θ a : ℝ) : ℝ := Explicit.baseline .low a (θ-a) 0
def HScalar (θ a : ℝ) : ℝ := zeroScalar θ a+V R (Explicit.k .low θ) 1 θ
def GScalar (θ a : ℝ) : ℝ := HScalar θ a+
  Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+Explicit.l .low θ*(Real.cos frameCap-Real.cos θ)
def equalScalar (θ a : ℝ) : ℝ := Explicit.baseline .low a (θ-a) θ
def separatedScalar (θ : ℝ) (i : Fin 3) (atH : Bool) (a : ℝ) : ℝ :=
  zeroScalar θ a+Explicit.U .low θ (θ-a) i (frameCap-θ)+
    V R (Explicit.k .low θ) (LowSeparated.larger atH θ) frameCap

theorem zero_identity (θ a : ℝ) :
    zeroScalar θ a=TwoPositive.splitBase (Explicit.k .low θ) (Explicit.l .low θ)
      (Explicit.c .low θ) θ a := by
  simp only [zeroScalar,Explicit.baseline,show a+(θ-a)=θ by ring,
    Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,add_zero,
    TwoPositive.splitBase,PositiveTD.baseline]
  dsimp [Explicit.m,Explicit.eta,Explicit.sigma,PositiveTD.tilted,PositiveTD.eta,PositiveTD.sigma]
  ring

theorem equal_identity {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (a : ℝ) :
    equalScalar θ a=zeroScalar θ a+LowD.diagonalCorrection θ := by
  have he : a+(θ-a)=θ := by ring
  exact LowD.diagonal_baseline (a:=a) (z:=θ-a) (s:=θ) (by rw [he]; exact hθ)
    (by rw [he]; exact ⟨hθ.1,le_rfl⟩)

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
    (TwoPositive.Split.add_constant (H_concave hθ) (Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)))
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
    ⟨by simp only [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  fin_cases i
  · exact TwoPositive.Split.add_constant (zero_concave hθ) (U R (Explicit.k .low θ) 1 (frameCap-θ))
  · exact TwoPositive.Split.add_constant (zero_concave hθ)
      (U R (Explicit.k .low θ) (Explicit.l .low θ) (frameCap-θ))
  · have hh := TwoPositive.Split.low_increment_concave
      (k:=Explicit.k .low θ) (s:=frameCap-θ) (g:=PositiveAngularEnvelope.phi (frameCap-θ)-1)
      (e:=0) hr.1 hr.2.1 hr.2.2.1 hθ
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
    simp only [Certificate.lowBase,Explicit.splitM,LowSeparated.larger,Bool.false_eq_true,ite_false] at hh ⊢
    linarith
  · have hh := Certificate.low_SH_positive e hθ
    simp only [Certificate.lowBase,Explicit.splitM,LowSeparated.larger,ite_true] at hh ⊢
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

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSplit
end
end
end

section
/-!
## Complete low-total negative-DE / positive-TD2 scalar exclusion

Pure positive, pure negative,
same-block saturation, and distinct-block saturation are all included.
The ordinary concentration uses both original signed budgets and never
changes the original A/TD split or the actual E magnitude.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Low
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinarySignedBudgetConcentration

theorem pure_negative_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 (a+z)) (i : Fin 3) :
    0<Explicit.baseline .low a z s+Explicit.V .low (a+z) z i (a+z-s) := by
  have he := LowSplit.original_endpoints hθ ha hz
  have hmin : 0< min
      (Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) 1 (a+z))
      (Explicit.baseline .low a z (a+z)) := lt_min he.1 he.2.2.1
  have hh := hmin.trans_le (LowNegative.original_endpoint_lower hθ hs)
  have hc := LowNegative.pure_comparison hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
    (show a+z-s∈Icc 0 (a+z) from ⟨by linarith [hs.2],by linarith [hs.1]⟩) i
  linarith

theorem pure_positive_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (a+z) frameCap) (i : Fin 3) :
    0<Explicit.baseline .low a z s+Explicit.U .low (a+z) z i (s-(a+z)) := by
  have he := (LowSplit.original_endpoints hθ ha hz).2.2.1
  exact he.trans_le (LowPositive.equal_le_positive_surplus hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) hs i)

theorem same_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    0<Explicit.baseline .low a z s+mixedBlock R
      (Explicit.p .low (a+z) z i) (Explicit.q .low (a+z) z i)
        (frameCap-(a+z)) (frameCap-s) := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  by_cases hi : i=1
  · subst i
    have he := (LowSplit.original_endpoints hθ ha hz).2.1
    have hl := LowSame.original_zero_lower hθ hzd hs
    have hh := he.trans_le hl
    simpa only [LowSame.ordinary,Explicit.p,Explicit.q,Matrix.cons_val] using hh
  · have hi' : i=0∨i=2 := by fin_cases i <;> simp_all
    by_cases horder : s≤a+z
    · have hp := pure_negative_positive hθ ha hz ⟨hs.1,horder⟩ i
      have hc := LowSame.HB_negative hθ hzd ⟨hs.1,horder⟩ i hi'
      linarith
    · have horder' : a+z ≤ s := (lt_of_not_ge horder).le
      have hp := pure_positive_positive hθ ha hz ⟨horder',hs.2⟩ i
      have hc := LowSame.HB_positive hθ hzd ⟨horder',hs.2⟩ i hi'
      linarith

theorem separated_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (i j : Fin 3) :
    0<Explicit.baseline .low a z s+Explicit.U .low (a+z) z i (frameCap-(a+z))+
      Explicit.V .low (a+z) z j (frameCap-s) := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hH := LowSeparated.original_negative_zero_le true hθ hs
  have hG := LowSeparated.original_negative_zero_le false hθ hs
  have he := (LowSplit.original_endpoints hθ ha hz).2.2.2
  fin_cases j
  · have hp := he i true
    simp only [LowSeparated.larger,ite_true,Explicit.V,Explicit.p,Explicit.q,Fin.reduceFinMk,
      Matrix.cons_val] at hp hH ⊢
    generalize frameCap = F at hp hH ⊢
    linarith
  · have hp := he i false
    simp only [LowSeparated.larger,Bool.false_eq_true,ite_false,Explicit.V,Explicit.p,Explicit.q,
      Fin.reduceFinMk,Matrix.cons_val] at hp hG ⊢
    generalize frameCap = F at hp hG ⊢
    linarith
  · have hp := he i true
    have hB := LowNegative.B_dominates_H hθ hzd
      (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hs.2],by linarith [hs.1]⟩)
    simp only [LowSeparated.larger,ite_true] at hp hH
    simp only [Fin.reduceFinMk]
    generalize frameCap = F at hp hH hB ⊢
    linarith

theorem intrinsic_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (i j : Fin 3) :
    0<Explicit.baseline .low a z s+
      min (pure R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) i j s (a+z))
        (saturated R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) i j s (a+z)) := by
  have hp : 0<Explicit.baseline .low a z s+
      pure R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) i j s (a+z) := by
    by_cases horder : s≤a+z
    · simpa only [OrdinarySignedBudgetConcentration.pure,horder,↓reduceIte,Explicit.V] using
        pure_negative_positive hθ ha hz ⟨hs.1,horder⟩ j
    · simpa only [OrdinarySignedBudgetConcentration.pure,horder,↓reduceIte,Explicit.U] using
        pure_positive_positive hθ ha hz ⟨(lt_of_not_ge horder).le,hs.2⟩ i
  have hsaturated : 0<Explicit.baseline .low a z s+
      saturated R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) i j s (a+z) := by
    by_cases hij : i=j
    · subst j
      simpa only [saturated,↓reduceIte] using same_positive hθ ha hz hs i
    · simpa only [saturated,hij,↓reduceIte,Explicit.U,Explicit.V,add_assoc] using
        separated_positive hθ ha hz hs i j
  rw [add_min]
  exact lt_min hp hsaturated

/-- Positivity for the actual original ordinary allocation, with its
unchanged signed balance and both actual total budgets. -/
theorem scalar_positive {a z s : ℝ} (P N : Fin 3→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.baseline .low a z s+∑i,mixedBlock R
      (Explicit.p .low (a+z) z i) (Explicit.q .low (a+z) z i) (P i) (N i) := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hp := LowRanges.pairs hθ hzd
  have htf : a+z∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  obtain ⟨i,j,hij⟩ := concentrate R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) P N
    (Real.sqrt_nonneg qCap) radius_sq.le (fun i => (hp i).1)
    (fun i => (hp i).2.1) (fun i => (hp i).2.2.1) hP hN hs htf hPb hNb hbalance
  have hh := intrinsic_positive hθ ha hz hs i j
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Low
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

theorem low_original {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12) (hsmall : total C ga ab≤1/6)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  let k := Explicit.k .low (total C ga ab)
  let l := Explicit.l .low (total C ga ab)
  let c := Explicit.c .low (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hθ : total C ga ab∈Icc (0:ℝ) (1/6) := ⟨hb.total_domain.1,hsmall⟩
  have hn := scalar_nonpositive hg ga ab .low hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hz hs hflat hθ hfeasible
  have hp := Low.scalar_positive
    (a:=aTotal C ga ab) (z:=delta C.theta T) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l c i).P)
    (fun i => (blocks C hg ga ab k l c i).N) hθ ha hz hb.de_domain
    (fun i => (blocks C hg ga ab k l c i).P_nonneg)
    (fun i => (blocks C hg ga ab k l c i).N_nonneg)
    hb.positive_bound hb.negative_bound hb.balance
  change 0<Explicit.baseline .low (aTotal C ga ab) (delta C.theta T) (magnitude C)+
    ∑i,mixedBlock R (Explicit.p .low (total C ga ab) (delta C.theta T) i)
      (Explicit.q .low (total C ga ab) (delta C.theta T) i)
      (blocks C hg ga ab k l c i).P (blocks C hg ga ab k l c i).N at hp
  exact (not_le_of_gt hp) hn

theorem original {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  by_cases hsmall : total C ga ab≤1/6
  · exact low_original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
      hvar ha hz hs hflat hsmall hfeasible
  · exact high_original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
      hvar ha hz hs hflat (lt_of_not_ge hsmall).le hfeasible

/-- The seven original witnesses suffice; neither the size of the total
nor a reduced scalar endpoint is an additional premise. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 3) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  apply original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy hvar ha hz hs hflat
  intro i
  fin_cases i
  · simpa [owners,H] using hhg
  · simpa [owners,G] using hGA
  · simpa [owners,A] using hAB
  · simpa [owners,B] using hBT
  · simpa [owners,T] using hTD
  · simpa [owners,D] using hDE
  · simpa [owners,E] using hEH

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
end
end
end
