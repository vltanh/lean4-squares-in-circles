module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD0OriginalStress
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Source

/-!
# Genuine core EH1 with nonnegative A total and original BT2/TD0

Uncompiled source completion of
HAND_G3_CORE_E_NEGATIVE_EH1_NONNEGATIVE_A_TD0_EXCLUSION.md.
The short-total case is already handled by NegativeELowA.source_false;
the high-total scalar follows from the previously drafted EH1/BT3
four-block theorem at zero tilt. This analytic substitution does NOT
select BT3: the independent, original BT2 error stays inside B's
ordinary signed block, and the arbitrary TD0 error stays in D.

The source conclusion below retains all seven actual weak separators.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHTD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

private abbrev Family := NegativeEHBT3.Family
private abbrev sleft := NegativeEHBT3.Scalar.left
private abbrev sright := NegativeEHBT3.Scalar.right
private abbrev eleft := NegativeEHBT3.Scalar.eLeft
private abbrev eright := NegativeEHBT3.Scalar.eRight

theorem high_family_cover {a s : ℝ}
    (ha : a∈Icc (1/6:ℝ) frameCap) (hs : s∈Icc (0:ℝ) (1/4)) :
    ∃f : NegativeEHBT3.Family,f≠.smallLow ∧ a∈Icc (NegativeEHBT3.Scalar.left f) (NegativeEHBT3.Scalar.right f) ∧
      s∈Icc (NegativeEHBT3.Scalar.eLeft f) (NegativeEHBT3.Scalar.eRight f) := by
  by_cases he : s≤1/10
  · exact ⟨.smallHigh,by decide,⟨ha.1,ha.2⟩,⟨hs.1,he⟩⟩
  · by_cases ht : a≤1/4
    · exact ⟨.farLow,by decide,
        ⟨by simp only [NegativeEHBT3.Scalar.left]; linarith [ha.1],ht⟩,
        ⟨(lt_of_not_ge he).le,hs.2⟩⟩
    · exact ⟨.farHigh,by decide,⟨(lt_of_not_ge ht).le,ha.2⟩,
        ⟨(lt_of_not_ge he).le,hs.2⟩⟩

lemma regime_mag (f : NegativeEHBT3.Family) {s : ℝ}
    (hs : s∈Icc (NegativeEHBT3.Scalar.eLeft f) (NegativeEHBT3.Scalar.eRight f)) :
    s∈Icc (NegativeEHPositiveTD.Explicit.eLeft
      (if NegativeEHBT3.far f then .far else .small))
      (NegativeEHPositiveTD.Explicit.eRight
      (if NegativeEHBT3.far f then .far else .small)) := by
  cases f <;> simpa [NegativeEHBT3.Scalar.eLeft,NegativeEHBT3.Scalar.eRight,NegativeEHBT3.Scalar.eLeft,
    NegativeEHBT3.Scalar.eRight,NegativeEHBT3.far,
    NegativeEHPositiveTD.Explicit.eLeft,NegativeEHPositiveTD.Explicit.eRight] using hs

lemma regime_charge (f : NegativeEHBT3.Family) (s : ℝ) :
    NegativeEHBT3.charge f s =
      ehLower (if NegativeEHBT3.far f then .far else .small) s := by
  cases f <;>
    simp [NegativeEHBT3.charge,NegativeEHBT3.gain,NegativeEHBT3.far,
      ehLower,NegativeEHBT3.Source.ehLower,
      NegativeEHPositiveTD.Explicit.gain,
      NegativeEH.g,NegativeEH.G,NegativeEH.K,NegativeEH.beta] <;> ring

/-- For any actual signed A total in [1/6,h], all four circle forces
force a strictly positive scalar, impossible at the selected witnesses. -/
theorem original_flat_high_false {Q : ℝ} {C : SignedCycle}
    (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12)
    (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hmag : magnitude C≤1/4)
    (hhg : hg=0∨hg=2)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have ha0 : 0≤aTotal C ga ab := by linarith [ha.1]
  have hm0 : 0 ≤ magnitude C := neg_nonneg.mpr hs
  obtain ⟨f,hne,hfa,hfs⟩ :=
    high_family_cover ha ⟨hm0,hmag⟩
  let a := aTotal C ga ab
  let k := NegativeEHBT3.Explicit.k f a
  let l := NegativeEHBT3.Explicit.l f a
  let c := NegativeEHBT3.Explicit.m f a
  let r : Regime := if NegativeEHBT3.far f then .far else .small
  have hzero : (0:ℝ)∈Icc 0 a := ⟨le_rfl,ha0⟩
  have hcoef := NegativeEHBT3.Source.coefficients f hfa hzero
  have hkfar : r=.far→k∈Icc (3/5:ℝ) (4/5) := by
    intro hr
    have hh : NegativeEHBT3.far f=true := by
      cases f <;> simp_all [r,NegativeEHBT3.far]
    exact NegativeEHBT3.Source.far_k f hfa hh
  have hbud := budgets hg ga ab k l c hvar ha0 hs
  have hsumneg := full_scalar_nonpositive (r:=r) (hg:=hg) ga ab
    hsorted hcontained hQ hHy hGy hBy hDy hvar ha0 hs
    hcoef.1 hcoef.2.2.2 hcoef.2.2.1 hkfar hflat hb
    (regime_mag f hfs) hhg hf
  have hp := NegativeEHBT3.Scalar.scalar_positive f
    (a:=a) (z:=0) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l c i).P)
    (fun i => (blocks C hg ga ab k l c i).N)
    (by simpa only [add_zero] using hfa) ha0 le_rfl hfs
    (fun i => (blocks C hg ga ab k l c i).P_nonneg)
    (fun i => (blocks C hg ga ab k l c i).N_nonneg)
    (by simpa only [sub_zero,add_zero] using hbud.positive_bound)
    hbud.negative_bound
    (by simpa only [sub_zero,add_zero] using hbud.balance)
  have heqbase : NegativeEHBT3.baseline f a a 0 =
      PositiveATD0.fullBaseline (NegativeEHBT3.Explicit.k f a)
        (NegativeEHBT3.Explicit.l f a) (NegativeEHBT3.Explicit.m f a)+
      NegativeEHBT3.Explicit.l f a*TwoPositive.ASupport.charge a := by
    have he (k l c : ℝ) :
        PositiveBT3.Analytic.fullBaseline k l c 0=PositiveATD0.fullBaseline k l c := by
      simp only [PositiveBT3.Analytic.fullBaseline,PositiveATD0.fullBaseline,
        PositiveBT3.tilted,edgeWidth_zero,Real.cos_zero,Real.sin_zero,mul_zero,add_zero,
        mul_one,sub_zero]
      ring
    simp only [NegativeEHBT3.baseline,hne,↓reduceIte,he]
  have heqgain := regime_charge f (magnitude C)
  have heqsum :
      (∑i,fullBlock r k l c i
        (blocks C hg ga ab k l c i).P
        (blocks C hg ga ab k l c i).N)=
      (∑i,NegativeEHBT3.Scalar.block f a 0
        (blocks C hg ga ab k l c i).P
        (blocks C hg ga ab k l c i).N i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact full_block_eq_scalar f hne a i
      (blocks C hg ga ab k l c i).P
      (blocks C hg ga ab k l c i).N
  dsimp [a,k,l,c,r] at hsumneg hp heqbase heqgain heqsum
  simp only [add_zero] at hp
  rw [heqbase,heqgain,←heqsum] at hp
  exact (not_le_of_gt hp) hsumneg

/-- Original BT2/TD0 witness theorem, with unrestricted signed T and B. -/
theorem original_high_false {Q : ℝ} {C : SignedCycle}
    (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (hs : delta C.theta E<0) (hnot : ¬C.Feasible E 0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 1) : False := by
  obtain ⟨hflat,hb,hmag⟩ :=
    NegativeEHPositiveTD.Source.genuine_domain hsorted hcontained hQ
      hHy hEy hEc hvar hs hEH hnot
  obtain ⟨hg,hhg,hHG'⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  apply original_flat_high_false hg ga ab hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hs.le hflat hb hmag hhg
  intro i
  fin_cases i
  · simpa [owners,NonnegativeTotals.TD0.owners,H] using hHG'
  · simpa [owners,NonnegativeTotals.TD0.owners,G] using hGA
  · simpa [owners,NonnegativeTotals.TD0.owners,A] using hAB
  · simpa [owners,NonnegativeTotals.TD0.owners,B] using hBT
  · simpa [owners,NonnegativeTotals.TD0.owners,T] using hTD
  · simpa [owners,NonnegativeTotals.TD0.owners,D] using hDE
  · simpa [owners,NonnegativeTotals.TD0.owners,E] using hEH

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHTD0
