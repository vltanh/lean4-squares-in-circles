module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3SourceCoefficients
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Source

/-!
# Complete original genuine-negative-EH1 / nonnegative-BT3 exclusion

Uncompiled source conclusion of the EH1/BT3 companion. The scalar
family is selected from the unchanged original A/BT total and EH
magnitude. The small-low family uses the original sorted-D stress;
the other three use the original full-circle stress. In every case
D retains the actual TD0 and DE2 errors. The two selected A errors
may have opposite signs. No scalar or endpoint hypothesis is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

def regime (f : Family) : Regime := if far f then .far else .small

@[simp] lemma regime_charge (f : Family) : errorCharge (regime f)=epsilon f := by cases f <;> rfl
@[simp] lemma regime_gain (f : Family) (s : ℝ) : ehLower (regime f) s=charge f s := by cases f <;> rfl
lemma family_eLeft (f : Family) :
    Scalar.eLeft f=NegativeEHPositiveTD.Explicit.eLeft (regime f) := by cases f <;> rfl
lemma family_eRight (f : Family) :
    Scalar.eRight f=NegativeEHPositiveTD.Explicit.eRight (regime f) := by cases f <;> rfl

/-- Every scalar family is forced nonpositive by the original seven
selected inequalities, with its actual signed masses. -/
theorem scalar_nonpositive {Q : ℝ} {C : SignedCycle} (f : Family)
    {hg : Fin 4} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hθ : total C ga ab∈Icc (Scalar.left f) (Scalar.right f))
    (he : magnitude C∈Icc (Scalar.eLeft f) (Scalar.eRight f))
    (hhg : hg=0∨hg=2) (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    baseline f (total C ga ab) (aTotal C ga ab) (delta C.theta B)+charge f (magnitude C)+
      ∑i,Scalar.block f (total C ga ab) (delta C.theta B)
        (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
          (Explicit.m f (total C ga ab)) i).P
        (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
          (Explicit.m f (total C ga ab)) i).N i≤0 := by
  by_cases hf : f=.smallLow
  · subst f
    have hh := low_scalar_nonpositive ga ab hsorted hcontained hQ hHy hGy hBy hDy
      hvar ha hz hs hθ hflat hb he hhg hfeasible
    simpa [baseline,Scalar.block,SmallLow.block,SmallLow.p,SmallLow.q,SmallLow.dCost,
      lowBlock,lowP,lowQ,PositiveBT3.slope,Explicit.k,Explicit.l,Explicit.m,
      PositiveBT3.lowK,PositiveBT3.lowM,charge,far,gain,NegativeEH.g,NegativeEH.K,NegativeEH.beta]
      using hh
  · have he' : magnitude C∈Icc (NegativeEHPositiveTD.Explicit.eLeft (regime f))
        (NegativeEHPositiveTD.Explicit.eRight (regime f)) := by
      simpa only [family_eLeft,family_eRight] using he
    have hbud := budgets hg ga ab 1 1 1 hvar ha hz hs
    have hc := coefficients f hθ hbud.bt_domain
    have hfar : regime f=.far→Explicit.k f (total C ga ab)∈Icc (3/5:ℝ) (4/5) := by
      intro hr
      have hff : far f=true := by cases f <;> simp_all [regime,far]
      exact far_k f hθ hff
    have hh := full_scalar_nonpositive (regime f) ga ab hsorted hcontained hQ
      hHy hGy hBy hDy hvar ha hz hs hc.1 hc.2.2.2 hc.2.2.1 hfar
      hflat hb he' hhg hfeasible
    simpa only [baseline,if_neg hf,Scalar.block,fullBlock,regime_gain,regime_charge,
      Blocks.block,ChargedOrdinaryConcentration.block,Blocks.p,Blocks.q,Explicit.c,add_assoc] using hh

/-- Closed flat-domain exclusion, including zero BT error and all
adjacent scalar-regime boundaries. -/
theorem original_flat_false {Q : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hcap : magnitude C≤1/4)
    (hhg : hg=0∨hg=2) (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hbud0 := budgets hg ga ab 1 1 1 hvar ha hz hs
  obtain ⟨f,hθ,he⟩ := Scalar.family_cover hbud0.total_domain ⟨hbud0.eh_domain.1,hcap⟩
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let m := Explicit.m f (total C ga ab)
  have hbud := budgets hg ga ab k l m hvar ha hz hs
  have hn := scalar_nonpositive f ga ab hsorted hcontained hQ hHy hGy hBy hDy
    hvar ha hz hs hflat hb hθ he hhg hfeasible
  have hp := Scalar.scalar_positive f
    (a:=aTotal C ga ab) (z:=delta C.theta B) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l m i).P)
    (fun i => (blocks C hg ga ab k l m i).N) hθ ha hz he
    (fun i => (blocks C hg ga ab k l m i).P_nonneg)
    (fun i => (blocks C hg ga ab k l m i).N_nonneg)
    hbud.positive_bound hbud.negative_bound hbud.balance
  exact (not_le_of_gt hp) hn

/-- Genuine EH1 gives flatness and the full angle bound from the
original E,H pair, independently of the BT and TD owners. -/
theorem original {Q : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E<0)
    (hnot : ¬C.Feasible E 0) (hhg : hg=0∨hg=2)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hEH : C.Feasible E 1 := by simpa [owners,PositiveBT3.Source.owners,E] using hfeasible E
  obtain ⟨hf,hb,hu⟩ := NegativeEHPositiveTD.Source.genuine_domain
    hsorted hcontained hQ hHy hEy hEc hvar hs hEH hnot
  exact original_flat_false ga ab hsorted hcontained hQ hHy hGy hBy hDy hvar ha hz hs.le
    hf hb hu hhg hfeasible

/-- Original seven witnesses, without selecting a favorable HG owner. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E<0)
    (hnot : ¬C.Feasible E 0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible Candidate.D 2) (hEH : C.Feasible E 1) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with h|h
    · exact ⟨0,Or.inl rfl,h⟩
    · exact ⟨2,Or.inr rfl,h⟩
  apply original ga ab hsorted hcontained hQ hHy hGy hBy hDy hEy hEc hvar ha hz hs hnot hhg
  intro i
  fin_cases i
  · simpa [owners,PositiveBT3.Source.owners,H] using hHG
  · simpa [owners,PositiveBT3.Source.owners,G] using hGA
  · simpa [owners,PositiveBT3.Source.owners,A] using hAB
  · simpa [owners,PositiveBT3.Source.owners,B] using hBT
  · simpa [owners,PositiveBT3.Source.owners,T] using hTD
  · simpa [owners,PositiveBT3.Source.owners,Candidate.D] using hDE
  · simpa [owners,PositiveBT3.Source.owners,E] using hEH

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
