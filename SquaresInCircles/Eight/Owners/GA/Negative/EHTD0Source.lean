module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3LowStress
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3SourceCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2Source

/-!
# Eight squares: a core EH1 with nonnegative A total, BT2 and TD0

The short-total case is excluded by `NegativeELowA.actual_false`; the high-total scalar follows
from the four-block EH1/BT3 theorem at zero tilt (`original_flat_high_false`). This analytic step
does not select BT3: the independent BT2 error stays in the ordinary signed block of B, and the
TD0 error, of either sign, stays in D.

`original_high_false` keeps all seven weak separators of the cycle.
-/

section
/-!
## The four negative-EH1 / positive-BT3 families on the cycle

The scalar coefficients and the signed mass budgets refer to one and the same cycle. In the
small-low family D keeps its sorted two-sign support. In all other families the four ordinary
blocks, TD0 and DE2 included, are kept (`full_scalar_identity`, `scalar_nonpositive`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

def familyRegime (f : Family) : Regime := if far f then .far else .small

private theorem full_scalar_identity (f : Family) (hf : f≠.smallLow)
    (θ a z s : ℝ) (P N : Fin 4→ℝ) :
    baseline f θ a z+charge f s+
      (∑i,Scalar.block f θ z (P i) (N i) i)=
    PositiveBT3.Analytic.fullBaseline (Explicit.k f θ) (Explicit.l f θ)
      (Explicit.m f θ) z+
    Explicit.l f θ*TwoPositive.ASupport.charge a+
    ehLower (familyRegime f) s+
      (∑i,fullBlock (familyRegime f) (Explicit.k f θ) (Explicit.l f θ)
        (Explicit.m f θ) z i (P i) (N i)) := by
  cases f with
  | smallLow => exact (hf rfl).elim
  | smallHigh =>
      simp [familyRegime,baseline,charge,Scalar.block,Blocks.block,
        ChargedOrdinaryConcentration.block,fullBlock,epsilon,far,errorCharge,
        NegativeEHPositiveTD.Explicit.errorCharge,
        NegativeEHPositiveTD.Explicit.gain,SmallLow.gain_eq,Blocks.p,Blocks.q,Explicit.c]
  | farLow =>
      simp [familyRegime,baseline,charge,Scalar.block,Blocks.block,
        ChargedOrdinaryConcentration.block,fullBlock,epsilon,far,errorCharge,
        NegativeEHPositiveTD.Explicit.errorCharge,NegativeEH.epsilon,
        NegativeEHPositiveTD.Explicit.gain,NegativeEH.G,SmallLow.gain_eq,Blocks.p,Blocks.q,
        Explicit.c]
  | farHigh =>
      simp [familyRegime,baseline,charge,Scalar.block,Blocks.block,
        ChargedOrdinaryConcentration.block,fullBlock,epsilon,far,errorCharge,
        NegativeEHPositiveTD.Explicit.errorCharge,NegativeEH.epsilon,
        NegativeEHPositiveTD.Explicit.gain,NegativeEH.G,SmallLow.gain_eq,Blocks.p,Blocks.q,
        Explicit.c]

/-- The scalar is nonpositive at the selected weak edges of the cycle. No G/T endpoint
normalization and no moved configuration enter; the two signed caps are passed as they are. -/

theorem scalar_nonpositive {Q : ℝ} {C : SignedCycle} (f : Family) {hg : Fin 4}
    (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B)
    (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hθ : total C ga ab∈Icc (Scalar.left f) (Scalar.right f))
    (he : magnitude C∈Icc (Scalar.eLeft f) (Scalar.eRight f))
    (hhg : hg=0∨hg=2)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    baseline f (total C ga ab) (aTotal C ga ab) (delta C.theta B)+
      charge f (magnitude C)+
      (∑i,Scalar.block f (total C ga ab) (delta C.theta B)
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).P
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).N i)≤0 := by
  let θ := total C ga ab
  let k := Explicit.k f θ
  let l := Explicit.l f θ
  let m := Explicit.m f θ
  have hbud := budgets hg ga ab k l m hvar ha hz hs
  by_cases hlow : f=.smallLow
  · subst f
    have hactual := low_scalar_nonpositive (hg:=hg) ga ab hsorted hcontained hQ
      hHy hGy hBy hDy hvar ha hz hs hθ hflat hb he hhg hfeasible
    simpa [θ,k,l,m,baseline,Scalar.block,SmallLow.block,lowBlock,
      SmallLow.dCost,PositiveBT3.slope,charge,far,SmallLow.gain_eq,
      Explicit.k,Explicit.l,Explicit.m,PositiveBT3.lowK,PositiveBT3.lowM,PositiveBT3.Cmax,
      lowP,lowQ,SmallLow.p,SmallLow.q] using hactual
  · have hc := coefficients f hθ hbud.bt_domain
    have he' : magnitude C∈Icc
        (NegativeEHPositiveTD.Explicit.eLeft (familyRegime f))
        (NegativeEHPositiveTD.Explicit.eRight (familyRegime f)) := by
      cases f <;> simp_all [familyRegime,Scalar.eLeft,Scalar.eRight,far,
        NegativeEHPositiveTD.Explicit.eLeft,NegativeEHPositiveTD.Explicit.eRight]
    have hkfar : familyRegime f=.far→k∈Icc (3/5:ℝ) (4/5) := by
      intro hh
      have hf : far f=true := by
        cases f <;> simp_all [familyRegime,far]
      exact far_k f hθ hf
    have hactual := full_scalar_nonpositive (k:=k) (l:=l) (m:=m)
      (hg:=hg) (familyRegime f) ga ab hsorted hcontained hQ
      hHy hGy hBy hDy hvar ha hz hs hc.1 hc.2.2.2 hc.2.2.1
      hkfar hflat hb he' hhg hfeasible
    have hid := full_scalar_identity f hlow θ (aTotal C ga ab)
      (delta C.theta B) (magnitude C)
      (fun i => (blocks C hg ga ab k l m i).P)
      (fun i => (blocks C hg ga ab k l m i).N)
    change _≤0 at hactual
    rw [hid]
    exact hactual

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
end
end
end

section
/-!
## The negative-EH1 / nonnegative-BT3 exclusion

The four analytic families are chosen inside the proof from the errors of the cycle. The TD0 and
DE2 errors keep both signs; HG has either weak owner, and the four selected A-owner choices allow
single errors of mixed signs. The entry of EH1 gives the flatness of E and the short magnitude
from the points E and H (`original`). No endpoint or scalar hypothesis remains.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

theorem original_flat_false {Q : ℝ} {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hcap : magnitude C≤1/4)
    (hhg : hg=0∨hg=2)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hb0 := budgets hg ga ab 1 1 1 hvar ha hz hs
  obtain ⟨f,hθ,he⟩ := Scalar.family_cover hb0.total_domain ⟨hb0.eh_domain.1,hcap⟩
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let m := Explicit.m f (total C ga ab)
  have hbud := budgets hg ga ab k l m hvar ha hz hs
  have hn := scalar_nonpositive f (hg:=hg) ga ab hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hz hs hflat hb hθ he hhg hfeasible
  have hp := Scalar.scalar_positive f
    (a:=aTotal C ga ab) (z:=delta C.theta B) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l m i).P)
    (fun i => (blocks C hg ga ab k l m i).N) hθ ha hz he
    (fun i => (blocks C hg ga ab k l m i).P_nonneg)
    (fun i => (blocks C hg ga ab k l m i).N_nonneg)
    hbud.positive_bound hbud.negative_bound hbud.balance
  exact (not_le_of_gt hp) hn

/-- EH1 is tested on the cycle itself, before any move. -/
theorem original {Q : ℝ} {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E<0)
    (hnot : ¬C.Feasible E 0)
    (hhg : hg=0∨hg=2)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hEH : C.Feasible E 1 := by simpa [owners,PositiveBT3.Source.owners,E] using hfeasible E
  obtain ⟨hf,hb,hu⟩ := NegativeEHPositiveTD.Source.genuine_domain
    hsorted hcontained hQ hHy hEy hEc hvar hs hEH hnot
  exact original_flat_false hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
    hvar ha hz hs.le hf hb hu hhg hfeasible

/-- All seven witnesses of the cycle, with either HG owner. -/

theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E<0)
    (hnot : ¬C.Feasible E 0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 1) : False := by
  obtain ⟨hg,hhg,hHG'⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  apply original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy hEy hEc
    hvar ha hz hs hnot hhg
  intro i
  fin_cases i
  · simpa [owners,PositiveBT3.Source.owners,H] using hHG'
  · simpa [owners,PositiveBT3.Source.owners,G] using hGA
  · simpa [owners,PositiveBT3.Source.owners,A] using hAB
  · simpa [owners,PositiveBT3.Source.owners,B] using hBT
  · simpa [owners,PositiveBT3.Source.owners,T] using hTD
  · simpa [owners,PositiveBT3.Source.owners,D] using hDE
  · simpa [owners,PositiveBT3.Source.owners,E] using hEH

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
end
end
end

section
/-!
## High A and negative EH1 with BT2 and TD0 errors of either sign

The EH1 scalar is the four-block EH1/BT3 analytic theorem at zero T tilt; it does not claim that
BT3 is feasible. The BT2 and TD0 errors stay in the B and D circle blocks (`fullBlock`), and all
selected A primary errors keep their signs. The fourth D pair, the E force and both signed mass
budgets are unchanged (`full_scalar_nonpositive`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

abbrev Regime := NegativeEHBT3.Source.Regime
abbrev ehWeight := NegativeEHBT3.Source.ehWeight
abbrev errorCharge := NegativeEHBT3.Source.errorCharge
abbrev ehLower := NegativeEHBT3.Source.ehLower

def fullBlock (r : Regime) (k l c : ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  mixedBlock R (PositiveBT3.pWeights k l c c i)
    (PositiveBT3.qWeights k l c c i) P N-errorCharge r*P

theorem full_blocks_lower {Q : ℝ} {C : SignedCycle} (r : Regime)
    (hg : Fin 4) (ga ab : Bool) {k l c : ℝ}
    (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta E≤0)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : k≤l) (hc : 0<c)
    (hfar : r=.far→k∈Icc (3/5:ℝ) (4/5)) (i : Fin 4) :
    fullBlock r k l c i
      (blocks C hg ga ab k l c i).P (blocks C hg ga ab k l c i).N≤
        actualBlocks C hg ga ab k l c (ehWeight r) i := by
  have hb := budgets hg ga ab k l c hvar ha hs
  have hcoef := block_coefficients (C:=C) (hg:=hg) (c:=c) ga ab
    (show k≤1 by linarith [hk.2]) hl
  have hk0 : 0<k := by linarith [hk.1]
  have hp (j : Fin 4) : 0<PositiveBT3.pWeights k l c c j := by
    fin_cases j <;> simp [PositiveBT3.pWeights,lt_min_iff,hk0,hc]
    linarith
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y)
      (hP : P.Contained Q) :
      fullBlock r k l c j
        (blocks C hg ga ab k l c j).P (blocks C hg ga ab k l c j).N≤
      PositiveTD.actualPairIncrement (blocks C hg ga ab k l c j) P := by
    have hpos : 0≤(blocks C hg ga ab k l c j).p := by
      rw [(hcoef j).1]
      exact (hp j).le
    have hmin := PositiveTD.actual_block_minorant hy hP hQ hpos
      (block_budgets hg ga ab k l c hvar ha hs j).1
      (block_budgets hg ga ab k l c hvar ha hs j).2
    rw [(hcoef j).1,(hcoef j).2] at hmin
    have hcost := mul_nonneg (NegativeEHBT3.Source.charge_nonnegative r)
      (blocks C hg ga ab k l c j).P_nonneg
    dsimp [fullBlock]
    linarith
  fin_cases i
  · have hP : positivePart (if hg=0 then 0 else delta C.theta H)≤frameCap := by
      simpa [blocks,NonnegativeTotals.TD0.blocks,Block.P] using
        (block_budgets hg ga ab k l c hvar ha hs 0).1
    have hN : negativePart (if hg=0 then 0 else delta C.theta H)≤frameCap := by
      simpa [blocks,NonnegativeTotals.TD0.blocks,Block.N] using
        (block_budgets hg ga ab k l c hvar ha hs 0).2
    have hh := NegativeEHPositiveTD.Source.actual_H_minorant r
      hHy (hcontained H) hQ hk hfar hP hN
    simpa [fullBlock,PositiveBT3.pWeights,PositiveBT3.qWeights,
      blocks,NonnegativeTotals.TD0.blocks,hBlock,actualBlocks,
      ehWeight,errorCharge,NegativeEHBT3.Source.ehWeight,NegativeEHBT3.Source.errorCharge,
      NegativeEHPositiveTD.Explicit.ehWeight,
      NegativeEHPositiveTD.Explicit.errorCharge,Block.P,Block.N] using hh
  · simpa [actualBlocks] using hordinary 1
      (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hcontained G)
  · simpa [actualBlocks] using hordinary 2
      (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hcontained B)
  · simpa [actualBlocks] using hordinary 3
      (P:=(C.point D).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hcontained D)

theorem stress_nonpositive {C : SignedCycle} (hg : Fin 4)
    (ga ab : Bool) {k l c w : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0≤c) (hw : 0≤w)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) :
    stress C hg ga ab k l c w≤0 := by
  have hweights (i : Vertex) : 0≤weights k l c w i := by
    fin_cases i <;> simp [weights] <;> positivity
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hf i
  exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (sub_nonpos.mpr hi)

/-- The stress of the cycle is nonpositive, with all its angles in four blocks. Every witness is
that of the cycle; none is inferred from another owner. -/
theorem full_scalar_nonpositive {Q : ℝ} {C : SignedCycle}
    (r : Regime) {hg : Fin 4} (ga ab : Bool) {k l c : ℝ}
    (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta E≤0)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : k≤l) (hc : 0<c)
    (hfar : r=.far→k∈Icc (3/5:ℝ) (4/5))
    (hflat : (C.point E).a=7/12)
    (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (he : magnitude C∈Icc (NegativeEHPositiveTD.Explicit.eLeft r)
      (NegativeEHPositiveTD.Explicit.eRight r))
    (hhg : hg=0∨hg=2)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) :
    PositiveATD0.fullBaseline k l c+
      l*TwoPositive.ASupport.charge (aTotal C ga ab)+
      ehLower r (magnitude C)+
        (∑i,fullBlock r k l c i
          (blocks C hg ga ab k l c i).P
          (blocks C hg ga ab k l c i).N)≤0 := by
  have hbud := budgets hg ga ab k l c hvar ha hs
  have hn : negativeVariation C.theta≤frameCap := by
    rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    hbud.a_domain
  have hAg := mul_le_mul_of_nonneg_left hA (show 0≤l by linarith [hk.1,hl])
  have hE := NegativeEHBT3.Source.eh_gain_lower r
    (k:=k) hflat hb he hfar
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    full_blocks_lower r hg ga ab hcontained hQ hHy hGy hBy hDy
      hvar ha hs hk hl hc hfar i)
  have hid := decomposition C ga ab hhg k l c (ehWeight r)
  have hupper := stress_nonpositive (k:=k) (l:=l) (c:=c) (w:=ehWeight r) hg ga ab
    (by linarith [hk.1])
    (by linarith [hk.1,hl]) hc.le
    (NegativeEHBT3.Source.weight_nonnegative r) hf
  change l*TwoPositive.ASupport.charge (aTotal C ga ab)≤
    l*PairedE.primaryGain (C.point A) ga ab
      (delta C.theta G) (delta C.theta A) at hAg
  linarith

theorem full_block_eq_scalar (f : NegativeEHBT3.Family)
    (hf : f≠.smallLow) (a : ℝ) (i : Fin 4) (P N : ℝ) :
    fullBlock (if NegativeEHBT3.far f then .far else .small)
      (NegativeEHBT3.Explicit.k f a) (NegativeEHBT3.Explicit.l f a)
      (NegativeEHBT3.Explicit.m f a) i P N =
      NegativeEHBT3.Scalar.block f a 0 P N i := by
  cases f with
  | smallLow => exact (hf rfl).elim
  | smallHigh => simp [fullBlock,NegativeEHBT3.Scalar.block,
      NegativeEHBT3.Blocks.block,ChargedOrdinaryConcentration.block,
      NegativeEHBT3.Blocks.p,NegativeEHBT3.Blocks.q,
      errorCharge,NegativeEHPositiveTD.Explicit.errorCharge,
      NegativeEHBT3.epsilon,NegativeEHBT3.far,
      NegativeEHBT3.Explicit.c,PositiveBT3.tilted]
  | farLow => simp [fullBlock,NegativeEHBT3.Scalar.block,
      NegativeEHBT3.Blocks.block,ChargedOrdinaryConcentration.block,
      NegativeEHBT3.Blocks.p,NegativeEHBT3.Blocks.q,
      errorCharge,NegativeEHPositiveTD.Explicit.errorCharge,
      NegativeEHBT3.epsilon,NegativeEHBT3.far,
      NegativeEHBT3.Explicit.c,PositiveBT3.tilted]
  | farHigh => simp [fullBlock,NegativeEHBT3.Scalar.block,
      NegativeEHBT3.Blocks.block,ChargedOrdinaryConcentration.block,
      NegativeEHBT3.Blocks.p,NegativeEHBT3.Blocks.q,
      errorCharge,NegativeEHPositiveTD.Explicit.errorCharge,
      NegativeEHBT3.epsilon,NegativeEHBT3.far,
      NegativeEHBT3.Explicit.c,PositiveBT3.tilted]

end SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

private abbrev Family := NegativeEHBT3.Family

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
      NegativeEH.g,NegativeEH.G,NegativeEH.K,NegativeEH.beta]

/-- For a signed A total in `[1/6, frameCap]`, the four circle forces give a strictly positive
scalar, which the selected witnesses forbid. -/
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

/-- The theorem for the BT2 and TD0 witnesses of the cycle, with no sign restriction on T and
B. -/
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

end SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
end
end
end
