module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3SourceData

/-!
# The original BT3 stress implies the exact scalar necessary inequality

Uncompiled source comparison. The D singleton is bounded at its actual
secant, actual force, and actual signed TD0 argument. The T support uses
the total-dependent eta only as a weight direction at the unchanged
original T square. No selected-angle sign, support maximizer, or scalar
positivity premise is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks PairedE

lemma family_eta_nonnegative (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) : 0≤Explicit.eta f θ := by
  cases f
  · norm_num [Explicit.eta]
  · linarith [(Explicit.high_eta hθ).1]

lemma actual_T_support {Q eta : ℝ} {P : SignedPoint}
    (hc : P.Contained Q) (hQ : Q≤qCap) (he : 0≤eta) :
    P.a+eta*P.y≤fullSupport 1 eta := by
  have hh := raw_full_support (f:=1) (g:=eta) (hc.trans hQ)
  have hp := mul_le_mul_of_nonneg_left (le_abs_self P.y) he
  linarith

lemma tReserve_nonnegative {Q m eta : ℝ} {C : SignedCycle}
    (hc : (C.point T).Contained Q) (hQ : Q≤qCap) (hm : 0≤m) (he : 0≤eta)
    (hz : delta C.theta B∈Icc 0 frameCap) : 0≤tReserve C m eta :=
  mul_nonneg (mul_nonneg hm (transport_trig hz).2.2.1)
    (sub_nonneg.mpr (actual_T_support hc hQ he))

lemma baseline_identity {C : SignedCycle} (ga ab : Bool) (f : Family)
    (hs : magnitude C∈Icc 0 frameCap) :
    base C (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
        (Explicit.m f (total C ga ab)) (Explicit.eta f (total C ga ab))+
      Explicit.l f (total C ga ab)*TwoPositive.ASupport.charge (aTotal C ga ab)=
      Explicit.baseline f (aTotal C ga ab) (delta C.theta B) (magnitude C) := by
  have hd : Real.cos (delta C.theta D)=Real.cos (magnitude C) := by simp [magnitude,NegativeDEPositiveTD.Source.magnitude]
  rw [base,NegativeDEPositiveTD.Source.deCorrection_identity hs,hd]
  dsimp [Explicit.baseline,total,Explicit.sigma,Explicit.c,Explicit.sec,
    NegativeELargeA.secant,tilted,Explicit.K,NegativeDEPositiveTD.Explicit.K,
    NegativeDEPositiveTD.Explicit.secant]
  ring

lemma family_block_coefficients {C : SignedCycle} (hg ga ab : Bool) (f : Family)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f))
    (hz : delta C.theta B∈Icc 0 (total C ga ab)) (i : Fin 4) :
    (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.m f (total C ga ab)) i).p=Blocks.p f (total C ga ab) i ∧
    (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.m f (total C ga ab)) i).q=Blocks.q f (total C ga ab) i := by
  have hc := Explicit.source_coefficients f hθ hz
  exact block_coefficients (C:=C) hg ga ab
    (m:=Explicit.m f (total C ga ab)) (by linarith [hc.1.2]) hc.2.1 i

lemma actual_D_minorant {Q k c s t : ℝ} {P : SignedPoint}
    (hsorted : P.Sorted) (hy : P.y≤0) (hcontained : P.Contained Q) (hQ : Q≤qCap)
    (hk : k∈Icc (1/2:ℝ) (17/20))
    (hc : c∈Icc SecantD.PositiveEndpoint.d SecantD.cUpper) (hkc : k≤c)
    (hs : s∈Icc 0 frameCap) (ht : |t|≤frameCap) :
    -SecantD.slope*max (Explicit.sec s) c*positivePart t+V R k 1 (negativePart t)≤
      SecantD.actualIncrement (Explicit.sec s) c t P := by
  have hq := SecantD.sec_bounds hs
  have hcf : c∈Icc SecantD.cLower SecantD.cUpper :=
    ⟨by dsimp [SecantD.PositiveEndpoint.d,SecantD.cLower] at *; linarith [hc.1],hc.2⟩
  have hh := SecantD.original hsorted hy hcontained hQ hq hcf hk hkc ht
  by_cases hpos : 0≤t
  · have hN : negativePart t=0 := max_eq_right (by linarith)
    have hP : positivePart t=t := max_eq_left hpos
    simpa [if_pos hpos,hP,hN,V_zero] using hh
  · have hP : positivePart t=0 := max_eq_right (le_of_not_ge hpos)
    have hN : negativePart t= -t := max_eq_left (by linarith)
    simpa [if_neg hpos,hP,hN] using hh

lemma actual_blocks_lower {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 4) :
    Blocks.block f (total C ga ab) (delta C.theta B) (magnitude C)
      (blocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).P
      (blocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).N i≤
    actualBlocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.m f (total C ga ab)) (Explicit.eta f (total C ga ab)) i := by
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let m := Explicit.m f (total C ga ab)
  have hb := budgets hg ga ab k l m hvar ha hz hs
  have hc := Explicit.source_coefficients f hθ hb.bt_domain
  have hp := Blocks.family_pairs f hθ
  have hcoef := family_block_coefficients hg ga ab f hθ hb.bt_domain
  have hbudget := block_budgets hg ga ab k l m hvar ha hz hs
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      mixedBlock R (Blocks.p f (total C ga ab) j) (Blocks.q f (total C ga ab) j)
        (blocks C hg ga ab k l m j).P (blocks C hg ga ab k l m j).N≤
      PositiveTD.actualPairIncrement (blocks C hg ga ab k l m j) P := by
    have hpos : 0≤(blocks C hg ga ab k l m j).p := by rw [(hcoef j).1]; exact (hp j).1.le
    have hh := PositiveTD.actual_block_minorant hy hP hQ hpos (hbudget j).1 (hbudget j).2
    rwa [(hcoef j).1,(hcoef j).2] at hh
  fin_cases i
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,m] using hordinary 0 hHy (hcontained H)
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,m] using hordinary 1 (P:=(C.point G).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hcontained G)
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,m] using hordinary 2 (P:=(C.point B).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hcontained B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    have hh := actual_D_minorant (hsorted D) hDy (hcontained D) hQ
      hc.1 hc.2.2.2.2.1 hc.2.2.2.2.2 hb.de_domain (original_error_bound hvar hn T)
    simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,blocks,Blocks.p,Blocks.q,Explicit.gamma,Explicit.c,Explicit.sec,
      NegativeELargeA.secant,magnitude,NegativeDEPositiveTD.Source.magnitude,
      Block.P,Block.N,tilted,k,l,m] using hh

lemma stress_nonpositive {C : SignedCycle} (hg ga ab : Bool) {k l m eta : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0≤m)
    (hc : 0≤tilted m eta (delta C.theta B))
    (hs : magnitude C∈Icc 0 frameCap)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : stress C hg ga ab k l m eta≤0 := by
  have hsec : 0≤1/Real.cos (delta C.theta D) := by
    have hcos := NegativeESecant.cos_pos hs
    simpa [magnitude,NegativeDEPositiveTD.Source.magnitude] using
      (div_nonneg (by norm_num : (0:ℝ)≤1) hcos.le)
  have hw (i : Vertex) : 0≤weights C k l m eta i := by
    fin_cases i <;> simp only [weights,Matrix.cons_val_succ,Matrix.cons_val_zero] <;> positivity
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hfeasible i
  exact mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr hi)

theorem scalar_nonpositive {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f))
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    Explicit.baseline f (aTotal C ga ab) (delta C.theta B) (magnitude C)+
      ∑i,Blocks.block f (total C ga ab) (delta C.theta B) (magnitude C)
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).P
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).N i≤0 := by
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let m := Explicit.m f (total C ga ab)
  let e := Explicit.eta f (total C ga ab)
  have hb := budgets hg ga ab k l m hvar ha hz hs
  have hc := Explicit.source_coefficients f hθ hb.bt_domain
  have hl : 0≤l := hc.2.2.1.le
  have hm : 0≤m := hc.2.2.2.1.le
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    (show aTotal C ga ab∈Icc 0 frameCap from ⟨ha,hb.a_domain.2.trans hb.total_domain.2⟩)
  have hAg := mul_le_mul_of_nonneg_left hA hl
  have hzframe : delta C.theta B∈Icc 0 frameCap := ⟨hz,hb.bt_domain.2.trans hb.total_domain.2⟩
  have hT := tReserve_nonnegative (hcontained T) hQ hm (family_eta_nonnegative f hθ) hzframe
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower hg ga ab f hsorted hcontained hQ hHy hGy hBy hDy hvar ha hz hs hθ i)
  have hcos : Real.cos (delta C.theta D)≠0 := by
    simpa [magnitude,NegativeDEPositiveTD.Source.magnitude] using (NegativeESecant.cos_pos hb.de_domain).ne'
  have hidentity := decomposition C hg ga ab k l m e hflat hcos
  have hbase := baseline_identity ga ab f hb.de_domain
  have hrot : 0≤tilted m e (delta C.theta B) := by
    change 0≤Explicit.c f (total C ga ab) (delta C.theta B)
    linarith [hc.2.2.2.2.1.1]
  have hupper := stress_nonpositive hg ga ab (by linarith [hc.1.1]) hl hm hrot hb.de_domain hfeasible
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Source
