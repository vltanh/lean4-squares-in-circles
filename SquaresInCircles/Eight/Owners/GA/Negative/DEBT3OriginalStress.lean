module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3Blocks
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3SourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress
public import SquaresInCircles.Eight.Owners.GA.Secant.DSingleAngle

/-!
# Eight squares: the original BT3 stress implies the exact scalar necessary inequality

The D singleton is bounded at its actual
secant, actual force, and actual signed TD0 argument. The T support uses
the total-dependent eta only as a weight direction at the unchanged
original T square. No selected-angle sign, support maximizer, or scalar
positivity premise is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
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
    (hc : (C.point T).Contained Q) (hQ : Q≤qCap) (hm : 0≤ m) (he : 0≤eta)
    (hz : delta C.theta B∈Icc 0 frameCap) : 0≤tReserve C m eta :=
  mul_nonneg (mul_nonneg hm (transport_trig hz).2.2.1)
    (sub_nonneg.mpr (actual_T_support hc hQ he))

lemma baseline_identity {C : SignedCycle} (ga ab : Bool) (f : Family)
    (hs : magnitude C∈Icc 0 frameCap) :
    base C (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
        (Explicit.m f (total C ga ab)) (Explicit.eta f (total C ga ab))+
      Explicit.l f (total C ga ab)*TwoPositive.ASupport.charge (aTotal C ga ab)=
      Explicit.baseline f (aTotal C ga ab) (delta C.theta B) (magnitude C) := by
  have hd : Real.cos (delta C.theta D)=Real.cos (NegativeDEPositiveTD.Source.magnitude C) := by
    simp only [NegativeDEPositiveTD.Source.magnitude,Real.cos_neg]
  simp only [base,deCorrection,magnitude]
  rw [NegativeDEPositiveTD.Source.deCorrection_identity hs,hd]
  simp only [Explicit.baseline,total,Explicit.sigma,Explicit.c,Explicit.sec,
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
  have hq := NegativeELargeA.secant_range hs
  have hcf : c∈Icc SecantD.cLower SecantD.cUpper := by
    refine ⟨?_,hc.2⟩
    have h1 := hc.1
    simp only [SecantD.PositiveEndpoint.d] at h1
    simp only [SecantD.cLower]
    linarith
  exact SecantD.actual_minorant hsorted hy hcontained hQ hq hk hcf hkc ht

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
    (hk : 0≤k) (hl : 0≤l) (hm : 0≤ m)
    (hc : 0≤tilted m eta (delta C.theta B))
    (hs : magnitude C∈Icc 0 frameCap)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : stress C hg ga ab k l m eta≤0 := by
  have hsec : 0≤1/Real.cos (delta C.theta D) := by
    have hcos := NegativeESecant.cos_pos hs
    have hd : Real.cos (delta C.theta D)=Real.cos (magnitude C) := by
      simp only [magnitude,NegativeDEPositiveTD.Source.magnitude,Real.cos_neg]
    rw [hd]
    exact div_nonneg zero_le_one hcos.le
  have hw (i : Vertex) : 0≤weights C k l m eta i := by
    obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl :
        i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by revert i; decide
    · exact hk
    · exact hl
    · exact hl
    · exact hm
    · exact hc
    · exact hsec
    · exact zero_le_one
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    have h := hfeasible i
    simp only [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] at h
    exact h
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
  have hb := budgets hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
    (Explicit.m f (total C ga ab)) hvar ha hz hs
  have hc := Explicit.source_coefficients f hθ hb.bt_domain
  have hl : 0≤Explicit.l f (total C ga ab) := hc.2.2.1.le
  have hm : 0≤Explicit.m f (total C ga ab) := hc.2.2.2.1.le
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
    have hd : Real.cos (delta C.theta D)=Real.cos (magnitude C) := by
      simp only [magnitude,NegativeDEPositiveTD.Source.magnitude,Real.cos_neg]
    rw [hd]
    exact (NegativeESecant.cos_pos hb.de_domain).ne'
  have hidentity := decomposition C hg ga ab (Explicit.k f (total C ga ab))
    (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab))
    (Explicit.eta f (total C ga ab)) hflat hcos
  have hbase := baseline_identity ga ab f hb.de_domain
  have haT : aTotal C ga ab=PairedE.total ga ab (delta C.theta G) (delta C.theta A) := rfl
  rw [←haT] at hAg
  have hrot : 0≤tilted (Explicit.m f (total C ga ab)) (Explicit.eta f (total C ga ab))
      (delta C.theta B) := by
    change 0≤Explicit.c f (total C ga ab) (delta C.theta B)
    have h1 := hc.2.2.2.2.1.1
    have h0 : (0:ℝ)≤SecantD.PositiveEndpoint.d := by norm_num [SecantD.PositiveEndpoint.d]
    exact h0.trans h1
  have hk0 : 0≤Explicit.k f (total C ga ab) := by linarith [hc.1.1]
  have hupper := stress_nonpositive hg ga ab hk0 hl hm hrot hb.de_domain hfeasible
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
