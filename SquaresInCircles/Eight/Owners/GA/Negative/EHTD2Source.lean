module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLow
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SmallHigh
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SmallLowPure
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3SmallLowSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SourceHSupport
public import SquaresInCircles.Eight.Owners.Negative.CoreEEntry

/-!
# Eight squares: the negative-EH1 / nonnegative-TD2 exclusion

The scalar regime and the total-angle family are selected by the errors of the cycle. Both HG
owners, all four A choices, every sign of the single selected A errors and every DE2 sign are
covered. The EH1 witness gives the flatness of E, its tangent bound and its short negative angle
directly from the core and the square H (`genuine_domain`). No scalar bound, endpoint assumption or
moved configuration is needed.
-/

section
/-!
## The negative-EH scalar inequality forced by the cycle

The H coefficient, the selected A gains, the T support and the DE2 singleton of the cycle are all
kept. The far EH charge is taken once from each positive block mass. The full-circle D baseline is
used only as a lower bound of the sorted support (`baseline_lower`). No scalar positivity is
assumed (`scalar_nonpositive`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks PairedE

lemma charge_nonnegative (r : Regime) : 0≤Explicit.errorCharge r := by
  cases r <;> norm_num [Explicit.errorCharge,NegativeEH.epsilon]

lemma clipped_le_full (c : ℝ) : clippedSupport 1 c≤fullSupport 1 c := by
  by_cases h : 1≤c
  · rw [clippedSupport,ite_eq_left h]
    have hh := raw_full_support (a:=GlobalGA.Secondary.diagonal) (b:=GlobalGA.Secondary.diagonal) (f:=1) (g:=c)
      (show (GlobalGA.Secondary.diagonal+1/2)^2+(GlobalGA.Secondary.diagonal+1/2)^2≤qCap by nlinarith [diagonal_circle])
    simpa [diagonalSupport,add_mul] using hh
  · simp [clippedSupport,h]

lemma baseline_lower (r : Regime) (f : Family) (a z : ℝ) :
    Explicit.baseline r f a z≤
      PositiveTD.baseline (Explicit.k r f (a+z)) (Explicit.l r f (a+z))
        (Explicit.c r f (a+z)) z+Explicit.l r f (a+z)*TwoPositive.ASupport.charge a := by
  have hc := clipped_le_full (Explicit.c r f (a+z))
  have hm : Explicit.m r f (a+z) z=PositiveTD.tilted (Explicit.c r f (a+z)) z := rfl
  simp only [Explicit.baseline,PositiveTD.baseline,hm]
  change _≤_
  dsimp only [Explicit.sigma,NegativeDEPositiveTD.Explicit.sigma,PositiveTD.sigma,
    NegativeDEPositiveTD.Explicit.eta,PositiveTD.eta]
  split_ifs <;> linarith

lemma eh_gain_lower {C : SignedCycle} (r : Regime) (f : Family)
    (ga ab : Bool) (hflat : (C.point E).a=7/12)
    (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hθ : total C ga ab∈Icc (Explicit.left r f) (Explicit.right r f))
    (hs : magnitude C∈Icc (Explicit.eLeft r) (Explicit.eRight r)) :
    Explicit.gain r (magnitude C)≤
      ehGain C (Explicit.k r f (total C ga ab)) (Explicit.ehWeight r) := by
  have hsf := Explicit.e_frame_domain r hs
  have he : delta C.theta E= -magnitude C := by simp [magnitude]
  cases r
  · have hh := NegativeEH.small_actual_gain hb hsf
    rw [edgeWidth_positive_formula hsf] at hh
    rw [ehGain,he,hflat,edgeWidth_negative_formula hsf]
    simp only [Real.sin_neg,Real.cos_neg,Explicit.ehWeight,Explicit.gain]
    linarith
  · have hh := NegativeEH.far_actual_gain hb (Explicit.far_k_domain f hθ) hs
    rw [edgeWidth_positive_formula hsf] at hh
    rw [ehGain,he,hflat,edgeWidth_negative_formula hsf]
    simp only [Real.sin_neg,Real.cos_neg,Explicit.ehWeight,Explicit.gain]
    linarith

lemma family_block_coefficients {C : SignedCycle} (hg ga ab : Bool)
    (r : Regime) (f : Family)
    (hθ : total C ga ab∈Icc (Explicit.left r f) (Explicit.right r f))
    (hz : delta C.theta T∈Icc 0 (total C ga ab)) (i : Fin 4) :
    (blocks C hg ga ab (Explicit.k r f (total C ga ab))
      (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).p=
        Blocks.p r f (total C ga ab) (delta C.theta T) i ∧
    (blocks C hg ga ab (Explicit.k r f (total C ga ab))
      (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).q=
        Blocks.q r f (total C ga ab) (delta C.theta T) i := by
  have hc := Explicit.source_coefficients r f hθ hz
  simpa only [Blocks.p,Blocks.q,Explicit.m,Explicit.eta,
    NegativeDEPositiveTD.Explicit.eta,PositiveTD.tilted,PositiveTD.eta]
    using block_coefficients (C:=C) hg ga ab (c:=Explicit.c r f (total C ga ab))
      (by linarith [hc.1.2]) hc.2.1 i

theorem actual_blocks_lower {Q : ℝ} {C : SignedCycle}
    (hg ga ab : Bool) (r : Regime) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta E≤0)
    (hθ : total C ga ab∈Icc (Explicit.left r f) (Explicit.right r f)) (i : Fin 4) :
    Blocks.block r f (total C ga ab) (delta C.theta T)
      (blocks C hg ga ab (Explicit.k r f (total C ga ab))
        (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).P
      (blocks C hg ga ab (Explicit.k r f (total C ga ab))
        (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).N i≤
    actualBlocks C hg ga ab (Explicit.k r f (total C ga ab))
      (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) (Explicit.ehWeight r) i := by
  let k := Explicit.k r f (total C ga ab)
  let l := Explicit.l r f (total C ga ab)
  let c := Explicit.c r f (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hc := Explicit.source_coefficients r f hθ hb.td_domain
  have hp := Blocks.original_pair r f hθ hb.td_domain
  have hcoef := family_block_coefficients hg ga ab r f hθ hb.td_domain
  have hbudget := block_budgets hg ga ab k l c hvar ha hz hs
  have hcharge (j : Fin 4) := mul_nonneg (charge_nonnegative r)
    (blocks C hg ga ab k l c j).P_nonneg
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      mixedBlock R (Blocks.p r f (total C ga ab) (delta C.theta T) j)
        (Blocks.q r f (total C ga ab) (delta C.theta T) j)
        (blocks C hg ga ab k l c j).P (blocks C hg ga ab k l c j).N-
          Explicit.errorCharge r*(blocks C hg ga ab k l c j).P≤
        PositiveTD.actualPairIncrement (blocks C hg ga ab k l c j) P := by
    have hpos : 0≤(blocks C hg ga ab k l c j).p := by
      rw [(hcoef j).1]
      exact (hp j).1.le
    have hh := PositiveTD.actual_block_minorant hy hP hQ hpos
      (hbudget j).1 (hbudget j).2
    rw [(hcoef j).1,(hcoef j).2] at hh
    exact (sub_le_self _ (hcharge j)).trans hh
  fin_cases i
  · have hfar : r=.far→k∈Icc (3/5:ℝ) (4/5) := by
      intro he
      subst r
      exact Explicit.far_k_domain f hθ
    have hP : positivePart (NegativePrimary.erase (!hg) (delta C.theta H))≤frameCap := by
      simpa [blocks,Block.P] using (hbudget 0).1
    have hN : negativePart (NegativePrimary.erase (!hg) (delta C.theta H))≤frameCap := by
      simpa [blocks,Block.N] using (hbudget 0).2
    have hh := actual_H_minorant r hHy (hcontained H) hQ hc.1 hfar hP hN
    simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      Blocks.p,Blocks.q,blocks,actualBlocks,hBlock,Block.P,Block.N,k,l,c] using hh
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,c] using hordinary 1 (P:=(C.point G).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hcontained G)
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,c] using hordinary 2 (P:=(C.point B).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hcontained B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hsorted D)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hcontained D) hQ hc.1 ⟨hc.2.2.1,hc.2.2.2⟩
      (original_error_bound hvar hn D)
    have he := (sub_le_self _ (hcharge 3)).trans hh
    simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,blocks,Blocks.p,Blocks.q,Block.P,Block.N,Blocks.dCost,k,l,c] using he

theorem stress_nonpositive {C : SignedCycle} (hg ga ab : Bool) {k l c u : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hu : 0≤u)
    (hz : delta C.theta T∈Icc 0 frameCap)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : stress C hg ga ab k l c u≤0 := by
  have hm := PositiveTD.tilted_pos hc hz
  have hw (i : Vertex) : 0≤weights C k l c u i := by
    fin_cases i
    · exact hk
    · exact hl
    · exact hl
    · exact hm.le
    · exact hc.le
    · show (0:ℝ)≤1
      norm_num
    · exact hu
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hfeasible i
  exact mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr hi)

theorem scalar_nonpositive {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (r : Regime) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hθ : total C ga ab∈Icc (Explicit.left r f) (Explicit.right r f))
    (he : magnitude C∈Icc (Explicit.eLeft r) (Explicit.eRight r))
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    Explicit.stressBase r f (aTotal C ga ab) (delta C.theta T) (magnitude C)+
      ∑i,Blocks.block r f (total C ga ab) (delta C.theta T)
        (blocks C hg ga ab (Explicit.k r f (total C ga ab))
          (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).P
        (blocks C hg ga ab (Explicit.k r f (total C ga ab))
          (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).N i≤0 := by
  let k := Explicit.k r f (total C ga ab)
  let l := Explicit.l r f (total C ga ab)
  let c := Explicit.c r f (total C ga ab)
  have hbud := budgets hg ga ab k l c hvar ha hz hs
  have hp := Explicit.family_positive r f hθ hbud.td_domain
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    (show aTotal C ga ab∈Icc 0 frameCap from
      ⟨ha,hbud.a_domain.2.trans hbud.total_domain.2⟩)
  change TwoPositive.ASupport.charge (aTotal C ga ab)≤
    primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A) at hA
  have hAg := mul_le_mul_of_nonneg_left hA hp.2.1.le
  have hzframe : delta C.theta T∈Icc 0 frameCap :=
    ⟨hz,hbud.td_domain.2.trans hbud.total_domain.2⟩
  have hT := PositiveTD.tReserve_nonneg (hsorted T) (hcontained T) hQ hp.2.2.1.le hzframe
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower hg ga ab r f hsorted hcontained hQ hHy hGy hBy hDy
      hvar ha hz hs hθ i)
  have hE := eh_gain_lower r f ga ab hflat hb hθ he
  have hbase := baseline_lower r f (aTotal C ga ab) (delta C.theta T)
  have hidentity := decomposition C hg ga ab k l c (Explicit.ehWeight r)
  have hu : 0≤Explicit.ehWeight r := by cases r <;> norm_num [Explicit.ehWeight,NegativeEH.p]
  have hupper := stress_nonpositive hg ga ab hp.1.le hp.2.1.le hp.2.2.1 hu hzframe hfeasible
  have htot : aTotal C ga ab+delta C.theta T=total C ga ab := rfl
  rw [htot] at hbase
  simp only [k,l,c] at hidentity
  dsimp only [Explicit.stressBase]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Source
end
end
end

section
/-!
## Complete small-EH low-total scalar exclusion

The
actual DE2 singleton is included as the fourth block. Its same-block
term is already separated, and its negative term is exactly the H
minorant. Every pure and saturated alternative is strictly positive.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem separated_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i j : Fin 4) :
    0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.positive .small .low (a+z) z (frameCap-(a+z)) i+
        Blocks.negative .small .low (a+z) z (frameCap-s) j := by
  have hH := separated_monotone true hθ (by norm_num) hs hs.1
  have hG := separated_monotone false hθ (by norm_num) hs hs.1
  have h0H := zero_separated_positive hθ ha hz i true
  have h0G := zero_separated_positive hθ ha hz i false
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hg0 : NegativeEH.g 0=0 := by simp [NegativeEH.g]
  simp only [hg0,sub_zero,zero_add,NegativeDEPositiveTD.LowSeparated.larger,Bool.false_eq_true,
    reduceIte] at hH hG h0H h0G
  fin_cases j
  · change 0<Explicit.baseline .small .low a z+NegativeEH.g s+_+
      V R (Explicit.k .small .low (a+z)) 1 (frameCap-s)
    linarith
  · change 0<Explicit.baseline .small .low a z+NegativeEH.g s+_+
      V R (Explicit.k .small .low (a+z)) (NegativeDEPositiveTD.Explicit.l .low (a+z)) (frameCap-s)
    linarith
  · have hB : V R (Explicit.k .small .low (a+z)) 1 (frameCap-s)≤
        NegativeDEPositiveTD.Explicit.V .low (a+z) z 2 (frameCap-s) :=
      NegativeDEPositiveTD.LowNegative.B_dominates_H hθ
      (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
      (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hsf.2],by linarith [hsf.1]⟩)
    change 0<Explicit.baseline .small .low a z+NegativeEH.g s+_+
      NegativeDEPositiveTD.Explicit.V .low (a+z) z 2 (frameCap-s)
    linarith
  · change 0<Explicit.baseline .small .low a z+NegativeEH.g s+_+
      V R (Explicit.k .small .low (a+z)) 1 (frameCap-s)
    linarith

theorem same_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 4) :
    0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.block .small .low (a+z) z (frameCap-(a+z)) (frameCap-s) i := by
  by_cases hiD : i=3
  · subst i
    rw [Blocks.block_D]
    simpa only [add_assoc] using separated_positive hθ ha hz hs 3 3
  by_cases hiG : i=1
  · subst i
    have hm := G_same_monotone hθ (by norm_num) hs hs.1
    have h0 : 0<Explicit.baseline .small .low a z+mixedBlock R
        (NegativeDEPositiveTD.Explicit.k .low (a+z)) (NegativeDEPositiveTD.Explicit.l .low (a+z))
        (frameCap-(a+z)) frameCap := zero_G_same_positive hθ ha hz
    have hg0 : NegativeEH.g 0=0 := by simp [NegativeEH.g]
    simp only [hg0,sub_zero,zero_add,NegativeDEPositiveTD.LowSame.ordinary] at hm
    have hb : Blocks.block .small .low (a+z) z (frameCap-(a+z)) (frameCap-s) 1=
        mixedBlock R (NegativeDEPositiveTD.Explicit.k .low (a+z))
          (NegativeDEPositiveTD.Explicit.l .low (a+z)) (frameCap-(a+z)) (frameCap-s)-
          0*(frameCap-(a+z)) :=
      Blocks.block_ordinary .small .low (a+z) z (frameCap-(a+z)) (frameCap-s) 1
    rw [hb]
    linarith
  obtain ⟨j,hj,hcase⟩ : ∃j : Fin 3,j.castSucc=i ∧ (j=0∨j=2) := by
    fin_cases i
    · exact ⟨0,rfl,Or.inl rfl⟩
    · exact absurd rfl hiG
    · exact ⟨2,rfl,Or.inr rfl⟩
    · exact absurd rfl hiD
  subst i
  rw [Blocks.block_ordinary]
  simp only [Explicit.errorCharge,zero_mul,sub_zero]
  by_cases horder : s≤a+z
  · have hp := pure_negative_positive hθ ha hz hs horder j.castSucc
    have hh : Explicit.V .small .low (a+z) z j (a+z-s)≤ mixedBlock R
        (Explicit.p .small .low (a+z) z j) (Explicit.q .small .low (a+z) z j)
        (frameCap-(a+z)) (frameCap-s) := NegativeDEPositiveTD.LowSame.HB_negative hθ
      (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) ⟨hs.1,horder⟩ j hcase
    rw [Blocks.negative_ordinary] at hp
    linarith
  · have horder' : a+z ≤ s := (lt_of_not_ge horder).le
    have hp := pure_positive_positive hθ ha hz ⟨horder',hs.2⟩ j.castSucc
    have hh : Explicit.U .small .low (a+z) z j (s-(a+z))≤ mixedBlock R
        (Explicit.p .small .low (a+z) z j) (Explicit.q .small .low (a+z) z j)
        (frameCap-(a+z)) (frameCap-s) := NegativeDEPositiveTD.LowSame.HB_positive hθ
      (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
      (show s∈Icc (a+z) frameCap from ⟨horder',by norm_num [frameCap]; linarith [hs.2]⟩) j hcase
    rw [Blocks.positive_ordinary] at hp
    simp only [Explicit.errorCharge,zero_mul,sub_zero] at hp
    linarith

theorem intrinsic_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i j : Fin 4) :
    0<Explicit.baseline .small .low a z+NegativeEH.g s+
      min (Blocks.pure .small .low (a+z) z s i j)
        (Blocks.saturated .small .low (a+z) z s i j) := by
  have hp : 0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.pure .small .low (a+z) z s i j := by
    by_cases horder : s≤a+z
    · simpa only [Blocks.pure,ChargedHybridConcentration.pure,ite_eq_left horder,Blocks.negative] using
        pure_negative_positive hθ ha hz hs horder j
    · simpa only [Blocks.pure,ChargedHybridConcentration.pure,ite_eq_right horder,Blocks.positive] using
        pure_positive_positive hθ ha hz ⟨(lt_of_not_ge horder).le,hs.2⟩ i
  have ht : 0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.saturated .small .low (a+z) z s i j := by
    by_cases hij : i=j
    · subst j
      rw [Blocks.saturated,ChargedHybridConcentration.saturated,ite_eq_left rfl]
      exact same_positive hθ ha hz hs i
    · simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,ite_eq_right hij,
        Blocks.positive,Blocks.negative,add_assoc] using separated_positive hθ ha hz hs i j
  rw [add_min]
  exact lt_min hp ht

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase .small .low a z s+
      ∑i,Blocks.block .small .low (a+z) z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .small .low P N hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) hs hP hN hPb hNb hbalance
  have hh := intrinsic_positive hθ ha hz hs i j
  dsimp [Explicit.stressBase,Explicit.gain]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallLow
end
end
end

section
/-!
## Every negative-EH / positive-TD2 scalar regime

The two EH-magnitude regimes and the two families of the total positive angle cover the whole
closed range (`family_cover`). Boundaries are included in both adjacent proofs. `scalar_positive`
is a scalar theorem; the exclusion of a signed cycle (`NegativeEHPositiveTD.Source.original`) adds
the stress comparison of the cycle, both mass budgets and the signed balance.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Scalar
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem family_cover {θ s : ℝ} (hθ : θ∈Icc 0 frameCap)
    (hs : s∈Icc (0:ℝ) (1/4)) :
    ∃ r : Regime,∃ f : Family,
      θ∈Icc (Explicit.left r f) (Explicit.right r f) ∧
      s∈Icc (Explicit.eLeft r) (Explicit.eRight r) := by
  by_cases he : s≤1/10
  · by_cases ht : θ≤1/6
    · exact ⟨.small,.low,⟨hθ.1,ht⟩,⟨hs.1,he⟩⟩
    · exact ⟨.small,.high,⟨show (1/6:ℝ) ≤ θ by linarith,hθ.2⟩,⟨hs.1,he⟩⟩
  · by_cases ht : θ≤1/4
    · exact ⟨.far,.low,⟨hθ.1,ht⟩,⟨show (1/10:ℝ) ≤ s by linarith,hs.2⟩⟩
    · exact ⟨.far,.high,⟨show (1/4:ℝ) ≤ θ by linarith,hθ.2⟩,⟨show (1/10:ℝ) ≤ s by linarith,hs.2⟩⟩

theorem scalar_positive (r : Regime) (f : Family) {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (Explicit.left r f) (Explicit.right r f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (Explicit.eLeft r) (Explicit.eRight r))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase r f a z s+∑i,Blocks.block r f (a+z) z (P i) (N i) i := by
  cases r <;> cases f
  · exact SmallLow.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact SmallHigh.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact FarLow.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact FarHigh.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Scalar
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

theorem original_flat_false {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hcap : magnitude C≤1/4)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hb0 := budgets hg ga ab 1 1 1 hvar ha hz hs
  obtain ⟨r,f,hθ,he⟩ := Scalar.family_cover hb0.total_domain ⟨hb0.eh_domain.1,hcap⟩
  let k := Explicit.k r f (total C ga ab)
  let l := Explicit.l r f (total C ga ab)
  let c := Explicit.c r f (total C ga ab)
  have hbud := budgets hg ga ab k l c hvar ha hz hs
  have hn := scalar_nonpositive hg ga ab r f hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hz hs hflat hb hθ he hfeasible
  have hp := Scalar.scalar_positive r f
    (a:=aTotal C ga ab) (z:=delta C.theta T) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l c i).P)
    (fun i => (blocks C hg ga ab k l c i).N) hθ ha hz he
    (fun i => (blocks C hg ga ab k l c i).P_nonneg)
    (fun i => (blocks C hg ga ab k l c i).N_nonneg)
    hbud.positive_bound hbud.negative_bound hbud.balance
  exact (not_le_of_gt hp) hn

/-- The EH1 owner gives every analytic cut at the radius of the cycle. -/
theorem genuine_domain {Q : ℝ} {C : SignedCycle}
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hEy : (C.point E).y≤0)
    (hEc : (C.point E).Core) (hvar : positiveVariation C.theta≤frameCap)
    (hs : delta C.theta E<0) (hEH : C.Feasible E 1) (hnot : ¬C.Feasible E 0) :
    (C.point E).a=7/12 ∧ -(C.point E).y∈Icc (0:ℝ) (39/250) ∧ magnitude C≤1/4 := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have herr := original_error_bound hvar hn E
  have hm : magnitude C∈Ioc 0 frameCap :=
    ⟨neg_pos.mpr hs,(neg_le_abs (delta C.theta E)).trans herr⟩
  have hd : delta C.theta E= -magnitude C := by simp [magnitude]
  have hprimary : quarterFeasible (C.point E) (C.point H) (-magnitude C) 1 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg,magnitude] using hEH
  have hsecondary : ¬quarterFeasible (C.point E) (C.point H) (-magnitude C) 0 := by
    intro h
    apply hnot
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg,magnitude] using h
  have hh := NegativeCoreE.genuine_negative_flat (hsorted E) hEy hEc
    (hsorted H) hHy (hcontained H) hQ hm hprimary hsecondary
  exact ⟨hh.1,⟨neg_nonneg.mpr hEy,hh.2.1.le⟩,hh.2.2.le⟩

theorem original {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta E<0)
    (hnot : ¬C.Feasible E 0)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hEH : C.Feasible E 1 := by simpa [owners,E] using hfeasible E
  obtain ⟨hf,hb,hu⟩ := genuine_domain hsorted hcontained hQ hHy hEy hEc hvar hs hEH hnot
  exact original_flat_false hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
    hvar ha hz hs.le hf hb hu hfeasible

/-- The seven witnesses of the cycle, for either HG owner. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta E<0)
    (hnot : ¬C.Feasible E 0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 1) : False := by
  obtain ⟨hg,hhg⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  apply original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy hEy hEc
    hvar ha hz hs hnot
  intro i
  fin_cases i
  · simpa [owners,H] using hhg
  · simpa [owners,G] using hGA
  · simpa [owners,A] using hAB
  · simpa [owners,B] using hBT
  · simpa [owners,T] using hTD
  · simpa [owners,D] using hDE
  · simpa [owners,E] using hEH

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Source
end
end
end
