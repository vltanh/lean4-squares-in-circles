module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAStress
public import SquaresInCircles.Eight.Owners.GA.Negative.ELowAStress
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TAlignedGain
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TPairedConcentration
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TSourceData
public import SquaresInCircles.Eight.Owners.GA.Paired.ELowASource

/-!
# Eight squares: small nonnegative A and negative core E at the BT3 alignment

Independent negative
DE/EH secants retain their proved actual H/D corrections; the two aligned
T primaries supply the full removed angular charge. The scalar reserve
uses the original A signed total, including opposite individual signs.
-/

section
/-!
## The aligned original T stress pays the complete paired scalar

The unchanged H/G/B/D points pay
all four signed blocks, A/E pay their signed-total support charges, and
the current T point pays its proved kappa charge at its actual alignment.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NonnegativeTotals.Source (aTotal eTotal)

theorem block_lower {Q ε s : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    (hε : ε∈Icc 0 frameCap)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hs : s∈Icc 0 frameCap) (hd : delta C.theta B=-s) (hTD : delta C.theta T=0) (i : Fin 4) :
    Concentration.block ε i (blocks C hg ga ab de eh ε i).P (blocks C hg ga ab de eh ε i).N≤
      actualBlocks C hg ga ab de eh ε i := by
  have hr := ranges hε
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      mixedBlock R (p ε j) (q ε j)
        (blocks C hg ga ab de eh ε j).P (blocks C hg ga ab de eh ε j).N≤
          PositiveTD.actualPairIncrement (blocks C hg ga ab de eh ε j) P := by
    have hco := block_coefficients (C:=C) (hg:=hg) ga ab de eh hε j
    have hpn : 0≤(blocks C hg ga ab de eh ε j).p := by
      rw [hco.1]
      exact (coefficients hε j).1.le
    have hb := block_budgets hg ga ab de eh ε hvar ha he hs hd hTD j
    have hh := PositiveTD.actual_block_minorant hy hP hQ hpn hb.1 hb.2
    rwa [hco.1,hco.2] at hh
  fin_cases i
  · simpa [Concentration.block,NonnegativeTotals.NegativeTD.Concentration.block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 0 hHy (hc H)
  · simpa [Concentration.block,NonnegativeTotals.NegativeTD.Concentration.block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 1
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G)
  · simpa [Concentration.block,NonnegativeTotals.NegativeTD.Concentration.block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    have hsmall := NegativePrimary.erase_abs_bound de (original_error_bound hvar hn D)
    have hk : k ε∈Icc (1/2:ℝ) (17/20:ℝ) := ⟨by linarith [hr.1],by linarith [hr.2.1]⟩
    have hcoef : c∈Icc (k ε) 2 := ⟨by dsimp [c]; linarith [hr.2.1],by norm_num [c]⟩
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hsort D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hQ hk hcoef hsmall
    simpa [Concentration.block,NonnegativeTotals.NegativeTD.Concentration.block,PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,p,q,aD,NonnegativeTotals.NegativeTD.p,NonnegativeTotals.NegativeTD.q,NonnegativeTotals.NegativeTD.aD] using hh

theorem stress_lower {Q ε s : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    (hε : ε∈Icc 0 frameCap)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hs : s∈Icc 0 frameCap) (hd : delta C.theta B=-s) (hTD : delta C.theta T=0) (hhg : hg=0∨hg=2) :
    base ε+l ε*TwoPositive.ASupport.charge (aTotal C ga ab)+
      TwoPositive.ASupport.charge (eTotal C de eh)+gain s+
      (∑i,Concentration.block ε i (blocks C hg ga ab de eh ε i).P (blocks C hg ga ab de eh ε i).N)≤
        actualStress C hg ga ab de eh ε := by
  have hb := budgets hg ga ab de eh ε hvar ha he hs hd hTD
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall := original_error_bound hvar hn
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => block_lower ga ab de eh hε
    hsort hc hQ hHy hGy hBy hDy hvar ha he hs hd hTD i (hg:=hg))
  have hres := NonnegativeTotals.Source.primary_reserves ga ab de eh hsort hc hQ hsmall
    (show 0≤l ε by linarith [(ranges hε).2.2.1]) hb.2.1 hb.2.2.1
  have hgain := mul_le_mul_of_nonneg_left
    (aligned_work_lower (hsort T) hcoreT (hc T) hQ hs)
    (show 0≤c by norm_num [c,NonnegativeTotals.NegativeTD.c])
  rw [decomposition C ga ab de eh hhg hd hTD]
  dsimp [gain]
  linarith

theorem weights_nonnegative {ε : ℝ} {C : SignedCycle}
    (hε : ε∈Icc 0 frameCap) (i : Vertex) : 0≤weights C ε i := by
  have hr := ranges hε
  have hk : 0≤k ε := by linarith [hr.1]
  have hl : 0≤l ε := by linarith [hr.2.2.1]
  fin_cases i <;> simp [weights,c,NonnegativeTotals.NegativeTD.c] <;> positivity

theorem stress_nonpositive {ε : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    (hε : ε∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : actualStress C hg ga ab de eh ε≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,NonnegativeTotals.Source.owners,H] using hHG
    · simpa [owners,NonnegativeTotals.Source.owners,G] using hGA
    · simpa [owners,NonnegativeTotals.Source.owners,A] using hAB
    · simpa [owners,NonnegativeTotals.Source.owners,B] using hBT
    · simpa [owners,NonnegativeTotals.Source.owners,T] using hTD
    · simpa [owners,NonnegativeTotals.Source.owners,D] using hDE
    · simpa [owners,NonnegativeTotals.Source.owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonnegative hε) hf)

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Source
end
end
end

section
/-!
## The actual aligned-T exclusion above the small primary-total range

The short T magnitude is
derived from the current two projections. Every concentration inequality
and every scalar endpoint is then supplied to the original weighted
separation inequality, with arbitrary signs in both selected A/E pairs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Source
open Candidate Secondary PositiveAngularEnvelope
open NonnegativeTotals.Source (aTotal eTotal)

theorem high_actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hδ : delta C.theta B≤0) (htd : delta C.theta T=0)
    (hlarge : L≤total C ga ab de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  let s : ℝ := -delta C.theta B
  let ε : ℝ := eTotal C de eh
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall := original_error_bound hvar hn B
  have hs : s∈Icc 0 frameCap := ⟨neg_nonneg.mpr hδ,(neg_le_abs _).trans hsmall⟩
  have hbt : delta C.theta B=-s := by dsimp [s]; ring
  have hM := aligned_short hsort hcoreT hc hQ hDy hs hBT hTD hbt htd
  have hb := budgets hg ga ab de eh ε hvar ha he hs hbt htd
  have hε : ε∈Icc 0 frameCap := hb.2.2.1
  have hp := Concentration.sum_scalar_positive
    (fun i => (blocks C hg ga ab de eh ε i).P)
    (fun i => (blocks C hg ga ab de eh ε i).N)
    (show total C ga ab de eh∈Icc L frameCap from ⟨hlarge,hb.1.2⟩)
    (show ε∈Icc 0 (total C ga ab de eh) from ⟨he,by dsimp [ε,total]; linarith⟩)
    (show s∈Icc 0 M from ⟨hs.1,hM.le⟩)
    (fun i => (blocks C hg ga ab de eh ε i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh ε i).N_nonneg)
    hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  have hcost : primaryCost (total C ga ab de eh) ε=
      l ε*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh) := by
    simp [primaryCost,NonnegativeTotals.NegativeTD.primaryCost,total,ε]
  rw [hcost] at hp
  have hlow := stress_lower ga ab de eh hε hsort hc hcoreT hQ hHy hGy hBy hDy
    hvar ha he hs hbt htd hhg
  have hu := stress_nonpositive ga ab de eh hε hHG hGA hAB hBT hTD hDE hEH
  linarith [hp,hlow,hu]

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Source
end
end
end

section
/-!
## The small A-total fixed stress with an aligned negative BT3

The same charged four-circle
reference deletes both original T arguments analytically. Its actual
T gain dominates the complete angular charge on [0,h]. The original
signed A/E pair support comparisons retain every selected primary tie.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.LowA
open Candidate Secondary NegativePrimary
open PairedE (cycleTotal primaryGain selected_charge cycle_total_bounds charge_linear)

abbrev aTotal := PairedE.LowA.aTotal
abbrev owners := Paired.Source.owners

def weights : Vertex→ℝ :=
  ![PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowL,PositiveATD0.lowC,
    PositiveATD0.lowC,1,1]
def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) : ℝ :=
  ∑i,weights i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))
def reference (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) : ℝ :=
  PositiveATD0.lowBaseline+
    (if hg=0 then
      PositiveATD0.pairIncrement PositiveATD0.lowK 1 0
        (erase eh (delta C.theta E)) (C.point H)+
      PositiveATD0.pairIncrement PositiveATD0.lowK PositiveATD0.lowL (delta C.theta H)
        (erase ga (delta C.theta G)) (C.point G).reflect
    else
      PositiveATD0.pairIncrement PositiveATD0.lowK 1 (delta C.theta H)
        (erase eh (delta C.theta E)) (C.point H)+
      PositiveATD0.pairIncrement PositiveATD0.lowK PositiveATD0.lowL 0
        (erase ga (delta C.theta G)) (C.point G).reflect)+
    PositiveATD0.pairIncrement PositiveATD0.lowL PositiveATD0.lowC
      (erase ab (delta C.theta A)) 0 (C.point B).reflect+
    PositiveATD0.Source.dIncrement 0 (erase de (delta C.theta D)) (C.point D).reflect

def tGain (C : SignedCycle) : ℝ :=
  PositiveATD0.lowC*PairedA.work (C.point T) (delta C.theta B) 0

private theorem r92lo_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92lo_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92lo_e0 (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j :=
  r92lo_edge_zero C 0 j (by decide)
private theorem r92lo_e1 (C : SignedCycle) (j : Fin 4) :
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j :=
  r92lo_edge_quarter C 1 j (by decide)
private theorem r92lo_e2 (C : SignedCycle) (j : Fin 4) :
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j :=
  r92lo_edge_zero C 2 j (by decide)
private theorem r92lo_e3 (C : SignedCycle) (j : Fin 4) :
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j :=
  r92lo_edge_quarter C 3 j (by decide)
private theorem r92lo_e4 (C : SignedCycle) (j : Fin 4) :
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j :=
  r92lo_edge_zero C 4 j (by decide)
private theorem r92lo_e5 (C : SignedCycle) (j : Fin 4) :
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j :=
  r92lo_edge_quarter C 5 j (by decide)
private theorem r92lo_e6 (C : SignedCycle) (j : Fin 4) :
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j :=
  r92lo_edge_quarter C 6 j (by decide)

private theorem r92lo_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

private def r92lo_u (α u : ℝ) (P : SignedPoint) : ℝ :=
  α*(edgeWidth u-1)-α*Real.sin u*P.a-α*Real.cos u*P.y
private def r92lo_v (β v : ℝ) (P : SignedPoint) : ℝ :=
  β*(edgeWidth v-1)-β*Real.cos v*P.a-β*Real.sin v*P.y

private theorem r92lo_pinc (p q a b : ℝ) (P : SignedPoint) :
    PositiveATD0.pairIncrement p q a b P=
      r92lo_u p a P+r92lo_v q b P+fullSupport q p+PositiveATD0.charge*a+PositiveATD0.charge*b := by
  simp only [PositiveATD0.pairIncrement,pairF,pairG,r92lo_u,r92lo_v]
  ring

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) (hTD : delta C.theta T=0) :
    actualStress C hg ga ab de eh=
      reference C hg ga ab de eh+
        PositiveATD0.charge*(aTotal C ga ab+cycleTotal C de eh+delta C.theta B)+
        PositiveATD0.lowL*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
        primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E)+tGain C := by
  have hsum := r92lo_delta_sum C
  have hT4 : delta C.theta 4=0 := hTD
  have h1 : actualStress C hg ga ab de eh=
      PositiveATD0.lowK*(edgeWidth (delta C.theta H)-C.edge H hg)+
      PositiveATD0.lowL*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      PositiveATD0.lowL*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      PositiveATD0.lowC*(edgeWidth (delta C.theta B)-C.edge B 3)+
      PositiveATD0.lowC*(edgeWidth (delta C.theta T)-C.edge T 2)+
      1*(edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [actualStress,Fin.sum_univ_seven,weights,owners,Paired.Source.owners,
      Matrix.cons_val,H,G,A,B,T,D,E]
  have hG : PositiveATD0.lowL*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      r92lo_v PositiveATD0.lowL (erase ga (delta C.theta G)) (C.point G).reflect+
      PositiveATD0.lowL*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*
        Real.sin (delta C.theta G)+(C.point A).y*(1-Real.cos (delta C.theta G))) else 0)+
      PositiveATD0.lowL+PositiveATD0.lowL*(C.point A).y := by
    cases ga <;>
      simp only [r92lo_v,r92lo_e1,G,A,quarterProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hA : PositiveATD0.lowL*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      r92lo_u PositiveATD0.lowL (erase ab (delta C.theta A)) (C.point B).reflect+
      PositiveATD0.lowL*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*
        Real.sin (delta C.theta A)+(C.point A).y*(Real.cos (delta C.theta A)-1)) else 0)+
      PositiveATD0.lowL-PositiveATD0.lowL*(C.point A).y := by
    cases ab <;>
      simp only [r92lo_u,r92lo_e2,A,B,zeroProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hB : PositiveATD0.lowC*(edgeWidth (delta C.theta B)-C.edge B 3)=
      r92lo_v PositiveATD0.lowC 0 (C.point B).reflect+tGain C+PositiveATD0.lowC+
        PositiveATD0.lowC*(C.point T).y := by
    simp only [r92lo_v,r92lo_e3,B,T,quarterProjection,tGain,PairedA.work,
      SignedPoint.reflect,Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    ring
  have hT : PositiveATD0.lowC*(edgeWidth (delta C.theta T)-C.edge T 2)=
      PositiveATD0.lowC*(1-(C.point T).y+(C.point D).y) := by
    simp only [r92lo_e4,T,D,zeroProjection,hT4,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
      edgeWidth_zero]
    ring
  have hDv : 1*(edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      PositiveATD0.Source.dIncrement 0 (erase de (delta C.theta D)) (C.point D).reflect+
      (if de then edgeWidth (delta C.theta D)-1-((C.point E).a*Real.sin (delta C.theta D)+
        (C.point E).y*(1-Real.cos (delta C.theta D))) else 0)+
      (C.point E).y-PositiveATD0.lowC-PositiveATD0.lowC*(C.point D).y+
      (1+PositiveATD0.lowC)*(1-Secondary.diagonal)-
      PositiveATD0.charge*erase de (delta C.theta D) := by
    cases de <;>
      simp only [r92lo_e5,D,E,quarterProjection,PositiveATD0.Source.dIncrement,PositiveATD0.dF,
        PositiveATD0.dG,erase,SignedPoint.reflect,Bool.false_eq_true,↓reduceIte,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero] <;>
      ring
  have hEv : 1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      r92lo_v 1 (erase eh (delta C.theta E)) (C.point H)+
      (if eh then edgeWidth (delta C.theta E)-1-((C.point E).a*Real.sin (delta C.theta E)+
        (C.point E).y*(Real.cos (delta C.theta E)-1)) else 0)+1-(C.point E).y := by
    cases eh <;>
      simp only [r92lo_v,r92lo_e6,E,H,quarterProjection,erase,Bool.false_eq_true,↓reduceIte,
        Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero] <;>
      ring
  have hGs : erase ga (delta C.theta G)+PairedE.selected ga (delta C.theta G)=delta C.theta G := by
    cases ga <;> simp [PairedE.selected]
  have hAs : erase ab (delta C.theta A)+PairedE.selected ab (delta C.theta A)=delta C.theta A := by
    cases ab <;> simp [PairedE.selected]
  have hDs : erase de (delta C.theta D)+PairedE.selected de (delta C.theta D)=delta C.theta D := by
    cases de <;> simp [PairedE.selected]
  have hEs : erase eh (delta C.theta E)+PairedE.selected eh (delta C.theta E)=delta C.theta E := by
    cases eh <;> simp [PairedE.selected]
  rw [h1,hG,hA,hB,hT,hDv,hEv]
  rcases hhg with rfl|rfl
  · have hH : PositiveATD0.lowK*(edgeWidth (delta C.theta H)-C.edge H 0)=
        r92lo_u PositiveATD0.lowK 0 (C.point H)+
        r92lo_u PositiveATD0.lowK (delta C.theta H) (C.point G).reflect+PositiveATD0.lowK := by
      simp only [r92lo_u,r92lo_e0,H,G,zeroProjection,SignedPoint.reflect,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
    rw [hH]
    simp only [reference,PositiveATD0.lowBaseline,r92lo_pinc,aTotal,PairedE.LowA.aTotal,
      cycleTotal,PairedE.total,primaryGain,↓reduceIte]
    simp only [H,G,A,B,T,D,E] at hGs hAs hDs hEs ⊢
    linear_combination (-PositiveATD0.charge)*(hGs+hAs+hDs+hEs+hsum)+PositiveATD0.charge*hT4
  · have hH : PositiveATD0.lowK*(edgeWidth (delta C.theta H)-C.edge H 2)=
        r92lo_u PositiveATD0.lowK (delta C.theta H) (C.point H)+
        r92lo_u PositiveATD0.lowK 0 (C.point G).reflect+PositiveATD0.lowK := by
      simp only [r92lo_u,r92lo_e0,H,G,zeroProjection,SignedPoint.reflect,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
    rw [hH]
    simp only [reference,PositiveATD0.lowBaseline,r92lo_pinc,aTotal,PairedE.LowA.aTotal,
      cycleTotal,PairedE.total,primaryGain,show ((2:Fin 4)=0)=False by decide,↓reduceIte]
    simp only [H,G,A,B,T,D,E] at hGs hAs hDs hEs ⊢
    linear_combination (-PositiveATD0.charge)*(hGs+hAs+hDs+hEs+hsum)+PositiveATD0.charge*hT4

theorem reference_lower {q : ℝ} {C : SignedCycle} (hg : Fin 4)
    (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    PositiveATD0.lowBaseline≤reference C hg ga ab de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab true
  simp only [erase_true] at hbb
  have hB := PositiveATD0.actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,
    Matrix.cons_val] at hB
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) true de
  simp only [erase_true] at hdb
  have hde := pair_error_bounds hdb.1 hdb.2
  have hd := PositiveATD0.actual_D_lower (P:=(C.point D).reflect)
    (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  have hD : 0≤PositiveATD0.Source.dIncrement 0
      (erase de (delta C.theta D)) (C.point D).reflect := by
    simpa [PositiveATD0.Source.dIncrement,sub_nonneg] using hd
  by_cases hhg : hg=0
  · have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) true eh
    have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) false ga
    simp only [erase_true,erase_false] at hhb hgb
    have hH := PositiveATD0.actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
    have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq hgb.1 hgb.2
    simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,
      Matrix.cons_val] at hH hG
    simp only [reference,hhg,↓reduceIte]
    linarith
  · have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) false eh
    have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) true ga
    simp only [erase_true,erase_false] at hhb hgb
    have hH := PositiveATD0.actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
    have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq hgb.1 hgb.2
    simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,
      Matrix.cons_val] at hH hG
    simp only [reference,hhg,↓reduceIte]
    linarith

theorem t_gain_lower {C : SignedCycle}
    (hs : (C.point T).Sorted) (hcore : (C.point T).AvoidsCore)
    (hB : delta C.theta B≤0) (hsmall : |delta C.theta B|≤frameCap) :
    (PositiveATD0.charge+19/875)*(-delta C.theta B)≤tGain C := by
  let s : ℝ := -delta C.theta B
  have hsdom : s∈Icc 0 frameCap := ⟨neg_nonneg.mpr hB,(neg_le_abs _).trans hsmall⟩
  have hw := Paired.aligned_work_weak hs hcore hsdom
  have hp := PairedE.phi_chord hsdom
  have hh := mul_le_mul_of_nonneg_left hw
    (show 0≤PositiveATD0.lowC by norm_num [PositiveATD0.lowC])
  dsimp [tGain,PositiveAngularEnvelope.phi,PositiveATD0.charge,PositiveATD0.lowC,s] at *
  simp only [neg_neg] at hh
  linarith

theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (hb : delta C.theta B≤0) (htd : delta C.theta T=0) (he : 0≤cycleTotal C de eh) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hweights (i : Vertex) : 0≤weights i := by
    fin_cases i <;> norm_num [weights,PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowC]
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,Paired.Source.owners,H] using hHG
    · simpa [owners,Paired.Source.owners,G] using hGA
    · simpa [owners,Paired.Source.owners,A] using hAB
    · simpa [owners,Paired.Source.owners,B] using hBT
    · simpa [owners,Paired.Source.owners,T] using hTD
    · simpa [owners,Paired.Source.owners,D] using hDE
    · simpa [owners,Paired.Source.owners,E] using hEH
  have hu : actualStress C hg ga ab de eh≤0 := by
    apply Finset.sum_nonpos
    intro i _
    have hh := hf i
    change 0≤C.edge i (owners hg ga ab de eh i)-edgeWidth (delta C.theta i) at hh
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hreference := reference_lower hg ga ab de eh hs hc hQ hHy hGy hBy hDy hvar
  have hAmem : aTotal C ga ab∈Icc 0 frameCap :=
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hAcharge := selected_charge ga ab (hs A) (hc A) hQ (hsmall G) (hsmall A) hAmem
  have hAweighted := mul_le_mul_of_nonneg_left hAcharge
    (show 0≤PositiveATD0.lowL by norm_num [PositiveATD0.lowL])
  have hscalar := PositiveATD0.low_scalar_positive ha
  have hEmem := cycle_total_bounds de eh hvar he
  have hEcharge := selected_charge de eh (hs E) (hc E) hQ (hsmall D) (hsmall E) hEmem
  have hElinear := charge_linear hEmem
  have hTgain := t_gain_lower (hs T) hcoreT hb (hsmall B)
  rw [decomposition C ga ab de eh hhg htd] at hu
  change PositiveATD0.lowL*TwoPositive.ASupport.charge (aTotal C ga ab)≤_ at hAweighted
  change TwoPositive.ASupport.charge (cycleTotal C de eh)≤_ at hEcharge
  dsimp only [PositiveATD0.charge,PositiveATD0.lowL] at hu hscalar hTgain hAweighted
  linarith [hEmem.1]

end LowA

namespace Paired.Source
open Candidate Secondary
open NonnegativeTotals.Source (aTotal eTotal)

/-- All selected nonnegative A/E totals at the actual negative-BT3
TD-alignment endpoint; the small and large scalar ranges are exhaustive. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hb : delta C.theta B≤0) (htd : delta C.theta T=0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  by_cases hlow : total C ga ab de eh≤L
  · have hA : LowA.aTotal C ga ab=aTotal C ga ab := rfl
    have haLow : LowA.aTotal C ga ab∈Icc 0 (1/6:ℝ) :=
      ⟨hA ▸ ha,by dsimp [total,L] at hlow; linarith⟩
    exact LowA.actual_false ga ab de eh hsort hc hcoreT hQ hHy hGy hBy hDy
      hvar hHG hGA hAB hBT hTD hDE hEH haLow hb htd he
  · exact high_actual_false ga ab de eh hsort hc hcoreT hQ hHy hGy hBy hDy
      hvar ha he hb htd (lt_of_not_ge hlow).le hHG hGA hAB hBT hTD hDE hEH

end Paired.Source
end SquaresInCircles.Eight.GlobalGA.NonpositiveT
end
end

section
/-!
## Large-A negative-E blocks with the aligned BT3 pair removed

The DE secant and the EH charge are unchanged. Both T arguments are deleted only in the analytic
blocks, and the TD alignment is kept in every signed budget (`budgets`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.LargeE
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks
open NegativePrimary (erase)
open PairedE NegativeELargeA

abbrev aTotal := LowA.aTotal
abbrev magnitude := NegativeELowA.magnitude

def negativeTotal (C : SignedCycle) (de eh : Bool) : ℝ :=
  magnitude C D de+magnitude C E eh-delta C.theta B

def owners (hg ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    3,2,if de then 3 else 2,if eh then 1 else 0]

def weights (C : SignedCycle) (de : Bool) : Vertex→ℝ :=
  ![NegativeELargeA.k,NegativeELargeA.l,NegativeELargeA.l,c,c,if de then 1/Real.cos (delta C.theta D) else 1,1]

def stress (C : SignedCycle) (hg ga ab de eh : Bool) : ℝ :=
  ∑i,weights C de i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))

def blocks (C : SignedCycle) (hg ga ab de eh : Bool) : Fin 4→Block :=
  ![⟨NegativeELargeA.k,1,erase (!hg) (delta C.theta H),erase eh (delta C.theta E)⟩,
    ⟨NegativeELargeA.k,NegativeELargeA.l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩,
    ⟨NegativeELargeA.l,c,erase ab (delta C.theta A),0⟩,
    ⟨NegativeELargeA.k,1,erase de (delta C.theta D),0⟩]

def actualBlocks (C : SignedCycle) (hg ga ab de eh : Bool) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab de eh 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh 2) (C.point B).reflect,
    if de then 0 else PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect]

abbrev deGain := NegativeELargeA.Source.deGain
abbrev ehGain := NegativeELargeA.Source.ehGain

def tGain (C : SignedCycle) : ℝ :=
  c*PairedA.work (C.point T) (delta C.theta B) 0

private theorem r92le_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92le_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92le_e0 (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j :=
  r92le_edge_zero C 0 j (by decide)
private theorem r92le_e1 (C : SignedCycle) (j : Fin 4) :
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j :=
  r92le_edge_quarter C 1 j (by decide)
private theorem r92le_e2 (C : SignedCycle) (j : Fin 4) :
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j :=
  r92le_edge_zero C 2 j (by decide)
private theorem r92le_e3 (C : SignedCycle) (j : Fin 4) :
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j :=
  r92le_edge_quarter C 3 j (by decide)
private theorem r92le_e4 (C : SignedCycle) (j : Fin 4) :
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j :=
  r92le_edge_zero C 4 j (by decide)
private theorem r92le_e5 (C : SignedCycle) (j : Fin 4) :
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j :=
  r92le_edge_quarter C 5 j (by decide)
private theorem r92le_e6 (C : SignedCycle) (j : Fin 4) :
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j :=
  r92le_edge_quarter C 6 j (by decide)

private def r92le_u (α u : ℝ) (P : SignedPoint) : ℝ :=
  α*(edgeWidth u-1)-α*Real.sin u*P.a-α*Real.cos u*P.y
private def r92le_v (β v : ℝ) (P : SignedPoint) : ℝ :=
  β*(edgeWidth v-1)-β*Real.cos v*P.a-β*Real.sin v*P.y

private theorem r92le_increment (α β u v : ℝ) (P : SignedPoint) :
    PositiveTD.actualPairIncrement ⟨α,β,u,v⟩ P=r92le_u α u P+r92le_v β v P+fullSupport β α := by
  simp only [PositiveTD.actualPairIncrement,pairF,pairG,r92le_u,r92le_v]
  ring

theorem decomposition (C : SignedCycle) (hg ga ab de eh : Bool)
    (hflat : (C.point E).a=7/12)
    (hTD : delta C.theta T=0) (hD : Real.cos (delta C.theta D)≠0) :
    stress C hg ga ab de eh=base+(∑i,actualBlocks C hg ga ab de eh i)+
      NegativeELargeA.l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      deGain C de+ehGain C eh+tGain C := by
  have hT4 : delta C.theta 4=0 := hTD
  have hE6 : (C.point 6).a=7/12 := hflat
  have hinv : Real.cos (delta C.theta 5)*(Real.cos (delta C.theta 5))⁻¹=1 := mul_inv_cancel₀ hD
  have hclip : clippedSupport 1 c=(1+c)*Secondary.diagonal := by
    rw [clippedSupport,ite_eq_left (by norm_num [c]),diagonalSupport]
  have h1 : stress C hg ga ab de eh=
      NegativeELargeA.k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))+
      NegativeELargeA.l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      NegativeELargeA.l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      c*(edgeWidth (delta C.theta B)-C.edge B 3)+c*(edgeWidth (delta C.theta T)-C.edge T 2)+
      (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [stress,Fin.sum_univ_seven,weights,owners,Matrix.cons_val,H,G,A,B,T,D,E]
  have hH : NegativeELargeA.k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))=
      r92le_u NegativeELargeA.k (erase (!hg) (delta C.theta H)) (C.point H)+
      r92le_u NegativeELargeA.k (erase hg (delta C.theta H)) (C.point G).reflect+
      NegativeELargeA.k := by
    cases hg <;>
      simp only [r92le_u,r92le_e0,H,G,zeroProjection,erase,SignedPoint.reflect,Bool.not_true,
        Bool.not_false,Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hG : NegativeELargeA.l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      r92le_v NegativeELargeA.l (erase ga (delta C.theta G)) (C.point G).reflect+
      NegativeELargeA.l*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*
        Real.sin (delta C.theta G)+(C.point A).y*(1-Real.cos (delta C.theta G))) else 0)+
      NegativeELargeA.l+NegativeELargeA.l*(C.point A).y := by
    cases ga <;>
      simp only [r92le_v,r92le_e1,G,A,quarterProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hA : NegativeELargeA.l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      r92le_u NegativeELargeA.l (erase ab (delta C.theta A)) (C.point B).reflect+
      NegativeELargeA.l*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*
        Real.sin (delta C.theta A)+(C.point A).y*(Real.cos (delta C.theta A)-1)) else 0)+
      NegativeELargeA.l-NegativeELargeA.l*(C.point A).y := by
    cases ab <;>
      simp only [r92le_u,r92le_e2,A,B,zeroProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hB : c*(edgeWidth (delta C.theta B)-C.edge B 3)=
      r92le_v c 0 (C.point B).reflect+tGain C+c+c*(C.point T).y := by
    simp only [r92le_v,r92le_e3,B,T,quarterProjection,tGain,PairedA.work,SignedPoint.reflect,
      Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    ring
  have hT : c*(edgeWidth (delta C.theta T)-C.edge T 2)=
      c*(1-(C.point T).y+(C.point D).y) := by
    simp only [r92le_e4,T,D,zeroProjection,hT4,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
      edgeWidth_zero]
    ring
  have hDv : (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      (if de then 0 else PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect)+
      deGain C de+1+(C.point E).y-c*(C.point D).y-clippedSupport 1 c := by
    cases de
    · simp only [r92le_e5,D,E,quarterProjection,deGain,NegativeELargeA.Source.deGain,
        PositiveTD.actualDIncrement,SignedPoint.reflect,Bool.false_eq_true,↓reduceIte,
        Matrix.cons_val]
      ring
    · simp only [r92le_e5,D,E,quarterProjection,deGain,NegativeELargeA.Source.deGain,hE6,
        ↓reduceIte,Matrix.cons_val]
      linear_combination (C.point 6).y*hinv
  have hEv : 1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      r92le_v 1 (erase eh (delta C.theta E)) (C.point H)+ehGain C eh+1-(C.point E).y := by
    cases eh <;>
      simp only [r92le_v,r92le_e6,E,H,quarterProjection,ehGain,NegativeELargeA.Source.ehGain,erase,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  rw [h1,hH,hG,hA,hB,hT,hDv,hEv]
  simp only [actualBlocks,blocks,Fin.sum_univ_four,Matrix.cons_val,r92le_increment,base,
    primaryGain]
  linear_combination -hclip

def selectedA (C : SignedCycle) (ga ab : Bool) (f : ℝ→ℝ) : ℝ :=
  selected ga (f (delta C.theta G))+selected ab (f (delta C.theta A))

def selectedNegative (C : SignedCycle) (de eh : Bool) (f : ℝ→ℝ) : ℝ :=
  f (delta C.theta B)+f (delta C.theta T)+selected de (f (delta C.theta D))+selected eh (f (delta C.theta E))

theorem sum_parts (C : SignedCycle) (hg ga ab de eh : Bool)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab de eh i).u+f (blocks C hg ga ab de eh i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-selectedNegative C de eh f := by
  cases hg <;> cases ga <;> cases ab <;> cases de <;> cases eh <;>
    simp [blocks,erase,selectedA,selectedNegative,selected,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem selectedA_signed (C : SignedCycle) (ga ab : Bool) :
    selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab := by
  have hG := positive_sub_negative (delta C.theta G)
  have hA := positive_sub_negative (delta C.theta A)
  cases ga <;> cases ab <;>
    simp [selectedA,aTotal,PairedE.LowA.aTotal,PairedE.total,PairedE.selected] <;> linarith

theorem selectedA_nonnegative (C : SignedCycle) (ga ab : Bool) (f : ℝ→ℝ)
    (hf : ∀x,0≤f x) : 0≤ selectedA C ga ab f := by
  have hG := hf (delta C.theta G)
  have hA := hf (delta C.theta A)
  cases ga <;> cases ab <;> simp [selectedA,selected] <;> positivity

theorem selectedNegative_parts {C : SignedCycle} (de eh : Bool)
    (ht : delta C.theta B≤0) (hTD : delta C.theta T=0) (hd : de=true→delta C.theta D≤0)
    (he : eh=true→delta C.theta E≤0) :
    selectedNegative C de eh positivePart=0 ∧
    selectedNegative C de eh negativePart=negativeTotal C de eh ∧
    0≤negativeTotal C de eh := by
  have hT0 : positivePart (delta C.theta B)=0 := max_eq_right ht
  have hTN : negativePart (delta C.theta B)= -delta C.theta B := max_eq_left (neg_nonneg.mpr ht)
  have hDE0 : selected de (positivePart (delta C.theta D))=0 := by
    cases hd' : de
    · simp [selected]
    · simp [selected,positivePart,max_eq_right (hd hd')]
  have hEH0 : selected eh (positivePart (delta C.theta E))=0 := by
    cases he' : eh
    · simp [selected]
    · simp [selected,positivePart,max_eq_right (he he')]
  have hDEN : selected de (negativePart (delta C.theta D))=magnitude C D de := by
    cases hd' : de
    · simp [selected,magnitude,NegativeELowA.magnitude]
    · simp [selected,magnitude,NegativeELowA.magnitude,negativePart,max_eq_left (neg_nonneg.mpr (hd hd'))]
  have hEHN : selected eh (negativePart (delta C.theta E))=magnitude C E eh := by
    cases he' : eh
    · simp [selected,magnitude,NegativeELowA.magnitude]
    · simp [selected,magnitude,NegativeELowA.magnitude,negativePart,max_eq_left (neg_nonneg.mpr (he he'))]
  have hneg0 : 0≤ selectedNegative C de eh negativePart := by
    have hB := negativePart_nonneg (delta C.theta B)
    have hT := negativePart_nonneg (delta C.theta T)
    have hD := negativePart_nonneg (delta C.theta D)
    have hE := negativePart_nonneg (delta C.theta E)
    cases de <;> cases eh <;> simp [selectedNegative,selected]
    all_goals positivity
  have hpos : selectedNegative C de eh positivePart=0 := by
    simp [selectedNegative,hT0,hTD,positivePart_zero,hDE0,hEH0]
  have hneg : selectedNegative C de eh negativePart=negativeTotal C de eh := by
    rw [selectedNegative,hTN,hTD,negativePart_zero,hDEN,hEHN]
    dsimp [negativeTotal]
    ring
  exact ⟨hpos,hneg,by rw [← hneg]; exact hneg0⟩

theorem budgets {C : SignedCycle} (hg ga ab de eh : Bool)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (ht : delta C.theta B≤0) (hTD : delta C.theta T=0) (hd : de=true→delta C.theta D≤0)
    (he : eh=true→delta C.theta E≤0) :
    aTotal C ga ab∈Icc 0 frameCap ∧ negativeTotal C de eh∈Icc 0 frameCap ∧
    (∑i,(blocks C hg ga ab de eh i).P)≤frameCap-aTotal C ga ab ∧
    (∑i,(blocks C hg ga ab de eh i).N)≤frameCap-negativeTotal C de eh ∧
    (∑i,(blocks C hg ga ab de eh i).N)-(∑i,(blocks C hg ga ab de eh i).P)=
      aTotal C ga ab-negativeTotal C de eh := by
  have hp := sum_parts C hg ga ab de eh positivePart positivePart_zero
  have hn := sum_parts C hg ga ab de eh negativePart negativePart_zero
  have hparts := selectedNegative_parts de eh ht hTD hd he
  have haSigned := selectedA_signed C ga ab
  have haN := selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab de eh i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab de eh i).N_nonneg)
  have hP : (∑i,(blocks C hg ga ab de eh i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart := by
    simpa only [Block.P,hparts.1,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab de eh i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-negativeTotal C de eh := by
    simpa only [Block.N,hparts.2.1,negativeVariation] using hn
  have hvariation := variations_equal C.theta
  exact ⟨⟨ha,by linarith⟩,⟨hparts.2.2,by linarith⟩,
    by linarith,by linarith,by linarith⟩

theorem block_coefficients (C : SignedCycle) (hg ga ab de eh : Bool) (i : Fin 4) :
    (blocks C hg ga ab de eh i).p=p i ∧ (blocks C hg ga ab de eh i).q=q i := by
  fin_cases i <;> norm_num [blocks,Block.p,Block.q,p,q,NegativeELargeA.k,NegativeELargeA.l,c]

theorem actual_blocks_lower {Q : ℝ} {C : SignedCycle} (hg ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hq : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (ht : delta C.theta B≤0) (hTD : delta C.theta T=0) (hd : de=true→delta C.theta D≤0)
    (he : eh=true→delta C.theta E≤0) (i : Fin 4) :
    block i (blocks C hg ga ab de eh i).P (blocks C hg ga ab de eh i).N≤
      actualBlocks C hg ga ab de eh i := by
  have hb := budgets hg ga ab de eh hvar ha ht hTD hd he
  have hbudget (i : Fin 4) : (blocks C hg ga ab de eh i).P≤frameCap ∧
      (blocks C hg ga ab de eh i).N≤frameCap := by
    have hP := Finset.single_le_sum (s:=Finset.univ)
      (fun j _ => (blocks C hg ga ab de eh j).P_nonneg) (Finset.mem_univ i)
    have hN := Finset.single_le_sum (s:=Finset.univ)
      (fun j _ => (blocks C hg ga ab de eh j).N_nonneg) (Finset.mem_univ i)
    exact ⟨by linarith [hb.2.2.1],by linarith [hb.2.1.1,hb.2.2.2.1]⟩
  have hordinary (i : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      OrdinaryAngleConcavity.mixedBlock R (p i) (q i)
        (blocks C hg ga ab de eh i).P (blocks C hg ga ab de eh i).N≤
        PositiveTD.actualPairIncrement (blocks C hg ga ab de eh i) P := by
    have hcoef := block_coefficients C hg ga ab de eh i
    have hminor := PositiveTD.actual_block_minorant hy hP hq
      (show 0≤(blocks C hg ga ab de eh i).p by rw [hcoef.1]; exact (coefficients i).1.le)
      (hbudget i).1 (hbudget i).2
    simpa only [hcoef.1,hcoef.2] using hminor
  fin_cases i
  · simpa [block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 0 hHy (hc H)
  · simpa [block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 1
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G)
  · simpa [block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B)
  · cases hde : de
    · have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
      have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect) (k:=NegativeELargeA.k) (c:=c)
        (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
        (by simpa using hc D) hq (by norm_num [NegativeELargeA.k]) (by norm_num [NegativeELargeA.k,c])
        (original_error_bound hvar hn D)
      simpa [block,PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,p,q,aD,erase] using hh
    · simp [block,PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,p,q,erase]

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.LargeE
end
end
end

section
/-!
## Large nonnegative A and negative E at the BT3 alignment

The BT3 state gives the flat-core linear gain (`t_gain_lower`), and its short magnitude follows
from the two T projections. The DE and EH gains are the secant and short tangent gains, and the
scalar bound of the fixed family uses their combined magnitude with the negative T magnitude
(`actual_false`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.LargeE
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks PairedE NegativeELargeA

theorem t_gain_lower {C : SignedCycle} (hflat : (C.point T).a=7/12)
    (hy : (C.point T).y≤39/250) (hs : -delta C.theta B∈Icc 0 Paired.M) :
    M*(-delta C.theta B)≤tGain C := by
  have hg := Paired.genuine_linear hflat hy hs
  simp only [neg_neg] at hg
  have hm := mul_le_mul_of_nonneg_left hg (show 0≤c by norm_num [c])
  dsimp [tGain,M,c]
  norm_num [c] at hm
  nlinarith [hs.1]

theorem negative_magnitudes {C : SignedCycle} (de eh : Bool)
    (ht : delta C.theta B≤0) (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 u) :
    0≤ magnitude C D de ∧ magnitude C E eh∈Icc 0 u ∧ 0≤-delta C.theta B := by
  have hD : 0≤ magnitude C D de := by
    cases hd : de
    · simp [magnitude,NegativeELowA.magnitude,selected]
    · simpa [magnitude,NegativeELowA.magnitude,selected] using neg_nonneg.mpr (hde hd)
  have hE : magnitude C E eh∈Icc 0 u := by
    cases he : eh
    · norm_num [magnitude,NegativeELowA.magnitude,selected,u]
    · simpa [magnitude,NegativeELowA.magnitude,selected] using heh he
  exact ⟨hD,hE,neg_nonneg.mpr ht⟩

/-- Simultaneous negative E primaries are allowed. All scalar quantities come from the weak
separating inequalities of the cycle. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hq : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : aTotal C ga ab∈Icc L frameCap) (ht : delta C.theta B≤0)
    (htd : delta C.theta T=0) (hTflat : (C.point T).a=7/12) (hTy : (C.point T).y≤39/250)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 u ∧ -(C.point E).y≤39/250) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have ha0 : 0≤aTotal C ga ab := by dsimp [L] at ha; linarith [ha.1]
  have hEsgn : eh=true→delta C.theta E≤0 := fun he => by linarith [(heh he).1.1]
  have hb := budgets hg ga ab de eh hvar ha0 ht htd hde hEsgn
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos (i : Vertex) := NegativePrimary.cos_pos (hsmall i)
  have hTpos := hcos T
  have hDpos := hcos D
  have hweights (i : Vertex) : 0≤weights C de i := by
    cases de <;> fin_cases i <;> simp [weights,NegativeELargeA.k,NegativeELargeA.l,c]
    all_goals positivity
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hupper : stress C hg ga ab de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have h := hf i
    change 0≤C.edge i (owners hg ga ab de eh i)-edgeWidth (delta C.theta i) at h
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hblocks := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower hg ga ab de eh hs hc hq hHy hGy hBy hDy hvar ha0 ht htd hde hEsgn i)
  have hA := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hb.1
  have hAmul := mul_le_mul_of_nonneg_left hA (show 0≤NegativeELargeA.l by norm_num [NegativeELargeA.l])
  have hDEgain := NegativeELargeA.Source.de_gain_lower de (hs D) (hc D) hq hDy (hsmall D) hde
  have hEHgain := NegativeELargeA.Source.eh_gain_lower eh hflat heh
  have hBt : -delta C.theta B∈Icc 0 frameCap := ⟨neg_nonneg.mpr ht,(neg_le_abs _).trans (hsmall B)⟩
  have hshort := Paired.aligned_short hs hcoreT hc hq hDy hBt hBT hTD (by simp) htd
  have hTgain := t_gain_lower hTflat hTy ⟨hBt.1,hshort.le⟩
  have hmags := negative_magnitudes de eh ht hde (fun he => (heh he).1)
  have hcombined := combined_gain_lower (s:=magnitude C E eh)
    (r:=magnitude C D de-delta C.theta B) hmags.2.1 (by linarith [hmags.1,hmags.2.2])
    (by dsimp [negativeTotal] at hb; linarith [hb.2.1.2])
  have hsumangle : magnitude C E eh+(magnitude C D de-delta C.theta B)=negativeTotal C de eh := by
    dsimp [negativeTotal]
    ring
  rw [hsumangle] at hcombined
  have hgain : min (M*negativeTotal C de eh) (jointGain (negativeTotal C de eh))≤
      deGain C de+ehGain C eh+tGain C := by linarith
  have hscalar := sum_scalar_positive
    (fun i => (blocks C hg ga ab de eh i).P) (fun i => (blocks C hg ga ab de eh i).N)
    ha hb.2.1 (fun i => (blocks C hg ga ab de eh i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh i).N_nonneg)
    hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hgain
  rw [decomposition C hg ga ab de eh hflat htd (hcos D).ne'] at hupper
  change NegativeELargeA.l*TwoPositive.ASupport.charge (aTotal C ga ab)≤_ at hAmul
  linarith


end SquaresInCircles.Eight.GlobalGA.NonpositiveT.LargeE
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.LowE
open Candidate Secondary NegativePrimary PairedE
abbrev k := NegativeELowA.k
abbrev l := NegativeELowA.l
abbrev c := NegativeELowA.c
abbrev L := NegativeELowA.L
abbrev magnitude := NegativeELowA.magnitude
abbrev deGain := NegativeELowA.deGain
abbrev ehGain := NegativeELowA.ehGain
abbrev tGain := LowA.tGain

def owners (hg ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    3,2,if de then 3 else 2,if eh then 1 else 0]
def weights (C : SignedCycle) (de eh : Bool) : Vertex→ℝ :=
  ![k,l,l,c,c,if de then 1/Real.cos (delta C.theta D) else 1,
    if eh then 1/Real.cos (delta C.theta E) else 1]
def stress (C : SignedCycle) (hg ga ab de eh : Bool) : ℝ :=
  ∑i,weights C de eh i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))
def reference (C : SignedCycle) (hg ga ab de eh : Bool) : ℝ :=
  PositiveATD0.lowBaseline+NegativeELowA.hIncrement C hg eh+
    PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
      (erase ga (delta C.theta G)) (C.point G).reflect+
    PositiveATD0.pairIncrement l c (erase ab (delta C.theta A))
      0 (C.point B).reflect+NegativeELowA.dIncrement C true de

private theorem r92lw_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92lw_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92lw_e0 (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j :=
  r92lw_edge_zero C 0 j (by decide)
private theorem r92lw_e1 (C : SignedCycle) (j : Fin 4) :
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j :=
  r92lw_edge_quarter C 1 j (by decide)
private theorem r92lw_e2 (C : SignedCycle) (j : Fin 4) :
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j :=
  r92lw_edge_zero C 2 j (by decide)
private theorem r92lw_e3 (C : SignedCycle) (j : Fin 4) :
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j :=
  r92lw_edge_quarter C 3 j (by decide)
private theorem r92lw_e4 (C : SignedCycle) (j : Fin 4) :
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j :=
  r92lw_edge_zero C 4 j (by decide)
private theorem r92lw_e5 (C : SignedCycle) (j : Fin 4) :
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j :=
  r92lw_edge_quarter C 5 j (by decide)
private theorem r92lw_e6 (C : SignedCycle) (j : Fin 4) :
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j :=
  r92lw_edge_quarter C 6 j (by decide)

private theorem r92lw_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

private def r92lw_u (α u : ℝ) (P : SignedPoint) : ℝ :=
  α*(edgeWidth u-1)-α*Real.sin u*P.a-α*Real.cos u*P.y
private def r92lw_v (β v : ℝ) (P : SignedPoint) : ℝ :=
  β*(edgeWidth v-1)-β*Real.cos v*P.a-β*Real.sin v*P.y

private theorem r92lw_pinc (p q a b : ℝ) (P : SignedPoint) :
    PositiveATD0.pairIncrement p q a b P=
      r92lw_u p a P+r92lw_v q b P+fullSupport q p+PositiveATD0.charge*a+PositiveATD0.charge*b := by
  simp only [PositiveATD0.pairIncrement,pairF,pairG,r92lw_u,r92lw_v]
  ring

theorem decomposition (C : SignedCycle) (hg ga ab de eh : Bool)
    (hflat : (C.point E).a=7/12) (hTD : delta C.theta T=0)
    (hD : Real.cos (delta C.theta D)≠0) (hE : Real.cos (delta C.theta E)≠0) :
    stress C hg ga ab de eh=reference C hg ga ab de eh+
      L*(PairedE.LowA.aTotal C ga ab-magnitude C D de-magnitude C E eh+delta C.theta B)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      deGain C de+ehGain C eh+tGain C := by
  have hsum := r92lw_delta_sum C
  have hT4 : delta C.theta 4=0 := hTD
  have hE6 : (C.point 6).a=7/12 := hflat
  have hinvD : Real.cos (delta C.theta 5)*(Real.cos (delta C.theta 5))⁻¹=1 :=
    mul_inv_cancel₀ hD
  have hinvE : Real.cos (delta C.theta 6)*(Real.cos (delta C.theta 6))⁻¹=1 :=
    mul_inv_cancel₀ hE
  have h1 : stress C hg ga ab de eh=
      k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))+
      l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      c*(edgeWidth (delta C.theta B)-C.edge B 3)+c*(edgeWidth (delta C.theta T)-C.edge T 2)+
      (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      (if eh then 1/Real.cos (delta C.theta E) else 1)*
        (edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [stress,Fin.sum_univ_seven,weights,owners,Matrix.cons_val,H,G,A,B,T,D,E]
  have hH : k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))=
      r92lw_u k (erase (!hg) (delta C.theta H)) (C.point H)+
      r92lw_u k (erase hg (delta C.theta H)) (C.point G).reflect+k := by
    cases hg <;>
      simp only [r92lw_u,r92lw_e0,H,G,zeroProjection,erase,SignedPoint.reflect,Bool.not_true,
        Bool.not_false,Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hG : l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      r92lw_v l (erase ga (delta C.theta G)) (C.point G).reflect+
      l*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*
        Real.sin (delta C.theta G)+(C.point A).y*(1-Real.cos (delta C.theta G))) else 0)+
      l+l*(C.point A).y := by
    cases ga <;>
      simp only [r92lw_v,r92lw_e1,G,A,quarterProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hA : l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      r92lw_u l (erase ab (delta C.theta A)) (C.point B).reflect+
      l*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*
        Real.sin (delta C.theta A)+(C.point A).y*(Real.cos (delta C.theta A)-1)) else 0)+
      l-l*(C.point A).y := by
    cases ab <;>
      simp only [r92lw_u,r92lw_e2,A,B,zeroProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hB : c*(edgeWidth (delta C.theta B)-C.edge B 3)=
      r92lw_v c 0 (C.point B).reflect+tGain C+c+c*(C.point T).y := by
    simp only [r92lw_v,r92lw_e3,B,T,quarterProjection,tGain,LowA.tGain,PairedA.work,
      SignedPoint.reflect,Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    ring
  have hT : c*(edgeWidth (delta C.theta T)-C.edge T 2)=
      c*(1-(C.point T).y+(C.point D).y) := by
    simp only [r92lw_e4,T,D,zeroProjection,hT4,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
      edgeWidth_zero]
    ring
  have hDv : (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      NegativeELowA.dIncrement C true de+deGain C de-L*magnitude C D de+(C.point E).y-c-
        c*(C.point D).y-L*delta C.theta D+(1+c)*(1-Secondary.diagonal) := by
    cases de
    · simp only [r92lw_e5,D,E,quarterProjection,NegativeELowA.dIncrement,deGain,
        NegativeELowA.deGain,magnitude,NegativeELowA.magnitude,selected,erase_true,
        PositiveATD0.Source.dIncrement,PositiveATD0.dF,PositiveATD0.dG,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero]
      ring
    · simp only [r92lw_e5,D,E,quarterProjection,NegativeELowA.dIncrement,deGain,
        NegativeELowA.deGain,magnitude,NegativeELowA.magnitude,selected,erase_true,
        NegativeELowA.dSecantIncrement,NegativeELowA.rawE,SignedPoint.reflect,hE6,
        ↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      linear_combination (C.point 6).y*hinvD
  have hEv : (if eh then 1/Real.cos (delta C.theta E) else 1)*
        (edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      NegativeELowA.hIncrement C hg eh-r92lw_u k (erase (!hg) (delta C.theta H)) (C.point H)-
        fullSupport 1 k-L*erase (!hg) (delta C.theta H)-L*delta C.theta E+ehGain C eh-
        L*magnitude C E eh+1-(C.point E).y := by
    cases eh
    · simp only [r92lw_e6,E,H,quarterProjection,NegativeELowA.hIncrement,ehGain,
        NegativeELowA.ehGain,magnitude,NegativeELowA.magnitude,selected,r92lw_pinc,r92lw_v,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val]
      ring
    · simp only [r92lw_e6,E,H,quarterProjection,NegativeELowA.hIncrement,ehGain,
        NegativeELowA.ehGain,magnitude,NegativeELowA.magnitude,selected,
        NegativeELowA.hSecantIncrement,NegativeELowA.rawE,r92lw_u,hE6,↓reduceIte,Matrix.cons_val]
      linear_combination -(C.point 6).y*hinvE
  have hHs : erase (!hg) (delta C.theta H)+erase hg (delta C.theta H)=delta C.theta H := by
    cases hg <;> simp
  have hGs : erase ga (delta C.theta G)+selected ga (delta C.theta G)=delta C.theta G := by
    cases ga <;> simp [selected]
  have hAs : erase ab (delta C.theta A)+selected ab (delta C.theta A)=delta C.theta A := by
    cases ab <;> simp [selected]
  rw [h1,hH,hG,hA,hB,hT,hDv,hEv]
  simp only [reference,PositiveATD0.lowBaseline,r92lw_pinc,PairedE.LowA.aTotal,total,
    primaryGain]
  simp only [H,G,A,B,T,D,E] at hHs hGs hAs ⊢
  linear_combination (-L)*hHs+(-L)*hGs+(-L)*hAs+(-L)*hsum+L*hT4

theorem reference_lower {q : ℝ} {C : SignedCycle} (hg ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) :
    PositiveATD0.lowBaseline≤reference C hg ga ab de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hgb := erased_pair_budgets (i := H) (j := G) hvar hn (by norm_num [H,G]) hg ga
  have hbb := erased_pair_budgets (i := A) (j := B) hvar hn (by norm_num [A,B]) ab true
  simp only [erase_true] at hbb
  have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P := (C.point G).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (by simpa using hc G) hq hgb.1 hgb.2
  have hB := PositiveATD0.actual_fixed_pair_nonneg 2 (P := (C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hH := NegativeELowA.hIncrement_nonneg hg eh (hc H) hq hHy hvar heh
  have hD := NegativeELowA.dIncrement_nonneg true de (hs D) (hc D) hq hDy hvar hde
  simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,Matrix.cons_val] at hG hB
  dsimp [reference,k,l,c,NegativeELowA.k,NegativeELowA.l,NegativeELowA.c]
  linarith

theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : PairedE.LowA.aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (hb : delta C.theta B≤0) (htd : delta C.theta T=0)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos (i : Vertex) := NegativePrimary.cos_pos (hsmall i)
  have hTpos := hcos T
  have hDpos := hcos D
  have hEpos := hcos E
  have hweights (i : Vertex) : 0≤weights C de eh i := by
    cases de <;> cases eh <;> fin_cases i <;>
      simp [weights,k,l,c,NegativeELowA.k,NegativeELowA.l,NegativeELowA.c,PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowC]
    all_goals positivity
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hu : stress C hg ga ab de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hh := hf i
    change 0≤C.edge i (owners hg ga ab de eh i)-edgeWidth (delta C.theta i) at hh
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hreference := reference_lower hg ga ab de eh hs hc hq hHy hGy hBy hDy hvar hde heh
  have hAmem : PairedE.LowA.aTotal C ga ab∈Icc 0 frameCap :=
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hA := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hAmem
  have hAweighted := mul_le_mul_of_nonneg_left hA (show 0≤l by norm_num [l,PositiveATD0.lowL])
  have hscalar := PositiveATD0.low_scalar_positive ha
  have hE := NegativeELowA.e_gain_lower de eh hsmall hde heh
  have hT := LowA.t_gain_lower (hs T) hcoreT hb (hsmall B)
  rw [decomposition C hg ga ab de eh hflat htd (hcos D).ne' (hcos E).ne'] at hu
  change l*TwoPositive.ASupport.charge (PairedE.LowA.aTotal C ga ab)≤_ at hAweighted
  dsimp only [L,c,l,NegativeELowA.L,NegativeELowA.c,NegativeELowA.l,magnitude,deGain,ehGain,
    tGain,PositiveATD0.charge,PositiveATD0.lowL] at hu hE hT hscalar hAweighted
  linarith


end SquaresInCircles.Eight.GlobalGA.NonpositiveT.LowE
end
end
end
