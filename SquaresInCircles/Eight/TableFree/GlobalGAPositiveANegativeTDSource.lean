module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDConcentration

/-!
# The positive-A/nonpositive-TD2 contradiction on the original weak axes

Uncompiled transcription of the final application of the fixed high-A
stress. Its ordinary and sorted-D minorants concern the unchanged source
points, while the secant TD2 gain uses the actual signed T coordinate.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD
namespace Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks SignedStress
open TwoPositive.Source (aError aWork aReserve a_reserve_nonneg)

def actualHighBlocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg atG Fixed.k Fixed.l Fixed.c 0) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg atG Fixed.k Fixed.l Fixed.c 1) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg atG Fixed.k Fixed.l Fixed.c 2) (C.point B).reflect,
    PositiveTD.actualDIncrement Fixed.c (delta C.theta D) (C.point D).reflect]

private theorem r80_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r80_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r80_e0 (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j :=
  r80_edge_zero C 0 j (by decide)
private theorem r80_e1 (C : SignedCycle) (j : Fin 4) :
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j :=
  r80_edge_quarter C 1 j (by decide)
private theorem r80_e2 (C : SignedCycle) (j : Fin 4) :
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j :=
  r80_edge_zero C 2 j (by decide)
private theorem r80_e3 (C : SignedCycle) (j : Fin 4) :
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j :=
  r80_edge_quarter C 3 j (by decide)
private theorem r80_e4 (C : SignedCycle) (j : Fin 4) :
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j :=
  r80_edge_zero C 4 j (by decide)
private theorem r80_e5 (C : SignedCycle) (j : Fin 4) :
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j :=
  r80_edge_quarter C 5 j (by decide)
private theorem r80_e6 (C : SignedCycle) (j : Fin 4) :
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j :=
  r80_edge_quarter C 6 j (by decide)

/-- The identity needs the original sign of the T error: for `delta T>0` the secant
weight leaves `c*tan (delta T)` unaccounted. -/
theorem high_decomposition (C : SignedCycle) {hg : Fin 4} (atG : Bool)
    (hhg : hg=0 ∨ hg=2) (hcos : Real.cos (delta C.theta T)≠0)
    (hs : sError C∈Icc 0 frameCap) :
    actualStress C hg atG Fixed.k Fixed.l Fixed.c=
      Fixed.base+Fixed.l*TwoPositive.ASupport.charge (aError C atG)+
        (∑i,actualHighBlocks C hg atG i)+aReserve C atG Fixed.l+
        gain Fixed.c (sError C) (C.point T).a (-(C.point D).y) := by
  have ht := transport_trig hs
  simp only [sError,Real.cos_neg,Real.sin_neg] at ht
  have hw : edgeWidth (delta C.theta 4)=
      (1-Real.sin (delta C.theta 4)+Real.cos (delta C.theta 4))/2 := by
    rw [edgeWidth,pairWidth,abs_of_nonpos (by simpa [T] using ht.2.2.1),
      abs_of_pos (by simp only [T] at ht; linarith [ht.1])]
    ring
  have hinv : Real.cos (delta C.theta 4)*(Real.cos (delta C.theta 4))⁻¹=1 :=
    mul_inv_cancel₀ (by simpa [T] using hcos)
  have hclip : clippedSupport 1 Fixed.c=(1+Fixed.c)*Secondary.diagonal := by
    rw [clippedSupport,if_pos (by norm_num [Fixed.c]),diagonalSupport]
  rw [actualStress,demand,← sum_force_work]
  simp only [Fin.sum_univ_seven,Fin.sum_univ_four,weights,owners,Matrix.cons_val,r80_e0,r80_e1,
    r80_e2,r80_e3,r80_e4,r80_e5,r80_e6,zeroProjection,quarterProjection,actualHighBlocks,blocks,
    PositiveTD.actualPairIncrement,pairF,pairG,PositiveTD.actualDIncrement,hclip,Fixed.base,
    aReserve,aWork,aError,sError,gain,SignedPoint.reflect,Real.sin_neg,Real.cos_neg,
    Real.sin_zero,Real.cos_zero,edgeWidth_zero,H,G,A,B,T,D,E,hw]
  cases atG <;> rcases hhg with rfl|rfl <;>
    simp only [Bool.false_eq_true,↓reduceIte,Fin.isValue,show ((2:Fin 4)=0)=False by decide,
      Real.sin_zero,Real.cos_zero,edgeWidth_zero,Matrix.cons_val] <;>
    linear_combination Fixed.c*(1-(C.point 4).y+(C.point 5).y)*hinv

theorem high_block_coefficients {C : SignedCycle} {hg : Fin 4} (atG : Bool) (i : Fin 4) :
    (blocks C hg atG Fixed.k Fixed.l Fixed.c i).p=Fixed.p i ∧
      (blocks C hg atG Fixed.k Fixed.l Fixed.c i).q=Fixed.q i := by
  fin_cases i <;> norm_num [blocks,Block.p,Block.q,Fixed.p,Fixed.q,Fixed.k,Fixed.l,Fixed.c]

theorem high_blocks_lower {q : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG)
    (hz : delta C.theta T≤0) (i : Fin 4) :
    Fixed.block i (blocks C hg atG Fixed.k Fixed.l Fixed.c i).P
      (blocks C hg atG Fixed.k Fixed.l Fixed.c i).N≤actualHighBlocks C hg atG i := by
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (Fixed.p j) (Fixed.q j)
        (blocks C hg atG Fixed.k Fixed.l Fixed.c j).P
        (blocks C hg atG Fixed.k Fixed.l Fixed.c j).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG Fixed.k Fixed.l Fixed.c j) P := by
    have hd := high_block_coefficients (C:=C) (hg:=hg) atG j
    have hp : 0≤(blocks C hg atG Fixed.k Fixed.l Fixed.c j).p := by
      rw [hd.1]
      exact (Fixed.coefficients j).1.le
    have hb := block_budgets hg atG Fixed.k Fixed.l Fixed.c hvar ha hz j
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hb.1 hb.2
    rw [hd.1,hd.2] at hh
    exact hh
  fin_cases i
  · simpa [Fixed.block,PositiveTD.Hybrid.block,actualHighBlocks] using hordinary 0
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G)
  · simpa [Fixed.block,PositiveTD.Hybrid.block,actualHighBlocks] using hordinary 1 hHy (hc H)
  · simpa [Fixed.block,PositiveTD.Hybrid.block,actualHighBlocks] using hordinary 2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (k:=Fixed.k) (c:=Fixed.c)
      (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hq (by norm_num [Fixed.k]) (by norm_num [Fixed.k,Fixed.c])
      (original_error_bound hvar hn D)
    simpa [Fixed.block,PositiveTD.Hybrid.block,actualHighBlocks,blocks,Block.P,Block.N,
      Fixed.p,Fixed.q,Fixed.aD] using hh

theorem high_actual_false {q : ℝ} {C : SignedCycle} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aError C atG∈Icc Fixed.L frameCap) (hz : delta C.theta T≤0)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0 ∨ hg=2) ∧ C.Feasible H hg := by
    rcases hHG with hh | hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have ha0 : 0≤aError C atG := by simp only [Fixed.L] at ha; linarith [ha.1]
  have hb := original_budgets hg atG Fixed.k Fixed.l Fixed.c hvar ha0 hz
  have hcos : Real.cos (delta C.theta T)≠0 := by
    have hh := (transport_trig hb.2.1).1
    simpa [sError] using (ne_of_gt (show 0<Real.cos (sError C) by linarith))
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => high_blocks_lower atG hs hc hq hHy hGy hBy hDy hvar ha0 hz i (hg:=hg))
  have hscalar := Fixed.sum_scalar_positive
    (fun i => (blocks C hg atG Fixed.k Fixed.l Fixed.c i).P)
    (fun i => (blocks C hg atG Fixed.k Fixed.l Fixed.c i).N) ha hb.2.1
    (fun i => (blocks C hg atG Fixed.k Fixed.l Fixed.c i).P_nonneg)
    (fun i => (blocks C hg atG Fixed.k Fixed.l Fixed.c i).N_nonneg)
    hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
  have hA := a_reserve_nonneg (l:=Fixed.l) atG (hs A) (hc A) hq
    (by norm_num [Fixed.l]) hb.1
  have hgain := actual_gain_lower (hs T) hcoreT (hc T) (hs D) hDy (hc D) hq
    (show 0≤Fixed.c by norm_num [Fixed.c]) hb.2.1
  have hdecomp := high_decomposition C atG hhg hcos hb.2.1
  have hupper := stress_nonpos (k:=Fixed.k) (l:=Fixed.l) (c:=Fixed.c) atG
    (by norm_num [Fixed.k]) (by norm_num [Fixed.l]) (by norm_num [Fixed.c])
    hb.2.1 hHG hGA hAB hBT hTD hDE hEH
  simp only [Fixed.speed,Fixed.c,Fixed.l,Fixed.k] at *
  linarith

/-- Both A ranges are discharged without a scalar or ordering premise. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aError C atG) (hz : delta C.theta T≤0)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  by_cases hlow : aError C atG≤1/6
  · exact low_actual_false atG hs hc hcoreT hq hHy hGy hBy hDy hvar ⟨ha,hlow⟩ hz
      hHG hGA hAB hBT hTD hDE hEH
  · have hb := (original_budgets 0 atG Fixed.k Fixed.l Fixed.c hvar ha hz).1
    exact high_actual_false atG hs hc hcoreT hq hHy hGy hBy hDy hvar
      ⟨(lt_of_not_ge hlow).le,hb.2⟩ hz hHG hGA hAB hBT hTD hDE hEH

end Source
open Candidate

/-- Original boundary version: all signs, core bounds and angular
budgets are consequences of the given source frame. -/
theorem frame_one_positive_nonpositive_TD2_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (atG : Bool)
    (hGA : (forwardAxis (if atG then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if atG then 0 else 2)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 2).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H))
    (ha : 0≤TwoPositive.Source.aError (SignedCycle.atFrame F) atG)
    (hz : delta F.theta T≤0) : False := by
  have hn := SignedCycle.atFrame_necessary F
  have hanchors := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hhigh : (if atG then (3:Fin 4) else 2)=2 ∨
      (if atG then (3:Fin 4) else 2)=3 := by cases atG <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    (if atG then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  have hHGactual := (SignedCycle.atFrame_feasible F H _).1
    (SignedCycle.retainedOwner_feasible F H)
  have hHG : (SignedCycle.atFrame F).Feasible H 0 ∨ (SignedCycle.atFrame F).Feasible H 2 := by
    rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) _ hHGactual with hh | hh
    · exact Or.inl (hh.1 ▸ SignedCycle.retainedOwner_feasible F H)
    · exact Or.inr (hh.1 ▸ SignedCycle.retainedOwner_feasible F H)
  apply Source.actual_false atG hn.sorted hn.contained (hn.core T) hq.2
    hanchors.2.1.le ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
    hanchors.2.2.2.1.le hanchors.2.2.2.2.2.le
    (FramePhysicalTransport.candidate_variations F hq).1.le ha hz hHG
  · exact (SignedCycle.atFrame_feasible F G _).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A _).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 2).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D 2).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E 0).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD
