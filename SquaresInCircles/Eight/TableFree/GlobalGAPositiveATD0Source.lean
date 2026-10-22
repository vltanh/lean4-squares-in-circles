module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveATD0HighScalar

/-!
# The full positive-A/TD0 exclusion at the original radius

Uncompiled transcription of Sections 4--6 of the positive-A/TD0 hand
proof. Four ordinary blocks include both actual TD0 and DE2 errors.
The full-circle concentration and the pure-A polynomial endpoints close
the high range; the fixed charged stress closes the low range.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveATD0
namespace Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open ActualOrdinaryBlocks SignedStress
open TwoPositive.Source (aError aWork aReserve a_reserve_nonneg)

def actualFullBlocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg atG k l c 0) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg atG k l c 1) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg atG k l c 2) (C.point B).reflect,
    PositiveTD.actualPairIncrement (blocks C hg atG k l c 3) (C.point D).reflect]

theorem full_decomposition (C : SignedCycle) {hg : Fin 4} (atG : Bool)
    (hhg : hg=0 ∨ hg=2) (k l c : ℝ) :
    actualStress C hg atG k l c=
      fullBaseline k l c+l*TwoPositive.ASupport.charge (aError C atG)+
        (∑i,actualFullBlocks C hg atG k l c i)+aReserve C atG l := by
  cases atG <;> rcases hhg with rfl | rfl <;>
    simp [actualStress,demand,force,source,target,work,add,scale,
      previous,owners,weights,blocks,actualFullBlocks,PositiveTD.actualPairIncrement,
      pairF,pairG,fullBaseline,aReserve,aWork,aError,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,edgeWidth,pairWidth] <;> ring

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l c : ℝ}
    (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg atG k l c i).p=pWeights k l c i ∧
      (blocks C hg atG k l c i).q=qWeights k l c i := by
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,pWeights,qWeights,min_eq_left hk,max_eq_right hk,
      min_eq_left hl,max_eq_right hl,min_comm,max_comm]

theorem full_blocks_lower {q k l c : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG)
    (hk : k≤1) (hl : k≤l) (hp : ∀i,0<pWeights k l c i) (i : Fin 4) :
    mixedBlock R (pWeights k l c i) (qWeights k l c i)
      (blocks C hg atG k l c i).P (blocks C hg atG k l c i).N≤
        actualFullBlocks C hg atG k l c i := by
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (pWeights k l c j) (qWeights k l c j)
        (blocks C hg atG k l c j).P (blocks C hg atG k l c j).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG k l c j) P := by
    have hd := block_coefficients (C:=C) (hg:=hg) (c:=c) atG hk hl j
    have hpn : 0≤(blocks C hg atG k l c j).p := by rw [hd.1]; exact (hp j).le
    have hb := block_budgets hg atG k l c hvar ha j
    have hh := PositiveTD.actual_block_minorant hy hP hq hpn hb.1 hb.2
    rw [hd.1,hd.2] at hh
    exact hh
  fin_cases i
  · simpa [actualFullBlocks] using hordinary 0
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G)
  · simpa [actualFullBlocks] using hordinary 1 hHy (hc H)
  · simpa [actualFullBlocks] using hordinary 2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B)
  · simpa [actualFullBlocks] using hordinary 3
      (P:=(C.point D).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D)

/-- The high-angle branch has no scalar-envelope or support premises. -/
theorem high_actual_false {q : ℝ} {C : SignedCycle} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aError C atG∈Icc (1/6:ℝ) frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0 ∨ hg=2) ∧ C.Feasible H hg := by
    rcases hHG with hh | hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  let a := aError C atG
  let k := TwoPositive.highK a
  let l := TwoPositive.highL a
  let c := TwoPositive.highC a
  have ha0 : 0≤aError C atG := by linarith [ha.1]
  have hr := TwoPositive.high_ranges ha
  have hd := high_coefficient_ranges ha
  have hb := original_budgets hg atG k l c hvar ha0
  have hcoefK : k≤1 := by dsimp [k,a]; linarith [hr.2.1]
  have hcoefL : k≤l := by dsimp [k,l,a]; linarith [hr.2.1,hr.2.2.1]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    full_blocks_lower atG hc hq hHy hGy hBy hDy hvar ha0 hcoefK hcoefL hd.1 i (hg:=hg))
  obtain ⟨i,j,hij⟩ := ordinary_concentration R (pWeights k l c) (qWeights k l c)
    (fun i => (blocks C hg atG k l c i).P) (fun i => (blocks C hg atG k l c i).N)
    (Real.sqrt_nonneg qCap) radius_sq.le hd.1 hd.2.1
    (fun i => by linarith [hd.2.2.1 i])
    (fun i => (blocks C hg atG k l c i).P_nonneg)
    (fun i => (blocks C hg atG k l c i).N_nonneg)
    hb.1 hb.2.1 hb.2.2
  have hend := high_endpoint_lower ha i j
  change endpoint k l c a i j≤_ at hij
  have henv : envelope k l c a≤∑i,actualFullBlocks C hg atG k l c i := by
    exact hend.trans (hij.trans hsum)
  have hA := a_reserve_nonneg (l:=l) atG (hs A) (hc A) hq
    (show 0≤l by dsimp [l,a]; linarith [hr.2.2.1]) hb.1
  have hdecomp := full_decomposition C atG hhg k l c
  have hscalar := high_scalar_positive ha
  have hupper := stress_nonpos (k:=k) (l:=l) (c:=c) atG
    (by dsimp [k,a]; linarith [hr.1])
    (by dsimp [l,a]; linarith [hr.2.2.1])
    (by dsimp [c,a]; linarith [hr.2.2.2.2.1]) hHG hGA hAB hBT hTD hDE hEH
  change 0<fullBaseline k l c+l*TwoPositive.ASupport.charge a+envelope k l c a at hscalar
  linarith

/-- Both ranges of the actual nonnegative A-primary error are now
closed. The original TD0 error has either sign. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  by_cases hlow : aError C atG≤1/6
  · exact low_actual_false atG hs hc hq hHy hGy hBy hDy hvar ⟨ha,hlow⟩
      hHG hGA hAB hBT hTD hDE hEH
  · have hb := (original_budgets 0 atG lowK lowL lowC hvar ha).1
    exact high_actual_false atG hs hc hq hHy hGy hBy hDy hvar
      ⟨(lt_of_not_ge hlow).le,hb.2⟩ hHG hGA hAB hBT hTD hDE hEH

end Source

/-- The full positive-A/TD0 statement on the original boundary cycle. -/
theorem frame_one_positive_TD0_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (atG : Bool)
    (hGA : (forwardAxis (if atG then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if atG then 0 else 2)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H))
    (ha : 0≤TwoPositive.Source.aError (SignedCycle.atFrame F) atG) : False := by
  have hn := SignedCycle.atFrame_necessary F
  have hanchors := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hhigh : (if atG then (3:Fin 4) else 2)=2 ∨
      (if atG then (3:Fin 4) else 2)=3 := by cases atG <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    (if atG then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  let j := SignedCycle.retainedOwner F H
  have hHGactual := (SignedCycle.atFrame_feasible F H j).1
    (SignedCycle.retainedOwner_feasible F H)
  have hHG : (SignedCycle.atFrame F).Feasible H 0 ∨ (SignedCycle.atFrame F).Feasible H 2 := by
    rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) j hHGactual with hh | hh
    · exact Or.inl (by simpa [hh.1] using SignedCycle.retainedOwner_feasible F H)
    · exact Or.inr (by simpa [hh.1] using SignedCycle.retainedOwner_feasible F H)
  apply Source.actual_false atG hn.sorted hn.contained hq.2
    hanchors.2.1.le ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
    hanchors.2.2.2.1.le hanchors.2.2.2.2.2.le
    (FramePhysicalTransport.candidate_variations F hq).1.le ha hHG
  · exact (SignedCycle.atFrame_feasible F G _).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A _).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 0).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D 2).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E 0).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveATD0
