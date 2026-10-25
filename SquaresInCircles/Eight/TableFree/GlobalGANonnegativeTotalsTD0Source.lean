module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsTD0Data
public import SquaresInCircles.Eight.TableFree.GlobalGAPairedELowASource

/-!
# Arbitrary TD0 with nonnegative A and E totals

Uncompiled source closure of Section 8. The low total uses the already
proved fixed charged stress; the large total uses the complete A
endpoint on its original triangle or rectangle. In both cases the
TD0 error remains arbitrary and both primary pairs retain their
individual signs and all weak owner ties.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.TD0
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open NonnegativeTotals.Source (aTotal eTotal)

theorem high_actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q) (hq : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh) (hlarge : 1/6≤total C ga ab de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hbud0 := budgets hg ga ab de eh 1 1 1 hvar ha he
  obtain ⟨r,x,y,hd,hA,hE⟩ := Explicit.coordinates ha he ⟨hlarge,hbud0.1.2⟩
  let k := Explicit.k r x y
  let l := Explicit.l r x y
  let c := Explicit.c r x y
  have hδ : Explicit.delta r x y=total C ga ab de eh := by
    simp [Explicit.delta,total,hA,hE]
  have hbase := Explicit.base_bounds r hd
  have hcoef := coefficient_domain r hd
  have hbud := budgets hg ga ab de eh k l c hvar ha he
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    full_blocks_lower ga ab de eh hc hq hHy hGy hBy hDy hvar ha he
      (show k≤1 by dsimp [k]; linarith [hbase.k_upper]) hbase.k_le_l
      (fun i => (hcoef i).1) i (hg:=hg))
  obtain ⟨i,j,hendpoint⟩ := ordinary_concentration R (p k l c) (q k l c)
    (fun i => (blocks C hg ga ab de eh k l c i).P)
    (fun i => (blocks C hg ga ab de eh k l c i).N)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hcoef i).1) (fun i => (hcoef i).2.1)
    (fun i => by linarith [(hcoef i).2.2,(hcoef i).1])
    (fun i => (blocks C hg ga ab de eh k l c i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh k l c i).N_nonneg)
    hbud.1 hbud.2.2.2.1 hbud.2.2.2.2
  have henv := endpoint_lower r hd i j
  rw [hδ] at henv
  change PositiveATD0.endpoint k l c (total C ga ab de eh) i j≤_ at hendpoint
  have hsumenv : PositiveATD0.envelope k l c (total C ga ab de eh)≤
      ∑i,actualBlocks C hg ga ab de eh k l c i := henv.trans (hendpoint.trans hsum)
  have hpositive := A_endpoint_positive r hd
  rw [hA,hE,hδ] at hpositive
  change 0<PositiveATD0.fullBaseline k l c+l*TwoPositive.ASupport.charge (aTotal C ga ab)+
    TwoPositive.ASupport.charge (eTotal C de eh)+PositiveATD0.envelope k l c (total C ga ab de eh) at hpositive
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hres := NonnegativeTotals.Source.primary_reserves ga ab de eh hs hc hq
    (original_error_bound hvar hn) hbase.l_positive.le hbud.2.1 hbud.2.2.1
  have hu := stress_nonpositive ga ab de eh
    (show 0≤k by dsimp [k]; linarith [hbase.k_lower]) hbase.l_positive.le hbase.c_positive.le
    hHG hGA hAB hBT hTD hDE hEH
  rw [decomposition C ga ab de eh hhg k l c] at hu
  linarith

/-- The physical core avoidance of T is used only by the inherited
low charged-stress interface; no restriction is placed on its angle. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hq : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  by_cases hlow : total C ga ab de eh≤1/6
  · have haLow : aTotal C ga ab∈Icc 0 (1/6:ℝ) :=
      ⟨ha,by dsimp [total] at hlow; linarith⟩
    exact PairedE.LowA.actual_false ga ab false de eh hs hc hcoreT hq
      hHy hGy hBy hDy hvar hHG hGA hAB hBT hTD hDE hEH haLow
      (by intro h; cases h) he
  · exact high_actual_false ga ab de eh hs hc hq hHy hGy hBy hDy
      hvar ha he (lt_of_not_ge hlow).le hHG hGA hAB hBT hTD hDE hEH

end TD0

open Candidate Secondary

/-- Original-radius TD0 companion of `frame_TD2_false`. -/
theorem frame_TD0_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (ga ab de eh : Bool)
    (hGA : (forwardAxis (if ga then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if ab then 2 else 0)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis (if de then 3 else 2)).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis (if eh then 1 else 0)).Feasible (C.square E) (C.square H))
    (ha : 0≤Source.aTotal (SignedCycle.atFrame F) ga ab)
    (he : 0≤Source.eTotal (SignedCycle.atFrame F) de eh) : False := by
  have hn := SignedCycle.atFrame_necessary F
  have hanchors := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hhigh : (if ga then (3:Fin 4) else 2)=2∨(if ga then (3:Fin 4) else 2)=3 := by
    cases ga <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    (if ga then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  obtain ⟨j,hjdef⟩ : ∃ j,j=SignedCycle.retainedOwner F H := ⟨_,rfl⟩
  have hfe := SignedCycle.retainedOwner_feasible F H
  rw [←hjdef] at hfe
  have hj := (SignedCycle.atFrame_feasible F H j).1 hfe
  have hHG : (SignedCycle.atFrame F).Feasible H 0∨(SignedCycle.atFrame F).Feasible H 2 := by
    rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) j hj with hh|hh
    · exact Or.inl (hh.1 ▸ hfe)
    · exact Or.inr (hh.1 ▸ hfe)
  apply TD0.actual_false ga ab de eh hn.sorted hn.contained (hn.core T) hq.2
    hanchors.2.1.le ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
    hanchors.2.2.2.1.le hanchors.2.2.2.2.2.le
    (FramePhysicalTransport.candidate_variations F hq).1.le ha he hHG
  · exact (SignedCycle.atFrame_feasible F G _).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A _).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 0).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D _).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E _).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals
