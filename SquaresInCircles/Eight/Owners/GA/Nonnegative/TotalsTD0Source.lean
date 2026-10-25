module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsTD0Data
public import SquaresInCircles.Eight.Owners.GA.Paired.ELowASource

/-!
# Eight squares: a TD0 error of either sign with nonnegative A and E totals

The low total uses the fixed charged stress; the large total uses the A endpoint on its triangle or
rectangle (`high_actual_false`). In both cases the TD0 error has either sign, and both primary pairs
keep the signs of their single errors and all weak owner ties (`actual_false`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.TD0
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

/-- The core avoidance of T is used only by the low charged stress; its angle is not
restricted. -/
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

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals
