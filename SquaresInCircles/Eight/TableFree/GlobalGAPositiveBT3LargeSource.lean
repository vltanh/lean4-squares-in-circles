module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Stress

/-!
# Original BT3/TD0 exclusion for every large nonnegative A/E total

Uncompiled source assembly of Sections 4--8. The native family is
constructed at theta=a+u and the actual signed E total. Its coefficients,
all concentration alternatives, and all split endpoints are discharged
internally. TD0 keeps its arbitrary original error throughout.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open NonnegativeTotals

theorem large_actual_false {q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hu : 0≤delta C.theta B) (he : 0≤eTotal C de eh)
    (hlarge : 1/6≤total C ga ab de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible Candidate.D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hbud0 := budgets hg ga ab de eh 1 1 1 hvar ha hu he
  obtain ⟨r,x,y,hd,hTheta,hE⟩ := Explicit.coordinates
    (show 0≤aTotal C ga ab+delta C.theta B by linarith) he ⟨hlarge,hbud0.1.2⟩
  let k := Explicit.k r x y
  let l := Explicit.l r x y
  let m := Explicit.c r x y
  have hδ : Explicit.delta r x y=total C ga ab de eh := by
    simp [Explicit.delta,total,hTheta,hE]
  have huTheta : delta C.theta B∈Icc 0 (Explicit.theta r x y) :=
    ⟨hu,by rw [hTheta]; linarith⟩
  have haTheta : aTotal C ga ab∈Icc 0 (Explicit.theta r x y) :=
    ⟨ha,by rw [hTheta]; linarith⟩
  have huId : Explicit.theta r x y-aTotal C ga ab=delta C.theta B := by rw [hTheta]; ring
  have hbase := Explicit.base_bounds r hd
  have hcoef := Balanced.pair_domain r hd huTheta
  have hbud := budgets hg ga ab de eh k l m hvar ha hu he
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    full_blocks_lower ga ab de eh hc hq hHy hGy hBy hDy hvar ha hu he
      (show k≤1 by dsimp [k]; linarith [hbase.k_upper]) hbase.k_le_l
      (fun i => (hcoef i).1) i (hg:=hg))
  obtain ⟨i,j,hendpoint⟩ := ordinary_concentration R
    (pWeights k l m (tilted m (delta C.theta B)))
    (qWeights k l m (tilted m (delta C.theta B)))
    (fun i => (blocks C hg ga ab de eh k l m i).P)
    (fun i => (blocks C hg ga ab de eh k l m i).N)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hcoef i).1) (fun i => (hcoef i).2.1)
    (fun i => by
      have h1 : 0<pWeights k l m (tilted m (delta C.theta B)) i := (hcoef i).1
      have h3 : 2*qWeights k l m (tilted m (delta C.theta B)) i≤
          3*pWeights k l m (tilted m (delta C.theta B)) i := (hcoef i).2.2
      linarith)
    (fun i => (blocks C hg ga ab de eh k l m i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh k l m i).N_nonneg)
    hbud.1 hbud.2.2.2.2.1 hbud.2.2.2.2.2
  have henv := Balanced.endpoint_lower r hd huTheta i j
  rw [hδ] at henv
  change endpoint k l m (tilted m (delta C.theta B)) (total C ga ab de eh) i j≤_ at hendpoint
  have hsumenv : TwoPositive.balancedEnvelope k l m (total C ga ab de eh)≤
      ∑i,actualBlocks C hg ga ab de eh k l m i := henv.trans (hendpoint.trans hsum)
  have hpositive (i : Fin 3) := Analytic.large_scalar_positive r i hd haTheta
  have h0 := hpositive 0
  have h1 := hpositive 1
  have h2 := hpositive 2
  simp only [Analytic.largeScalar,Analytic.negative,NonnegativeTotals.Analytic.negative,
    Matrix.cons_val_zero,Matrix.cons_val_succ,hE,hTheta,add_sub_cancel_left] at h0 h1 h2
  have hmin : 0<Analytic.fullBaseline k l m (delta C.theta B)+
      l*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
      TwoPositive.balancedEnvelope k l m (total C ga ab de eh) := by
    unfold TwoPositive.balancedEnvelope
    rw [add_min,add_min]
    exact lt_min h0 (lt_min h1 h2)
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hprimary := NonnegativeTotals.Source.primary_reserves ga ab de eh hs hc hq
    (original_error_bound hvar hn) hbase.l_positive.le hbud.2.1 hbud.2.2.2.1
  have hT := tReserve_nonnegative (hs T) (hc T) hq hbase.c_positive.le hbud.2.2.1
  have hupper := stress_nonpositive ga ab de eh
    (show 0≤k by dsimp [k]; linarith [hbase.k_lower]) hbase.l_positive.le
    hbase.c_positive hbud.2.2.1 hHG hGA hAB hBT hTD hDE hEH
  rw [decomposition C ga ab de eh hhg k l m] at hupper
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Source
