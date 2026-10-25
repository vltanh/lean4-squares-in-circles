module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongLowStress
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongScalar
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Source

/-!
# Eight squares: original negative-A / positive-BT3 exclusion when e≥s

All twelve endpoints,
their concavity, both signed budgets, and the original A gain are
discharged internally. The actual T point has no tangent-sign or
radial-kind restriction, and TD0 retains its arbitrary original error.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

namespace Source

theorem large_actual_false {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (19/50:ℝ)) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hlarge : 1/6≤delta C.theta B+eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have hb0 := budgets hg atG de eh 1 1 1 hvar hs.1 ha hz he
  obtain ⟨r,x,y,hd,hZ,hE⟩ := NonnegativeTotals.Explicit.coordinates hz hb0.e_domain.1
    ⟨hlarge,hb0.total_upper⟩
  let k := NonnegativeTotals.Explicit.k r x y
  let l := NonnegativeTotals.Explicit.l r x y
  let m := NonnegativeTotals.Explicit.c r x y
  have hsf : s∈Icc 0 (min (NonnegativeTotals.Explicit.e r x y) (19/50)) :=
    ⟨hs.1,le_min (by rwa [hE]) hs.2⟩
  have hz' : delta C.theta B∈Icc 0 (NonnegativeTotals.Explicit.theta r x y) := ⟨hz,by rw [hZ]⟩
  have hc := PositiveBT3.Balanced.pair_domain r hd hz'
  have hbase := NonnegativeTotals.Explicit.base_bounds r hd
  have hb := budgets hg atG de eh k l m hvar hs.1 ha hz he
  have hsum := full_stress_lower atG de eh hsorted hcontained hq hHy hGy hBy hDy
    hvar hs.1 ha hz he hgain hhg
    (show k≤1 by dsimp [k]; linarith [hbase.k_upper]) hbase.k_le_l
    hbase.l_positive.le hbase.c_positive.le (fun i => (hc i).1)
  have haux : ∀ {p q : ℝ},0<p → 2*q≤3*p → q≤2*p := fun h1 h2 => by linarith
  obtain ⟨i,j,hendpoint⟩ := ordinary_concentration R
    (PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)))
    (PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)))
    (fun i => (blocks C hg atG de eh k l m i).P)
    (fun i => (blocks C hg atG de eh k l m i).N)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hc i).1) (fun i => (hc i).2.1)
    (fun i => haux (hc i).1 (hc i).2.2)
    (fun i => (blocks C hg atG de eh k l m i).P_nonneg)
    (fun i => (blocks C hg atG de eh k l m i).N_nonneg)
    hb.residual_domain hb.positive_bound hb.balance
  change PositiveBT3.endpoint k l m (PositiveBT3.tilted m (delta C.theta B))
    (effective C de eh s) i j≤_ at hendpoint
  have hpositive := large_concentration_positive r hd hsf i j
  rw [hZ,hE] at hpositive
  have hupper := stress_nonpositive atG de eh
    (show 0≤k by dsimp [k]; linarith [hbase.k_lower]) hbase.l_positive.le
    hbase.c_positive hb.bt_domain hHG hGA hAB hBT hTD hDE hEH
  dsimp [concentrationScalar,effective] at hpositive hendpoint
  linarith

theorem low_actual_false {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hsmall : delta C.theta B+eTotal C de eh≤1/6)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  let t := effective C de eh s
  let k := PositiveBT3.lowK t
  let m := PositiveBT3.lowM t
  have ht : t∈Icc 0 (1/6:ℝ) := by dsimp [t,effective]; constructor <;> linarith
  have hb := budgets hg atG de eh k 1 m hvar hs ha hz he
  have henv := PositiveBT3.LowEnvelope.lower ht
    (fun i => (blocks C hg atG de eh k 1 m i).P)
    (fun i => (blocks C hg atG de eh k 1 m i).N)
    (fun i => (blocks C hg atG de eh k 1 m i).P_nonneg)
    (fun i => (blocks C hg atG de eh k 1 m i).N_nonneg)
    hb.balance hb.positive_bound
  have hminor := low_stress_lower atG de eh hsorted hcontained hq hHy hGy hBy hDy
    hvar hs ha hz he hgain hhg ht
  have hpositive := low_scalar_positive hz hs he hsmall
  have hr := PositiveBT3.Analytic.low_ranges ht
  have hupper := stress_nonpositive atG de eh
    (show 0≤k by dsimp [k,t]; linarith [hr.1.1]) (by norm_num : (0:ℝ)≤1)
    (show 0< m by dsimp [m,t]; linarith [hr.2.1]) hb.bt_domain
    hHG hGA hAB hBT hTD hDE hEH
  change 0<PositiveBT3.Analytic.lowBaseline k m (delta C.theta B)+gain s+
    TwoPositive.ASupport.charge (eTotal C de eh)+V R k 1 t at hpositive
  linarith

end Source

theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : Source.aError C atG= -s) (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (he : s≤PairedE.cycleTotal C de eh) (hz : 0≤delta C.theta B)
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have he0 : 0≤PairedE.cycleTotal C de eh := hs.1.trans he
  by_cases hsecondary : atG=true ∧ C.Feasible G 2
  · rcases hsecondary with ⟨rfl,hGA2⟩
    have hHG' : C.Feasible H 0∨C.Feasible H 2 := by
      rcases hhg with rfl|rfl
      · exact Or.inl hHG
      · exact Or.inr hHG
    exact PositiveBT3.Source.actual_false false false de eh hsorted hcontained hq
      hHy hGy hBy hDy hvar (by simp [PositiveBT3.Source.aTotal,PairedE.total,PairedE.selected])
      hz he0 hHG' hGA2 (by simpa using hAB) hBT hTD hDE hEH
  have hnot : atG=true → ¬C.Feasible G 2 := by
    intro hh hf
    exact hsecondary ⟨hh,hf⟩
  have hgain := Source.gain_lower atG hsorted hcontained hq hGy hBy hflat hAy hs ha hnot hGA hAB
  have hs' : s∈Icc 0 (19/50:ℝ) := by
    refine ⟨hs.1,?_⟩
    cases atG <;> simp only [NegativeAPositiveTD.Explicit.angleCut,ite_true,ite_false,
      Bool.false_eq_true] at hs <;> linarith [hs.2]
  by_cases hsmall : delta C.theta B+PairedE.cycleTotal C de eh≤1/6
  · exact Source.low_actual_false atG de eh hsorted hcontained hq hHy hGy hBy hDy
      hvar hs.1 ha hz he hsmall hgain hhg hHG hGA hAB hBT hTD hDE hEH
  · exact Source.large_actual_false atG de eh hsorted hcontained hq hHy hGy hBy hDy
      hvar hs' ha hz he (lt_of_not_ge hsmall).le hgain hhg hHG hGA hAB hBT hTD hDE hEH

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
