module

public import SquaresInCircles.Eight.TableFree.NegativeOrdinaryBlocks
public import SquaresInCircles.Eight.TableFree.NegativeTEntry

/-!
# Actual secondary-E exclusion in the negative-T regimes

Uncompiled source draft. The original T boundary gives either an already
available secondary physical owner, or the proved short flat-core branch.
The latter uses the exact original T work, original seven-angle budgets,
and the strict secant gain. Negative BT uses the actual TD alignment
provided by the preceding T-pair preprocessing.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeSecondaryEExclusion
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity
open SecondaryEStress PositivePrimaryBaselines PositiveStressCoefficients
open PositiveSecondaryEExclusion FlatTStress NegativeOrdinaryBlocks

theorem scalar_min_positive {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+
      min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d) := by
  have hs := PositiveScalarTransfer.seven_scalar_bounds hd
  have hV := hs.2.2.2.1
  have hL := hs.2.2.2.2.1
  rw [scalar_V_eq] at hV
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+
    V (Real.sqrt qCap) (lN d) k d at hV
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+
    lambdaN d*d at hL
  rcases le_total (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d) with h | h
  · rw [min_eq_left h]; exact hV
  · rw [min_eq_right h]; exact hL

theorem flat_negative_TD_false {C : SignedCycle} {q s : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hs : s∈Ioc 0 (3/10))
    (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 i)) : False := by
  let d : ℝ := delta C.theta G
  have hd : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hC.spread (next G) G)⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := coefficient_bounds hd
  have hc : 0<cN d := by linarith [hb.2.2.2.2.1,show k=(863/1000 : ℝ) from rfl]
  have hnec := negative_TD_necessary (k := k) (l := lN d) (c := cN d) (η := 19/50)
    hq hC hnormal hab (by norm_num [k])
    (by linarith [hb.2.2.1]) hc (by norm_num : (0:ℝ)≤19/50) hG hs' hT hflat hf
  have hinc := TD_increment_lower hab hvar hd (Ioc_subset_Icc_self hs) hT
  have hgain := PositiveSecantGain.negative_TD_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd (show s∈Ioc 0 frameCap from ⟨hs.1,hs'.2⟩)
  have hstrict := scalar_min_positive hd
  dsimp [d] at *
  linarith

theorem flat_negative_BT_false {C : SignedCycle} {q s : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hs : s∈Ioc 0 (9/100))
    (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 i)) : False := by
  let d : ℝ := delta C.theta G
  have hd : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hC.spread (next G) G)⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := coefficient_bounds hd
  have hc : 0<cN d := by linarith [hb.2.2.2.2.1,show k=(863/1000 : ℝ) from rfl]
  have hnec := negative_BT_necessary (k := k) (l := lN d) (c := cN d) (η := 19/50)
    hq hC hnormal hab (by norm_num [k])
    (by linarith [hb.2.2.1]) hc (by norm_num : (0:ℝ)≤19/50) hG hs' hB hflat hf
  have hinc := BT_increment_lower hab hvar hd (Ioc_subset_Icc_self hs) hB
  have hgain := ShortSecantGain.negative_BT_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd hs
  have hstrict := scalar_min_positive hd
  dsimp [d] at *
  linarith

theorem BT_contact (C : SignedCycle) (j : Fin 4) :
    C.Feasible B j ↔ quarterFeasible (C.point B) (C.point T) (delta C.theta B) j := by
  simp [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,next,B,T,
    quarterFeasible,sub_nonneg]

theorem TD_contact (C : SignedCycle) (j : Fin 4) :
    C.Feasible T j ↔ zeroFeasible (C.point T) (C.point D) (delta C.theta T) j := by
  simp [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,next,T,D,
    zeroFeasible,sub_nonneg]

theorem reselect_TD {C : SignedCycle} {ab td : Fin 4}
    (hf : ∀ i,C.Feasible i (owners ab 2 td i)) (hT : C.Feasible T 0) :
    ∀ i,C.Feasible i (owners ab 2 0 i) := by
  intro i
  by_cases hi : i=T
  · subst hi
    exact hT
  · have he : ∀ ab td : Fin 4,∀ j : Vertex,j≠T → owners ab 2 0 j=owners ab 2 td j := by
      decide
    rw [he ab td i hi]
    exact hf i

theorem reselect_BT {C : SignedCycle} {ab bt : Fin 4}
    (hf : ∀ i,C.Feasible i (owners ab bt 0 i)) (hB : C.Feasible B 2) :
    ∀ i,C.Feasible i (owners ab 2 0 i) := by
  intro i
  by_cases hi : i=B
  · subst hi
    exact hB
  · have he : ∀ ab bt : Fin 4,∀ j : Vertex,j≠B → owners ab 2 0 j=owners ab bt 0 j := by
      decide
    rw [he ab bt i hi]
    exact hf i

theorem negative_TD_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hT : delta C.theta T<0)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 i)) : False := by
  let s : ℝ := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hTs : delta C.theta T= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 2 :=
    (BT_contact C 2).1 (by simpa [owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hTs]
    exact (TD_contact C 2).1 (by simpa [owners,T] using hf T)
  have he := NegativeTEntry.negative_TD_entry (hC.sorted B) (hC.sorted T) (hC.sorted D)
    (hC.contained B) hTb (hC.contained D) (hC.core T) (hC.core D)
    hq hnormal.D_nonpos hs hBT hTD
  rcases he with hsecondary | ⟨hcore,hflat,hy,hyu,hshort⟩
  · have hsecondary' : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hTs] using hsecondary)
    exact secondary_T_false hq hC hnormal hvar hab hG (reselect_TD hf hsecondary')
  · exact flat_negative_TD_false hq hC hnormal hvar hab hG ⟨hs.1,hshort.le⟩ hTs hflat hf

theorem negative_BT_aligned_false {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 i)) : False := by
  by_cases hsecondary : C.Feasible B 2
  · exact secondary_T_false hq hC hnormal hvar hab hG (reselect_BT hf hsecondary)
  let s : ℝ := -delta C.theta B
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next B) B)⟩
  have hBs : delta C.theta B= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    rw [← hBs]
    exact (BT_contact C 3).1 (by simpa [owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) 0 0 := by
    rw [← halign]
    exact (TD_contact C 0).1 (by simpa [owners,T] using hf T)
  have hnot : ¬quarterFeasible (C.point B) (C.point T) (-s) 2 := by
    intro hh
    exact hsecondary ((BT_contact C 2).2 (by simpa [hBs] using hh))
  obtain ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hq hnormal.B_nonpos hnormal.D_nonpos hs hBT hTD hnot
  exact flat_negative_BT_false hq hC hnormal hvar hab hG ⟨hs.1,hshort.le⟩ hBs hflat hf

/-- The full original secondary-E owner union after T-pair preprocessing.
The only frame alignment used is the actual negative-BT endpoint clause. -/
theorem preprocessed_secondary_E_false {C : SignedCycle} {q : ℝ} {ab bt td : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hT : (bt=2 ∧ td=0) ∨ (bt=2 ∧ td=2) ∨
      (bt=3 ∧ td=0 ∧ (delta C.theta B<0 → delta C.theta T=0)))
    (hf : ∀ i,C.Feasible i (owners ab bt td i)) : False := by
  rcases hT with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl,halign⟩
  · exact secondary_T_false hq hC hnormal hvar hab hG hf
  · by_cases ht : 0≤delta C.theta T
    · exact positive_TD_false hq hC hnormal hvar hab hG ht hf
    · exact negative_TD_false hq hC hnormal hvar hab hG hTb (lt_of_not_ge ht) hf
  · by_cases hb : 0≤delta C.theta B
    · exact positive_BT_false hq hC hnormal hvar hab hG hb hf
    · have hb' : delta C.theta B<0 := lt_of_not_ge hb
      exact negative_BT_aligned_false hq hC hnormal hvar hab hG hTb hb' (halign hb') hf

end SquaresInCircles.Eight.TableFree.NegativeSecondaryEExclusion
