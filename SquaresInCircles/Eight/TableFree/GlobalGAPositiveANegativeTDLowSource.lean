module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDGain

/-!
# The low-A secant-weight contradiction with nonpositive original TD2

Uncompiled transcription of Sections 2--3 of the positive-A/negative-TD2
hand proof. The original signed T coordinate is canceled by its secant
weight, and only the two indicated angles are removed from the analytic
circle blocks. Their original variation contributions remain explicit.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD
namespace Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks SignedStress
open TwoPositive.Source (aError aWork aReserve a_reserve_nonneg)

def sError (C : SignedCycle) : ℝ := -delta C.theta T

def owners (hg : Fin 4) (atG : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,2,2,2,0]

def weights (k l c s : ℝ) : Vertex→ℝ := ![k,l,l,c,c/Real.cos s,1,1]

def blocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![⟨k,l,if hg=0 then delta C.theta H else 0,if atG then 0 else delta C.theta G⟩,
    ⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨l,c,if atG then delta C.theta A else 0,delta C.theta B⟩,
    ⟨k,1,delta C.theta D,0⟩]

def actualStress (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : ℝ :=
  demand C (weights k l c (sError C))-
    ∑i,work (force C (owners hg atG) (weights k l c (sError C)) i) (C.point i)

def actualLowBlocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) : Fin 4→ℝ :=
  ![PositiveATD0.pairIncrement PositiveATD0.lowK PositiveATD0.lowL
      (blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 0).u
      (blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 0).v (C.point G).reflect,
    PositiveATD0.pairIncrement PositiveATD0.lowK 1
      (blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 1).u
      (blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 1).v (C.point H),
    PositiveATD0.pairIncrement PositiveATD0.lowL PositiveATD0.lowC
      (blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 2).u
      (blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 2).v (C.point B).reflect,
    PositiveATD0.Source.dIncrement 0 (delta C.theta D) (C.point D).reflect]

theorem weights_nonneg {k l c s : ℝ} (hk : 0≤k) (hl : 0≤l) (hc : 0≤c)
    (hs : s∈Icc 0 frameCap) (i : Vertex) : 0≤weights k l c s i := by
  have hcos := (transport_trig hs).1
  have hsec : 0≤c/Real.cos s := div_nonneg hc (by linarith)
  fin_cases i <;> simp [weights,hk,hl,hc,hsec]

theorem stress_nonpos {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0≤c) (hs : sError C∈Icc 0 frameCap)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    actualStress C hg atG k l c≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg atG i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonneg hk hl hc hs) hf)

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG k l c i).u+f (blocks C hg atG k l c i).v))=
      (∑j,f (delta C.theta j))-f (aError C atG)-f (delta C.theta T) := by
  cases atG <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

/-- Both original removed angles keep their signed variation charge. -/
theorem original_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG)
    (hz : delta C.theta T≤0) :
    aError C atG∈Icc 0 frameCap ∧ sError C∈Icc 0 frameCap ∧
      (∑i,(blocks C hg atG k l c i).P)≤frameCap-aError C atG ∧
      (∑i,(blocks C hg atG k l c i).N)≤frameCap-sError C ∧
      (∑i,(blocks C hg atG k l c i).N)=aError C atG-sError C+∑i,(blocks C hg atG k l c i).P := by
  have hp := sum_parts C hg atG k l c positivePart positivePart_zero
  have hn := sum_parts C hg atG k l c negativePart negativePart_zero
  have hpa : positivePart (aError C atG)=aError C atG := max_eq_left ha
  have hna : negativePart (aError C atG)=0 := max_eq_right (by linarith)
  have hpz : positivePart (delta C.theta T)=0 := max_eq_right hz
  have hnz : negativePart (delta C.theta T)=sError C := max_eq_left (neg_nonneg.mpr hz)
  have hp' : (∑i,(blocks C hg atG k l c i).P)=positiveVariation C.theta-aError C atG := by
    change (∑i,(positivePart (blocks C hg atG k l c i).u+
      positivePart (blocks C hg atG k l c i).v))=_
    simpa only [hpa,hpz,positiveVariation,sub_zero] using hp
  have hn' : (∑i,(blocks C hg atG k l c i).N)=negativeVariation C.theta-sError C := by
    change (∑i,(negativePart (blocks C hg atG k l c i).u+
      negativePart (blocks C hg atG k l c i).v))=_
    simpa only [hna,hnz,negativeVariation,sub_zero] using hn
  have hp0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg atG k l c i).P_nonneg)
  have hn0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg atG k l c i).N_nonneg)
  have heq := variations_equal C.theta
  have hs0 : 0≤ sError C := neg_nonneg.mpr hz
  exact ⟨⟨ha,by linarith⟩,⟨hs0,by linarith⟩,by linarith,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG)
    (hz : delta C.theta T≤0) (i : Fin 4) :
    (blocks C hg atG k l c i).P≤frameCap ∧ (blocks C hg atG k l c i).N≤frameCap := by
  have hb := original_budgets hg atG k l c hvar ha hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c j).N_nonneg) (Finset.mem_univ i)
  constructor <;> linarith [hb.1.1,hb.2.1.1,hb.2.2.1,hb.2.2.2.1]

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

private theorem r80_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

/-- The identity needs the original sign of the T error: for `delta T>0` the secant
weight leaves `lowC*tan (delta T)` unaccounted. -/
theorem low_decomposition (C : SignedCycle) {hg : Fin 4} (atG : Bool)
    (hhg : hg=0 ∨ hg=2) (hcos : Real.cos (delta C.theta T)≠0)
    (hs : sError C∈Icc 0 frameCap) :
    actualStress C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC=
      PositiveATD0.lowBaseline+PositiveATD0.charge*(aError C atG-sError C)+
        PositiveATD0.lowL*TwoPositive.ASupport.charge (aError C atG)+
        (∑i,actualLowBlocks C hg atG i)+aReserve C atG PositiveATD0.lowL+
        gain PositiveATD0.lowC (sError C) (C.point T).a (-(C.point D).y) := by
  have hsum := r80_delta_sum C
  have ht := transport_trig hs
  simp only [sError,Real.cos_neg,Real.sin_neg] at ht
  have hw : edgeWidth (delta C.theta 4)=
      (1-Real.sin (delta C.theta 4)+Real.cos (delta C.theta 4))/2 := by
    rw [edgeWidth,pairWidth,abs_of_nonpos (by simpa [T] using ht.2.2.1),
      abs_of_pos (by simp only [T] at ht; linarith [ht.1])]
    ring
  have hinv : Real.cos (delta C.theta 4)*(Real.cos (delta C.theta 4))⁻¹=1 :=
    mul_inv_cancel₀ (by simpa [T] using hcos)
  rw [actualStress,demand,← sum_force_work]
  simp only [Fin.sum_univ_seven,Fin.sum_univ_four,weights,owners,Matrix.cons_val,r80_e0,r80_e1,r80_e2,r80_e3,
    r80_e4,r80_e5,r80_e6,zeroProjection,quarterProjection,actualLowBlocks,blocks,
    PositiveATD0.pairIncrement,pairF,pairG,PositiveATD0.Source.dIncrement,PositiveATD0.dF,
    PositiveATD0.dG,PositiveATD0.lowBaseline,aReserve,aWork,aError,sError,gain,
    SignedPoint.reflect,Real.sin_neg,Real.cos_neg,Real.sin_zero,Real.cos_zero,edgeWidth_zero,
    H,G,A,B,T,D,E,hw]
  cases atG <;> rcases hhg with rfl|rfl <;>
    simp only [Bool.false_eq_true,↓reduceIte,Fin.isValue,show ((2:Fin 4)=0)=False by decide,
      Real.sin_zero,Real.cos_zero,edgeWidth_zero,Matrix.cons_val] <;>
    linear_combination (-PositiveATD0.charge)*hsum+
      PositiveATD0.lowC*(1-(C.point 4).y+(C.point 5).y)*hinv

theorem actual_low_blocks_nonneg {q : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG)
    (hz : delta C.theta T≤0) (i : Fin 4) : 0≤actualLowBlocks C hg atG i := by
  have hb := block_budgets hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC hvar ha hz
  fin_cases i
  · have hh := PositiveATD0.actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (a:=(blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 0).u)
      (b:=(blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 0).v)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq (hb 0).1 (hb 0).2
    simpa [actualLowBlocks,PositiveATD0.coefficientP,PositiveATD0.coefficientQ] using hh
  · have hh := PositiveATD0.actual_fixed_pair_nonneg 1 (P:=C.point H)
      (a:=(blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 1).u)
      (b:=(blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 1).v)
      hHy (hc H) hq (hb 1).1 (hb 1).2
    simpa [actualLowBlocks,PositiveATD0.coefficientP,PositiveATD0.coefficientQ] using hh
  · have hh := PositiveATD0.actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
      (a:=(blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 2).u)
      (b:=(blocks C hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC 2).v)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B) hq (hb 2).1 (hb 2).2
    simpa [actualLowBlocks,PositiveATD0.coefficientP,PositiveATD0.coefficientQ] using hh
  · have he := pair_error_bounds (hb 3).1 (hb 3).2
    simp only [blocks,Matrix.cons_val] at he
    have hh := PositiveATD0.actual_D_lower (P:=(C.point D).reflect)
      (z:=0) (d:=delta C.theta D)
      (by simpa using hs D)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hq (by norm_num [frameCap]) he.1 (by simpa using he.1)
    simpa [actualLowBlocks,PositiveATD0.Source.dIncrement,sub_nonneg] using hh

/-- All original nonpositive TD2 errors are covered in the low-A range. -/
theorem low_actual_false {q : ℝ} {C : SignedCycle} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aError C atG∈Icc 0 (1/6:ℝ)) (hz : delta C.theta T≤0)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0 ∨ hg=2) ∧ C.Feasible H hg := by
    rcases hHG with hh | hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hbudget := original_budgets hg atG PositiveATD0.lowK PositiveATD0.lowL PositiveATD0.lowC
    hvar ha.1 hz
  have hcos : Real.cos (delta C.theta T)≠0 := by
    have hh := (transport_trig hbudget.2.1).1
    simpa [sError] using (ne_of_gt (show 0<Real.cos (sError C) by linarith))
  have hu := stress_nonpos (k:=PositiveATD0.lowK) (l:=PositiveATD0.lowL) (c:=PositiveATD0.lowC)
    atG (by norm_num [PositiveATD0.lowK]) (by norm_num [PositiveATD0.lowL])
    (by norm_num [PositiveATD0.lowC]) hbudget.2.1 hHG hGA hAB hBT hTD hDE hEH
  have hb := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => actual_low_blocks_nonneg atG hs hc hq hHy hGy hBy hDy hvar ha.1 hz i (hg:=hg))
  have hA := a_reserve_nonneg (l:=PositiveATD0.lowL) atG (hs A) (hc A) hq
    (by norm_num [PositiveATD0.lowL]) hbudget.1
  have hgain := actual_gain_lower (hs T) hcoreT (hc T) (hs D) hDy (hc D) hq
    (show 0≤PositiveATD0.lowC by norm_num [PositiveATD0.lowC]) hbudget.2.1
  have hp := PositiveATD0.low_scalar_positive ha
  have he := low_decomposition C atG hhg hcos hbudget.2.1
  have hcharge : 0≤((9/10)*PositiveATD0.lowC-PositiveATD0.charge)*sError C := by
    apply mul_nonneg _ hbudget.2.1.1
    norm_num [PositiveATD0.lowC,PositiveATD0.charge]
  simp only [PositiveATD0.lowC,PositiveATD0.charge,PositiveATD0.lowL] at *
  linarith

end Source
end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD
