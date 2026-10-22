module

public import SquaresInCircles.Eight.TableFree.GlobalGAPairedENegativeSource
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDLowSource

/-!
# Nonnegative E total with a small nonnegative A total

Uncompiled transcription of Section 7 of the combined-E hand proof.
Both original primary pairs allow opposite individual signs. The
reference deletes only their selected angular arguments, retains an
arbitrary actual TD0 error, and uses the original TD2 secant multiplier
when that owner has nonpositive error. All points are unchanged.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PairedE.LowA
open Candidate Secondary NegativePrimary

def aTotal (C : SignedCycle) (ga ab : Bool) : ℝ :=
  total ga ab (delta C.theta G) (delta C.theta A)

def weights (C : SignedCycle) (td : Bool) : Vertex→ℝ :=
  ![PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowL,PositiveATD0.lowC,
    if td then PositiveATD0.lowC/Real.cos (delta C.theta T) else PositiveATD0.lowC,1,1]

def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab td de eh : Bool) : ℝ :=
  ∑i,weights C td i*(edgeWidth (delta C.theta i)-C.edge i (Negative.owners hg ga ab td de eh i))

def reference (C : SignedCycle) (hg : Fin 4) (ga ab td de eh : Bool) : ℝ :=
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
      (erase ab (delta C.theta A)) (delta C.theta B) (C.point B).reflect+
    PositiveATD0.Source.dIncrement (erase td (delta C.theta T))
      (erase de (delta C.theta D)) (C.point D).reflect

def tGain (C : SignedCycle) (td : Bool) : ℝ :=
  if td then PositiveANegativeTD.gain PositiveATD0.lowC (-delta C.theta T)
    (C.point T).a (-(C.point D).y) else 0

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab td de eh : Bool)
    (hhg : hg=0∨hg=2) (hcos : Real.cos (delta C.theta T)≠0) :
    actualStress C hg ga ab td de eh=
      reference C hg ga ab td de eh+
        PositiveATD0.charge*(aTotal C ga ab+cycleTotal C de eh-Negative.tMagnitude C td)+
        PositiveATD0.lowL*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
        primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E)+tGain C td := by
  cases ga <;> cases ab <;> cases td <;> cases de <;> cases eh <;>
    rcases hhg with rfl|rfl <;>
    simp [actualStress,weights,Negative.owners,reference,erase,SignedCycle.edge,
      zeroProjection,quarterProjection,Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      PositiveATD0.lowBaseline,PositiveATD0.pairIncrement,PositiveATD0.Source.dIncrement,
      pairF,pairG,PositiveATD0.dF,PositiveATD0.dG,aTotal,cycleTotal,total,selected,
      Negative.tMagnitude,primaryGain,tGain,PositiveANegativeTD.gain,
      edgeWidth,pairWidth,SignedPoint.reflect,PositiveATD0.lowK,PositiveATD0.lowL,
      PositiveATD0.lowC,PositiveATD0.charge]
  all_goals
    have hcos' : Real.cos (C.theta D-C.theta T)≠0 := hcos
    field_simp [hcos']
    ring

theorem reference_lower {q : ℝ} {C : SignedCycle} (hg : Fin 4)
    (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    PositiveATD0.lowBaseline≤reference C hg ga ab td de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab false
  simp only [erase_false] at hbb
  have hB := PositiveATD0.actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,
    Matrix.cons_val_succ,Matrix.cons_val_zero] at hB
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) td de
  have hde := pair_error_bounds hdb.1 hdb.2
  have hd := PositiveATD0.actual_D_lower (P:=(C.point D).reflect)
    (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  have hD : 0≤PositiveATD0.Source.dIncrement (erase td (delta C.theta T))
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
      Matrix.cons_val_succ,Matrix.cons_val_zero] at hH hG
    simp only [reference,if_pos hhg]
    linarith
  · have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) false eh
    have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) true ga
    simp only [erase_true,erase_false] at hhb hgb
    have hH := PositiveATD0.actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
    have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq hgb.1 hgb.2
    simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,
      Matrix.cons_val_succ,Matrix.cons_val_zero] at hH hG
    simp only [reference,if_neg hhg]
    linarith

theorem t_gain_lower {q : ℝ} {C : SignedCycle} (td : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : (C.point T).AvoidsCore) (hq : q≤qCap) (hDy : (C.point D).y≤0)
    (hsmall : |delta C.theta T|≤frameCap) (htd : td=true→delta C.theta T≤0) :
    (9/10)*PositiveATD0.lowC*Negative.tMagnitude C td≤tGain C td := by
  cases hh : td
  · simp [tGain,Negative.tMagnitude,selected]
  · have hz : -delta C.theta T∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr (htd hh),(neg_le_abs _).trans hsmall⟩
    simpa [tGain,Negative.tMagnitude,selected] using PositiveANegativeTD.actual_gain_lower
      (hs T) hcore (hc T) (hs D) hDy (hc D) hq
      (show 0≤PositiveATD0.lowC by norm_num [PositiveATD0.lowC]) hz

/-- The selected A and E totals include both original errors when both
primaries occur; neither individual sign is restricted. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (htd : td=true→delta C.theta T≤0) (he : 0≤cycleTotal C de eh) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos : 0<Real.cos (delta C.theta T) := NegativePrimary.cos_pos (hsmall T)
  have hweights (i : Vertex) : 0≤weights C td i := by
    have hs : 0≤PositiveATD0.lowC/Real.cos (delta C.theta T) :=
      div_nonneg (by norm_num [PositiveATD0.lowC]) hcos.le
    cases td <;> fin_cases i <;>
      simp [weights,PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowC,hs]
  have hf (i : Vertex) : C.Feasible i (Negative.owners hg ga ab td de eh i) := by
    fin_cases i
    · simpa [Negative.owners,H] using hHG
    · simpa [Negative.owners,G] using hGA
    · simpa [Negative.owners,A] using hAB
    · simpa [Negative.owners,B] using hBT
    · simpa [Negative.owners,T] using hTD
    · simpa [Negative.owners,D] using hDE
    · simpa [Negative.owners,E] using hEH
  have hu : actualStress C hg ga ab td de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hh := hf i
    change 0≤C.edge i (Negative.owners hg ga ab td de eh i)-edgeWidth (delta C.theta i) at hh
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hreference := reference_lower hg ga ab td de eh hs hc hq hHy hGy hBy hDy hvar
  have hAmem : aTotal C ga ab∈Icc 0 frameCap :=
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hAcharge := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hAmem
  have hAweighted := mul_le_mul_of_nonneg_left hAcharge
    (show 0≤PositiveATD0.lowL by norm_num [PositiveATD0.lowL])
  have hscalar := PositiveATD0.low_scalar_positive ha
  have hEmem := cycle_total_bounds de eh hvar he
  have hEcharge := selected_charge de eh (hs E) (hc E) hq (hsmall D) (hsmall E) hEmem
  have hElinear := charge_linear hEmem
  have hTgain := t_gain_lower td hs hc hcoreT hq hDy (hsmall T) htd
  have ht0 : 0≤Negative.tMagnitude C td := by
    cases hh : td
    · simp [Negative.tMagnitude,selected]
    · simpa [Negative.tMagnitude,selected] using neg_nonneg.mpr (htd hh)
  rw [decomposition C ga ab td de eh hhg hcos.ne'] at hu
  change PositiveATD0.lowL*TwoPositive.ASupport.charge (aTotal C ga ab)≤_ at hAweighted
  change TwoPositive.ASupport.charge (cycleTotal C de eh)≤_ at hEcharge
  dsimp [PositiveATD0.charge,PositiveATD0.lowC] at hu hscalar hTgain
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PairedE.LowA
