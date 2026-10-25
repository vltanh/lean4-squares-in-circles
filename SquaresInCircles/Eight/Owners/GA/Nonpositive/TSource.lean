module

public import SquaresInCircles.Eight.Owners.GA.OuterESelection
public import SquaresInCircles.Eight.Owners.GA.Negative.ACycle
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESource
public import SquaresInCircles.Eight.Owners.GA.Negative.Flat.EExclusion
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TAlignedGain
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TLowESource
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TNegativeASource

/-!
# Eight squares: every A/E owner at the actual negative-BT3 alignment

E is
normalized first, while the full physical source domain is available.
A is normalized afterward as a necessary-system transport. Its endpoint
is used only by the proved source stress inequalities. The current BT3
entry supplies its own flat-core cut, and all E cuts are derived before
the A transport. The resulting theorem retains an actual BT2 witness.
-/

section
/-!
## Simultaneous negative A/E primaries at the negative-BT3 alignment

Both
negative E secants retain the original core-E cancellation. The actual
aligned T pair adds a nonnegative charged gain to the already proved
negative A/E reserve; no inherited marker is applied to the moved point.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.NegativeAE
open Candidate Secondary NegativeFlatE
open NegativePrimary (erase erase_positive_le erase_negative_le erase_abs_bound erased_pair_budgets)

def owners (hg ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    3,2,if de then 3 else 2,if eh then 1 else 0]

abbrev weights := NegativeFlatE.weights

def stress (hg ga ab de eh : Bool) (C : SignedCycle) : ℝ :=
  ∑i,weights ga ab de eh C i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))

abbrev dIncrement := NegativeFlatE.dIncrement

def reference (hg ga ab de eh : Bool) (C : SignedCycle) : ℝ :=
  lowBaseline+
    NegativeFlatE.pairIncrement lowK lowL (erase hg (delta C.theta H))
      (erase ga (delta C.theta G)) (C.point G).reflect+
    NegativeFlatE.pairIncrement lowK 1 (erase (!hg) (delta C.theta H))
      (erase eh (delta C.theta E)) (C.point H)+
    NegativeFlatE.pairIncrement lowL lowC (erase ab (delta C.theta A))
      0 (C.point B).reflect+
    dIncrement 0 (erase de (delta C.theta D)) (C.point D).reflect

def tGain (C : SignedCycle) : ℝ :=
  lowC*PairedA.work (C.point T) (delta C.theta B) 0+NegativeFlatE.charge*delta C.theta B

def gains (ga ab de eh : Bool) (C : SignedCycle) : ℝ :=
  NegativeFlatE.gains ga ab false de eh C+tGain C

abbrev weights_nonneg := NegativeFlatE.weights_nonneg

theorem stress_nonpos {hg ga ab de eh : Bool} {C : SignedCycle}
    (hsmall : ∀i,|delta C.theta i|≤frameCap)
    (hf : ∀i,C.Feasible i (owners hg ga ab de eh i)) :
    stress hg ga ab de eh C≤0 := by
  apply Finset.sum_nonpos
  intro i _
  have hi := hf i
  change 0≤C.edge i (owners hg ga ab de eh i)-edgeWidth (delta C.theta i) at hi
  exact mul_nonpos_of_nonneg_of_nonpos (weights_nonneg ga ab de eh C hsmall i) (by linarith)

private def r92ae_aslot (p x : ℝ) (P : SignedPoint) : ℝ :=
  p*(edgeWidth x-1)-p*Real.sin x*P.a-p*Real.cos x*P.y+NegativeFlatE.charge*x

private def r92ae_bslot (q x : ℝ) (P : SignedPoint) : ℝ :=
  q*(edgeWidth x-1)-q*Real.cos x*P.a-q*Real.sin x*P.y+NegativeFlatE.charge*x

private def r92ae_zslot (x : ℝ) (P : SignedPoint) : ℝ :=
  lowC*edgeWidth x-lowC*Real.sin x*P.a-lowC*Real.cos x*P.y+NegativeFlatE.charge*x

private def r92ae_dslot (x : ℝ) (P : SignedPoint) : ℝ :=
  edgeWidth x-Real.cos x*P.a-Real.sin x*P.y+NegativeFlatE.charge*x

private theorem r92ae_pair_split (p q a b : ℝ) (P : SignedPoint) :
    NegativeFlatE.pairIncrement p q a b P=r92ae_aslot p a P+r92ae_bslot q b P+fullSupport q p := by
  simp only [NegativeFlatE.pairIncrement,pairF,pairG,r92ae_aslot,r92ae_bslot]
  ring

private theorem r92ae_d_split (z d : ℝ) (P : SignedPoint) :
    NegativeFlatE.dIncrement z d P=
      r92ae_zslot z P+r92ae_dslot d P-(1+lowC)*(1-GlobalGA.Secondary.diagonal) := by
  simp only [NegativeFlatE.dIncrement,NegativeFlatE.dF,NegativeFlatE.dG,r92ae_zslot,r92ae_dslot]
  ring

private theorem r92ae_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

private theorem r92ae_edge_H (hg ga ab de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 0*(edgeWidth (delta C.theta 0)-C.edge 0 (owners hg ga ab de eh 0))=
      r92ae_aslot lowK (erase hg (delta C.theta 0)) (C.point 1).reflect+
      r92ae_aslot lowK (erase (!hg) (delta C.theta 0)) (C.point 0)+lowK-NegativeFlatE.charge*delta C.theta 0 := by
  cases hg <;>
    simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,zeroProjection,r92ae_aslot,
      SignedPoint.reflect] <;> ring

private theorem r92ae_edge_G (hg ga ab de eh : Bool) (C : SignedCycle)
    (hG : Real.cos (delta C.theta 1)≠0) :
    weights ga ab de eh C 1*(edgeWidth (delta C.theta 1)-C.edge 1 (owners hg ga ab de eh 1))=
      r92ae_bslot lowL (erase ga (delta C.theta 1)) (C.point 1).reflect+
      (if ga then NegativeFlatE.primaryGain (delta C.theta 1) (C.point 2).a (C.point 1).a+
        NegativeFlatE.charge*delta C.theta 1 else 0)+lowL+lowL*(C.point 2).y-NegativeFlatE.charge*delta C.theta 1 := by
  cases ga
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot,
      SignedPoint.reflect]
    ring
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot,
      SignedPoint.reflect,NegativeFlatE.primaryGain,G,A]
    field_simp
    ring

private theorem r92ae_edge_A (hg ga ab de eh : Bool) (C : SignedCycle)
    (hA : Real.cos (delta C.theta 2)≠0) :
    weights ga ab de eh C 2*(edgeWidth (delta C.theta 2)-C.edge 2 (owners hg ga ab de eh 2))=
      r92ae_aslot lowL (erase ab (delta C.theta 2)) (C.point 3).reflect+
      (if ab then NegativeFlatE.primaryGain (delta C.theta 2) (C.point 2).a (-(C.point 3).y)+
        NegativeFlatE.charge*delta C.theta 2 else 0)+lowL-lowL*(C.point 2).y-NegativeFlatE.charge*delta C.theta 2 := by
  cases ab
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,zeroProjection,r92ae_aslot,
      SignedPoint.reflect]
    ring
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,zeroProjection,r92ae_aslot,
      SignedPoint.reflect,NegativeFlatE.primaryGain,G,A]
    field_simp
    ring

private theorem r92ae_edge_B (hg ga ab de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 3*(edgeWidth (delta C.theta 3)-C.edge 3 (owners hg ga ab de eh 3))=
      r92ae_bslot lowC 0 (C.point 3).reflect+tGain C+lowC+lowC*(C.point 4).y-
        NegativeFlatE.charge*delta C.theta 3 := by
  simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot,
    SignedPoint.reflect,tGain,PairedA.work,B,T]
  ring

private theorem r92ae_edge_T (hg ga ab de eh : Bool) (C : SignedCycle)
    (hT : delta C.theta 4=0) :
    weights ga ab de eh C 4*(edgeWidth (delta C.theta 4)-C.edge 4 (owners hg ga ab de eh 4))=
      r92ae_zslot 0 (C.point 5).reflect-lowC*(C.point 4).y := by
  simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,zeroProjection,r92ae_zslot,
    SignedPoint.reflect,hT]
  ring

private theorem r92ae_edge_D (hg ga ab de eh : Bool) (C : SignedCycle)
    (hflat : (C.point 6).a=7/12) (hD : Real.cos (delta C.theta 5)≠0) :
    weights ga ab de eh C 5*(edgeWidth (delta C.theta 5)-C.edge 5 (owners hg ga ab de eh 5))=
      r92ae_dslot (erase de (delta C.theta 5)) (C.point 5).reflect+
      (if de then NegativeFlatE.eGain (delta C.theta 5) (C.point 5).a+NegativeFlatE.charge*delta C.theta 5 else 0)+
        (C.point 6).y-NegativeFlatE.charge*delta C.theta 5 := by
  cases de
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_dslot,
      SignedPoint.reflect]
    ring
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_dslot,
      SignedPoint.reflect,NegativeFlatE.eGain,hflat,D]
    field_simp
    ring

private theorem r92ae_edge_E (hg ga ab de eh : Bool) (C : SignedCycle)
    (hflat : (C.point 6).a=7/12) (hE : Real.cos (delta C.theta 6)≠0) :
    weights ga ab de eh C 6*(edgeWidth (delta C.theta 6)-C.edge 6 (owners hg ga ab de eh 6))=
      r92ae_bslot 1 (erase eh (delta C.theta 6)) (C.point 0)+
      (if eh then NegativeFlatE.eGain (delta C.theta 6) (C.point 0).a+NegativeFlatE.charge*delta C.theta 6 else 0)+
        1-(C.point 6).y-NegativeFlatE.charge*delta C.theta 6 := by
  cases eh
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot]
    ring
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot,
      NegativeFlatE.eGain,hflat,E]
    field_simp
    ring

theorem decomposition (hg ga ab de eh : Bool) (C : SignedCycle)
    (hflat : (C.point E).a=7/12)
    (hG : Real.cos (delta C.theta G)≠0) (hA : Real.cos (delta C.theta A)≠0)
    (hD : Real.cos (delta C.theta D)≠0) (hE : Real.cos (delta C.theta E)≠0) (hTD : delta C.theta T=0) :
    stress hg ga ab de eh C=reference hg ga ab de eh C+gains ga ab de eh C := by
  simp only [G,A,D,E,T] at hflat hG hA hD hE hTD
  have hH' := r92ae_edge_H hg ga ab de eh C
  have hG' := r92ae_edge_G hg ga ab de eh C hG
  have hA' := r92ae_edge_A hg ga ab de eh C hA
  have hB' := r92ae_edge_B hg ga ab de eh C
  have hT' := r92ae_edge_T hg ga ab de eh C hTD
  have hD' := r92ae_edge_D hg ga ab de eh C hflat hD
  have hE' := r92ae_edge_E hg ga ab de eh C hflat hE
  have hs := r92ae_delta_sum C
  simp only [stress,Fin.sum_univ_seven,reference,gains,NegativeFlatE.gains,r92ae_pair_split,
    dIncrement,r92ae_d_split,lowBaseline,Bool.false_eq_true,↓reduceIte,H,G,A,B,D,E]
  linear_combination hH'+hG'+hA'+hB'+hT'+hD'+hE'-NegativeFlatE.charge*hs+NegativeFlatE.charge*hTD

theorem reference_reserve {q : ℝ} {C : SignedCycle} (hg ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) : baseline<reference hg ga ab de eh C := by
  have hn : negativeVariation C.theta≤frameCap := by rwa [←variations_equal]
  have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) hg ga
  have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) (!hg) eh
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab true
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) true de
  simp only [NegativePrimary.erase_true] at hbb hdb
  have hG := actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hc G) hq hgb.1 hgb.2
  have hH := actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
  have hB := actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hc B) hq hbb.1 hbb.2
  have hde := pair_error_bounds hdb.1 hdb.2
  have hD := NegativeFlatE.actual_D_lower (P:=(C.point D).reflect)
    (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  simp only [coefficientP,coefficientQ,Matrix.cons_val] at hG hH hB
  have hL := low_baseline_reserve
  dsimp only [reference,dIncrement,NegativeFlatE.dIncrement,baseline]
  have hsum := add_nonneg (add_nonneg (add_nonneg hG hH) hB) (sub_nonneg.mpr hD)
  exact lt_of_lt_of_le hL (le_of_le_of_eq (le_add_of_nonneg_right hsum) (by ring))

theorem t_gain_nonneg {C : SignedCycle} (hs : (C.point T).Sorted)
    (hcore : (C.point T).AvoidsCore) (hb : delta C.theta B≤0)
    (hsmall : |delta C.theta B|≤frameCap) : 0≤tGain C := by
  have hsdom : -delta C.theta B∈Icc 0 frameCap :=
    ⟨neg_nonneg.mpr hb,(neg_le_abs _).trans hsmall⟩
  have hw := Paired.aligned_work_weak hs hcore hsdom
  have hp := td_arc_charge hsdom
  have hh := mul_le_mul_of_nonneg_left hw (show 0≤lowC by norm_num [lowC])
  dsimp [PositiveAngularEnvelope.phi] at hh
  simp only [neg_neg] at hh
  dsimp only [tGain]
  dsimp only [NegativeFlatE.charge,NegativeFlatE.lowC] at hp hh ⊢
  linarith [hsdom.1]

theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2)) (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2)) (hEH : C.Feasible E (if eh then 1 else 0))
    (hga : ga=true→delta C.theta G≤0) (hab : ab=true→delta C.theta A≤0)
    (hb : delta C.theta B≤0) (htd : delta C.theta T=0)
    (hde : de=true→delta C.theta D≤0) (heh : eh=true→delta C.theta E≤0) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hu := stress_nonpos hsmall hf
  have hr := reference_reserve hg ga ab de eh hs hc hQ hHy hGy hBy hDy hvar
  have hgain := NegativeFlatE.gains_reserve ga ab false de eh hs hc hcore hQ hvar hga hab
    (by simp) hde heh
  have htg := t_gain_nonneg (hs T) (hcore T) hb (hsmall B)
  have hid := decomposition hg ga ab de eh C hflat
    (NegativePrimary.cos_pos (hsmall G)).ne' (NegativePrimary.cos_pos (hsmall A)).ne'
    (NegativePrimary.cos_pos (hsmall D)).ne' (NegativePrimary.cos_pos (hsmall E)).ne' htd
  rw [hid] at hu
  dsimp [gains] at hu
  linarith

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.NegativeAE
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA
open Candidate SignedCycle Secondary

namespace NegativeANormalForm.CycleResult

theorem other_delta {Q : ℝ} {C : SignedCycle} (O : CycleResult Q C)
    (i : Vertex) (hiG : i≠G) (hiA : i≠A) : delta O.cycle.theta i=delta C.theta i := by
  have hn : next i≠A := by
    fin_cases i <;> first | (exfalso; exact hiG rfl) | (exfalso; exact hiA rfl) | decide
  simp [delta,O.theta_other i hiA,O.theta_other (next i) hn]

end NegativeANormalForm.CycleResult

namespace NonpositiveT.Source
open PairedE

def ERegime (C : SignedCycle) (de eh : Bool) : Prop :=
  0≤cycleTotal C de eh ∨
    ((C.point E).a=7/12 ∧ (de=true→delta C.theta D≤0) ∧
      (eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ) ∧ -(C.point E).y≤39/250))

theorem prepared_false {Q : ℝ} {C : SignedCycle} (I : SourceDomain Q C)
    (hqL : qLow≤Q) (hqU : Q≤qCap) (de eh : Bool)
    (hDE : C.Feasible D (if de then 3 else 2)) (hEH : C.Feasible E (if eh then 1 else 0))
    (hreg : ERegime C de eh)
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hb : delta C.theta B<0) (htd : delta C.theta T=0)
    (hTflat : (C.point T).a=7/12) (hTy : (C.point T).y≤39/250) : False := by
  obtain ⟨ga,hga⟩ : ∃ga : Bool,I.owner G=(if ga then 3 else 2) := by
    have ho : I.owner G=2∨I.owner G=3 := by simpa [highGAOwners,G] using I.allowed G
    rcases ho with ho|ho
    · exact ⟨false,ho⟩
    · exact ⟨true,ho⟩
  obtain ⟨ab,hab⟩ : ∃ab : Bool,I.owner A=(if ab then 2 else 0) := by
    have ho : I.owner A=0∨I.owner A=2 := by simpa [highGAOwners,A] using I.allowed A
    rcases ho with ho|ho
    · exact ⟨false,ho⟩
    · exact ⟨true,ho⟩
  have hGA : C.Feasible G (if ga then 3 else 2) := by simpa [hga] using I.feasible G
  have hAB : C.Feasible A (if ab then 2 else 0) := by simpa [hab] using I.feasible A
  obtain ⟨O⟩ := NegativeANormalForm.cycle_reduce ga ab
    (by norm_num [qLow] at hqL ⊢; linarith) hqU I.necessary I.radial I.G_negative.le
    (I.outer B (by simp [H,G,B,D])) I.B_negative.le I.A_upper I.A_nonpos_outer
    I.strict_spread hGA hAB
  have hH := O.point_other H (by norm_num [H,A])
  have hG := O.point_other G (by norm_num [G,A])
  have hB := O.point_other B (by norm_num [B,A])
  have hT := O.point_other T (by norm_num [T,A])
  have hD := O.point_other D (by norm_num [D,A])
  have hE := O.point_other E (by norm_num [E,A])
  have hδB := O.other_delta B (by norm_num [B,G]) (by norm_num [B,A])
  have hδT := O.other_delta T (by norm_num [T,G]) (by norm_num [T,A])
  have hδD := O.other_delta D (by norm_num [D,G]) (by norm_num [D,A])
  have hδE := O.other_delta E (by norm_num [E,G]) (by norm_num [E,A])
  have hHy : 0≤(O.cycle.point H).y := by rw [hH]; exact I.H_positive.le
  have hGy : (O.cycle.point G).y≤0 := by rw [hG]; exact I.G_negative.le
  have hBy : (O.cycle.point B).y≤0 := by rw [hB]; exact I.B_negative.le
  have hDy : (O.cycle.point D).y≤0 := by rw [hD]; exact I.D_negative.le
  have hvar := O.variation.trans I.positive_variation.le
  have hHG : O.cycle.Feasible H 0∨O.cycle.Feasible H 2 := by
    rcases NegativeELowA.original_HG I with hh|hh
    · exact Or.inl ((O.other_edges H (by norm_num [H,G,A]) 0).2 hh)
    · exact Or.inr ((O.other_edges H (by norm_num [H,G,A]) 2).2 hh)
  have hBT' := (O.other_edges B (by norm_num [B,G,A]) 3).2 hBT
  have hTD' := (O.other_edges T (by norm_num [T,G,A]) 2).2 hTD
  have hDE' := (O.other_edges D (by norm_num [D,G,A]) _).2 hDE
  have hEH' := (O.other_edges E (by norm_num [E,G,A]) _).2 hEH
  have hb' : delta O.cycle.theta B≤0 := by rw [hδB]; exact hb.le
  have htd' : delta O.cycle.theta T=0 := by rw [hδT]; exact htd
  have hTflat' : (O.cycle.point T).a=7/12 := by rw [hT]; exact hTflat
  have hTy' : (O.cycle.point T).y≤39/250 := by rw [hT]; exact hTy
  have hreg' : ERegime O.cycle de eh := by
    simpa only [ERegime,cycleTotal,total,hδD,hδE,hE] using hreg
  have negativeA_false
      (hga : O.ga=true→delta O.cycle.theta G≤0)
      (hab : O.ab=true→delta O.cycle.theta A≤0) : False := by
    rcases hreg' with he|⟨hflat,hde,heh⟩
    · exact NonpositiveT.NegativeA.actual_false O.ga O.ab de eh O.necessary.sorted
        O.necessary.contained O.necessary.core hqU hHy hGy hBy hDy hvar hHG
        O.GA O.AB hBT' hTD' hDE' hEH' hga hab hb' htd' he
    · exact NegativeAE.actual_false O.ga O.ab de eh O.necessary.sorted O.necessary.contained
        O.necessary.core hqU hHy hGy hBy hDy hflat hvar hHG O.GA O.AB hBT' hTD' hDE' hEH'
        hga hab hb' htd' hde (fun h => by linarith [(heh h).1.1])
  rcases O.reduced with ha|⟨hga,hab,_,_,hu⟩|⟨hga,hab,_,_,hv⟩
  · have ha0 : 0≤PairedE.LowA.aTotal O.cycle O.ga O.ab := ha
    rcases hreg' with he|⟨hflat,hde,heh⟩
    · exact Paired.Source.actual_false O.ga O.ab de eh O.necessary.sorted O.necessary.contained
        (O.necessary.core T) hqU hHy hGy hBy hDy hvar ha0 he hb' htd'
        hHG O.GA O.AB hBT' hTD' hDE' hEH'
    · by_cases hlow : PairedE.LowA.aTotal O.cycle O.ga O.ab≤1/6
      · exact LowE.actual_false O.ga O.ab de eh O.necessary.sorted O.necessary.contained
          (O.necessary.core T) hqU hHy hGy hBy hDy hflat hvar hHG O.GA O.AB hBT' hTD' hDE' hEH'
          ⟨ha0,hlow⟩ hb' htd' hde (fun h => (heh h).1)
      · have hn : negativeVariation O.cycle.theta≤frameCap := by rw [←variations_equal]; exact hvar
        have hpair := original_pair_budgets (i:=G) (j:=A) hvar hn (by norm_num [G,A])
        have hbound := total_bounds O.ga O.ab hpair.1 hpair.2 ha0
        exact LargeE.actual_false O.ga O.ab de eh O.necessary.sorted O.necessary.contained
          (O.necessary.core T) hqU hHy hGy hBy hDy hflat hvar hHG O.GA O.AB hBT' hTD' hDE' hEH'
          ⟨(lt_of_not_ge hlow).le,hbound.2⟩ hb' htd' hTflat' hTy' hde heh
  · exact negativeA_false (fun _ => hu.2.le) (by intro h; rw [hab] at h; cases h)
  · exact negativeA_false (by intro h; rw [hga] at h; cases h) (fun _ => hv.2.le)

theorem reduced_core_false {Q : ℝ} {C : SignedCycle} (I : SourceDomain Q C)
    (hqL : qLow≤Q) (hqU : Q≤qCap) (hEc : (C.point E).Core)
    (hr : CoreENormalForm.Reduced C (I.owner D) (I.owner E))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hb : delta C.theta B<0) (htd : delta C.theta T=0)
    (hTflat : (C.point T).a=7/12) (hTy : (C.point T).y≤39/250) : False := by
  have hn := I.necessary
  rcases hr with hnonneg|⟨hflat,hnegative⟩
  · obtain ⟨de,hde⟩ : ∃de : Bool,I.owner D=(if de then 3 else 2) := by
      have ho : I.owner D=2∨I.owner D=3 := by simpa [highGAOwners,D] using I.allowed D
      rcases ho with ho|ho
      · exact ⟨false,ho⟩
      · exact ⟨true,ho⟩
    obtain ⟨eh,heh⟩ : ∃eh : Bool,I.owner E=(if eh then 1 else 0) := by
      have ho : I.owner E=0∨I.owner E=1 := by simpa [highGAOwners,E] using I.allowed E
      rcases ho with ho|ho
      · exact ⟨false,ho⟩
      · exact ⟨true,ho⟩
    have hDE : C.Feasible D (if de then 3 else 2) := by simpa [hde] using I.feasible D
    have hEH : C.Feasible E (if eh then 1 else 0) := by simpa [heh] using I.feasible E
    have he : 0≤cycleTotal C de eh := by
      rw [hde,heh,CoreENegativeTotal.selected_total] at hnonneg
      exact hnonneg
    exact prepared_false I hqL hqU de eh hDE hEH (Or.inl he) hBT hTD hb htd hTflat hTy
  · rcases hnegative with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · have hDE : C.Feasible D 3 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 0 := by simpa [heh] using I.feasible E
      exact prepared_false I hqL hqU true false hDE hEH
        (Or.inr ⟨hflat,fun _ => hd.le,by intro h; cases h⟩) hBT hTD hb htd hTflat hTy
    · have hDE : C.Feasible D 2 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 1 := by simpa [heh] using I.feasible E
      by_cases hEH0 : C.Feasible E 0
      · exact prepared_false I hqL hqU false false hDE hEH0
          (Or.inl (by simp [cycleTotal,total,selected])) hBT hTD hb htd hTflat hTy
      · have hnE : -delta C.theta E∈Ioc 0 frameCap :=
          ⟨neg_pos.mpr he,(neg_le_abs _).trans (hn.spread (next E) E)⟩
        have hlocal : quarterFeasible (C.point E) (C.point H) (-(-delta C.theta E)) 1 := by
          simpa [Feasible,slack,edge,word,next,E,H,quarterFeasible,sub_nonneg] using hEH
        have hnot : ¬quarterFeasible (C.point E) (C.point H) (-(-delta C.theta E)) 0 := by
          intro hh
          apply hEH0
          simpa [Feasible,slack,edge,word,next,E,H,quarterFeasible,sub_nonneg] using hh
        have hcut := NegativeCoreE.genuine_negative_flat (hn.sorted E) I.E_nonpos hEc
          (hn.sorted H) I.H_positive.le (hn.contained H) hqU hnE hlocal hnot
        have hreg : ERegime C false true := by
          refine Or.inr ⟨hflat,?_,?_⟩
          · intro h
            cases h
          · intro _
            exact ⟨⟨hnE.1.le,hcut.2.2.le⟩,hcut.2.1.le⟩
        exact prepared_false I hqL hqU false true hDE hEH hreg hBT hTD hb htd hTflat hTy

/-- Every negative-BT3 TD-alignment endpoint has the actual BT2 witness.
Both radial kinds, every E owner/sign, and every A selected total are
handled inside the theorem. No scalar or tangent-cut premise remains. -/
theorem aligned_has_BT2 {Q : ℝ} {C : SignedCycle} (I : SourceDomain Q C)
    (hqL : qLow≤Q) (hqU : Q≤qCap) (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hb : delta C.theta B<0) (htd : delta C.theta T=0) (hy : 0<(C.point T).y) :
    C.Feasible B 2 := by
  by_contra hBT2
  have hs : -delta C.theta B∈Ioc 0 frameCap :=
    ⟨neg_pos.mpr hb,(neg_le_abs _).trans (I.necessary.spread (next B) B)⟩
  have hlocal : quarterFeasible (C.point B) (C.point T) (-(-delta C.theta B)) 3 := by
    simpa [Feasible,slack,edge,word,next,B,T,quarterFeasible,sub_nonneg] using hBT
  have hcut := GlobalGA.NegativeA.GA_entry (I.necessary.sorted B) (I.necessary.contained B)
    (I.necessary.sorted T) (I.radial T) hqU I.B_negative.le
    (fun h => (not_le_of_gt hy h).elim) hs hlocal
  rcases hcut with hsecondary|⟨hTflat,_,hTy,_⟩
  · apply hBT2
    simpa [Feasible,slack,edge,word,next,B,T,quarterFeasible,sub_nonneg] using hsecondary
  · rcases I.radial E with houter|hcore
    · let S := OuterE.select I hqU houter
      exact prepared_false I hqL hqU S.de S.eh S.DE S.EH (Or.inl S.total_nonneg)
        hBT hTD hb htd hTflat hTy.le
    · obtain ⟨O⟩ := CoreENormalForm.reduce I hqL hqU hcore
      have hBT' := (O.other_feasible B (by norm_num [B,D]) (by norm_num [B,E]) 3).2 hBT
      have hTD' := (O.other_feasible T (by norm_num [T,D]) (by norm_num [T,E]) 2).2 hTD
      have hδB := O.other_delta B (by norm_num [B,D]) (by norm_num [B,E])
      have hδT := O.other_delta T (by norm_num [T,D]) (by norm_num [T,E])
      have hpoint := O.point_other T (by norm_num [T,E])
      exact reduced_core_false O.source hqL hqU O.E_core O.reduced hBT' hTD'
        (by rw [hδB]; exact hb) (by rw [hδT]; exact htd)
        (by rw [hpoint]; exact hTflat) (by rw [hpoint]; exact hTy.le)

end NonpositiveT.Source
end SquaresInCircles.Eight.GlobalGA
end
end
end
