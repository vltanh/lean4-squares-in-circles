module

public import SquaresInCircles.Eight.Owners.GA.Negative.AShortEComparison
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2OriginalStress
public import SquaresInCircles.Eight.Owners.GA.Negative.Primary.Stress
public import SquaresInCircles.Eight.Owners.GA.Paired.ECharge

/-!
# Eight squares: the algebraic shorter-E reference vector

The `reference` cycle keeps every point and changes only angular arguments inside a weighted sum;
its edges need not be separating witnesses. The deleted selected E errors may have opposite signs.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.ShortE
open Candidate Secondary SignedStress
open NegativeAPositiveTD

def reference (C : SignedCycle) (atG de eh : Bool) : SignedCycle where
  point := C.point
  theta := fun i => C.theta i+
    ![0,0,if atG then PairedE.cycleTotal C de eh else 0,
      PairedE.cycleTotal C de eh,PairedE.cycleTotal C de eh,
      PairedE.cycleTotal C de eh,PairedE.selected eh (delta C.theta E)] i

@[simp] theorem reference_point (C : SignedCycle) (atG de eh : Bool) (i : Vertex) :
    (reference C atG de eh).point i=C.point i := rfl

theorem reference_delta (C : SignedCycle) (atG de eh : Bool) (i : Vertex) :
    delta (reference C atG de eh).theta i=
      ![delta C.theta H,
        delta C.theta G+(if atG then PairedE.cycleTotal C de eh else 0),
        delta C.theta A+(if atG then 0 else PairedE.cycleTotal C de eh),
        delta C.theta B,delta C.theta T,
        NegativePrimary.erase de (delta C.theta D),
        NegativePrimary.erase eh (delta C.theta E)] i := by
  cases atG <;> cases de <;> cases eh <;> fin_cases i <;>
    simp [reference,delta,next,PairedE.cycleTotal,PairedE.total,PairedE.selected,
      NegativePrimary.erase,H,G,A,B,T,D,E] <;> ring

@[simp] theorem reference_T (C : SignedCycle) (atG de eh : Bool) :
    delta (reference C atG de eh).theta T=delta C.theta T := by
  simpa [T] using reference_delta C atG de eh T

theorem reference_aError {C : SignedCycle} {s : ℝ} (atG de eh : Bool)
    (ha : Source.aError C atG= -s) :
    Source.aError (reference C atG de eh) atG= -(s-PairedE.cycleTotal C de eh) := by
  cases atG <;> simp only [Source.aError,Bool.false_eq_true,ite_false,ite_true] at ha ⊢
  · rw [reference_delta]
    simp [A] at ha ⊢
    linarith
  · rw [reference_delta]
    simp [G] at ha ⊢
    linarith

/-- The deletion identity, before any sign is imposed on an error. -/
theorem reference_parts (C : SignedCycle) (atG de eh : Bool)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,f (delta (reference C atG de eh).theta i))=
      (∑i,f (delta C.theta i))-f (Source.aError C atG)+
        f (Source.aError C atG+PairedE.cycleTotal C de eh)-
        f (PairedE.selected de (delta C.theta D))-
        f (PairedE.selected eh (delta C.theta E)) := by
  simp_rw [reference_delta]
  cases atG <;> cases de <;> cases eh <;>
    simp [Source.aError,NegativePrimary.erase,PairedE.cycleTotal,PairedE.total,
      PairedE.selected,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

/-- Both variations lose exactly the total of the deleted positive E
parts, equivalently `e` plus the deleted negative E parts. -/
theorem reference_variations {C : SignedCycle} {s : ℝ} (atG de eh : Bool)
    (hs : 0≤ s) (ha : Source.aError C atG= -s)
    (he : PairedE.cycleTotal C de eh∈Icc 0 s) :
    positiveVariation (reference C atG de eh).theta=
      positiveVariation C.theta-PairedE.cycleTotal C de eh-
        negativePart (PairedE.selected de (delta C.theta D))-
        negativePart (PairedE.selected eh (delta C.theta E)) ∧
    negativeVariation (reference C atG de eh).theta=
      negativeVariation C.theta-PairedE.cycleTotal C de eh-
        negativePart (PairedE.selected de (delta C.theta D))-
        negativePart (PairedE.selected eh (delta C.theta E)) := by
  have hp := reference_parts C atG de eh positivePart positivePart_zero
  have hn := reference_parts C atG de eh negativePart negativePart_zero
  have hpA : positivePart (Source.aError C atG)=0 := by
    rw [ha]; exact max_eq_right (by linarith)
  have hpA' : positivePart (Source.aError C atG+PairedE.cycleTotal C de eh)=0 := by
    rw [ha]; exact max_eq_right (by linarith [he.2])
  have hnA : negativePart (Source.aError C atG)=s := by
    rw [ha]; simpa [negativePart] using max_eq_left hs
  have hnA' : negativePart (Source.aError C atG+PairedE.cycleTotal C de eh)=
      s-PairedE.cycleTotal C de eh := by
    rw [ha]
    dsimp [negativePart]
    rw [max_eq_left (show 0≤ -(-s+PairedE.cycleTotal C de eh) by linarith [he.2])]
    ring
  rw [hpA,hpA'] at hp
  rw [hnA,hnA'] at hn
  have hd := positive_sub_negative (PairedE.selected de (delta C.theta D))
  have hh := positive_sub_negative (PairedE.selected eh (delta C.theta E))
  have heid : PairedE.cycleTotal C de eh=
      PairedE.selected de (delta C.theta D)+PairedE.selected eh (delta C.theta E) := rfl
  change positiveVariation (reference C atG de eh).theta=
    positiveVariation C.theta-0+0-_-_ at hp
  change negativeVariation (reference C atG de eh).theta=
    negativeVariation C.theta-s+(s-PairedE.cycleTotal C de eh)-_-_ at hn
  exact ⟨by linarith,by linarith⟩

theorem reference_variation_le {C : SignedCycle} {s : ℝ} (atG de eh : Bool)
    (hs : 0≤ s) (ha : Source.aError C atG= -s)
    (he : PairedE.cycleTotal C de eh∈Icc 0 s)
    (hvar : positiveVariation C.theta≤frameCap) :
    positiveVariation (reference C atG de eh).theta≤frameCap := by
  rw [(reference_variations atG de eh hs ha he).1]
  have hd := negativePart_nonneg (PairedE.selected de (delta C.theta D))
  have hh := negativePart_nonneg (PairedE.selected eh (delta C.theta E))
  linarith [he.1]

def actualOwners (hg : Fin 4) (atG de eh : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,2,2,
    if de then 3 else 2,if eh then 1 else 0]

def actualStress (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool)
    (k l c x : ℝ) : ℝ :=
  demand C (Source.weights atG k l c x (delta C.theta T))-
    ∑i,work (force C (actualOwners hg atG de eh)
      (Source.weights atG k l c x (delta C.theta T)) i) (C.point i)

def gainCoefficient (C : SignedCycle) (atG : Bool) : ℝ :=
  if atG then (C.point A).y+1/2 else 1/2-(C.point A).y

/-- The comparison is made inside one weighted sum on the points of the cycle; no reference edge
needs to be feasible. -/
theorem stress_identity {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool)
    (k l c : ℝ) (hs : s∈Icc 0 frameCap)
    (ha : Source.aError C atG= -s) (hflat : (C.point A).a=7/12)
    (he : PairedE.cycleTotal C de eh∈Icc 0 s) :
    actualStress C hg atG de eh k l c (s-PairedE.cycleTotal C de eh)=
      Source.actualStress (reference C atG de eh) hg atG k l c
        (s-PairedE.cycleTotal C de eh)+
      l/Real.cos (s-PairedE.cycleTotal C de eh)*
        (gain (gainCoefficient C atG) s-
          gain (gainCoefficient C atG) (s-PairedE.cycleTotal C de eh))+
      PairedE.primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E) := by
  have hx : s-PairedE.cycleTotal C de eh∈Icc 0 frameCap :=
    ⟨by linarith [he.2],by linarith [he.1,hs.2]⟩
  have ha' := reference_aError atG de eh ha
  have hcos : Real.cos (s-PairedE.cycleTotal C de eh)≠0 :=
    (show 0<Real.cos (s-PairedE.cycleTotal C de eh) by
      linarith [(transport_trig hx).1]).ne'
  have hsub : -s+PairedE.cycleTotal C de eh= -(s-PairedE.cycleTotal C de eh) := by ring
  have hflat2 : (C.point 2).a=7/12 := hflat
  unfold actualStress Source.actualStress
  rw [←sum_force_work,←sum_force_work]
  simp only [reference_T,demand,Fin.sum_univ_seven]
  generalize hW : Source.weights atG k l c (s-PairedE.cycleTotal C de eh) (delta C.theta T)=W
  have hedge (i : Vertex) (j : Fin 4)
      (hd : delta (reference C atG de eh).theta i=delta C.theta i) :
      (reference C atG de eh).edge i j=C.edge i j := by
    unfold SignedCycle.edge
    rw [hd]
    rfl
  have hsame (i : Vertex) (hd : delta (reference C atG de eh).theta i=delta C.theta i)
      (ho : Source.owners hg atG i=actualOwners hg atG de eh i) :
      W i*edgeWidth (delta C.theta i)-W i*C.edge i (actualOwners hg atG de eh i)=
        W i*edgeWidth (delta (reference C atG de eh).theta i)-
          W i*(reference C atG de eh).edge i (Source.owners hg atG i) := by
    rw [hedge i _ hd,hd,ho]
  have h0 := hsame 0 (by rw [reference_delta]; rfl) (by simp [Source.owners,actualOwners])
  have h3 := hsame 3 (by rw [reference_delta]; rfl) (by simp [Source.owners,actualOwners])
  have h4 := hsame 4 (by rw [reference_delta]; rfl) (by simp [Source.owners,actualOwners])
  have hW5 : W 5=1 := by rw [←hW]; rfl
  have hW6 : W 6=1 := by rw [←hW]; rfl
  have h5 : W 5*edgeWidth (delta C.theta 5)-W 5*C.edge 5 (actualOwners hg atG de eh 5)=
      W 5*edgeWidth (delta (reference C atG de eh).theta 5)-
        W 5*(reference C atG de eh).edge 5 (Source.owners hg atG 5)+
      (if de then edgeWidth (delta C.theta 5)-1-((C.point 6).a*Real.sin (delta C.theta 5)+
        (C.point 6).y*(1-Real.cos (delta C.theta 5))) else 0) := by
    cases de
    · have hh := hsame 5 (by rw [reference_delta]; rfl) (by simp [Source.owners,actualOwners])
      rw [hh]
      simp
    · have hd5 : delta (reference C atG true eh).theta 5=0 := by rw [reference_delta]; rfl
      have e1 : C.edge 5 (actualOwners hg atG true eh 5)=(C.point 5).a+
          (C.point 6).a*Real.sin (delta C.theta 5)-(C.point 6).y*Real.cos (delta C.theta 5) := rfl
      have e2 : (reference C atG true eh).edge 5 (Source.owners hg atG 5)=
          (C.point 5).a*Real.cos (delta (reference C atG true eh).theta 5)-
            (C.point 5).y*Real.sin (delta (reference C atG true eh).theta 5)-(C.point 6).y := rfl
      rw [e1,e2,hd5,hW5]
      simp only [edgeWidth_zero,Real.cos_zero,Real.sin_zero,ite_true]
      ring
  have h6 : W 6*edgeWidth (delta C.theta 6)-W 6*C.edge 6 (actualOwners hg atG de eh 6)=
      W 6*edgeWidth (delta (reference C atG de eh).theta 6)-
        W 6*(reference C atG de eh).edge 6 (Source.owners hg atG 6)+
      (if eh then edgeWidth (delta C.theta 6)-1-((C.point 6).a*Real.sin (delta C.theta 6)+
        (C.point 6).y*(Real.cos (delta C.theta 6)-1)) else 0) := by
    cases eh
    · have hh := hsame 6 (by rw [reference_delta]; rfl) (by simp [Source.owners,actualOwners])
      rw [hh]
      simp
    · have hd6 : delta (reference C atG de true).theta 6=0 := by rw [reference_delta]; rfl
      have e1 : C.edge 6 (actualOwners hg atG de true 6)=(C.point 0).a+
          (C.point 6).a*Real.sin (delta C.theta 6)+(C.point 6).y*Real.cos (delta C.theta 6) := rfl
      have e2 : (reference C atG de true).edge 6 (Source.owners hg atG 6)=
          (C.point 6).y+(C.point 0).a*Real.cos (delta (reference C atG de true).theta 6)+
            (C.point 0).y*Real.sin (delta (reference C atG de true).theta 6) := rfl
      rw [e1,e2,hd6,hW6]
      simp only [edgeWidth_zero,Real.cos_zero,Real.sin_zero,ite_true]
      ring
  have hpg : PairedE.primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E)=
      (if de then edgeWidth (delta C.theta 5)-1-((C.point 6).a*Real.sin (delta C.theta 5)+
        (C.point 6).y*(1-Real.cos (delta C.theta 5))) else 0)+
      (if eh then edgeWidth (delta C.theta 6)-1-((C.point 6).a*Real.sin (delta C.theta 6)+
        (C.point 6).y*(Real.cos (delta C.theta 6)-1)) else 0) := rfl
  rw [hpg]
  cases atG
  · have h1 := hsame 1 (by rw [reference_delta]; show delta C.theta G+0=_; rw [add_zero]; rfl)
      (by simp [Source.owners,actualOwners])
    have ha2 : delta C.theta 2= -s := ha
    have hd2 : delta (reference C false de eh).theta 2= -(s-PairedE.cycleTotal C de eh) := ha'
    have hW2 : W 2=l/Real.cos (s-PairedE.cycleTotal C de eh) := by rw [←hW]; rfl
    have e1 : C.edge 2 (actualOwners hg false de eh 2)=(C.point 2).a*Real.sin (delta C.theta 2)+
        (C.point 2).y*Real.cos (delta C.theta 2)-(C.point 3).y := rfl
    have e2 : (reference C false de eh).edge 2 (Source.owners hg false 2)=
        (C.point 2).a*Real.sin (delta (reference C false de eh).theta 2)+
          (C.point 2).y*Real.cos (delta (reference C false de eh).theta 2)-(C.point 3).y := rfl
    have hgc : gainCoefficient C false=1/2-(C.point 2).y := rfl
    have h2 : W 2*edgeWidth (delta C.theta 2)-W 2*C.edge 2 (actualOwners hg false de eh 2)=
        W 2*edgeWidth (delta (reference C false de eh).theta 2)-
          W 2*(reference C false de eh).edge 2 (Source.owners hg false 2)+
        l/Real.cos (s-PairedE.cycleTotal C de eh)*
          (gain (gainCoefficient C false) s-
            gain (gainCoefficient C false) (s-PairedE.cycleTotal C de eh)) := by
      rw [e1,e2,hd2,ha2,hW2,hgc,edgeWidth_negative_formula hs,edgeWidth_negative_formula hx,
        Real.sin_neg,Real.cos_neg,Real.sin_neg,Real.cos_neg,hflat2]
      unfold gain
      ring
    linear_combination h0+h1+h2+h3+h4+h5+h6
  · have h2 := hsame 2 (by rw [reference_delta]; show delta C.theta A+0=_; rw [add_zero]; rfl)
      (by simp [Source.owners,actualOwners])
    have ha1 : delta C.theta 1= -s := ha
    have hd1 : delta (reference C true de eh).theta 1= -(s-PairedE.cycleTotal C de eh) := ha'
    have hW1 : W 1=l/Real.cos (s-PairedE.cycleTotal C de eh) := by rw [←hW]; rfl
    have e1 : C.edge 1 (actualOwners hg true de eh 1)=(C.point 1).a+
        (C.point 2).a*Real.sin (delta C.theta 1)-(C.point 2).y*Real.cos (delta C.theta 1) := rfl
    have e2 : (reference C true de eh).edge 1 (Source.owners hg true 1)=(C.point 1).a+
        (C.point 2).a*Real.sin (delta (reference C true de eh).theta 1)-
          (C.point 2).y*Real.cos (delta (reference C true de eh).theta 1) := rfl
    have hgc : gainCoefficient C true=(C.point 2).y+1/2 := rfl
    have h1 : W 1*edgeWidth (delta C.theta 1)-W 1*C.edge 1 (actualOwners hg true de eh 1)=
        W 1*edgeWidth (delta (reference C true de eh).theta 1)-
          W 1*(reference C true de eh).edge 1 (Source.owners hg true 1)+
        l/Real.cos (s-PairedE.cycleTotal C de eh)*
          (gain (gainCoefficient C true) s-
            gain (gainCoefficient C true) (s-PairedE.cycleTotal C de eh)) := by
      rw [e1,e2,hd1,ha1,hW1,hgc,edgeWidth_negative_formula hs,edgeWidth_negative_formula hx,
        Real.sin_neg,Real.cos_neg,Real.sin_neg,Real.cos_neg,hflat2]
      unfold gain
      ring
    linear_combination h0+h1+h2+h3+h4+h5+h6

theorem actual_stress_nonpositive {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) {k l c x : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c)
    (hx : x∈Icc 0 frameCap) (hz : delta C.theta T∈Icc 0 frameCap)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) :
    actualStress C hg atG de eh k l c x≤0 := by
  have hf (i : Vertex) : C.Feasible i (actualOwners hg atG de eh i) := by
    fin_cases i
    · simpa [actualOwners,H] using hHG
    · simpa [actualOwners,G] using hGA
    · simpa [actualOwners,A] using hAB
    · simpa [actualOwners,B] using hBT
    · simpa [actualOwners,T] using hTD
    · simpa [actualOwners,D] using hDE
    · simpa [actualOwners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation
    (Source.weights_nonnegative atG hk hl hc hx hz) hf)

end SquaresInCircles.Eight.GlobalGA.NegativeA.ShortE
