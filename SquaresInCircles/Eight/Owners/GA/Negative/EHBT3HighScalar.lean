module

public import SquaresInCircles.Eight.Frames.Ordinary.ShortSecantGrowth
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedPositive
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Source
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3HighSplit
public import SquaresInCircles.Eight.Owners.GA.Negative.Primary.Stress
public import SquaresInCircles.Eight.Owners.GA.Paired.ECharge

/-!
# Eight squares: both complete high-total EH1/BT3 scalar exclusions

Every original A/BT split is included.
The actual EH magnitude is reduced by concavity only after all common
mass has been paid. The fourth negative alternative is compared with H
using its actual moving coefficient. The result has only the two signed
budgets and their exact balance as mass hypotheses.
-/

section
/-!
## The algebraic shorter-E reference vector

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
end
end
end

section
/-!
## The actual single-negative-A / shorter-E exclusion

Both original A
owners, all four selected E-owner choices, and both TD weight families
are dispatched here. The positive reference stress is used only as an
algebraic comparison; every feasibility premise concerns the actual cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.ShortE
open Candidate Secondary SignedStress
open NegativeAPositiveTD
open Certificate (Family)

theorem family_minimum_L (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    minimumL≤Explicit.l f z := by
  cases f
  · have hz' : z∈Icc 0 (1/5:ℝ) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
      exact ⟨hz.1,by linarith [hz.2]⟩
    exact (Explicit.low_ranges hz').2.2.1.le
  · have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split,
        PositiveTD.Certificate.h] at hz
      exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
    have hh := (Explicit.high_ranges hz').2.2.1
    dsimp [minimumL]
    linarith

theorem gain_coefficient_bounds {q s : ℝ} {C : SignedCycle} (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hBy : (C.point B).y≤0)
    (hAy : 0≤(C.point A).y)
    (hcut : (C.point A).y≤ if atG then 39/250 else 1/2)
    (hflat : (C.point A).a=7/12) (hs : s∈Icc 0 frameCap)
    (ha : Source.aError C atG= -s)
    (hAB : C.Feasible A (if atG then 0 else 2)) :
    gainCoefficient C atG∈Icc 0 (capB atG) := by
  cases atG
  · have hAB' : zeroFeasible (C.point A) (C.point B) (-s) 2 := by
      change delta C.theta A= -s at ha
      have h : 0≤zeroProjection (C.point A) (C.point B) (delta C.theta A) 2-
          edgeWidth (delta C.theta A) := hAB
      rw [ha] at h
      exact sub_nonneg.mp h
    have hl := AB_tangent_lower (hsorted B) (hcontained B) hq hBy hAy hflat hs hAB'
    simp only [Bool.false_eq_true,ite_false] at hcut
    simp only [gainCoefficient,capB,Bool.false_eq_true,ite_false]
    exact ⟨by linarith,by linarith⟩
  · simp only [ite_true] at hcut
    simp only [gainCoefficient,capB,ite_true]
    exact ⟨by linarith,by linarith⟩

/-- The whole original necessary cycle is contradictory when the selected
signed E total lies between zero and the single negative A magnitude. -/
theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : Source.aError C atG= -s)
    (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (hcut : (C.point A).y≤ if atG then 39/250 else 1/2)
    (he : PairedE.cycleTotal C de eh∈Icc 0 s)
    (hz : 0≤delta C.theta T) (hhg : hg=0∨hg=2)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  let e := PairedE.cycleTotal C de eh
  let x := s-e
  let C' := reference C atG de eh
  have hsframe := (Explicit.angle_domain atG hs).2
  have hxcut : x∈Icc 0 (Explicit.angleCut atG) :=
    ⟨by dsimp [x,e]; linarith [he.2],by dsimp [x,e]; linarith [he.1,hs.2]⟩
  have hxframe := (Explicit.angle_domain atG hxcut).2
  have hrefvar := reference_variation_le atG de eh hs.1 ha he hvar
  have hrefa := reference_aError atG de eh ha
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hzframe : delta C.theta T∈Icc 0 frameCap :=
    ⟨hz,(le_abs_self _).trans (original_error_bound hvar hn T)⟩
  have heframe := PairedE.cycle_total_bounds de eh hvar he.1
  have hB := gain_coefficient_bounds atG hsorted hcontained hq hBy hAy hcut
    hflat hsframe ha hAB
  have hE := PairedE.selected_charge de eh (hsorted E) (hcontained E) hq
    (original_error_bound hvar hn D) (original_error_bound hvar hn E) heframe
  change TwoPositive.ASupport.charge (PairedE.cycleTotal C de eh)≤
    PairedE.primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E) at hE
  have hfamily (f : Family)
      (hf : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) : False := by
    let k := Explicit.k f (delta C.theta T)
    let l := Explicit.l f (delta C.theta T)
    let c := Explicit.c f (delta C.theta T)
    have hp : 0<Source.actualStress C' hg atG k l c x := by
      have hh := Source.family_stress_positive (C:=C') f atG
        (by intro i; exact hsorted i) (by intro i; exact hcontained i) hq
        hHy hGy hBy hDy hrefvar hxcut hrefa hflat
        (by simpa [C'] using hf) hhg
      simpa only [C',reference_T] using hh
    have hgain := transfer atG hB hs he (family_minimum_L f hf)
    have hid := stress_identity hg atG de eh k l c hsframe ha hflat he
    have hcomp : Source.actualStress C' hg atG k l c x≤
        actualStress C hg atG de eh k l c x := by
      dsimp [C',x,e]
      rw [hid]
      change 0≤Explicit.l f (delta C.theta T)/Real.cos (s-PairedE.cycleTotal C de eh)*
        (gain (gainCoefficient C atG) s-gain (gainCoefficient C atG)
          (s-PairedE.cycleTotal C de eh))+
        TwoPositive.ASupport.charge (PairedE.cycleTotal C de eh) at hgain
      dsimp [l]
      linarith only [hgain,hE]
    have hpos := Explicit.family_positive f hf
    have hnp := actual_stress_nonpositive atG de eh hpos.1.le hpos.2.1.le
      hpos.2.2.1 hxframe hzframe hHG hGA hAB hBT hTD hDE hEH
    exact (not_le_of_gt (hp.trans_le hcomp)) hnp
  by_cases hlow : delta C.theta T≤1/5
  · exact hfamily .low ⟨by norm_num [Certificate.left]; exact hz,
      by norm_num [Certificate.right,Certificate.split]; exact hlow⟩
  · have hz2 := hzframe.2
    simp only [frameCap] at hz2
    exact hfamily .high ⟨by norm_num [Certificate.left,Certificate.split]; linarith,
      by norm_num [Certificate.right,PositiveTD.Certificate.h]; exact hz2⟩

end SquaresInCircles.Eight.GlobalGA.NegativeA.ShortE
end
end
end

section
/-!
## Removing all common signed mass in both high-total EH1/BT3 families

The four actual ordinary blocks remain
separate throughout concentration. Small-high uses the original common
coefficient scale; far-high uses the .6 bound on total negative mass.
The far EH charge is paid by the same-block reserve and the separated
negative-slope reserve, not dropped after concentrating the masses.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.HighMass
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope

lemma reduce_negative (f : Family) {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hpair : ∀i,0<Blocks.p f θ z i ∧ Blocks.p f θ z i≤Blocks.q f θ z i ∧
      Blocks.q f θ z i≤2*Blocks.p f θ z i)
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc 0 θ)
    (hsame : ∀i,Blocks.negative f θ z (θ-s) i≤
      Blocks.block f θ z (frameCap-θ) (frameCap-s) i)
    (hsep : ∀i j,Blocks.negative f θ z (θ-s) j≤
      Blocks.positive f θ z (frameCap-θ) i+Blocks.negative f θ z (frameCap-s) j)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j,Blocks.negative f θ z (θ-s) j≤∑i,Blocks.block f θ z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate f P N hpair hθ ⟨hs.1,hs.2.trans hθ.2⟩
    hP hN hPb hNb hbalance
  have hsat : Blocks.negative f θ z (θ-s) j≤Blocks.saturated f θ z s i j := by
    by_cases he : i=j
    · subst j
      simpa only [Blocks.saturated,ChargedOrdinaryConcentration.saturated,↓reduceIte,
        Blocks.block] using hsame i
    · simpa only [Blocks.saturated,ChargedOrdinaryConcentration.saturated,ite_eq_right he,
        Blocks.positive,Blocks.negative] using hsep i j
  have hpure : Blocks.pure f θ z s i j=Blocks.negative f θ z (θ-s) j := by
    simp only [Blocks.pure,ChargedOrdinaryConcentration.pure,ite_eq_left hs.2,Blocks.negative]
  rw [hpure,min_eq_left hsat] at hij
  exact ⟨j,hij⟩

lemma small_high_same {θ z P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i : Fin 4) :
    Blocks.negative .smallHigh θ z (N-P) i≤Blocks.block .smallHigh θ z P N i := by
  have hp := Blocks.small_high_pairs hθ hz i
  have hNc : N∈Icc 0 frameCap := ⟨hP.trans hPN,hN⟩
  have hq : 0≤Blocks.q .smallHigh θ z i := (hp.1.trans_le hp.2.1).le
  have hsin := mul_le_mul_of_nonneg_left (transport_trig hNc).2.2.2.1.le hq
  have hsine : Blocks.q .smallHigh θ z i*Real.sin N≤Blocks.p .smallHigh θ z i := by
    nlinarith [hp.2.2]
  have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le ⟨hP,hPN⟩ hNc hsine
  simpa only [Blocks.block,Blocks.negative,ChargedOrdinaryConcentration.block,
    epsilon,far,Bool.false_eq_true,ite_false,zero_mul,sub_zero] using hh

lemma small_high_separated {θ z P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i j : Fin 4) :
    Blocks.negative .smallHigh θ z (N-P) j≤
      Blocks.positive .smallHigh θ z P i+Blocks.negative .smallHigh θ z N j := by
  have hi := Blocks.small_high_pairs hθ hz i
  have hj := Blocks.small_high_pairs hθ hz j
  have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
    hi.1 hi.2.1 (by linarith [hi.1,hi.2.2]) ⟨hP,hPN.trans hN⟩
  have hv := V_growth hj.1 hj.2.1 hj.2.2
    (show N-P∈Icc 0 frameCap from ⟨by linarith,by linarith⟩)
    (show N∈Icc 0 frameCap from ⟨hP.trans hPN,hN⟩) (by linarith)
  have hscalei := Blocks.small_high_scale hθ hz i
  have hscalej := Blocks.small_high_scale hθ hz j
  have hq : 0<Blocks.q .smallHigh θ z j := hj.1.trans_le hj.2.1
  have hmargin : 0≤(2/3)*Blocks.q .smallHigh θ z j-
      (109/200)*Blocks.q .smallHigh θ z i := by linarith
  have hpay := mul_nonneg hmargin hP
  simp only [Blocks.positive,Blocks.negative,ChargedOrdinaryConcentration.positive,
    epsilon,far,Bool.false_eq_true,ite_false,zero_mul,sub_zero]
  nlinarith only [hu,hv,hpay]

lemma small_high_to_negative {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (hs : s∈Icc (0:ℝ) (1/10))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j,Blocks.negative .smallHigh θ z (θ-s) j≤∑i,Blocks.block .smallHigh θ z (P i) (N i) i := by
  have ht : θ∈Icc 0 frameCap := ⟨by linarith [hθ.1],by simpa [frameCap] using hθ.2⟩
  have he : s≤θ := by linarith [hs.2,hθ.1]
  have hPc : 0≤frameCap-θ := by linarith [ht.2]
  have hPN : frameCap-θ≤frameCap-s := by linarith
  have hNc : frameCap-s≤frameCap := by linarith [hs.1]
  apply reduce_negative .smallHigh P N
    (fun i => ⟨(Blocks.small_high_pairs hθ hz i).1,(Blocks.small_high_pairs hθ hz i).2.1,
      by linarith [(Blocks.small_high_pairs hθ hz i).1,(Blocks.small_high_pairs hθ hz i).2.2]⟩)
    ht ⟨hs.1,he⟩
  · intro i
    simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using
      small_high_same hθ hz hPc hPN hNc i
  · intro i j
    simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using
      small_high_separated hθ hz hPc hPN hNc i j
  all_goals assumption

lemma far_high_positive_lower {θ z P : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : P∈Icc 0 frameCap) (i : Fin 4) :
    -(11/20)*P≤Blocks.positive .farHigh θ z P i := by
  have hp := Blocks.far_high_pairs hθ hz i
  have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
    (show 0<Blocks.p .farHigh θ z i by linarith [hp.1]) hp.2.1
    (show Blocks.q .farHigh θ z i≤2*Blocks.p .farHigh θ z i by linarith [hp.1,hp.2.2.1]) hP
  have hq := mul_le_mul_of_nonneg_right hp.2.2.2 hP.1
  simp only [Blocks.positive,ChargedOrdinaryConcentration.positive,epsilon,far,ite_true]
  nlinarith only [hh,hq]

lemma far_high_same {θ z P N : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) (i : Fin 4) :
    Blocks.negative .farHigh θ z (N-P) i≤Blocks.block .farHigh θ z P N i := by
  have hp := Blocks.far_high_pairs hθ hz i
  have hh := OrdinaryNegativeShortSlope.same_reserve (R:=R) hp.1 hp.2.2.1 hP hPN hN
  simp only [Blocks.block,Blocks.negative,ChargedOrdinaryConcentration.block,epsilon,far,ite_true]
  linarith

lemma far_high_separated {θ z P N : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) (i j : Fin 4) :
    Blocks.negative .farHigh θ z (N-P) j≤
      Blocks.positive .farHigh θ z P i+Blocks.negative .farHigh θ z N j := by
  have hp := Blocks.far_high_pairs hθ hz j
  have hu := far_high_positive_lower hθ hz
    (show P∈Icc 0 frameCap from ⟨hP,by norm_num [frameCap]; linarith⟩) i
  have hv := OrdinaryNegativeShortSlope.V_growth
    (show 0<Blocks.p .farHigh θ z j by linarith [hp.1]) hp.2.1
    (show (3/5)*Blocks.q .farHigh θ z j≤Blocks.p .farHigh θ z j by linarith [hp.2.2.1])
    (show N-P∈OrdinaryNegativeShortSlope.domain from ⟨by linarith,by linarith⟩)
    (show N∈OrdinaryNegativeShortSlope.domain from ⟨hP.trans hPN,hN⟩) (by linarith)
  have hpay := mul_nonneg (sub_nonneg.mpr hp.1) hP
  dsimp [Blocks.negative]
  nlinarith only [hu,hv,hpay,hP]

lemma far_high_to_negative {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (hz : z∈Icc 0 θ) (hs : s∈Icc (1/10:ℝ) (1/4))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j,Blocks.negative .farHigh θ z (θ-s) j≤∑i,Blocks.block .farHigh θ z (P i) (N i) i := by
  have ht : θ∈Icc 0 frameCap := ⟨by linarith [hθ.1],by simpa [frameCap] using hθ.2⟩
  have he : s≤θ := by linarith [hs.2,hθ.1]
  have hPc : 0≤frameCap-θ := by linarith [ht.2]
  have hPN : frameCap-θ≤frameCap-s := by linarith
  have hNc : frameCap-s≤3/5 := by norm_num [frameCap]; linarith [hs.1]
  apply reduce_negative .farHigh P N
    (fun i => ⟨by linarith [(Blocks.far_high_pairs hθ hz i).1],
      (Blocks.far_high_pairs hθ hz i).2.1,
      by linarith [(Blocks.far_high_pairs hθ hz i).1,(Blocks.far_high_pairs hθ hz i).2.2.1]⟩)
    ht ⟨by linarith [hs.1],he⟩
  · intro i
    simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using
      far_high_same hθ hz hPc hPN hNc i
  · intro i j
    simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using
      far_high_separated hθ hz hPc hPN hNc i j
  all_goals assumption

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.HighMass
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.HighScalar
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

@[simp] lemma charge_small_high (s : ℝ) : charge .smallHigh s=NegativeEH.g s := by
  dsimp [charge,far,gain,NegativeEH.g,NegativeEH.K,NegativeEH.beta]

@[simp] lemma charge_far_high (s : ℝ) : charge .farHigh s=NegativeEH.G s := by
  dsimp [charge,far,gain,NegativeEH.G,NegativeEH.g,NegativeEH.K,NegativeEH.beta,NegativeEH.p]

private lemma r76_ordinaryP_eq (f : Family) (θ z : ℝ) (i : Fin 3) :
    Blocks.ordinaryP f θ i=Blocks.p f θ z i.castSucc := by
  fin_cases i <;> rfl

private lemma r76_ordinaryQ_eq (f : Family) (θ z : ℝ) (i : Fin 3) :
    Blocks.ordinaryQ f θ i=Blocks.q f θ z i.castSucc := by
  fin_cases i <;> rfl

lemma small_high_ordinary_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 3) :
    0<baseline .smallHigh (a+z) a z+charge .smallHigh s+
      Blocks.ordinaryV .smallHigh (a+z) i (a+z-s) := by
  have hp := Blocks.small_high_pairs hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) i.castSucc
  have hpi : 0<Blocks.ordinaryP .smallHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z]; exact hp.1
  have hpq : Blocks.ordinaryP .smallHigh (a+z) i≤Blocks.ordinaryQ .smallHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z,r76_ordinaryQ_eq _ _ z]; exact hp.2.1
  have hqp : Blocks.ordinaryQ .smallHigh (a+z) i≤2*Blocks.ordinaryP .smallHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z,r76_ordinaryQ_eq _ _ z]
    linarith [hp.1,hp.2.2]
  have hg := NegativeEH.g_concave.subset
    (Icc_subset_Icc le_rfl (by norm_num [frameCap] : (1/10:ℝ)≤frameCap))
    (convex_Icc 0 (1/10:ℝ))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hpi hpq hqp)
    (a:=-1) (b:=a+z) (l:=0) (u:=1/10)
    (fun t ht => ⟨by linarith [ht.2,hθ.1],
      by norm_num [frameCap]; linarith [ht.1,hθ.2]⟩)
  have hc : ConcaveOn ℝ (Icc 0 (1/10)) (fun s => baseline .smallHigh (a+z) a z+
      charge .smallHigh s+Blocks.ordinaryV .smallHigh (a+z) i (a+z-s)) := by
    refine ((hg.add hv).add_const (baseline .smallHigh (a+z) a z)).congr ?_
    intro t _
    simp only [Pi.add_apply,neg_one_mul,neg_add_eq_sub,charge_small_high,Blocks.ordinaryV]
    ring
  have h0 := HighSplit.small_high_zero hθ ha hz i
  have h1 := HighSplit.small_high_cut hθ ha hz i
  have h0' : 0<baseline .smallHigh (a+z) a z+charge .smallHigh 0+
      Blocks.ordinaryV .smallHigh (a+z) i (a+z-0) := by
    simpa [NegativeEH.g] using h0
  have hh := concave_gt_of_endpoints hc ⟨hs.1,hs.2⟩ h0' h1
  exact hh

lemma far_high_ordinary_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (i : Fin 3) :
    0<baseline .farHigh (a+z) a z+charge .farHigh s+
      Blocks.ordinaryV .farHigh (a+z) i (a+z-s) := by
  have hp := Blocks.far_high_pairs hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) i.castSucc
  have hpi : 0<Blocks.ordinaryP .farHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z]
    linarith [hp.1]
  have hpq : Blocks.ordinaryP .farHigh (a+z) i≤Blocks.ordinaryQ .farHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z,r76_ordinaryQ_eq _ _ z]; exact hp.2.1
  have hqp : Blocks.ordinaryQ .farHigh (a+z) i≤2*Blocks.ordinaryP .farHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z,r76_ordinaryQ_eq _ _ z]
    linarith [hp.1,hp.2.2.1]
  have hg := NegativeEH.G_concave.subset
    (Icc_subset_Icc (by norm_num : (0:ℝ)≤1/10)
      (by norm_num [frameCap] : (1/4:ℝ)≤frameCap)) (convex_Icc (1/10:ℝ) (1/4))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hpi hpq hqp)
    (a:=-1) (b:=a+z) (l:=1/10) (u:=1/4)
    (fun t ht => ⟨by linarith [ht.2,hθ.1],
      by norm_num [frameCap]; linarith [ht.1,hθ.2]⟩)
  have hc : ConcaveOn ℝ (Icc (1/10) (1/4)) (fun s => baseline .farHigh (a+z) a z+
      charge .farHigh s+Blocks.ordinaryV .farHigh (a+z) i (a+z-s)) := by
    refine ((hg.add hv).add_const (baseline .farHigh (a+z) a z)).congr ?_
    intro t _
    simp only [Pi.add_apply,neg_one_mul,neg_add_eq_sub,charge_far_high,Blocks.ordinaryV]
    ring
  have h0 := HighSplit.far_high_cut false hθ ha hz i
  have h1 := HighSplit.far_high_cut true hθ ha hz i
  simp only [Bool.false_eq_true,↓reduceIte] at h0 h1
  have hh := concave_gt_of_endpoints hc ⟨hs.1,hs.2⟩ h0 h1
  exact hh

lemma small_high_D_lower {θ z t : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Blocks.ordinaryV .smallHigh θ 0 t≤Blocks.negative .smallHigh θ z t 3 := by
  have hd := Blocks.small_high_domain hθ
  have hb := NonnegativeTotals.Explicit.base_bounds .triangle hd
  have hz' : z∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (θ-1/6) 0) := by
    simpa [NonnegativeTotals.Explicit.theta] using hz
  have hh := Blocks.D_redundant
    (k:=NonnegativeTotals.Explicit.k .triangle (θ-1/6) 0)
    (c:=NonnegativeTotals.Explicit.tilted .triangle (θ-1/6) 0 z)
    ⟨by linarith [hb.k_lower],by linarith [hb.k_upper]⟩
    (NonnegativeTotals.Explicit.tilted_lower .triangle hd hz').le
    (NonnegativeTotals.Explicit.tilted_upper .triangle hd hz').le ht
  simpa [Blocks.ordinaryV,Blocks.ordinaryP,Blocks.ordinaryQ,Blocks.negative,
    Blocks.p,Blocks.q,PositiveBT3.pWeights,PositiveBT3.qWeights,
    Explicit.k,Explicit.l,Explicit.m,Explicit.c,L,
    NonnegativeTotals.Explicit.k,NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,
    NonnegativeTotals.Explicit.tilted,NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted] using hh

lemma far_high_D_lower {θ z t : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Blocks.ordinaryV .farHigh θ 0 t≤Blocks.negative .farHigh θ z t 3 := by
  have hr := NegativeEHPositiveTD.Explicit.far_high_ranges hθ
  have hc := NegativeEHPositiveTD.Explicit.far_high_tilted hθ hz
  have hkc : Explicit.k .farHigh θ≤Explicit.c .farHigh θ z :=
    (lt_min_iff.mp hc.2.2.1).2.le
  have hc1 : Explicit.c .farHigh θ z<1 := (max_lt_iff.mp hc.2.2.2.1).2
  have hh := Blocks.D_redundant (k:=Explicit.k .farHigh θ) (c:=Explicit.c .farHigh θ z)
    ⟨by change 0<NegativeEHPositiveTD.Explicit.k .far .high θ; linarith [hr.1.1],
      by change NegativeEHPositiveTD.Explicit.k .far .high θ≤1; linarith [hr.1.2]⟩
    hkc (by linarith) ht
  exact hh

lemma small_high_pure_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 4) :
    0<baseline .smallHigh (a+z) a z+charge .smallHigh s+
      Blocks.negative .smallHigh (a+z) z (a+z-s) i := by
  fin_cases i
  · exact small_high_ordinary_positive hθ ha hz hs 0
  · exact small_high_ordinary_positive hθ ha hz hs 1
  · exact small_high_ordinary_positive hθ ha hz hs 2
  · have hcmp := small_high_D_lower hθ ⟨hz,by linarith⟩
      (show a+z-s∈Icc 0 frameCap from ⟨by linarith [hθ.1,hs.2],
        by norm_num [frameCap]; linarith [hθ.2,hs.1]⟩)
    exact (small_high_ordinary_positive hθ ha hz hs 0).trans_le (add_le_add le_rfl hcmp)

lemma far_high_pure_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (i : Fin 4) :
    0<baseline .farHigh (a+z) a z+charge .farHigh s+
      Blocks.negative .farHigh (a+z) z (a+z-s) i := by
  fin_cases i
  · exact far_high_ordinary_positive hθ ha hz hs 0
  · exact far_high_ordinary_positive hθ ha hz hs 1
  · exact far_high_ordinary_positive hθ ha hz hs 2
  · have hcmp := far_high_D_lower hθ ⟨hz,by linarith⟩
      (show a+z-s∈Icc 0 frameCap from ⟨by linarith [hθ.1,hs.2],
        by norm_num [frameCap]; linarith [hθ.2,hs.1]⟩)
    exact (far_high_ordinary_positive hθ ha hz hs 0).trans_le (add_le_add le_rfl hcmp)

/-- The entire small-EH, high-total allocation domain. -/

theorem small_high_scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<baseline .smallHigh (a+z) a z+charge .smallHigh s+
      ∑i,Blocks.block .smallHigh (a+z) z (P i) (N i) i := by
  obtain ⟨i,hi⟩ := HighMass.small_high_to_negative P N hθ ⟨hz,by linarith⟩ hs
    hP hN hPb hNb hbalance
  have hh := small_high_pure_positive hθ ha hz hs i
  linarith

/-- The entire far-EH, high-total allocation domain, including the .005 charge. -/
theorem far_high_scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<baseline .farHigh (a+z) a z+charge .farHigh s+
      ∑i,Blocks.block .farHigh (a+z) z (P i) (N i) i := by
  obtain ⟨i,hi⟩ := HighMass.far_high_to_negative P N hθ ⟨hz,by linarith⟩ hs
    hP hN hPb hNb hbalance
  have hh := far_high_pure_positive hθ ha hz hs i
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.HighScalar
end
end
end
