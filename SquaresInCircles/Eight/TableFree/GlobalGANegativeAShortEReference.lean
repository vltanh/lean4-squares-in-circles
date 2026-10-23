module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAShortEComparison

/-!
# The algebraic shorter-E reference vector

Uncompiled transcription of Section 4 of the shorter-E hand proof. The
reference keeps every point and replaces only angular arguments inside a
weighted sum. No reference edge is asserted to be a separating witness.
The deleted selected E errors may have opposite individual signs.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.ShortE
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
  cases atG <;> simp only [Source.aError,Bool.false_eq_true,if_false,if_true] at ha ⊢
  · rw [reference_delta]
    simp [A]
    linarith
  · rw [reference_delta]
    simp [G]
    linarith

/-- Exact deletion identity, before imposing any sign on an error. -/
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
    (hs : 0≤s) (ha : Source.aError C atG= -s)
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
    (hs : 0≤s) (ha : Source.aError C atG= -s)
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

/-- The exact comparison is inside one weighted sum on the original
points. In particular, this theorem asserts no feasible reference edge. -/
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
  have hsub : -s+PairedE.cycleTotal C de eh= -(s-PairedE.cycleTotal C de eh) := by ring
  have hcos : Real.cos (s-PairedE.cycleTotal C de eh)≠0 :=
    (show 0<Real.cos (s-PairedE.cycleTotal C de eh) by
      linarith [(transport_trig hx).1]).ne'
  unfold actualStress Source.actualStress
  rw [←sum_force_work,←sum_force_work]
  simp only [reference_T]
  cases atG <;> cases de <;> cases eh <;>
    simp only [Source.aError,Bool.false_eq_true,if_false,if_true] at ha ha' <;>
    simp [demand,Source.weights,actualOwners,Source.owners,Fin.sum_univ_succ,
      SignedCycle.edge,word,zeroProjection,quarterProjection,reference_delta,
      reference_point,lambdaG,lambdaB,secant,gainCoefficient,gain,PairedE.primaryGain,
      NegativePrimary.erase,H,G,A,B,T,D,E,ha,ha',hflat,hsub,
      edgeWidth_negative_formula hs,edgeWidth_negative_formula hx,
      Real.sin_neg,Real.cos_neg] <;>
    field_simp [hcos] <;> ring

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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.ShortE
