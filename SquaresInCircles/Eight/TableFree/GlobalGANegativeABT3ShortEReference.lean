module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3OriginalStress
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAShortESource

/-!
# Comparing the shorter-E BT3 cycle with its algebraic reference

Uncompiled Section 9. The reference changes only angular arguments in
one weighted sum, retaining the actual BT3 and TD0 errors. Every point
and the rotating TD0 coefficient remain unchanged. The exact difference
is the already proved common A gain plus the actual selected E gain.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.ShortE
open Candidate Secondary SignedStress

abbrev reference := NegativeA.ShortE.reference
abbrev gainCoefficient := NegativeA.ShortE.gainCoefficient
abbrev gain := NegativeA.ShortE.gain

@[simp] theorem reference_B (C : SignedCycle) (atG de eh : Bool) :
    delta (reference C atG de eh).theta B=delta C.theta B := by
  simpa [B] using NegativeA.ShortE.reference_delta C atG de eh B

def actualOwners (hg : Fin 4) (atG de eh : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,3,0,
    if de then 3 else 2,if eh then 1 else 0]

def actualStress (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l m x : ℝ) : ℝ :=
  demand C (Source.weights atG k l m x (delta C.theta B))-
    ∑i,work (force C (actualOwners hg atG de eh)
      (Source.weights atG k l m x (delta C.theta B)) i) (C.point i)

theorem stress_identity {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool)
    (k l m : ℝ) (hs : s∈Icc 0 frameCap)
    (ha : Source.aError C atG= -s) (hflat : (C.point A).a=7/12)
    (he : PairedE.cycleTotal C de eh∈Icc 0 s) :
    actualStress C hg atG de eh k l m (s-PairedE.cycleTotal C de eh)=
      Source.actualStress (reference C atG de eh) hg atG k l m
        (s-PairedE.cycleTotal C de eh)+
      l/Real.cos (s-PairedE.cycleTotal C de eh)*
        (gain (gainCoefficient C atG) s-
          gain (gainCoefficient C atG) (s-PairedE.cycleTotal C de eh))+
      PairedE.primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E) := by
  have hx : s-PairedE.cycleTotal C de eh∈Icc 0 frameCap :=
    ⟨by linarith [he.2],by linarith [he.1,hs.2]⟩
  have ha' := NegativeA.ShortE.reference_aError atG de eh ha
  have hsub : -s+PairedE.cycleTotal C de eh= -(s-PairedE.cycleTotal C de eh) := by ring
  have hcos : Real.cos (s-PairedE.cycleTotal C de eh)≠0 :=
    (show 0<Real.cos (s-PairedE.cycleTotal C de eh) by
      linarith [(transport_trig hx).1]).ne'
  unfold actualStress Source.actualStress
  rw [←sum_force_work,←sum_force_work]
  simp only [reference_B]
  cases atG <;> cases de <;> cases eh <;>
    simp only [Source.aError,NegativeAPositiveTD.Source.aError,↓reduceIte] at ha ha' <;>
    simp [demand,Source.weights,actualOwners,Source.owners,Fin.sum_univ_succ,
      SignedCycle.edge,word,zeroProjection,quarterProjection,reference,
      NegativeA.ShortE.reference_delta,NegativeA.ShortE.reference_point,
      lambdaG,lambdaB,secant,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,
      NegativeAPositiveTD.secant,gainCoefficient,NegativeA.ShortE.gainCoefficient,
      gain,NegativeA.ShortE.gain,PairedE.primaryGain,NegativePrimary.erase,
      H,G,A,B,T,D,E,ha,ha',hflat,hsub,edgeWidth_negative_formula hs,
      edgeWidth_negative_formula hx,Real.sin_neg,Real.cos_neg] <;>
    field_simp [hcos] <;> ring

theorem actual_stress_nonpositive {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) {k l m x : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0<m)
    (hx : x∈Icc 0 frameCap) (hz : delta C.theta B∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) :
    actualStress C hg atG de eh k l m x≤0 := by
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
    (Source.weights_nonnegative atG hk hl hm hx hz) hf)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.ShortE
