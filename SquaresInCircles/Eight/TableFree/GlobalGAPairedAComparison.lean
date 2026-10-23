module

public import SquaresInCircles.Eight.TableFree.GlobalGAPairedACharge
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveAStress

/-!
# The paired-A virtual-zero comparison

Uncompiled transcription of Section 3 of the paired-A hand proof. The
comparison array puts both deleted A-edge arguments at their intrinsic
endpoint. It is used only to evaluate the already proved stress functions.
Individual feasible axes or boundary geometry for this array are neither
claimed nor needed. Every feasible separator in the theorem is original.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PairedA
open Candidate Secondary SignedStress

def total (C : SignedCycle) : ℝ := delta C.theta G+delta C.theta A

def comparison (C : SignedCycle) : SignedCycle :=
  ⟨Function.update C.point A ⟨(C.point A).a,|(C.point A).y|⟩,
    Function.update C.theta A (C.theta B)⟩

def owners (hg td : Fin 4) : Vertex→Fin 4 := ![hg,3,2,2,td,2,0]
def comparisonOwners (hg td : Fin 4) : Vertex→Fin 4 := ![hg,3,0,2,td,2,0]
def weights (k l b t : ℝ) : Vertex→ℝ := ![k,l,l,b,t,1,1]

def stress (C : SignedCycle) (owner : Vertex→Fin 4) (w : Vertex→ℝ) : ℝ :=
  demand C w-∑i,SignedStress.work (force C owner w i) (C.point i)

theorem comparison_points (C : SignedCycle) (i : Vertex) (hi : i≠A) :
    (comparison C).point i=C.point i := by
  simp [comparison,Function.update_of_ne hi]

@[simp] theorem comparison_a (C : SignedCycle) :
    TwoPositive.Source.aError (comparison C) true=total C := by
  simp [TwoPositive.Source.aError,comparison,total,delta,G,A,B,next,Function.update_apply]
  ring

@[simp] theorem comparison_T (C : SignedCycle) :
    delta (comparison C).theta T=delta C.theta T := by
  simp [comparison,delta,T,D,A,next,Function.update_apply]

theorem comparison_variations (C : SignedCycle) :
    positiveVariation (comparison C).theta≤positiveVariation C.theta ∧
      negativeVariation (comparison C).theta≤negativeVariation C.theta := by
  have hp := positivePart_add_le (delta C.theta G) (delta C.theta A)
  have hn := negativePart_add_le (delta C.theta G) (delta C.theta A)
  have he : delta C.theta G+delta C.theta A=C.theta B-C.theta G := by
    simp [delta,G,A,B,next]
    ring
  rw [he] at hp hn
  simp [positiveVariation,negativeVariation,comparison,Fin.sum_univ_succ,delta,next,
    H,G,A,B,T,D,E,Function.update_apply]
  constructor <;> linarith

theorem comparison_sorted {C : SignedCycle} (hs : ∀i,(C.point i).Sorted)
    (i : Vertex) : ((comparison C).point i).Sorted := by
  by_cases hi : i=A
  · subst i
    simpa [comparison,SignedPoint.Sorted,Function.update_apply] using hs A
  · rw [comparison_points C i hi]
    exact hs i

theorem comparison_contained {q : ℝ} {C : SignedCycle}
    (hc : ∀i,(C.point i).Contained q) (i : Vertex) :
    ((comparison C).point i).Contained q := by
  by_cases hi : i=A
  · subst i
    simpa [comparison,SignedPoint.Contained,SignedPoint.circle,Function.update_apply] using hc A
  · rw [comparison_points C i hi]
    exact hc i

theorem total_bounds {C : SignedCycle}
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤total C) :
    total C∈Icc 0 frameCap := by
  have hp := positive_error_le_variation (comparison C).theta G
  have hdelta : delta (comparison C).theta G=total C := by
    simpa only [TwoPositive.Source.aError,if_true] using comparison_a C
  rw [hdelta,show positivePart (total C)=total C by exact max_eq_left ha] at hp
  exact ⟨ha,hp.trans ((comparison_variations C).1.trans hvar)⟩

theorem stress_identity (C : SignedCycle) {hg td : Fin 4}
    (hhg : hg=0 ∨ hg=2) (htd : td=0 ∨ td=2) (k l b t : ℝ) :
    stress C (owners hg td) (weights k l b t)=
      stress (comparison C) (comparisonOwners hg td) (weights k l b t)+
        l*(PairedA.work (C.point A) (delta C.theta G) (delta C.theta A)-
          endpoint (C.point A).a |(C.point A).y| (total C)) := by
  have htotal : total C=C.theta B-C.theta G := by
    simp [total,delta,G,A,B,next]
    ring
  rcases hhg with rfl | rfl <;> rcases htd with rfl | rfl <;>
    simp [stress,comparison,owners,comparisonOwners,weights,PairedA.work,endpoint,htotal,
      demand,force,source,target,SignedStress.work,add,scale,previous,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,Function.update_apply,
      edgeWidth,pairWidth] <;> ring

/-- All axes here belong to the source. The conclusion is only a weighted
inequality for the virtual comparison array. -/
theorem comparison_stress_nonpos {q : ℝ} {C : SignedCycle} {hg td : Fin 4}
    {k l b t : ℝ} (hs : (C.point A).Sorted) (hc : (C.point A).Contained q)
    (hq : q≤qCap) (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤total C)
    (hhg : hg=0 ∨ hg=2) (htd : td=0 ∨ td=2)
    (hk : 0≤k) (hl : 0≤l) (hb : 0≤b) (ht : 0≤t)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G 3) (hAB : C.Feasible A 2)
    (hBT : C.Feasible B 2) (hTD : C.Feasible T td)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    stress (comparison C) (comparisonOwners hg td) (weights k l b t)≤0 := by
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hpair := actual_endpoint_lower hs hc hq
    (original_error_bound hvar hn G)
    (original_error_bound hvar hn A) (total_bounds hvar ha)
  have hm := mul_nonneg hl (sub_nonneg.mpr hpair)
  have hw (i : Vertex) : 0≤weights k l b t i := by
    fin_cases i <;> simp [weights,hk,hl,hb,ht]
  have hf (i : Vertex) : C.Feasible i (owners hg td i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hu : stress C (owners hg td) (weights k l b t)≤0 :=
    sub_nonpos.mpr (weighted_separation hw hf)
  rw [stress_identity C hhg htd k l b t] at hu
  change 0≤l*(PairedA.work (C.point A) (delta C.theta G) (delta C.theta A)-
    endpoint (C.point A).a |(C.point A).y| (total C)) at hm
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PairedA
