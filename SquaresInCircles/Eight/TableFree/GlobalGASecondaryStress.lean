module

public import SquaresInCircles.Eight.TableFree.GlobalGAActualPairs
public import SquaresInCircles.Eight.TableFree.GlobalGADSupport
public import SquaresInCircles.Eight.TableFree.GlobalGAOwners

/-!
# Exact original-axis collection for the secondary high-GA chain

Uncompiled source.  This file collects the seven original weak separators
with the fixed positive weights `(k,l,l,2,2,1,1)`.  A, T, and E cancel
algebraically.  The two HG owners retain their actual different force
formulas; the angular charge vanishes by the seven-cycle incidence law.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open Candidate SignedStress

def secondaryOwners (hg : Fin 4) : Vertex → Fin 4 := ![hg,2,0,2,0,2,0]

def actualSecondaryStress (hg : Fin 4) (C : SignedCycle) : ℝ :=
  demand C fourCircleWeights-
    ∑ i,work (force C (secondaryOwners hg) fourCircleWeights i) (C.point i)

def baseStress : ℝ :=
  79/8-fullSupport 1 k-fullSupport l k-fullSupport 2 l-3*diagonal

def dIncrement (z d : ℝ) (P : SignedPoint) : ℝ :=
  2*edgeWidth z+edgeWidth d-(dF z d*P.a+dG z d*P.y)+
    charge*(z+d)-(3-3*diagonal)

theorem baseStress_reserve : (627/10000:ℝ)<baseStress := by
  have h := fourCircle_radical_reserve
  norm_num [baseStress,fullSupport,R,k,l,diagonal] at h ⊢
  linarith

theorem actual_dIncrement_nonneg {q z d : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hz : |z|≤frameCap) (hd : |d|≤frameCap) (hsum : |z+d|≤frameCap) :
    0≤dIncrement z d P := by
  have h := actual_D_lower hs hy hc hq hz hd hsum
  dsimp [dIncrement]
  linarith

theorem secondary_stress_nonpos {C : SignedCycle} {hg : Fin 4}
    (hHG : C.Feasible H hg) (hGA : C.Feasible G 2)
    (hAB : C.Feasible A 0) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    actualSecondaryStress hg C≤0 := by
  have hf (i : Vertex) : C.Feasible i (secondaryOwners hg i) := by
    fin_cases i
    · simpa [secondaryOwners,H] using hHG
    · simpa [secondaryOwners,G] using hGA
    · simpa [secondaryOwners,A] using hAB
    · simpa [secondaryOwners,B] using hBT
    · simpa [secondaryOwners,T] using hTD
    · simpa [secondaryOwners,D] using hDE
    · simpa [secondaryOwners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation fourCircleWeights_nonneg hf)

theorem zero_stress_decomposition (C : SignedCycle) :
    actualSecondaryStress 0 C=baseStress+
      oneIncrement k 1 (delta C.theta E) (C.point H)+
      pairIncrement k l (delta C.theta H) (delta C.theta G) (C.point G).reflect+
      pairIncrement l 2 (delta C.theta A) (delta C.theta B) (C.point B).reflect+
      dIncrement (delta C.theta T) (delta C.theta D) (C.point D).reflect := by
  simp [actualSecondaryStress,demand,force,source,target,work,add,scale,
    previous,secondaryOwners,fourCircleWeights,Fin.sum_univ_succ,
    word,delta,next,H,G,A,B,T,D,E,baseStress,oneIncrement,pairIncrement,
    pairF,pairG,dIncrement,dF,dG,SignedPoint.reflect,k,l,charge]
  ring

theorem two_stress_decomposition (C : SignedCycle) :
    actualSecondaryStress 2 C=baseStress+
      pairIncrement k 1 (delta C.theta H) (delta C.theta E) (C.point H)+
      oneIncrement k l (delta C.theta G) (C.point G).reflect+
      pairIncrement l 2 (delta C.theta A) (delta C.theta B) (C.point B).reflect+
      dIncrement (delta C.theta T) (delta C.theta D) (C.point D).reflect := by
  simp [actualSecondaryStress,demand,force,source,target,work,add,scale,
    previous,secondaryOwners,fourCircleWeights,Fin.sum_univ_succ,
    word,delta,next,H,G,A,B,T,D,E,baseStress,oneIncrement,pairIncrement,
    pairF,pairG,dIncrement,dF,dG,SignedPoint.reflect,k,l,charge]
  ring

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
