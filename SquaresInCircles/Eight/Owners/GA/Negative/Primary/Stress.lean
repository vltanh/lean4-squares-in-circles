module

public import SquaresInCircles.Eight.Owners.GA.HybridConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.Primary.Scalar
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TD
public import SquaresInCircles.Eight.Owners.GA.One.AngleFunctions
public import SquaresInCircles.Eight.Owners.GA.SecondaryStress

/-!
# Eight squares: exact simultaneous negative-primary stress collection

The three Boolean flags mean GA3, AB2 and TD2 respectively.  A zero
error is substituted only in the displayed reference expression;
all seven actual inequalities are multiplied by positive weights.
The signed tangent of A cancels between each actual primary edge
and its reference term, including when both primary edges occur.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalGA.NegativePrimary

open Candidate Secondary

def erase (primary : Bool) (d : ℝ) : ℝ := if primary then 0 else d

@[simp] theorem erase_false (d : ℝ) : erase false d=d := rfl
@[simp] theorem erase_true (d : ℝ) : erase true d=0 := rfl

def owners (hg : Fin 4) (ga ab td : Bool) : Vertex→Fin 4 :=
  ![hg,if ga then 3 else 2,if ab then 2 else 0,2,if td then 2 else 0,2,0]

def weights (ga ab : Bool) (C : SignedCycle) : Vertex→ℝ :=
  ![k,if ga then l/Real.cos (delta C.theta G) else l,
    if ab then l/Real.cos (delta C.theta A) else l,2,2,1,1]

def stress (hg : Fin 4) (ga ab td : Bool) (C : SignedCycle) : ℝ :=
  ∑ i,weights ga ab C i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab td i))

def zeroReference (ga ab td : Bool) (C : SignedCycle) : ℝ :=
  baseStress+oneIncrement k 1 (delta C.theta E) (C.point H)+
    pairIncrement k l (delta C.theta H) (erase ga (delta C.theta G)) (C.point G).reflect+
    pairIncrement l 2 (erase ab (delta C.theta A)) (delta C.theta B) (C.point B).reflect+
    dIncrement (erase td (delta C.theta T)) (delta C.theta D) (C.point D).reflect

def twoReference (ga ab td : Bool) (C : SignedCycle) : ℝ :=
  baseStress+pairIncrement k 1 (delta C.theta H) (delta C.theta E) (C.point H)+
    oneIncrement k l (erase ga (delta C.theta G)) (C.point G).reflect+
    pairIncrement l 2 (erase ab (delta C.theta A)) (delta C.theta B) (C.point B).reflect+
    dIncrement (erase td (delta C.theta T)) (delta C.theta D) (C.point D).reflect

def gains (ga ab td : Bool) (C : SignedCycle) : ℝ :=
  (if ga then primaryIncrement (delta C.theta G) (C.point A).a (C.point G).a else 0)+
  (if ab then primaryIncrement (delta C.theta A) (C.point A).a (-(C.point B).y) else 0)+
  (if td then tdIncrement (delta C.theta T) (C.point T) else 0)

theorem weights_nonneg (ga ab : Bool) (C : SignedCycle)
    (hsmall : ∀i,|delta C.theta i|≤frameCap) : ∀i,0≤weights ga ab C i := by
  have hG := cos_pos (hsmall G)
  have hA := cos_pos (hsmall A)
  intro i
  cases ga <;> cases ab <;> fin_cases i <;> simp [weights,k,l] <;> positivity

theorem stress_nonpos {hg : Fin 4} {ga ab td : Bool} {C : SignedCycle}
    (hsmall : ∀i,|delta C.theta i|≤frameCap)
    (hf : ∀i,C.Feasible i (owners hg ga ab td i)) : stress hg ga ab td C≤0 := by
  apply Finset.sum_nonpos
  intro i _
  have hi := hf i
  change 0≤C.edge i (owners hg ga ab td i)-edgeWidth (delta C.theta i) at hi
  exact mul_nonpos_of_nonneg_of_nonpos (weights_nonneg ga ab C hsmall i) (by linarith)

private theorem r43_delta_sum (C : SignedCycle) :
    delta C.theta H+delta C.theta G+delta C.theta A+delta C.theta B+
      delta C.theta T+delta C.theta D+delta C.theta E=0 := by
  simp only [delta,next,H,G,A,B,T,D,E]
  norm_num

theorem zero_decomposition (ga ab td : Bool) (C : SignedCycle)
    (hG : Real.cos (delta C.theta G)≠0) (hA : Real.cos (delta C.theta A)≠0) :
    stress 0 ga ab td C=zeroReference ga ab td C+gains ga ab td C := by
  have hs := r43_delta_sum C
  have hiG := mul_inv_cancel₀ hG
  have hiA := mul_inv_cancel₀ hA
  simp only [stress,weights,owners,zeroReference,gains,erase,Fin.sum_univ_seven,
    SignedCycle.edge,H,G,A,B,T,D,E] at *
  simp only [word,next,zeroProjection,quarterProjection,baseStress,oneIncrement,pairIncrement,
    dIncrement,primaryIncrement,tdIncrement,pairF,pairG,dF,dG,SignedPoint.reflect]
  cases ga <;> cases ab <;> cases td <;>
    norm_num only [Fin.isValue,Fin.reduceAdd,Bool.false_eq_true,↓reduceIte,Matrix.cons_val,
      Real.sin_zero,Real.cos_zero,edgeWidth_zero]
  · linear_combination (-Secondary.charge)*hs
  · linear_combination (-Secondary.charge)*hs
  · linear_combination (-Secondary.charge)*hs+(-l*(C.point 2).y)*hiA
  · linear_combination (-Secondary.charge)*hs+(-l*(C.point 2).y)*hiA
  · linear_combination (-Secondary.charge)*hs+(l*(C.point 2).y)*hiG
  · linear_combination (-Secondary.charge)*hs+(l*(C.point 2).y)*hiG
  · linear_combination (-Secondary.charge)*hs+(l*(C.point 2).y)*hiG+(-l*(C.point 2).y)*hiA
  · linear_combination (-Secondary.charge)*hs+(l*(C.point 2).y)*hiG+(-l*(C.point 2).y)*hiA

theorem two_decomposition (ga ab td : Bool) (C : SignedCycle)
    (hG : Real.cos (delta C.theta G)≠0) (hA : Real.cos (delta C.theta A)≠0) :
    stress 2 ga ab td C=twoReference ga ab td C+gains ga ab td C := by
  have hs := r43_delta_sum C
  have hiG := mul_inv_cancel₀ hG
  have hiA := mul_inv_cancel₀ hA
  simp only [stress,weights,owners,twoReference,gains,erase,Fin.sum_univ_seven,
    SignedCycle.edge,H,G,A,B,T,D,E] at *
  simp only [word,next,zeroProjection,quarterProjection,baseStress,oneIncrement,pairIncrement,
    dIncrement,primaryIncrement,tdIncrement,pairF,pairG,dF,dG,SignedPoint.reflect]
  cases ga <;> cases ab <;> cases td <;>
    norm_num only [Fin.isValue,Fin.reduceAdd,Bool.false_eq_true,↓reduceIte,Matrix.cons_val,
      Real.sin_zero,Real.cos_zero,edgeWidth_zero]
  · linear_combination (-Secondary.charge)*hs
  · linear_combination (-Secondary.charge)*hs
  · linear_combination (-Secondary.charge)*hs+(-l*(C.point 2).y)*hiA
  · linear_combination (-Secondary.charge)*hs+(-l*(C.point 2).y)*hiA
  · linear_combination (-Secondary.charge)*hs+(l*(C.point 2).y)*hiG
  · linear_combination (-Secondary.charge)*hs+(l*(C.point 2).y)*hiG
  · linear_combination (-Secondary.charge)*hs+(l*(C.point 2).y)*hiG+(-l*(C.point 2).y)*hiA
  · linear_combination (-Secondary.charge)*hs+(l*(C.point 2).y)*hiG+(-l*(C.point 2).y)*hiA

end SquaresInCircles.Eight.GlobalGA.NegativePrimary
