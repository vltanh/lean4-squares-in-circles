module

public import SquaresInCircles.Eight.Words.Middle.NegativeContraction
public import SquaresInCircles.Eight.Owners.NecessaryCycle

/-!
# Eight squares: the exact AB2 dual of the direct middle contractions

Reflection is used only for the local triple
`(B.reflect, A.reflect, G.reflect)`.  The resulting hard cycle changes A
alone and leaves the actual E data and E sign intact.  A nonzero AB2
error is aligned when G is at or above both middle frames, with strict
loss on A's original circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddlePositiveContraction

namespace MiddleReflectedContraction

structure AContraction (G A B : SignedPoint) (γ : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  avoids : point.AvoidsCore
  normal : 0 < point.y
  circle_lt : point.circle < A.circle
  AB_exact : point.y-B.y=1
  AB_zero : zeroFeasible point B 0 0
  AB_two : zeroFeasible point B 0 2
  GA_exact : quarterProjection G point (-γ) 0=edgeWidth (-γ)

/-- Local physical owner reflection preserves the source anchor circle. -/
def reflectB {G A B : SignedPoint} {γ : ℝ}
    (O : BContraction B.reflect A.reflect G.reflect γ) : AContraction G A B γ where
  point := O.point.reflect
  sorted := by simpa using O.sorted
  avoids := by simpa using O.avoids
  normal := by simpa [SignedPoint.reflect] using neg_pos.mpr O.normal
  circle_lt := by simpa using O.circle_lt
  AB_exact := by
    have hh := O.AB_exact
    dsimp [SignedPoint.reflect] at hh ⊢
    linarith
  AB_zero := by
    have hh := (zeroFeasible_reflect O.point.reflect B 0 0).1
      (by simpa [reflectedOwner] using O.AB_two)
    exact hh
  AB_two := by
    have hh := (zeroFeasible_reflect O.point.reflect B 0 2).1
      (by simpa [reflectedOwner] using O.AB_zero)
    exact hh
  GA_exact := by
    have hp := quarterProjection_reflect G O.point.reflect (-γ) 0
    have he : quarterProjection O.point G.reflect (-γ) 2=
        quarterProjection G O.point.reflect (-γ) 0 := by
      simpa [reflectedOwner] using hp
    exact he.symm.trans O.BT_exact

end MiddleReflectedContraction

open MiddleReflectedContraction
namespace SignedCycle

def replaceA (C : SignedCycle) (P : SignedPoint) : SignedCycle :=
  replacePoint C A P (C.theta B)

theorem replaceA_unchanged (C : SignedCycle) (P : SignedPoint)
    (i : Vertex) (hi : i ≠ A) :
    (replaceA C P).point i=C.point i ∧ (replaceA C P).theta i=C.theta i := by
  simp [replaceA,replacePoint,hi]

theorem replaceA_spread {C : SignedCycle} (h : C.Spread) (P : SignedPoint) :
    (replaceA C P).Spread := by
  intro i j
  by_cases hi : i=A <;> by_cases hj : j=A
  · subst i; subst j
    simpa [replaceA,replacePoint] using h B B
  · subst i
    simpa [replaceA,replacePoint,hj] using h B j
  · subst j
    simpa [replaceA,replacePoint,hi] using h i B
  · simpa [replaceA,replacePoint,hi,hj] using h i j

theorem replaceA_GA (C : SignedCycle) (P : SignedPoint) (j : Fin 4) :
    (replaceA C P).Feasible G j ↔
      quarterFeasible (C.point G) P (C.theta B-C.theta G) j := by
  simp [replaceA,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,G,A,B,
    quarterFeasible,sub_nonneg]

theorem replaceA_AB (C : SignedCycle) (P : SignedPoint) (j : Fin 4) :
    (replaceA C P).Feasible A j ↔ zeroFeasible P (C.point B) 0 j := by
  simp [replaceA,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,A,B,
    zeroFeasible,sub_nonneg]

def Witnesses.replaceA {C : SignedCycle} (w : C.Witnesses)
    (O : AContraction (C.point G) (C.point A) (C.point B) (C.theta G-C.theta B)) :
    (SignedCycle.replaceA C O.point).Witnesses where
  owner i := if i=G then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · exact (replacePoint_other_feasible (v := A) (by decide : H ≠ A)
        (by decide : next H ≠ A)).2 (w.feasible H)
    · apply (replaceA_GA C O.point 0).2
      unfold quarterFeasible
      simpa only [neg_sub] using O.GA_exact.symm.le
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj
      · have hAG : A ≠ G := by decide
        exact (replaceA_AB C O.point _).2 (by
          show zeroFeasible O.point (C.point B) 0 (if A = G then 0 else w.owner A)
          simp only [hAG,↓reduceIte,hj]
          exact O.AB_zero)
      · have hAG : A ≠ G := by decide
        exact (replaceA_AB C O.point _).2 (by
          show zeroFeasible O.point (C.point B) 0 (if A = G then 0 else w.owner A)
          simp only [hAG,↓reduceIte,hj]
          exact O.AB_two)
    · exact (replacePoint_other_feasible (v := A) (by decide : B ≠ A)
        (by decide : next B ≠ A)).2 (w.feasible B)
    · exact (replacePoint_other_feasible (v := A) (by decide : T ≠ A)
        (by decide : next T ≠ A)).2 (w.feasible T)
    · exact (replacePoint_other_feasible (v := A) (by decide : D ≠ A)
        (by decide : next D ≠ A)).2 (w.feasible D)
    · exact (replacePoint_other_feasible (v := A) (by decide : E ≠ A)
        (by decide : next E ≠ A)).2 (w.feasible E)
  allowed := by
    intro i
    by_cases hi : i=G
    · subst i; norm_num [normalOwners,G]
    · simpa [hi] using w.allowed i

def HardInput.fromReflectedMiddle {q : ℝ} (I : HardInput q)
    (O : AContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta G-I.cycle.theta B)) : HardInput q where
  cycle := SignedCycle.replaceA I.cycle O.point
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceA,replacePoint] using O.sorted
      · simpa [replaceA,replacePoint,hi] using I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=A
      · subst i
        have hh := O.circle_lt.le.trans (I.necessary.contained A)
        simpa [replaceA,replacePoint,SignedPoint.Contained] using hh
      · simpa [replaceA,replacePoint,hi] using I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceA,replacePoint] using O.avoids
      · simpa [replaceA,replacePoint,hi] using I.necessary.core i
    spread := replaceA_spread I.necessary.spread O.point }
  anchors_normal := by
    constructor
    · simpa [replaceA,replacePoint,H,A] using I.anchors_normal.H_nonneg
    · simpa [replaceA,replacePoint] using O.normal.le
    · simpa [replaceA,replacePoint,B,A] using I.anchors_normal.B_nonpos
    · simpa [replaceA,replacePoint,D,A] using I.anchors_normal.D_nonpos
  E_nonpos := by simpa [replaceA,replacePoint,E,A] using I.E_nonpos
  witnesses := I.witnesses.replaceA O
  GA_hard := by
    apply (replaceA_GA I.cycle O.point 0).2
    unfold quarterFeasible
    simpa only [neg_sub] using O.GA_exact.symm.le
  BT_hard := (replacePoint_other_feasible (v := A) (by decide : B ≠ A)
    (by decide : next B ≠ A)).2 I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.replaceA,H,G] using hh
      simpa [replaceA,replacePoint,G,A] using I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.replaceA,T,G] using hh
      simpa [replaceA,replacePoint,T,A] using I.zero_signs.TD_canceling hj }
  E_radial := by simpa [replaceA,replacePoint,H,D,E,A] using I.E_radial

/-- The two actual AB0 contraction formulas reflected at the original
local triple.  Both AB2 error signs are covered in this frame sector. -/
theorem HardInput.reflected_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hG : max (I.cycle.theta A) (I.cycle.theta B) ≤ I.cycle.theta G)
    (hne : I.cycle.theta A ≠ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    Nonempty (AContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta G-I.cycle.theta B)) := by
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hABraw : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) 2 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hABref : zeroFeasible (I.cycle.point B).reflect (I.cycle.point A).reflect
      (I.cycle.theta B-I.cycle.theta A) 0 := by
    simpa [reflectedOwner] using (zeroFeasible_reflect _ _ _ 2).2 hABraw
  have hBTref : quarterFeasible (I.cycle.point A).reflect (I.cycle.point G).reflect
      (I.cycle.theta A-I.cycle.theta G) 2 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 0).2 hGA
  have hs1 : (I.cycle.point B).reflect.Sorted := by simpa using I.necessary.sorted B
  have hc1 : (I.cycle.point B).reflect.AvoidsCore := by simpa using I.necessary.core B
  have hq1 : (I.cycle.point B).reflect.circle ≤ qCap := by
    simpa using (I.necessary.contained B).trans hq
  have hs2 : (I.cycle.point A).reflect.Sorted := by simpa using I.necessary.sorted A
  have hq2 : (I.cycle.point A).reflect.circle ≤ qCap := by
    simpa using (I.necessary.contained A).trans hq
  have hy1 : 0 ≤ (I.cycle.point B).reflect.y := by
    simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos
  have hy2 : (I.cycle.point A).reflect.y ≤ 0 := by
    simpa [SignedPoint.reflect] using neg_nonpos.mpr I.anchors_normal.A_nonneg
  have hy3 : -(1/10 : ℝ) ≤ (I.cycle.point G).reflect.y := by
    dsimp [SignedPoint.reflect]
    linarith
  have hAG := (le_max_left (I.cycle.theta A) (I.cycle.theta B)).trans hG
  have hBG := (le_max_right (I.cycle.theta A) (I.cycle.theta B)).trans hG
  rcases lt_or_gt_of_ne hne with hpos | hneg
  · have hspan : (I.cycle.theta G-I.cycle.theta B)+
        (I.cycle.theta B-I.cycle.theta A) ≤ 7/10 := by
      have hh := I.necessary.spread G A
      have ha := le_abs_self (I.cycle.theta G-I.cycle.theta A)
      dsimp [frameCap] at hh
      linarith
    have hBT' : quarterFeasible (I.cycle.point A).reflect (I.cycle.point G).reflect
        (-((I.cycle.theta G-I.cycle.theta B)+(I.cycle.theta B-I.cycle.theta A))) 2 := by
      rw [show -((I.cycle.theta G-I.cycle.theta B)+
        (I.cycle.theta B-I.cycle.theta A))=I.cycle.theta A-I.cycle.theta G by ring]
      exact hBTref
    obtain ⟨O⟩ := MiddlePositiveContraction.actual_B_contraction
      hs1 hc1 hq1 hs2 hq2 hy1 hy2 hy3 (sub_nonneg.mpr hBG)
      (sub_pos.mpr hpos) hspan hABref hBT'
    exact ⟨reflectB O⟩
  · have hγu : I.cycle.theta G-I.cycle.theta B ≤ 7/10 := by
      have hh := I.necessary.spread G B
      have ha := le_abs_self (I.cycle.theta G-I.cycle.theta B)
      dsimp [frameCap] at hh
      linarith
    have hAB' : zeroFeasible (I.cycle.point B).reflect (I.cycle.point A).reflect
        (-(I.cycle.theta A-I.cycle.theta B)) 0 := by
      simpa only [neg_sub] using hABref
    have hBT' : quarterFeasible (I.cycle.point A).reflect (I.cycle.point G).reflect
        (-((I.cycle.theta G-I.cycle.theta B)-(I.cycle.theta A-I.cycle.theta B))) 2 := by
      rw [show -((I.cycle.theta G-I.cycle.theta B)-
        (I.cycle.theta A-I.cycle.theta B))=I.cycle.theta A-I.cycle.theta G by ring]
      exact hBTref
    obtain ⟨O⟩ := MiddleNegativeContraction.actual_B_contraction
      hs1 hc1 hq1 hs2 hq2 hy1 hy2 hy3 (sub_pos.mpr hneg)
      (show I.cycle.theta A-I.cycle.theta B ≤ I.cycle.theta G-I.cycle.theta B by linarith)
      hγu hAB' hBT'
    exact ⟨reflectB O⟩

end SignedCycle
end SquaresInCircles.Eight
