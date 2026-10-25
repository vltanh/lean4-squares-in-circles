module

public import SquaresInCircles.Eight.TableFree.FlatEBlocks

/-!
# The original seven-edge stress with both E secants

Uncompiled source. The two negative primary multipliers cancel E's
tangential force exactly. Its remaining work uses the original flat
coordinate 7/12. All other point bounds use the same original radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.FlatEStress
open Candidate SignedStress SecondaryEStress PositiveAngularEnvelope
open PositivePrimaryBaselines ActualCoreEBlocks FlatEBlocks

def weights (C : SignedCycle) (de eh : Fin 4) (n k l b t : ℝ) : Vertex → ℝ :=
  ![n,k,l,b,t,deWeight C de,ehWeight C eh]

def forces (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) : Vertex → Point :=
  force C (CoreEStress.owners ab bt td de eh) (weights C de eh n k l b t)

def bound (C : SignedCycle) (ab bt td de eh : Fin 4) (flatT : Bool)
    (n k l b t R : ℝ) : Vertex → ℝ :=
  let F := forces C ab bt td de eh n k l b t
  ![signedSupport R 1 (F H),circleSupport R (F G),signedSupport R 1 (F A),
    signedSupport R (-1) (F B),
    if flatT then work (F T) (C.point T) else circleSupport R (F T),
    signedSupport R (-1) (F D),work (F E) (C.point E)]

def defect (C : SignedCycle) (ab bt td de eh : Fin 4) (flatT : Bool)
    (n k l b t R : ℝ) : ℝ :=
  demand C (weights C de eh n k l b t)-∑ i,bound C ab bt td de eh flatT n k l b t R i

def anchorNorms (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) : ℝ :=
  pairNorm (ehWeight C eh) n (delta C.theta H+ordinaryEH C eh)+
  pairNorm k l (if ab=0 then 0 else delta C.theta A)+
  pairNorm l b ((if ab=0 then delta C.theta A else 0)+(if bt=2 then delta C.theta B else 0))+
  pairNorm (deWeight C de) t (ordinaryDE C de+(if td=0 then delta C.theta T else 0))

def halfShift (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) : ℝ :=
  (n*PositiveAngularEnvelope.phi (delta C.theta H)+ehWeight C eh*PositiveAngularEnvelope.phi (ordinaryEH C eh)+k+
    l*PositiveAngularEnvelope.phi (if ab=0 then 0 else delta C.theta A)+
    b*PositiveAngularEnvelope.phi (if bt=2 then delta C.theta B else 0)+
    l*PositiveAngularEnvelope.phi (if ab=0 then delta C.theta A else 0)+
    deWeight C de*PositiveAngularEnvelope.phi (ordinaryDE C de)+t*PositiveAngularEnvelope.phi (if td=0 then delta C.theta T else 0))/2

def zeroNorms (C : SignedCycle) (de eh : Fin 4) (n k l b t : ℝ) : ℝ :=
  pairNorm n (ehWeight C eh) 0+pairNorm k l 0+pairNorm l b 0+pairNorm (deWeight C de) t 0

def increment (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t R : ℝ) : ℝ :=
  ∑ i,(FlatEBlocks.blocks C ab bt td de eh n k l b t i).increment R

theorem force_H {eh : Fin 4} (heh : eh=0 ∨ eh=1)
    (C : SignedCycle) (ab bt td de : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t H=
      rotatedPair (ehWeight C eh) n (delta C.theta H) (ordinaryEH C eh) := by
  rcases heh with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,H,E,source,target,
      add,scale,rotatedPair,ordinaryEH] <;> (try refine ⟨?_,?_⟩) <;> ring

theorem force_A (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t A=CoreEStress.forces C ab bt td de eh n k l b t A := by
  simp [forces,CoreEStress.forces,force,weights,SecondaryEStress.weights,previous,A]

theorem force_B (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t B=CoreEStress.forces C ab bt td de eh n k l b t B := by
  simp [forces,CoreEStress.forces,force,weights,SecondaryEStress.weights,previous,B]

theorem force_D {td de : Fin 4} (htd : td=0 ∨ td=2) (hde : de=2 ∨ de=3)
    (C : SignedCycle) (ab bt eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t D=
      let v := rotatedPair (deWeight C de) t (if td=0 then delta C.theta T else 0) (ordinaryDE C de)
      (v.1,-v.2) := by
  rcases htd with rfl | rfl <;> rcases hde with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,D,T,source,target,
      add,scale,rotatedPair,ordinaryDE] <;> ring

theorem force_G (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t G=CoreEStress.forces C ab bt td de eh n k l b t G := by
  simp [forces,CoreEStress.forces,force,weights,SecondaryEStress.weights,previous,G]

theorem force_T (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t T=CoreEStress.forces C ab bt td de eh n k l b t T := by
  simp [forces,CoreEStress.forces,force,weights,SecondaryEStress.weights,previous,T]

theorem force_E {C : SignedCycle} {de eh : Fin 4}
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (ab bt td : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t E=
      (-(Real.tan (deAngle C de)+Real.tan (ehAngle C eh)),0) := by
  have hcD : Real.cos (delta C.theta 5)≠0 := (transport_cos_pos (hsmall 5)).ne'
  have hcE : Real.cos (delta C.theta 6)≠0 := (transport_cos_pos (hsmall 6)).ne'
  rcases hde with rfl | rfl <;> rcases heh with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,D,E,source,target,
      add,scale,deWeight,ehWeight,deAngle,ehAngle,primaryDE,primaryEH,
      Real.tan_eq_sin_div_cos] <;> (try refine ⟨?_,?_⟩) <;> field_simp [hcD,hcE] <;> ring

theorem E_work {C : SignedCycle} {de eh : Fin 4}
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hflat : (C.point E).a=7/12)
    (ab bt td : Fin 4) (n k l b t : ℝ) :
    work (forces C ab bt td de eh n k l b t E) (C.point E)=
      -(7/12)*(Real.tan (deAngle C de)+Real.tan (ehAngle C eh)) := by
  rw [force_E hde heh hsmall]
  simp [work,hflat]
  ring

theorem increment_eq {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (n k l b t R : ℝ) :
    increment C ab bt td de eh n k l b t R=
      n*psi (delta C.theta H)+l*psi (delta C.theta A)+
      b*psi (if bt=2 then delta C.theta B else 0)+t*psi (if td=0 then delta C.theta T else 0)+
      deWeight C de*psi (ordinaryDE C de)+ehWeight C eh*psi (ordinaryEH C eh)-
      R*(anchorNorms C ab bt td de eh n k l b t-zeroNorms C de eh n k l b t) := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;> rcases htd with rfl | rfl <;>
    simp [increment,FlatEBlocks.blocks,ActualOrdinaryBlocks.Block.increment,
      anchorNorms,zeroNorms,Fin.sum_univ_succ,pairNorm_symm k l,pairNorm_symm n (ehWeight C eh)] <;> ring

theorem defect_as_anchors {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (flatT : Bool) (n k l b t R : ℝ) :
    defect C ab bt td de eh flatT n k l b t R=
      demand C (weights C de eh n k l b t)+halfShift C ab bt td de eh n k l b t-
      R*anchorNorms C ab bt td de eh n k l b t-
      circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t G)-
      (if flatT then work (CoreEStress.forces C ab bt td de eh n k l b t T) (C.point T)
       else circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t T))-
      work (forces C ab bt td de eh n k l b t E) (C.point E) := by
  have hH := rotatedPair_signedSupport R (ehWeight C eh) n (delta C.theta H) (ordinaryEH C eh)
  have hA := rotatedPair_signedSupport R k l (if ab=0 then 0 else delta C.theta A) 0
  have hB := reflected_rotatedPair_signedSupport R b l
    (if ab=0 then delta C.theta A else 0) (if bt=2 then delta C.theta B else 0)
  have hD := reflected_rotatedPair_signedSupport R (deWeight C de) t
    (if td=0 then delta C.theta T else 0) (ordinaryDE C de)
  rw [pairNorm_symm b l] at hB
  unfold defect
  have hsum : (∑ i,bound C ab bt td de eh flatT n k l b t R i)=
      signedSupport R 1 (forces C ab bt td de eh n k l b t H)+
      circleSupport R (forces C ab bt td de eh n k l b t G)+
      signedSupport R 1 (forces C ab bt td de eh n k l b t A)+
      signedSupport R (-1) (forces C ab bt td de eh n k l b t B)+
      (if flatT then work (forces C ab bt td de eh n k l b t T) (C.point T)
       else circleSupport R (forces C ab bt td de eh n k l b t T))+
      signedSupport R (-1) (forces C ab bt td de eh n k l b t D)+
      work (forces C ab bt td de eh n k l b t E) (C.point E) := by
    simp [bound,Fin.sum_univ_succ,H,G,A,B,T,D,E]
    ring
  rw [hsum,force_H heh,force_A,force_B,CoreEStress.force_A hab,CoreEStress.force_B hab hbt,
    force_D htd hde,force_G,force_T,hH,hA,hB,hD]
  simp only [phi_zero,mul_one,zero_add,add_zero]
  dsimp [anchorNorms,halfShift]
  rw [add_comm (if td=0 then delta C.theta T else 0) (ordinaryDE C de)]
  ring

theorem necessary_at_cap {C : SignedCycle} {q : ℝ} {ab bt td de eh : Fin 4}
    {n k l b t : ℝ} (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (flatT : Bool) (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) :
    defect C ab bt td de eh flatT n k l b t (Real.sqrt qCap)≤0 := by
  have hsmall (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hp := primary_small (de := de) (eh := eh) hsmall
  have hcD : 0<Real.cos (deAngle C de) := by
    simpa [deAngle] using transport_cos_pos hp.1
  have hcE : 0<Real.cos (ehAngle C eh) := by
    simpa [ehAngle] using transport_cos_pos hp.2
  have hweight : ∀ i,0≤weights C de eh n k l b t i := by
    intro i
    fin_cases i <;> simp [weights,deWeight,ehWeight] <;>
      first | positivity | linarith [hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2]
  have hc (i : Vertex) : (C.point i).Contained ((Real.sqrt qCap)^2) := by
    rw [Real.sq_sqrt (show 0≤qCap by norm_num [qCap])]
    exact (hC.contained i).trans hq
  have hb : ∀ i,work (forces C ab bt td de eh n k l b t i) (C.point i)≤
      bound C ab bt td de eh flatT n k l b t (Real.sqrt qCap) i := by
    intro i
    fin_cases i
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc H) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.H_nonneg]) _
    · exact work_le_circleSupport (Real.sqrt_nonneg _) (hC.sorted G) (hc G) _
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc A) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.A_nonneg]) _
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc B) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.B_nonpos]) _
    · cases flatT
      · exact work_le_circleSupport (Real.sqrt_nonneg _) (hC.sorted T) (hc T) _
      · exact le_rfl
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc D) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.D_nonpos]) _
    · exact le_rfl
  have hh := weighted_separation_le hweight hf hb
  dsimp [defect]
  linarith

end SquaresInCircles.Eight.TableFree.FlatEStress
