module

public import SquaresInCircles.Eight.Words.Core.EStress

/-!
# Eight squares: exact seven-edge stress with independent E-edge multipliers

Both E multipliers remain symbolic, so the low,
middle, and high sole-primary stresses use the same original force
identity. The E work is evaluated at the original signed point. The
G and T supports permit either sign; H/A/B/D retain their normal signs.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleEStress
open Candidate SignedStress PositiveAngularEnvelope ActualCoreEBlocks
open PositivePrimaryBaselines SecondaryEStress

def weights (n k l b t p r : ℝ) : Vertex → ℝ := ![n,k,l,b,t,p,r]

def forces (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t p r : ℝ) : Vertex → Point :=
  force C (CoreEStress.owners ab bt td de eh) (weights n k l b t p r)

theorem force_H {eh : Fin 4} (heh : eh=0 ∨ eh=1)
    (C : SignedCycle) (ab bt td de : Fin 4) (n k l b t p r : ℝ) :
    forces C ab bt td de eh n k l b t p r H=
      rotatedPair r n (delta C.theta H) (ordinaryEH C eh) := by
  rcases heh with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,H,E,source,target,
      add,scale,rotatedPair,ordinaryEH] <;> (try refine ⟨?_,?_⟩) <;> ring

theorem force_A {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (C : SignedCycle) (bt td de eh : Fin 4) (n k l b t p r : ℝ) :
    forces C ab bt td de eh n k l b t p r A=
      rotatedPair k l (if ab=0 then 0 else delta C.theta A) 0 := by
  rcases hab with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,A,source,target,
      add,scale,rotatedPair] <;> ring

theorem force_B {ab bt : Fin 4} (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3)
    (C : SignedCycle) (td de eh : Fin 4) (n k l b t p r : ℝ) :
    forces C ab bt td de eh n k l b t p r B=
      let v := rotatedPair b l (if ab=0 then delta C.theta A else 0)
        (if bt=2 then delta C.theta B else 0)
      (v.1,-v.2) := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,A,B,source,target,
      add,scale,rotatedPair] <;> (try refine ⟨?_,?_⟩) <;> ring

theorem force_D {td de : Fin 4} (htd : td=0 ∨ td=2) (hde : de=2 ∨ de=3)
    (C : SignedCycle) (ab bt eh : Fin 4) (n k l b t p r : ℝ) :
    forces C ab bt td de eh n k l b t p r D=
      let v := rotatedPair p t (if td=0 then delta C.theta T else 0) (ordinaryDE C de)
      (v.1,-v.2) := by
  rcases htd with rfl | rfl <;> rcases hde with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,T,D,source,target,
      add,scale,rotatedPair,ordinaryDE] <;> (try refine ⟨?_,?_⟩) <;> ring

theorem force_G (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t p r : ℝ) :
    forces C ab bt td de eh n k l b t p r G=
      SecondaryEStress.forces C ab bt td n k l b t G := by
  simp [forces,SecondaryEStress.forces,force,CoreEStress.owners,SecondaryEStress.owners,
    weights,SecondaryEStress.weights,previous,word,G,source,target,add,scale]

theorem force_T (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t p r : ℝ) :
    forces C ab bt td de eh n k l b t p r T=
      SecondaryEStress.forces C ab bt td n k l b t T := by
  simp [forces,SecondaryEStress.forces,force,CoreEStress.owners,SecondaryEStress.owners,
    weights,SecondaryEStress.weights,previous,word,T,source,target,add,scale]

theorem force_E {de eh : Fin 4} (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (C : SignedCycle) (ab bt td : Fin 4) (n k l b t p r : ℝ) :
    forces C ab bt td de eh n k l b t p r E=
      (p*Real.sin (primaryDE C de)+r*Real.sin (primaryEH C eh),
        r*Real.cos (primaryEH C eh)-p*Real.cos (primaryDE C de)) := by
  rcases hde with rfl | rfl <;> rcases heh with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,D,E,source,target,
      add,scale,primaryDE,primaryEH] <;> (try refine ⟨?_,?_⟩) <;> ring

def blocks (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t p r : ℝ) : Fin 4 → ActualOrdinaryBlocks.Block :=
  ![⟨n,r,delta C.theta H,ordinaryEH C eh⟩,
    ⟨l,k,if ab=0 then 0 else delta C.theta A,0⟩,
    ⟨l,b,if ab=0 then delta C.theta A else 0,if bt=2 then delta C.theta B else 0⟩,
    ⟨p,t,ordinaryDE C de,if td=0 then delta C.theta T else 0⟩]

def anchorNorms (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t p r : ℝ) : ℝ :=
  pairNorm r n (delta C.theta H+ordinaryEH C eh)+
  pairNorm k l (if ab=0 then 0 else delta C.theta A)+
  pairNorm l b ((if ab=0 then delta C.theta A else 0)+
    (if bt=2 then delta C.theta B else 0))+
  pairNorm p t (ordinaryDE C de+(if td=0 then delta C.theta T else 0))

def zeroNorms (n k l b t p r : ℝ) : ℝ :=
  pairNorm r n 0+pairNorm k l 0+pairNorm l b 0+pairNorm p t 0

def halfShift (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t p r : ℝ) : ℝ :=
  (n*PositiveAngularEnvelope.phi (delta C.theta H)+r*PositiveAngularEnvelope.phi (ordinaryEH C eh)+k+
    l*PositiveAngularEnvelope.phi (if ab=0 then 0 else delta C.theta A)+
    b*PositiveAngularEnvelope.phi (if bt=2 then delta C.theta B else 0)+
    l*PositiveAngularEnvelope.phi (if ab=0 then delta C.theta A else 0)+
    p*PositiveAngularEnvelope.phi (ordinaryDE C de)+t*PositiveAngularEnvelope.phi (if td=0 then delta C.theta T else 0))/2

def bound (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t p r R : ℝ) : Vertex → ℝ :=
  let F := forces C ab bt td de eh n k l b t p r
  ![signedSupport R 1 (F H),circleSupport R (F G),signedSupport R 1 (F A),
    signedSupport R (-1) (F B),circleSupport R (F T),signedSupport R (-1) (F D),
    work (F E) (C.point E)]

def defect (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t p r R : ℝ) : ℝ :=
  demand C (weights n k l b t p r)-∑ i,bound C ab bt td de eh n k l b t p r R i

def increment (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t p r R : ℝ) : ℝ :=
  n*psi (delta C.theta H)+l*psi (delta C.theta A)+
    b*psi (if bt=2 then delta C.theta B else 0)+
    t*psi (if td=0 then delta C.theta T else 0)+
    p*psi (ordinaryDE C de)+r*psi (ordinaryEH C eh)-
    R*(anchorNorms C ab bt td de eh n k l b t p r-zeroNorms n k l b t p r)

theorem increment_eq (C : SignedCycle) {ab bt td : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (de eh : Fin 4) (n k l b t p r R : ℝ) :
    increment C ab bt td de eh n k l b t p r R=
      ∑ i,(blocks C ab bt td de eh n k l b t p r i).increment R := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;> rcases htd with rfl | rfl <;>
    simp [increment,blocks,ActualOrdinaryBlocks.Block.increment,anchorNorms,zeroNorms,
      Fin.sum_univ_succ,pairNorm_symm k l,pairNorm_symm n r] <;> ring

theorem sum_bounds (C : SignedCycle) {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1) (n k l b t p r R : ℝ) :
    (∑ i,bound C ab bt td de eh n k l b t p r R i)=
      R*anchorNorms C ab bt td de eh n k l b t p r-halfShift C ab bt td de eh n k l b t p r+
      circleSupport R (forces C ab bt td de eh n k l b t p r G)+
      circleSupport R (forces C ab bt td de eh n k l b t p r T)+
      work (forces C ab bt td de eh n k l b t p r E) (C.point E) := by
  have hH := rotatedPair_signedSupport R r n (delta C.theta H) (ordinaryEH C eh)
  have hA := rotatedPair_signedSupport R k l (if ab=0 then 0 else delta C.theta A) 0
  have hB := reflected_rotatedPair_signedSupport R b l
    (if ab=0 then delta C.theta A else 0) (if bt=2 then delta C.theta B else 0)
  have hD := reflected_rotatedPair_signedSupport R p t
    (if td=0 then delta C.theta T else 0) (ordinaryDE C de)
  rw [pairNorm_symm b l] at hB
  have hsum : (∑ i,bound C ab bt td de eh n k l b t p r R i)=
      signedSupport R 1 (forces C ab bt td de eh n k l b t p r H)+
      circleSupport R (forces C ab bt td de eh n k l b t p r G)+
      signedSupport R 1 (forces C ab bt td de eh n k l b t p r A)+
      signedSupport R (-1) (forces C ab bt td de eh n k l b t p r B)+
      circleSupport R (forces C ab bt td de eh n k l b t p r T)+
      signedSupport R (-1) (forces C ab bt td de eh n k l b t p r D)+
      work (forces C ab bt td de eh n k l b t p r E) (C.point E) := by
    simp [bound,Fin.sum_univ_succ,H,G,A,B,T,D,E]
    ring
  rw [hsum,force_H heh,force_A hab,force_B hab hbt,force_D htd hde,hH,hA,hB,hD]
  simp only [phi_zero,mul_one,add_zero]
  dsimp [anchorNorms,halfShift]
  rw [add_comm (if td=0 then delta C.theta T else 0) (ordinaryDE C de)]
  ring

theorem necessary {C : SignedCycle} {q R : ℝ} {ab bt td de eh : Fin 4}
    {n k l b t p r : ℝ} (hR : 0≤R) (hq : q≤R^2) (hC : C.Necessary q)
    (hn : C.NormalAnchors)
    (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t ∧ 0≤p ∧ 0≤r)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) :
    defect C ab bt td de eh n k l b t p r R≤0 := by
  have hweight : ∀ i,0≤weights n k l b t p r i := by
    intro i
    rcases hw with ⟨hn,hk,hl,hb,ht,hp,hr⟩
    fin_cases i <;> simp [weights] <;> linarith
  have hc (i : Vertex) : (C.point i).Contained (R^2) := (hC.contained i).trans hq
  have hb : ∀ i,work (forces C ab bt td de eh n k l b t p r i) (C.point i)≤
      bound C ab bt td de eh n k l b t p r R i := by
    intro i
    fin_cases i
    · exact work_le_signed_support hR (hc H) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.H_nonneg]) _
    · exact work_le_circleSupport hR (hC.sorted G) (hc G) _
    · exact work_le_signed_support hR (hc A) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.A_nonneg]) _
    · exact work_le_signed_support hR (hc B) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.B_nonpos]) _
    · exact work_le_circleSupport hR (hC.sorted T) (hc T) _
    · exact work_le_signed_support hR (hc D) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.D_nonpos]) _
    · exact le_rfl
  have hh := weighted_separation_le hweight hf hb
  dsimp [defect]
  linarith

theorem demand_eq (C : SignedCycle) (n k l b t p r : ℝ) :
    demand C (weights n k l b t p r)=
      n*edgeWidth (delta C.theta H)+k*edgeWidth (delta C.theta G)+
      l*edgeWidth (delta C.theta A)+b*edgeWidth (delta C.theta B)+
      t*edgeWidth (delta C.theta T)+p*edgeWidth (delta C.theta D)+r*edgeWidth (delta C.theta E) := by
  simp [demand,weights,Fin.sum_univ_succ,H,G,A,B,T,D,E]
  ring

def baseline (R k l c p r g x d e Ework : ℝ) : ℝ :=
  (3/2)*tiltedWeight k g x+2*l+3*c+(p+r)/2+k*(edgeWidth x+1/2)+
    p*edgeWidth d+r*edgeWidth e-
    R*zeroNorms (tiltedWeight k g x) k l c c p r-
    primarySupport R k g x-Ework

theorem secondary_decomposition {C : SignedCycle} {ab de eh : Fin 4} {R k l c p r g : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hg : 0≤g) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) :
    defect C ab 2 0 de eh (tiltedWeight k g (delta C.theta G)) k l c c p r R=
      baseline R k l c p r g (delta C.theta G) (primaryDE C de) (primaryEH C eh)
        (work (forces C ab 2 0 de eh (tiltedWeight k g (delta C.theta G)) k l c c p r E)
          (C.point E))+
      increment C ab 2 0 de eh (tiltedWeight k g (delta C.theta G)) k l c c p r R := by
  have ho := ordinary_small (de := de) (eh := eh) hsmall
  rw [defect,sum_bounds C hab (Or.inl rfl) (Or.inl rfl) hde heh,
    force_G,force_T,positive_G_support hk hg hx,SecondaryEStress.force_T_secondary,
    sub_self,circleSupport_zero,demand_eq,CoreEStress.DE_width_split hde,CoreEStress.EH_width_split heh]
  rw [width_eq (hsmall H),width_eq (hsmall A),width_eq (hsmall B),
    width_eq (hsmall T),width_eq ho.1,width_eq ho.2]
  rcases hab with rfl | rfl <;>
    simp [baseline,increment,halfShift,PositiveAngularEnvelope.phi] <;> ring

end SquaresInCircles.Eight.SoleEStress
