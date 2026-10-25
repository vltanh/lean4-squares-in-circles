module

public import SquaresInCircles.Eight.Boundary.ActualCoreEBlocks

/-!
# Eight squares: exact positive-primary stress with arbitrary normal E owners

The actual E force is evaluated at the original
point, rather than bounded by an outer-circle support. Each primary E
angle then appears in `charge`, and each secondary E angle remains in its
original H or D force. No E transport or boundary relabeling occurs here.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CoreEStress
open Candidate SignedStress PositiveAngularEnvelope PositivePrimaryBaselines
open SecondaryEStress ActualCoreEBlocks

def owners (ab bt td de eh : Fin 4) : Vertex → Fin 4 := ![2,1,ab,bt,td,de,eh]
def forces (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) : Vertex → Point :=
  force C (owners ab bt td de eh) (weights n k l b t)

theorem force_H {eh : Fin 4} (heh : eh=0 ∨ eh=1)
    (C : SignedCycle) (ab bt td de : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t H=
      rotatedPair 1 n (delta C.theta H) (ordinaryEH C eh) := by
  rcases heh with rfl | rfl <;>
    simp [forces,force,owners,weights,previous,word,H,E,source,target,
      add,scale,rotatedPair,ordinaryEH] <;> (try refine ⟨?_,?_⟩) <;> ring

theorem force_A {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (C : SignedCycle) (bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t A=
      rotatedPair k l (if ab=0 then 0 else delta C.theta A) 0 := by
  rcases hab with rfl | rfl
  · simp [forces,force,owners,weights,previous,word,A,source,target,
      add,scale,rotatedPair]
  · simp [forces,force,owners,weights,previous,word,A,source,target,
      add,scale,rotatedPair]
    ring

theorem force_B {ab bt : Fin 4} (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3)
    (C : SignedCycle) (td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t B=
      let v := rotatedPair b l (if ab=0 then delta C.theta A else 0)
        (if bt=2 then delta C.theta B else 0)
      (v.1,-v.2) := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;>
    simp [forces,force,owners,weights,previous,word,A,B,source,target,
      add,scale,rotatedPair] <;> ring

theorem force_D {td de : Fin 4} (htd : td=0 ∨ td=2) (hde : de=2 ∨ de=3)
    (C : SignedCycle) (ab bt eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t D=
      let v := rotatedPair 1 t (if td=0 then delta C.theta T else 0) (ordinaryDE C de)
      (v.1,-v.2) := by
  rcases htd with rfl | rfl <;> rcases hde with rfl | rfl <;>
    simp [forces,force,owners,weights,previous,word,T,D,source,target,
      add,scale,rotatedPair,ordinaryDE] <;> ring

theorem force_G (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t G=
      SecondaryEStress.forces C ab bt td n k l b t G := by
  simp [forces,SecondaryEStress.forces,force,owners,SecondaryEStress.owners,
    weights,previous,word,G,source,target,add,scale]

theorem force_T (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t T=
      SecondaryEStress.forces C ab bt td n k l b t T := by
  simp [forces,SecondaryEStress.forces,force,owners,SecondaryEStress.owners,
    weights,previous,word,T,source,target,add,scale]

theorem force_E {de eh : Fin 4} (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (C : SignedCycle) (ab bt td : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t E=
      (Real.sin (primaryDE C de)+Real.sin (primaryEH C eh),
        Real.cos (primaryEH C eh)-Real.cos (primaryDE C de)) := by
  rcases hde with rfl | rfl <;> rcases heh with rfl | rfl <;>
    simp [forces,force,owners,weights,previous,word,D,E,source,target,
      add,scale,primaryDE,primaryEH] <;> (try refine ⟨?_,?_⟩) <;> ring

def anchorNorms (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) : ℝ :=
  pairNorm 1 n (delta C.theta H+ordinaryEH C eh)+
  pairNorm k l (if ab=0 then 0 else delta C.theta A)+
  pairNorm l b ((if ab=0 then delta C.theta A else 0)+
    (if bt=2 then delta C.theta B else 0))+
  pairNorm 1 t (ordinaryDE C de+(if td=0 then delta C.theta T else 0))

def halfShift (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) : ℝ :=
  (n*PositiveAngularEnvelope.phi (delta C.theta H)+PositiveAngularEnvelope.phi (ordinaryEH C eh)+k+
    l*PositiveAngularEnvelope.phi (if ab=0 then 0 else delta C.theta A)+
    b*PositiveAngularEnvelope.phi (if bt=2 then delta C.theta B else 0)+
    l*PositiveAngularEnvelope.phi (if ab=0 then delta C.theta A else 0)+
    PositiveAngularEnvelope.phi (ordinaryDE C de)+t*PositiveAngularEnvelope.phi (if td=0 then delta C.theta T else 0))/2

def bound (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t R : ℝ) : Vertex → ℝ :=
  let F := forces C ab bt td de eh n k l b t
  ![signedSupport R 1 (F H),circleSupport R (F G),signedSupport R 1 (F A),
    signedSupport R (-1) (F B),circleSupport R (F T),signedSupport R (-1) (F D),
    work (F E) (C.point E)]

def defect (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t R : ℝ) : ℝ :=
  demand C (weights n k l b t)-∑ i,bound C ab bt td de eh n k l b t R i

def increment (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t R : ℝ) : ℝ :=
  n*psi (delta C.theta H)+l*psi (delta C.theta A)+
    b*psi (if bt=2 then delta C.theta B else 0)+
    t*psi (if td=0 then delta C.theta T else 0)+
    psi (ordinaryDE C de)+psi (ordinaryEH C eh)-
    R*(anchorNorms C ab bt td de eh n k l b t-zeroNorms n k l b t)

theorem increment_eq (C : SignedCycle) {ab bt td : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (de eh : Fin 4) (n k l b t R : ℝ) :
    increment C ab bt td de eh n k l b t R=
      ∑ i,(ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).increment R := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;> rcases htd with rfl | rfl <;>
    simp [increment,ActualCoreEBlocks.blocks,ActualOrdinaryBlocks.Block.increment,
      anchorNorms,zeroNorms,Fin.sum_univ_succ,pairNorm_symm k l,pairNorm_symm n 1] <;> ring_nf

theorem sum_bounds (C : SignedCycle) {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1) (n k l b t R : ℝ) :
    (∑ i,bound C ab bt td de eh n k l b t R i)=
      R*anchorNorms C ab bt td de eh n k l b t-halfShift C ab bt td de eh n k l b t+
      circleSupport R (forces C ab bt td de eh n k l b t G)+
      circleSupport R (forces C ab bt td de eh n k l b t T)+
      work (forces C ab bt td de eh n k l b t E) (C.point E) := by
  have hH := rotatedPair_signedSupport R 1 n (delta C.theta H) (ordinaryEH C eh)
  have hA := rotatedPair_signedSupport R k l (if ab=0 then 0 else delta C.theta A) 0
  have hB := reflected_rotatedPair_signedSupport R b l
    (if ab=0 then delta C.theta A else 0) (if bt=2 then delta C.theta B else 0)
  have hD := reflected_rotatedPair_signedSupport R 1 t
    (if td=0 then delta C.theta T else 0) (ordinaryDE C de)
  rw [pairNorm_symm b l] at hB
  have hsum : (∑ i,bound C ab bt td de eh n k l b t R i)=
      signedSupport R 1 (forces C ab bt td de eh n k l b t H)+
      circleSupport R (forces C ab bt td de eh n k l b t G)+
      signedSupport R 1 (forces C ab bt td de eh n k l b t A)+
      signedSupport R (-1) (forces C ab bt td de eh n k l b t B)+
      circleSupport R (forces C ab bt td de eh n k l b t T)+
      signedSupport R (-1) (forces C ab bt td de eh n k l b t D)+
      work (forces C ab bt td de eh n k l b t E) (C.point E) := by
    simp [bound,Fin.sum_univ_succ,H,G,A,B,T,D,E]
    ring
  rw [hsum,force_H heh,force_A hab,force_B hab hbt,force_D htd hde,hH,hA,hB,hD]
  simp only [phi_zero,mul_one,add_zero]
  dsimp [anchorNorms,halfShift]
  rw [add_comm (if td=0 then delta C.theta T else 0) (ordinaryDE C de)]
  ring

theorem necessary_at_cap {C : SignedCycle} {q : ℝ} {ab bt td de eh : Fin 4}
    {n k l b t : ℝ} (hq : q≤qCap) (hC : C.Necessary q)
    (hn : C.NormalAnchors) (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (owners ab bt td de eh i)) :
    defect C ab bt td de eh n k l b t (Real.sqrt qCap)≤0 := by
  have hweight : ∀ i,0≤weights n k l b t i := by
    intro i
    fin_cases i <;> simp [weights] <;>
      linarith [hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2]
  have hc (i : Vertex) : (C.point i).Contained ((Real.sqrt qCap)^2) := by
    rw [Real.sq_sqrt (show 0≤qCap by norm_num [qCap])]
    exact (hC.contained i).trans hq
  have hb : ∀ i,work (forces C ab bt td de eh n k l b t i) (C.point i)≤
      bound C ab bt td de eh n k l b t (Real.sqrt qCap) i := by
    intro i
    fin_cases i
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc H) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.H_nonneg]) _
    · exact work_le_circleSupport (Real.sqrt_nonneg _) (hC.sorted G) (hc G) _
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc A) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.A_nonneg]) _
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc B) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.B_nonpos]) _
    · exact work_le_circleSupport (Real.sqrt_nonneg _) (hC.sorted T) (hc T) _
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc D) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.D_nonpos]) _
    · exact le_rfl
  have hh := weighted_separation_le hweight hf hb
  dsimp [defect]
  linarith

theorem DE_width_split {de : Fin 4} (hde : de=2 ∨ de=3) (C : SignedCycle) :
    edgeWidth (delta C.theta D)=edgeWidth (ordinaryDE C de)+edgeWidth (primaryDE C de)-1 := by
  rcases hde with rfl | rfl <;> simp [ordinaryDE,primaryDE,edgeWidth,pairWidth]

theorem EH_width_split {eh : Fin 4} (heh : eh=0 ∨ eh=1) (C : SignedCycle) :
    edgeWidth (delta C.theta E)=edgeWidth (ordinaryEH C eh)+edgeWidth (primaryEH C eh)-1 := by
  rcases heh with rfl | rfl <;> simp [ordinaryEH,primaryEH,edgeWidth,pairWidth]

theorem td_decomposition {C : SignedCycle} {ab de eh : Fin 4} {R k l η : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hz : delta C.theta T∈Icc 0 frameCap) :
    defect C ab 2 2 de eh (tiltedWeight k η (delta C.theta G)) k l
        (tiltedWeight k η (delta C.theta T)) k R=
      tdBaseline R k l η (delta C.theta G) (delta C.theta T)+
        increment C ab 2 2 de eh (tiltedWeight k η (delta C.theta G)) k l
          (tiltedWeight k η (delta C.theta T)) k R+charge C de eh := by
  have ho := ordinary_small (de := de) (eh := eh) hsmall
  rw [defect,sum_bounds C hab (Or.inl rfl) (Or.inr rfl) hde heh,
    force_G,force_T,positive_G_support hk hη hx,positive_TD_support hk hη hz,
    force_E hde heh,demand_eq,DE_width_split hde,EH_width_split heh]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall B),width_eq (hsmall T),width_eq ho.1,width_eq ho.2,
    psi_positive hx,psi_positive hz]
  rcases hab with rfl | rfl <;>
    simp [tdBaseline,increment,halfShift,primaryCoefficient,primarySupport,
      tiltedWeight,PositiveAngularEnvelope.phi,ActualCoreEBlocks.charge,
      CoreECharge.pairDeficit,work] <;> ring

theorem bt_decomposition {C : SignedCycle} {ab de eh : Fin 4} {R k l η : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hz : delta C.theta B∈Icc 0 frameCap) :
    defect C ab 3 0 de eh (tiltedWeight k η (delta C.theta G)) k l k
        (tiltedWeight k η (delta C.theta B)) R=
      btBaseline R k l η (delta C.theta G) (delta C.theta B)+
        increment C ab 3 0 de eh (tiltedWeight k η (delta C.theta G)) k l k
          (tiltedWeight k η (delta C.theta B)) R+charge C de eh := by
  have ho := ordinary_small (de := de) (eh := eh) hsmall
  rw [defect,sum_bounds C hab (Or.inr rfl) (Or.inl rfl) hde heh,
    force_G,force_T,positive_G_support hk hη hx,positive_BT_support hk hη hz,
    force_E hde heh,demand_eq,DE_width_split hde,EH_width_split heh]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall B),width_eq (hsmall T),width_eq ho.1,width_eq ho.2,
    psi_positive hx,psi_positive hz]
  rcases hab with rfl | rfl <;>
    simp [btBaseline,increment,halfShift,primaryCoefficient,primarySupport,
      tiltedWeight,PositiveAngularEnvelope.phi,ActualCoreEBlocks.charge,
      CoreECharge.pairDeficit,work] <;> ring

theorem secondary_decomposition {C : SignedCycle} {ab de eh : Fin 4} {R k l c η : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) :
    defect C ab 2 0 de eh (tiltedWeight k η (delta C.theta G)) k l c c R=
      secondaryBaseline R k l c η (delta C.theta G)+
        increment C ab 2 0 de eh (tiltedWeight k η (delta C.theta G)) k l c c R+
          charge C de eh := by
  have ho := ordinary_small (de := de) (eh := eh) hsmall
  rw [defect,sum_bounds C hab (Or.inl rfl) (Or.inl rfl) hde heh,
    force_G,force_T,positive_G_support hk hη hx,SecondaryEStress.force_T_secondary,
    sub_self,circleSupport_zero,force_E hde heh,demand_eq,
    DE_width_split hde,EH_width_split heh]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall B),width_eq (hsmall T),width_eq ho.1,width_eq ho.2,psi_positive hx]
  rcases hab with rfl | rfl <;>
    simp [secondaryBaseline,increment,halfShift,primaryCoefficient,primarySupport,
      tiltedWeight,PositiveAngularEnvelope.phi,ActualCoreEBlocks.charge,
      CoreECharge.pairDeficit,work] <;> ring

theorem td_necessary {C : SignedCycle} {q k l η : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hl : 0≤l) (hη : 0≤η)
    (hx : 0≤delta C.theta G) (hz : 0≤delta C.theta T)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 de eh i)) :
    tdBaseline (Real.sqrt qCap) k l η (delta C.theta G) (delta C.theta T)+
      increment C ab 2 2 de eh (tiltedWeight k η (delta C.theta G)) k l
        (tiltedWeight k η (delta C.theta T)) k (Real.sqrt qCap)+charge C de eh≤0 := by
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hx' : delta C.theta G∈Icc 0 frameCap := ⟨hx,(le_abs_self _).trans (hs G)⟩
  have hz' : delta C.theta T∈Icc 0 frameCap := ⟨hz,(le_abs_self _).trans (hs T)⟩
  rw [← td_decomposition hab hde heh hk hη hs hx' hz']
  exact necessary_at_cap hq hC hn
    ⟨tiltedWeight_nonneg hk hη hx',hk,hl,tiltedWeight_nonneg hk hη hz',hk⟩ hf

theorem bt_necessary {C : SignedCycle} {q k l η : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hl : 0≤l) (hη : 0≤η)
    (hx : 0≤delta C.theta G) (hz : 0≤delta C.theta B)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 de eh i)) :
    btBaseline (Real.sqrt qCap) k l η (delta C.theta G) (delta C.theta B)+
      increment C ab 3 0 de eh (tiltedWeight k η (delta C.theta G)) k l k
        (tiltedWeight k η (delta C.theta B)) (Real.sqrt qCap)+charge C de eh≤0 := by
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hx' : delta C.theta G∈Icc 0 frameCap := ⟨hx,(le_abs_self _).trans (hs G)⟩
  have hz' : delta C.theta B∈Icc 0 frameCap := ⟨hz,(le_abs_self _).trans (hs B)⟩
  rw [← bt_decomposition hab hde heh hk hη hs hx' hz']
  exact necessary_at_cap hq hC hn
    ⟨tiltedWeight_nonneg hk hη hx',hk,hl,hk,tiltedWeight_nonneg hk hη hz'⟩ hf

theorem secondary_necessary {C : SignedCycle} {q k l c η : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hl : 0≤l) (hc : 0≤c) (hη : 0≤η)
    (hx : 0≤delta C.theta G)
    (hf : ∀ i,C.Feasible i (owners ab 2 0 de eh i)) :
    secondaryBaseline (Real.sqrt qCap) k l c η (delta C.theta G)+
      increment C ab 2 0 de eh (tiltedWeight k η (delta C.theta G)) k l c c
        (Real.sqrt qCap)+charge C de eh≤0 := by
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hx' : delta C.theta G∈Icc 0 frameCap := ⟨hx,(le_abs_self _).trans (hs G)⟩
  rw [← secondary_decomposition hab hde heh hk hη hs hx']
  exact necessary_at_cap hq hC hn ⟨tiltedWeight_nonneg hk hη hx',hk,hl,hc,hc⟩ hf

end SquaresInCircles.Eight.CoreEStress
