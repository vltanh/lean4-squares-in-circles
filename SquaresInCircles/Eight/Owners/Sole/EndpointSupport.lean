module

public import SquaresInCircles.Eight.Owners.OccupiedSignedConcentration
public import SquaresInCircles.Eight.Owners.Sole.NegativeTDSupport
public import SquaresInCircles.Eight.Owners.Sole.ECoefficients
public import SquaresInCircles.Eight.Owners.Sole.FixedSplit
public import SquaresInCircles.Eight.Owners.Sole.NormGain
public import SquaresInCircles.Eight.Owners.Sole.OrdinaryData
public import SquaresInCircles.Eight.Words.Core.EOrdinaryEnvelope

/-!
# Eight squares: the actual-radius E supports at the two intrinsic split endpoints

The high endpoint uses the complete circle support
in the positive folded direction. For sole-DE this support dominates
the work at the actual axis point of the same circle. No original
point is moved to that axis point, and no radius is enlarged.
-/

section
/-!
## Middle and high ordinary allocations reduce to actual pure charges

The growth reserve holds also for the middle sole-DE
coefficient cap 59/50. Every ordinary allocation is bounded by the least
of its four pure negative charges at the original total angle. The
endpoint positivity theorem below keeps all four strict alternatives.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleBalancedEnvelope
open SoleECoefficients SoleOrdinaryData SoleBalancedCoefficients SingleAngleConcavity

theorem ordinary_lower {b : Band} {de : Bool} {R t x e L : ℝ}
    (hb : b≠.low) (P N : Fin 4 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t+∑i,P i)
    (hsingle : ∀ i,single de i=true → P i=0 ∨ N i=0)
    (hpure : ∀ i,L≤pure (single de i) R (small b de t x e i)
      (large b de t x e i) (nu b de t x e i) t) :
    L≤∑i,F (single de i) R (small b de t x e i) (large b de t x e i)
      (nu b de t x e i) (P i) (N i) := by
  cases b
  · exact (hb rfl).elim
  · have hc := middle_conditions (de := de) ht hx he
    exact SoleAngleGrowth.balanced_envelope (single de) R (small .middle de t x e)
      (large .middle de t x e) (nu .middle de t x e) P N
      (qlo := 983/1000) (qhi := 59/50) hR hQL hQU (small_pos ht hx he)
      (small_le_large .middle de t x e) hc.1 (nu_between ht) hc.2 (by norm_num)
      hP hN (angle ht) hbudget hbalance hsingle hpure
  · have hc := high_conditions (de := de) ht hx he
    exact SoleAngleGrowth.balanced_envelope (single de) R (small .high de t x e)
      (large .high de t x e) (nu .high de t x e) P N
      (qlo := 1) (qhi := 113/100) hR hQL hQU (small_pos ht hx he)
      (small_le_large .high de t x e) hc.1 (nu_between ht) hc.2 (by norm_num)
      hP hN (angle ht) hbudget hbalance hsingle hpure

def minimumFour (f : Fin 4 → ℝ) : ℝ := min (f 0) (min (f 1) (min (f 2) (f 3)))

theorem minimumFour_le (f : Fin 4 → ℝ) (i : Fin 4) : minimumFour f≤f i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem minimumFour_positive {K : ℝ} {f : Fin 4 → ℝ}
    (hf : ∀ i,0<K+f i) : 0<K+minimumFour f := by
  have h0 : -K<f 0 := by linarith [hf 0]
  have h1 : -K<f 1 := by linarith [hf 1]
  have h2 : -K<f 2 := by linarith [hf 2]
  have h3 : -K<f 3 := by linarith [hf 3]
  have hh := lt_min h0 (lt_min h1 (lt_min h2 h3))
  change 0<K+min (f 0) (min (f 1) (min (f 2) (f 3)))
  linarith

end SquaresInCircles.Eight.SoleBalancedEnvelope
end
end
end

section
/-!
## Exact seven-edge stress with independent E-edge multipliers

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
      add,scale,rotatedPair]
  ring

theorem force_B {ab bt : Fin 4} (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3)
    (C : SignedCycle) (td de eh : Fin 4) (n k l b t p r : ℝ) :
    forces C ab bt td de eh n k l b t p r B=
      let v := rotatedPair b l (if ab=0 then delta C.theta A else 0)
        (if bt=2 then delta C.theta B else 0)
      (v.1,-v.2) := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,A,B,source,target,
      add,scale,rotatedPair] <;> ring

theorem force_D {td de : Fin 4} (htd : td=0 ∨ td=2) (hde : de=2 ∨ de=3)
    (C : SignedCycle) (ab bt eh : Fin 4) (n k l b t p r : ℝ) :
    forces C ab bt td de eh n k l b t p r D=
      let v := rotatedPair p t (if td=0 then delta C.theta T else 0) (ordinaryDE C de)
      (v.1,-v.2) := by
  rcases htd with rfl | rfl <;> rcases hde with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,T,D,source,target,
      add,scale,rotatedPair,ordinaryDE] <;> ring

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
end
end
end

section
/-!
## The low-family A charge and same-B-block comparison

The A angle keeps coefficient ell rather than the
larger force coefficient k. The positive cosine difference pays the
actual change from k to c. The same-block comparison uses the surviving
correlated trigonometric bound, whose ratio is weaker than the present
low-family ratio.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleLowAComparison
open SoleECoefficients SoleNormGain SingleAngleConcavity
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

theorem coefficient_interval {t : ℝ} (ht : t∈domain .low) :
    0<k .low t ∧ k .low t≤c .low t ∧
    (117/200)*c .low t≤ell .low t ∧ ell .low t≤(18/25)*k .low t ∧
    173/500<c .low t-ell .low t ∧ c .low t-k .low t=(3/10)*t := by
  have hb := low_bounds ht
  have hc := low_correlations ht
  have hp := positive ht
  have htc := mul_nonneg ht.1 hp.2.2.1.le
  refine ⟨hp.1,hb.2.2.1,?_,hc.2.2.1.le,hc.2.2.2,?_⟩
  · nlinarith [hc.1]
  · dsimp [c]
    ring

theorem cosine_loss_lower {t : ℝ} (ht : t∈Icc 0 (1/5 : ℝ)) :
    (299/600)*t^2≤1-Real.cos t := by
  have hc := cos_upper_four ht.1
  have ht2 : t^2≤1/25 := by
    have h := pow_le_pow_left₀ ht.1 ht.2 2
    norm_num at h
    linarith
  have ht4 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)
  nlinarith

theorem A_ge_B {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    Vnu R (ell .low t) (c .low t) (c .low t) t≤
      Vnu R (ell .low t) (k .low t) (ell .low t) t := by
  rcases coefficient_interval ht with ⟨hk,hkc,hr0,hr1,hcl,hck⟩
  have hg := coefficient_short hR hk hkc hr0 hr1 ht
  have hcos := cosine_loss_lower ht
  have hcos0 : 0≤1-Real.cos t := by linarith [Real.cos_le_one t]
  have hm := mul_le_mul_of_nonneg_right hcl.le hcos0
  have hm' := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤173/500)
  rw [hck] at hg
  dsimp [Vnu,V,normGain] at *
  nlinarith [sq_nonneg t]

theorem A_ge_B_at_cap {R t : ℝ} (hR : R∈Icc 0 2) (ht : t∈domain .low) :
    Vnu R (ell .low t) (c .low t) (c .low t) frameCap≤
      Vnu R (ell .low t) (k .low t) (ell .low t) frameCap := by
  rcases coefficient_interval ht with ⟨hk,hkc,hr0,hr1,hcl,hck⟩
  have hg := coefficient_cap hR hk hkc hr0 hr1
  have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hc : (117/500 : ℝ)≤1-Real.cos frameCap := by
    norm_num [frameCap] at hcos
    linarith
  have hm := mul_le_mul_of_nonneg_right hcl.le (show 0≤1-Real.cos frameCap by linarith)
  have hm' := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤173/500)
  have hcku : c .low t-k .low t≤3/50 := by rw [hck]; linarith [ht.2]
  dsimp [Vnu,V,normGain] at *
  linarith

theorem B_same_block {R t : ℝ} (ht : t∈domain .low) :
    V R (ell .low t) (c .low t) t≤M R (ell .low t) (c .low t) t := by
  have hc := (positive ht).2.2.1
  have hr := (low_correlations ht).1
  have htc := mul_nonneg ht.1 hc.le
  have hratio : PositiveStressCoefficients.ratio t*c .low t≤ell .low t := by
    dsimp [PositiveStressCoefficients.ratio]
    nlinarith
  have hh := CorrelatedSameBlock.negative_surplus (R := R) hc.le hratio (angle ht)
    (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
  have hid : mixedBlock R (ell .low t) (c .low t) (frameCap-t) frameCap=
      M R (ell .low t) (c .low t) t := by
    simpa only [show t+(frameCap-t)=frameCap by ring] using
      mixedBlock_saturated R (ell .low t) (c .low t) t
  simpa only [sub_zero,hid] using hh

end SquaresInCircles.Eight.SoleLowAComparison
end
end
end

section
/-!
## Every low-family ordinary allocation lies above the B charge

The coefficient data come from the actual original
split x,e. All signed ordinary allocations satisfying the exact balanced
variation equations are covered by continuous concentration. The gap at
the frame cap pays the universal positive-angle cost, with strict reserve.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleLowEnvelope
open SoleECoefficients SoleOrdinaryData SoleLowChargeBounds
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity

theorem pure_dominates {de : Bool} {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    V R (ell .low t) (c .low t) t≤
      pure (single de i) R (small .low de t x e i) (large .low de t x e i)
        (nu .low de t x e i) t ∧
    V R (ell .low t) (c .low t) frameCap≤
      pure (single de i) R (small .low de t x e i) (large .low de t x e i)
        (nu .low de t x e i) frameCap := by
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  fin_cases i
  · have hw := low_wide (de := de) ht hx he (Or.inl rfl)
    have hh := wide_dominates hR hQL hQU hw.1 (small_le_large .low de t x e 0)
      hw.2 ((nu_between ht 0).2.trans hw.2.2) ht
    cases de <;> simpa [single,SingleAngleConcavity.pure,nu,V,Vnu] using hh
  · rcases A_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    simp only [Fin.mk_one,Fin.isValue,hs,hl,hn,single,Matrix.cons_val_one,
      SingleAngleConcavity.pure]
    exact ⟨by simpa [V,Vnu] using SoleLowAComparison.A_ge_B ⟨hR,hR2⟩ ht,
      by simpa [V,Vnu] using SoleLowAComparison.A_ge_B_at_cap ⟨hR,hR2⟩ ht⟩
  · rcases B_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    simp [hs,hl,single,SingleAngleConcavity.pure]
  · have hw := low_wide (de := de) ht hx he (Or.inr rfl)
    have hh := wide_dominates hR hQL hQU hw.1 (small_le_large .low de t x e 3)
      hw.2 ((nu_between ht 3).2.trans hw.2.2) ht
    simpa [single,SingleAngleConcavity.pure,nu,V,Vnu] using hh

theorem same_block_dominates {de : Bool} {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (i : Fin 4) (hi : single de i=false) :
    V R (ell .low t) (c .low t) t≤
      M R (small .low de t x e i) (large .low de t x e i) t := by
  by_cases hB : i=2
  · subst i
    rcases B_data (de := de) (x := x) (e := e) ht with ⟨hs,hl,hn⟩
    rw [hs,hl]
    exact SoleLowAComparison.B_same_block ht
  have hwide : i=0 ∨ i=3 := by
    fin_cases i <;> simp_all [single]
  have hw := low_wide (de := de) ht hx he hwide
  have hp := small_pos (de := de) ht hx he i
  have hpq := small_le_large .low de t x e i
  have hratio : (2/3)*large .low de t x e i≤ small .low de t x e i := by
    dsimp [base] at hw
    linarith [hw.1,hw.2.2]
  have hM := M_ge_V (R := R) hp.le (hp.trans_le hpq).le (by linarith) (angle ht)
  have hV := (pure_dominates (de := de) hR hQL hQU ht hx he i).1
  simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte] at hV
  exact hV.trans hM

theorem positive_lower {de : Bool} {R t x e : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i : Fin 4) :
    -(763/2000 : ℝ)≤
      U R (small .low de t x e i) (large .low de t x e i) (frameCap-t) := by
  have hlen : 0≤frameCap-t := by linarith [(angle ht).2]
  have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (small_pos ht hx he i)
    (small_le_large .low de t x e i) (low_half_ratio ht hx he i)
    (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [ht.1]⟩)
  have hprod : large .low de t x e i*(frameCap-t)≤7/10 := by
    calc
      _≤(1+(7/10)*t)*(frameCap-t) :=
        mul_le_mul_of_nonneg_right (low_large_upper ht hx he i) hlen
      _≤7/10 := by dsimp [frameCap]; nlinarith [ht.1,sq_nonneg t]
  nlinarith

theorem separated_dominates {de : Bool} {R t x e : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (i j : Fin 4) :
    V R (ell .low t) (c .low t) t<
      U R (small .low de t x e i) (large .low de t x e i) (frameCap-t)+
      pure (single de j) R (small .low de t x e j) (large .low de t x e j)
        (nu .low de t x e j) frameCap := by
  have hU := positive_lower (de := de) hR hQU ht hx he i
  have hcap := (pure_dominates (de := de) hR hQL hQU ht hx he j).2
  have hgap := SoleLowGap.B_gap hR hQL ht
  linarith

/-- A closed analytic lower envelope with the original split coefficients.
The remaining arguments are the actual variation and one-angle data,
which are constructed from the original signed blocks in the next layer. -/
theorem ordinary_lower {de : Bool} {R t x e : ℝ} (P N : Fin 4 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t+∑i,P i)
    (hsingle : ∀ i,single de i=true → P i=0 ∨ N i=0) :
    V R (ell .low t) (c .low t) t≤
      ∑i,F (single de i) R (small .low de t x e i) (large .low de t x e i)
        (nu .low de t x e i) (P i) (N i) := by
  apply SingleAngleConcentration.lower_from_endpoints (single de) R
    (small .low de t x e) (large .low de t x e) (nu .low de t x e) P N
    hR hQU (small_pos ht hx he) (small_le_large .low de t x e)
    (low_half_ratio ht hx he) (fun i => (nu_between ht i).1)
    hP hN (angle ht) hbudget hbalance hsingle
  · intro i
    exact (pure_dominates hR hQL hQU ht hx he i).1
  · intro i hi
    exact same_block_dominates hR hQL hQU ht hx he i hi
  · intro i j _
    exact (separated_dominates hR hQL hQU ht hx he i j).le

end SquaresInCircles.Eight.SoleLowEnvelope
end
end
end

section
/-!
## The sole-E envelopes applied to the original signed cycle

The actual AB weak owner chooses which block contains
its signed angle. Only the selected positive E primary leaves the
ordinary budget. The coefficient split x,e may vary while the original
ordinary angles and their exact positive/negative totals stay fixed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleOriginalBlocks
open Candidate SoleECoefficients SoleOrdinaryData ActualOrdinaryBlocks
open ActualCoreEBlocks PositiveAngularEnvelope SingleAngleConcavity

def deOwner (de : Bool) : Fin 4 := if de then 3 else 2
def ehOwner (de : Bool) : Fin 4 := if de then 0 else 1
def primary (C : SignedCycle) (de : Bool) : ℝ :=
  if de then delta C.theta D else delta C.theta E
def eMultiplier (b : Band) (de : Bool) (t e : ℝ) : ℝ := if de then 1 else p b t e
def hMultiplier (b : Band) (de : Bool) (e : ℝ) : ℝ := if de then r b e else 1

def blocks (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t x e : ℝ) :
    Fin 4 → Block :=
  SoleEStress.blocks C ab 2 0 (deOwner de) (ehOwner de)
    (n b t x) (k b t) (ell b t) (c b t) (c b t)
    (eMultiplier b de t e) (hMultiplier b de e)

def increment (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (R t x e : ℝ) : ℝ :=
  SoleEStress.increment C ab 2 0 (deOwner de) (ehOwner de)
    (n b t x) (k b t) (ell b t) (c b t) (c b t)
    (eMultiplier b de t e) (hMultiplier b de e) R

theorem deOwner_cases (de : Bool) : deOwner de=2 ∨ deOwner de=3 := by
  cases de <;> simp [deOwner]
theorem ehOwner_cases (de : Bool) : ehOwner de=0 ∨ ehOwner de=1 := by
  cases de <;> simp [ehOwner]

theorem eTotal_eq (C : SignedCycle) (de : Bool) :
    eTotal C (deOwner de) (ehOwner de)=primary C de := by
  cases de <;> simp [eTotal,primaryDE,primaryEH,deOwner,ehOwner,primary]

theorem coefficients (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool)
    (t x e : ℝ) (i : Fin 4) :
    (blocks C ab b de t x e i).p=small b de t x e i ∧
    (blocks C ab b de t x e i).q=large b de t x e i := by
  fin_cases i <;> cases de <;>
    simp [blocks,SoleEStress.blocks,Block.p,Block.q,small,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,
      eMultiplier,hMultiplier,min_comm,max_comm]

theorem single_data (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool)
    (t x e : ℝ) (i : Fin 4) (hi : single de i=true) :
    (blocks C ab b de t x e i).v=0 ∧
      (blocks C ab b de t x e i).alpha=nu b de t x e i := by
  fin_cases i <;> cases de <;>
    simp_all [single,blocks,SoleEStress.blocks,nu,ehOwner,ordinaryEH,eMultiplier,hMultiplier]

theorem angles_small {C : SignedCycle} (ab : Fin 4) (b : Band) (de : Bool) (t x e : ℝ)
    (hs : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 4) :
    |(blocks C ab b de t x e i).u|≤frameCap ∧
      |(blocks C ab b de t x e i).v|≤frameCap := by
  have hzero : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hA : |if ab=0 then 0 else delta C.theta A|≤frameCap := by
    split_ifs <;> first | exact hzero | exact hs A
  have hB : |if ab=0 then delta C.theta A else 0|≤frameCap := by
    split_ifs <;> first | exact hzero | exact hs A
  have ho := ordinary_small (de := deOwner de) (eh := ehOwner de) hs
  fin_cases i <;> simp [blocks,SoleEStress.blocks,hs H,hs B,hs T,hA,hB,ho.1,ho.2]
  all_goals norm_num [frameCap]

theorem parts (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool)
    (t x e : ℝ) (i : Fin 4) :
    (blocks C ab b de t x e i).P=
      (ActualCoreEBlocks.blocks C ab 2 0 (deOwner de) (ehOwner de)
        (n b t x) (k b t) (ell b t) (c b t) (c b t) i).P ∧
    (blocks C ab b de t x e i).N=
      (ActualCoreEBlocks.blocks C ab 2 0 (deOwner de) (ehOwner de)
        (n b t x) (k b t) (ell b t) (c b t) (c b t) i).N := by
  fin_cases i <;> constructor <;> rfl

theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (b : Band) (de : Bool) (t x e : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hE : 0≤primary C de) (htotal : delta C.theta G+primary C de=t) :
    0≤t ∧ (∑i,(blocks C ab b de t x e i).P)≤frameCap-t ∧
      (∑i,(blocks C ab b de t x e i).N)=t+∑i,(blocks C ab b de t x e i).P := by
  have hh := ActualCoreEBlocks.block_budgets hab (Or.inl rfl) (Or.inl rfl)
    (deOwner_cases de) (ehOwner_cases de) (n b t x) (k b t) (ell b t) (c b t) (c b t)
    hvar hG (by intro h; norm_num at h) (by intro h; norm_num at h)
    (by simpa only [eTotal_eq] using hE)
  have hP := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => (parts C ab b de t x e i).1)
  have hN := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => (parts C ab b de t x e i).2)
  simp only [removed,eTotal_eq,show (2:Fin 4)≠3 by decide,
    show (0:Fin 4)≠2 by decide,ite_false,add_zero] at hh
  refine ⟨by linarith,?_,?_⟩
  · rw [hP]
    linarith [hh.2.2.1]
  · rw [hN,hP]
    linarith [hh.2.2.2]

theorem individual_budgets {C : SignedCycle} {ab : Fin 4} {b : Band} {de : Bool} {t x e : ℝ}
    (ht : 0≤t) (hP : (∑i,(blocks C ab b de t x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab b de t x e i).N)=t+∑i,(blocks C ab b de t x e i).P)
    (i : Fin 4) :
    (blocks C ab b de t x e i).P≤frameCap ∧ (blocks C ab b de t x e i).N≤frameCap := by
  have hpi := Finset.single_le_sum (fun j _ => (blocks C ab b de t x e j).P_nonneg)
    (Finset.mem_univ i)
  have hni := Finset.single_le_sum (fun j _ => (blocks C ab b de t x e j).N_nonneg)
    (Finset.mem_univ i)
  constructor <;> linarith

theorem single_parts (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool)
    (t x e : ℝ) (i : Fin 4) (hi : single de i=true) :
    (blocks C ab b de t x e i).P=0 ∨ (blocks C ab b de t x e i).N=0 := by
  have hv := (single_data C ab b de t x e i hi).1
  by_cases hu : 0≤(blocks C ab b de t x e i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right (show -(blocks C ab b de t x e i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]

theorem one_angle_minorant (B : Block) (R : ℝ) (hv : B.v=0) (hu : |B.u|≤frameCap) :
    F true R B.p B.q B.alpha B.P B.N≤B.increment R := by
  have hh := single_minorant (R := R) (p := B.p) (q := B.q) (nu := B.alpha)
    (min_le_left B.alpha B.beta) hu
  have hnorm := B.norm_min_max B.u
  have hnorm0 := B.norm_min_max 0
  simpa [Block.P,Block.N,Block.increment,hv,hnorm,hnorm0] using hh

theorem block_minorant {C : SignedCycle} {ab : Fin 4} {b : Band} {de : Bool} {R t x e : ℝ}
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab b de t x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab b de t x e i).N)=t+∑i,(blocks C ab b de t x e i).P)
    (i : Fin 4) :
    F (single de i) R (small b de t x e i) (large b de t x e i)
      (nu b de t x e i) (blocks C ab b de t x e i).P (blocks C ab b de t x e i).N≤
      (blocks C ab b de t x e i).increment R := by
  obtain ⟨hp,hq⟩ := coefficients C ab b de t x e i
  have hb := individual_budgets (angle ht).1 hP hN i
  by_cases hi : single de i=true
  · obtain ⟨hv,hnu⟩ := single_data C ab b de t x e i hi
    have hh := one_angle_minorant (blocks C ab b de t x e i) R hv
      (angles_small ab b de t x e hsmall i).1
    simpa only [hi,hp,hq,hnu] using hh
  · have hi' : single de i=false := Bool.eq_false_of_not_eq_true hi
    have hh := (blocks C ab b de t x e i).minorant R
      (by rw [hp]; exact (small_pos ht hx he i).le) hb.1 hb.2
    simpa only [F,hi',Bool.false_eq_true,↓reduceIte,hp,hq] using hh

theorem sum_minorant {C : SignedCycle} {ab : Fin 4} {b : Band} {de : Bool} {R t x e : ℝ}
    (hab : ab=0 ∨ ab=2) (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab b de t x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab b de t x e i).N)=t+∑i,(blocks C ab b de t x e i).P) :
    (∑i,F (single de i) R (small b de t x e i) (large b de t x e i)
      (nu b de t x e i) (blocks C ab b de t x e i).P (blocks C ab b de t x e i).N)≤
      increment C ab b de R t x e := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => block_minorant (R := R) ht hx he hsmall hP hN i)
  have heq := SoleEStress.increment_eq C hab (Or.inl rfl) (Or.inl rfl)
    (deOwner de) (ehOwner de) (n b t x) (k b t) (ell b t) (c b t) (c b t)
    (eMultiplier b de t e) (hMultiplier b de e) R
  simpa only [increment,blocks,heq] using hh

theorem low_original_increment {C : SignedCycle} {ab : Fin 4} {de : Bool} {R t x e : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain .low) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t) :
    OrdinaryAngleConcavity.V R (ell .low t) (c .low t) t≤ increment C ab .low de R t x e := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab .low de t x e hvar hG hE htotal
  have hh := SoleLowEnvelope.ordinary_lower
    (fun i => (blocks C ab .low de t x e i).P) (fun i => (blocks C ab .low de t x e i).N)
    hR hQL hQU ht hx he (fun i => (blocks C ab .low de t x e i).P_nonneg)
    (fun i => (blocks C ab .low de t x e i).N_nonneg) hP hN
    (single_parts C ab .low de t x e)
  exact hh.trans (sum_minorant hab ht hx he hsmall hP hN)

theorem balanced_original_increment {C : SignedCycle} {ab : Fin 4} {b : Band} {de : Bool}
    {R t x e L : ℝ} (hb : b≠.low)
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t)
    (hpure : ∀ i,L≤pure (single de i) R (small b de t x e i)
      (large b de t x e i) (nu b de t x e i) t) :
    L≤ increment C ab b de R t x e := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab b de t x e hvar hG hE htotal
  have hh := SoleBalancedEnvelope.ordinary_lower hb
    (fun i => (blocks C ab b de t x e i).P) (fun i => (blocks C ab b de t x e i).N)
    hR hQL hQU ht hx he (fun i => (blocks C ab b de t x e i).P_nonneg)
    (fun i => (blocks C ab b de t x e i).N_nonneg) hP hN
    (single_parts C ab b de t x e) hpure
  exact hh.trans (sum_minorant hab ht hx he hsmall hP hN)

end SquaresInCircles.Eight.SoleOriginalBlocks
end
end
end

section
/-!
## A primary split at fixed coordinates for the sole-E stress

The four anchor coordinates and every signed ordinary angle are fixed; only the positive primary
parameters `x` and `t - x` vary in the scalar `value` (`formula`). The high sole-EH expression uses
`|E.y|`, so its concavity needs no sign of E, and sole-DE uses the axis bound `M` in place of the
work of E (`concave`). Positivity at both endpoints gives positivity on the split
(`positive_of_endpoints`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleSplitModel
open Candidate SoleECoefficients SoleResiduals SoleOriginalBlocks
open PositiveAngularEnvelope SecondaryEStress

def transverse (C : SignedCycle) : ℝ :=
  edgeWidth (delta C.theta H)-(C.point H).a*Real.sin (delta C.theta H)-
    |(C.point H).y| *Real.cos (delta C.theta H)

def radial (C : SignedCycle) (de : Bool) : ℝ :=
  if de then edgeWidth (delta C.theta E)-(C.point H).a*Real.cos (delta C.theta E)-
    |(C.point H).y| *Real.sin (delta C.theta E)
  else edgeWidth (delta C.theta D)-(C.point D).a*Real.cos (delta C.theta D)-
    |(C.point D).y| *Real.sin (delta C.theta D)

def constant (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t : ℝ) : ℝ :=
  ell b t*(edgeWidth (delta C.theta A)-C.edge A ab)+
    c b t*(edgeWidth (delta C.theta B)-C.edge B 2)+
    c b t*(edgeWidth (delta C.theta T)-C.edge T 0)-k b t*(C.point A).a-
    (if de then (C.point D).a else (C.point H).a)

def eBound (C : SignedCycle) (b : Band) (de : Bool) (R M t e : ℝ) : ℝ :=
  if b=.high then
    if de then M*Real.sin e
    else (C.point E).a*Real.sin e+|(C.point E).y| *(1-Real.cos e)
  else (if de then M else sigma R (eta b t))*Real.sin e

def value (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (R M t x : ℝ) : ℝ :=
  if b=.high then
    SoleFixedSplit.high (constant C ab b de t+radial C de) (transverse C)
      (k b t) (g b t) (sigma R (g b t))
      (if de then M else (C.point E).a) (if de then 0 else |(C.point E).y|) t x
  else
    SoleFixedSplit.tilted (constant C ab b de t) (transverse C) (radial C de)
      (k b t) (g b t) (if de then 7/10 else eta b t)
      (sigma R (g b t)) (if de then M else sigma R (eta b t)) t x

theorem formula {C : SignedCycle} (ab : Fin 4) {b : Band} (de : Bool)
    (R M : ℝ) {t x : ℝ} (ht : t∈domain b) (hx : x∈Icc 0 t) :
    value C ab b de R M t x=
      constant C ab b de t+n b t x*transverse C+k b t*edgeWidth x-
        k b t*sigma R (g b t)*Real.sin x+
        (if de then r b (t-x) else p b t (t-x))*radial C de+
        edgeWidth (t-x)-eBound C b de R M t (t-x) := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans (angle ht).2⟩
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,(angle ht).2]⟩
  cases b <;> cases de <;>
    simp [value,eBound,SoleFixedSplit.tilted_formula,SoleFixedSplit.high_formula,
      n,p,r,tiltedWeight,edgeWidth_positive_formula hx',edgeWidth_positive_formula he] <;> ring

theorem coefficient_ranges {b : Band} {t : ℝ} (ht : t∈domain b) :
    (431/500 : ℝ)≤k b t ∧ g b t∈Icc (1/4 : ℝ) (7/20) ∧
      eta b t∈Icc (1/4 : ℝ) (7/20) := by
  cases b
  · rcases low_bounds ht with ⟨hk0,hk1,hkc,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
    dsimp [g]
    exact ⟨by linarith,⟨by norm_num,by norm_num⟩,⟨by linarith,by linarith⟩⟩
  · rcases middle_bounds ht with ⟨hk0,hk1,hc0,hc1,hl0,hl1,hlk,hcl,he0,he1⟩
    dsimp [g]
    exact ⟨by linarith,⟨by norm_num,by norm_num⟩,⟨by linarith,by linarith⟩⟩
  · rcases high_bounds ht with ⟨hk0,hk1,hc,hl0,hl1,hlk,hcl,hg0,hg1⟩
    dsimp [eta]
    exact ⟨by linarith,⟨by linarith,by linarith⟩,⟨by norm_num,by norm_num⟩⟩

theorem residual_bounds {C : SignedCycle} (de : Bool)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    -(13/200 : ℝ)≤transverse C ∧ -(83/200 : ℝ)≤radial C de := by
  refine ⟨(transverse_residual (hs H) (hc H) (ha H)).le,?_⟩
  cases de
  · exact (radial_residual (hs D) (hc D) (ha D)).le
  · exact (radial_residual (hs H) (hc H) (ha E)).le

/-- The scalar is concave in the split; this comes before the works of the four anchors are bounded
by their norm supports. -/
theorem concave {C : SignedCycle} (ab : Fin 4) {b : Band} (de : Bool) {R M t : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap) (hM : M≤283/200) (ht : t∈domain b)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    ConcaveOn ℝ (Icc 0 t) (value C ab b de R M t) := by
  obtain ⟨hMH,hMX⟩ := residual_bounds de hs hc ha
  obtain ⟨hk,hg,heta⟩ := coefficient_ranges ht
  have hG := (tilt_reserve hR hQU hg).le
  have hEta := (tilt_reserve hR hQU heta).le
  cases b
  · apply SoleFixedSplit.tilted_concave hMH hMX hk
      (by norm_num [g]) (by cases de <;> simp <;> linarith [heta.1]) hG
    · cases de <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
        linarith [heta.2]
    · exact ⟨ht.1,by linarith [ht.2]⟩
  · apply SoleFixedSplit.tilted_concave hMH hMX hk
      (by norm_num [g]) (by cases de <;> simp <;> linarith [heta.1]) hG
    · cases de <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
        linarith [heta.2]
    · exact ⟨(angle ht).1,ht.2⟩
  · have hb := high_bounds ht
    apply SoleFixedSplit.high_concave hMH ⟨hb.1,hb.2.1⟩
      ⟨by linarith [hg.1],hb.2.2.2.2.2.2.2.2⟩ hG
    · cases de
      · exact (contained_bounds (hs E) (hc E)).1.le
      · exact hM
    · cases de <;> simp
    · exact angle ht

theorem positive_of_endpoints {C : SignedCycle} {ab : Fin 4} {b : Band} {de : Bool}
    {R M t x : ℝ} (hconc : ConcaveOn ℝ (Icc 0 t) (value C ab b de R M t))
    (hx : x∈Icc 0 t) (h0 : 0<value C ab b de R M t 0)
    (h1 : 0<value C ab b de R M t t) : 0<value C ab b de R M t x := by
  exact (lt_min h0 h1).trans_le (hconc.min_le_of_mem_Icc
    (left_mem_Icc.mpr (hx.1.trans hx.2)) (right_mem_Icc.mpr (hx.1.trans hx.2)) hx)

end SquaresInCircles.Eight.SoleSplitModel
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleEndpointSupport
open Candidate SignedStress SoleECoefficients SoleResiduals SoleSplitModel

def highWork (R t : ℝ) : ℝ :=
  2*R*Real.sin (t/2)-(Real.sin t+1-Real.cos t)/2

def endpointWork (b : Band) (de : Bool) (R M t : ℝ) : ℝ :=
  if b=.high then highWork R t
  else if de then M*Real.sin t else sigma R (eta b t)*Real.sin t

theorem high_circle_support (R : ℝ) {t : ℝ} (ht : t∈Icc 0 frameCap) :
    circleSupport R (Real.sin t,1-Real.cos t)=highWork R t := by
  have hs := (transport_trig ht).2.2.1
  have hc : 0≤1-Real.cos t := sub_nonneg.mpr (Real.cos_le_one t)
  have hh : t/2∈Icc 0 frameCap := by
    have h1 := ht.1
    have h2 := ht.2
    simp only [frameCap] at h2 ⊢
    constructor <;> linarith
  have hsh := (transport_trig hh).2.2.1
  have hdouble := Real.cos_two_mul (t/2)
  rw [show 2*(t/2)=t by ring] at hdouble
  have hcos : Real.cos t=1-2*(Real.sin (t/2))^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (t/2)]
  have hnorm : (Real.sin t)^2+(1-Real.cos t)^2=(2*Real.sin (t/2))^2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  simp only [circleSupport,hnorm,Real.sqrt_sq_eq_abs,abs_of_nonneg hs,
    abs_of_nonneg hc,abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hsh),highWork]
  ring

theorem actual_axis {q : ℝ} (hq : qLow≤q) :
    0<axisCoordinate q ∧ (⟨axisCoordinate q,0⟩ : SignedPoint).Contained q := by
  have hq' : 0≤q-1/4 := by dsimp [qLow] at hq; linarith
  have hs := Real.sqrt_nonneg (q-1/4)
  have hsq := Real.sq_sqrt hq'
  constructor
  · dsimp [axisCoordinate]
    dsimp [qLow] at hq
    nlinarith
  · change (axisCoordinate q+1/2)^2+(|0|+1/2)^2≤q
    simp only [axisCoordinate,abs_zero]
    nlinarith

theorem primary_le_axis {q : ℝ} {p : SignedPoint}
    (hq : qLow≤q) (_hs : p.Sorted) (hc : p.Contained q) : p.a≤axisCoordinate q := by
  have hq' : 0≤q-1/4 := by dsimp [qLow] at hq; linarith
  have hroot := Real.sqrt_nonneg (q-1/4)
  have hsq := Real.sq_sqrt hq'
  have hcircle : (p.a+1/2)^2+(|p.y|+1/2)^2≤q := hc
  have hsmall : (p.a+1/2)^2≤q-1/4 := by
    nlinarith [abs_nonneg p.y,sq_nonneg |p.y|]
  dsimp [axisCoordinate]
  nlinarith

theorem axis_work_le {q t : ℝ} (hq : qLow≤q) (ht : t∈Icc 0 frameCap) :
    axisCoordinate q*Real.sin t≤highWork (Real.sqrt q) t := by
  obtain ⟨ha,hc⟩ := actual_axis hq
  have hq0 : 0≤q := by dsimp [qLow] at hq; linarith
  have hs : (⟨axisCoordinate q,0⟩ : SignedPoint).Sorted := by
    exact ⟨ha,by simpa using ha.le⟩
  have hc' : (⟨axisCoordinate q,0⟩ : SignedPoint).Contained ((Real.sqrt q)^2) := by
    simpa only [Real.sq_sqrt hq0] using hc
  have hw := work_le_circleSupport (Real.sqrt_nonneg q) hs hc'
    (Real.sin t,1-Real.cos t)
  rw [high_circle_support (Real.sqrt q) ht] at hw
  simpa [work,mul_comm] using hw

theorem folded_work_le {p : SignedPoint} {R t : ℝ} (hR : 0≤R)
    (hs : p.Sorted) (hc : p.Contained (R^2)) (ht : t∈Icc 0 frameCap) :
    p.a*Real.sin t+|p.y| *(1-Real.cos t)≤highWork R t := by
  let pf : SignedPoint := ⟨p.a,|p.y|⟩
  have hsf : pf.Sorted := ⟨hs.1,by simpa [pf] using hs.2⟩
  have hcf : pf.Contained (R^2) := by simpa [pf,SignedPoint.Contained,SignedPoint.circle] using hc
  have hh := work_le_circleSupport hR hsf hcf (Real.sin t,1-Real.cos t)
  rw [high_circle_support R ht] at hh
  simpa [work,pf,mul_comm] using hh

theorem at_G (C : SignedCycle) (b : Band) (de : Bool) (R M t : ℝ) :
    eBound C b de R M t 0=0 := by
  cases b <;> cases de <;> simp [eBound]

theorem at_E {C : SignedCycle} {b : Band} (de : Bool) {q t : ℝ}
    (hq : qLow≤q) (ht : t∈domain b)
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained q) :
    eBound C b de (Real.sqrt q) (axisCoordinate q) t t≤
      endpointWork b de (Real.sqrt q) (axisCoordinate q) t := by
  have hq0 : 0≤q := by dsimp [qLow] at hq; linarith
  by_cases hb : b=.high
  · subst b
    cases de
    · have hh := folded_work_le (Real.sqrt_nonneg q) hs
        (by simpa only [Real.sq_sqrt hq0] using hc) (angle ht)
      simpa [eBound,endpointWork] using hh
    · simpa [eBound,endpointWork] using axis_work_le hq (angle ht)
  · simp [eBound,endpointWork,hb]

end SquaresInCircles.Eight.SoleEndpointSupport
end
end
end
