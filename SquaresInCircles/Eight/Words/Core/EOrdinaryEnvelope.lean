module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Boundary.ActualSortedSupport
public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Owners.Flat.TStress
public import SquaresInCircles.Eight.Owners.Positive.SecondaryEExclusion

/-!
# Eight squares: concentration with the nonnegative signed E charge

The stress coefficients are fixed at the positive G/T total. Concavity then varies only the
analytic E charge and the ordinary sign totals. The varying-coefficient comparison is used at
E-total zero only. The final theorem `actual_lower` allows both E owners and opposite individual
E signs.
-/

section
/-!
## The far negative endpoint on the full core-E coefficient rectangle

At the one fixed far angle the negative norm
denominator is small enough to give separate concavity in both force
coefficients, including their ratios below one half.  Four intrinsic
coefficient corners then give the bound on the whole rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CoreEFarEndpoint
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison

def R : ℝ := Real.sqrt qCap
def Rlower : ℝ := 158303/80000
def F (p q : ℝ) : ℝ := V R p q frameCap-p+87/1250

theorem cap_mem : frameCap∈Icc 0 frameCap := by
  exact ⟨by norm_num [frameCap],le_rfl⟩

theorem radius_lower : Rlower<R := by
  have hs := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hn := Real.sqrt_nonneg qCap
  dsimp [R,Rlower,qCap] at *
  nlinarith

theorem rectangle_ratio {p q : ℝ}
    (hp : p∈Icc (1263/2500:ℝ) (4/5))
    (hq : q∈Icc (863/1000:ℝ) (26/25)) :
    0<p ∧ 0<q ∧ p/q∈Icc (12/25:ℝ) 1 := by
  have hp0 : 0<p := by linarith [hp.1]
  have hq0 : 0<q := by linarith [hq.1]
  refine ⟨hp0,hq0,?_,?_⟩
  · exact (le_div_iff₀ hq0).2 (by linarith [hp.1,hq.2])
  · exact (div_le_one hq0).2 (by linarith [hp.2,hq.1])

/-- The strict denominator comparison used by both coefficient Hessians.
The range begins at `.48`, so no half-ratio restriction is imported. -/
theorem far_fraction {r : ℝ} (hr : r∈Icc (12/25:ℝ) 1) :
    1/(shape r)^3<(Real.cos frameCap)^2/(root r (Real.sin frameCap))^3 := by
  have hr0 : 0<r := by linarith [hr.1]
  have hu := sin_mem cap_mem
  have hN := root_pos r hu
  have hS := shape_pos r
  have hN2 := root_sq r hu
  have hS2 := shape_sq r
  have hratio : (39/50)*(1+r^2)≤2*r := by
    have hh := mul_nonneg (show 0≤r-12/25 by linarith [hr.1])
      (show 0≤1-r by linarith [hr.2])
    nlinarith [hr.1]
  have hsin := mul_lt_mul_of_pos_left cap_sin_lower (by linarith : 0<2*r)
  have hhalf : (root r (Real.sin frameCap))^2<(shape r)^2/2 := by
    nlinarith [sq_nonneg r]
  have hNS : root r (Real.sin frameCap)<shape r := by
    nlinarith
  have hcos := (transport_trig cap_mem).1
  have hcos2 : (1/2:ℝ)<(Real.cos frameCap)^2 := by
    have hh : 0<(Real.cos frameCap-478/625)*(Real.cos frameCap+478/625) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hcube1 := mul_lt_mul_of_pos_right hhalf hN
  have hcube2 := mul_lt_mul_of_pos_left hNS
    (show 0<(shape r)^2/2 by positivity)
  have hcube3 := mul_lt_mul_of_pos_right hcos2 (pow_pos hS 3)
  have hcube : (root r (Real.sin frameCap))^3<
      (Real.cos frameCap)^2*(shape r)^3 := by
    nlinarith only [hcube1,hcube2,hcube3]
  exact (div_lt_div_iff₀ (pow_pos hS 3) (pow_pos hN 3)).2 (by simpa using hcube)

def smallerSecond (r : ℝ) : ℝ :=
  R*(1/(shape r)^3-(Real.cos frameCap)^2/(root r (Real.sin frameCap))^3)

theorem smallerD_deriv (r : ℝ) :
    HasDerivAt (fun a => smallerD R a frameCap) (smallerSecond r) r := by
  have hu := sin_mem cap_mem
  have hn := (root_pos r hu).ne'
  have hs := (shape_pos r).ne'
  have hS2 := shape_sq r
  have hN2 := root_sq r hu
  have hraw := (((hasDerivAt_id' r).div (shape_hasDerivAt r) hs).sub
    (((hasDerivAt_id' r).sub_const (Real.sin frameCap)).div
      (root_hasDerivAt_r hu) hn)).const_mul R
  have hc : (Real.cos frameCap)^2=1-(Real.sin frameCap)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq frameCap]
  have e1 : (1*shape r-r*(r/shape r))/(shape r)^2=1/(shape r)^3 := by
    field_simp
    linear_combination hS2
  have e2 : (1*root r (Real.sin frameCap)-(r-Real.sin frameCap)*
      ((r-Real.sin frameCap)/root r (Real.sin frameCap)))/(root r (Real.sin frameCap))^2=
      (Real.cos frameCap)^2/(root r (Real.sin frameCap))^3 := by
    rw [hc]
    field_simp
    linear_combination hN2
  rw [e1,e2] at hraw
  exact hraw

theorem smallerSecond_nonpos {r : ℝ} (hr : r∈Icc (12/25:ℝ) 1) :
    smallerSecond r≤0 := by
  dsimp [smallerSecond]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg qCap)
    (sub_nonpos.mpr (far_fraction hr).le)

theorem far_Dr_nonneg {r : ℝ} (hr : r∈Icc (12/25:ℝ) 1) :
    0≤Dr R r frameCap := by
  dsimp [Dr]
  exact mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg qCap) (by linarith [hr.1]))
    (sub_nonneg.mpr (far_fraction hr).le)

theorem F_concave_p {q : ℝ} (hq : q∈Icc (863/1000:ℝ) (26/25)) :
    ConcaveOn ℝ (Icc (1263/2500:ℝ) (4/5)) (fun p => F p q) := by
  have hq0 : 0<q := by linarith [hq.1]
  apply concave_of_deriv2
    (f' := fun p => smallerD R (p/q) frameCap-1)
    (f'' := fun p => smallerSecond (p/q)*(1/q))
  · intro p hp
    have hp0 := (rectangle_ratio hp hq).1
    have h1 : HasDerivAt (fun x => V R x q frameCap) (smallerD R (p/q) frameCap) p :=
      V_hasDerivAt_p hp0 hq0 cap_mem
    have h2 : HasDerivAt (fun x => V R x q frameCap-x+87/1250)
        (smallerD R (p/q) frameCap-1) p :=
      (h1.fun_sub (hasDerivAt_id' p)).add_const (87/1250)
    exact h2
  · intro p _
    have hd : HasDerivAt (fun x : ℝ => x/q) (1/q) p := (hasDerivAt_id' p).div_const q
    have hh := (smallerD_deriv (p/q)).comp p hd
    exact hh.sub_const 1
  · intro p hp
    exact mul_nonpos_of_nonpos_of_nonneg
      (smallerSecond_nonpos (rectangle_ratio hp hq).2.2) (one_div_pos.mpr hq0).le

theorem F_concave_q {p : ℝ} (hp : p∈Icc (1263/2500:ℝ) (4/5)) :
    ConcaveOn ℝ (Icc (863/1000:ℝ) (26/25)) (F p) := by
  have hp0 : 0<p := by linarith [hp.1]
  apply concave_of_deriv2
    (f' := fun q => D R (p/q) frameCap)
    (f'' := fun q => Dr R (p/q) frameCap*(-p/q^2))
  · intro q hq
    have hq0 := (rectangle_ratio hp hq).2.1
    have h1 : HasDerivAt (fun x => V R p x frameCap) (D R (p/q) frameCap) q :=
      V_hasDerivAt_q hp0 hq0 cap_mem
    have h2 : HasDerivAt (fun x => V R p x frameCap-p+87/1250) (D R (p/q) frameCap) q :=
      (h1.sub_const p).add_const (87/1250)
    exact h2
  · intro q hq
    exact D_quotient_hasDerivAt (rectangle_ratio hp hq).2.1 cap_mem
  · intro q hq
    exact mul_nonpos_of_nonneg_of_nonpos
      (far_Dr_nonneg (rectangle_ratio hp hq).2.2)
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp0.le) (sq_nonneg q))

/-- A lower zero-angle radical and upper negative-angle radical transfer
their exact rational reserve to the original norm expression. -/
theorem corner_lower {p q a b reserve : ℝ}
    (hp : 0<p) (hq : 0<q) (ha : 0≤a) (hb : 0<b) (hab : b<a)
    (haz : a^2<p^2+q^2)
    (hbn : p^2+q^2-2*p*q*HighOrderTaylor.S11 frameCap<b^2)
    (hreserve : reserve<q*(Arithmetic.cos10 frameCap-1)+
      Rlower*(a-b)-p+87/1250) : reserve<F p q := by
  have hzero : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hneg : |-frameCap|≤frameCap := by norm_num [frameCap]
  have hZ := pairNorm_pos hp hq hzero
  have hN := pairNorm_pos hp hq hneg
  have hZ2 := pairNorm_sq hp hq hzero
  have hN2 := pairNorm_sq hp hq hneg
  simp only [pairEnergy,pairProduct,Real.sin_zero,Real.sin_neg] at hZ2 hN2
  have hZlo : a<pairNorm p q 0 := by nlinarith
  have hS := HighOrderTaylor.S11_le_sin (show 0≤frameCap by norm_num [frameCap])
  have hSmul := mul_le_mul_of_nonneg_left hS (show 0≤2*p*q by positivity)
  have hNhi : pairNorm p q (-frameCap)<b := by nlinarith
  have hgap : a-b<pairNorm p q 0-pairNorm p q (-frameCap) := by linarith
  have hgap0 : 0<pairNorm p q 0-pairNorm p q (-frameCap) := by linarith
  have hR0 : 0<Rlower := by norm_num [Rlower]
  have hmul1 := mul_lt_mul_of_pos_left hgap hR0
  have hmul2 := mul_lt_mul_of_pos_right radius_lower hgap0
  have hC := Arithmetic.cos10_le_cos (show 0≤frameCap by norm_num [frameCap])
  have hCmul := mul_le_mul_of_nonneg_left hC hq.le
  dsimp [F,V]
  linarith

theorem corner_low_low : (1513/50000:ℝ)<F (1263/2500) (863/1000) := by
  apply corner_lower (a := 999998019/1000000000) (b := 662007699/1000000000)
  all_goals norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8,frameCap,Rlower]

theorem corner_low_high : (157/500000:ℝ)<F (1263/2500) (26/25) := by
  apply corner_lower (a := 1156212368/1000000000) (b := 812325543/1000000000)
  all_goals norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8,frameCap,Rlower]

theorem corner_high_low : (269/100000:ℝ)<F (4/5) (863/1000) := by
  apply corner_lower (a := 1176762083/1000000000) (b := 703728085/1000000000)
  all_goals norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8,frameCap,Rlower]

theorem corner_high_high : (2651/100000:ℝ)<F (4/5) (26/25) := by
  apply corner_lower (a := 1312097557/1000000000) (b := 805991172/1000000000)
  all_goals norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8,frameCap,Rlower]

theorem F_positive {p q : ℝ}
    (hp : p∈Icc (1263/2500:ℝ) (4/5))
    (hq : q∈Icc (863/1000:ℝ) (26/25)) : 0<F p q := by
  have hlo : 0<F (1263/2500) q :=
    concave_gt_of_endpoints (F_concave_q (by norm_num)) hq
      (by linarith [corner_low_low]) (by linarith [corner_low_high])
  have hhi : 0<F (4/5) q :=
    concave_gt_of_endpoints (F_concave_q (by norm_num)) hq
      (by linarith [corner_high_low]) (by linarith [corner_high_high])
  exact concave_gt_of_endpoints (f := fun p => F p q) (F_concave_p hq) hp hlo hhi

theorem rectangle_lower {p q : ℝ}
    (hp : p∈Icc (1263/2500:ℝ) (4/5))
    (hq : q∈Icc (863/1000:ℝ) (26/25)) :
    p-87/1250<OrdinaryAngleConcavity.V (Real.sqrt qCap) p q frameCap := by
  have hh := F_positive hp hq
  dsimp [F,R] at hh
  linarith

end SquaresInCircles.Eight.CoreEFarEndpoint
end
end
end

section
/-!
## Exact positive-primary stress with arbitrary normal E owners

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
end
end
end

section
/-!
## Original flat-T work with arbitrary normal E witnesses

Both special points are evaluated at their
original coordinates: T uses its actual flat radial coordinate, and E
contributes its exact signed primary charge. All four ordinary anchors
use their original containment inequalities at the same common radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CoreENegativeStress
open Candidate SignedStress SecondaryEStress PositiveAngularEnvelope
open PositivePrimaryBaselines ActualCoreEBlocks FlatTStress GlobalGA

def flatBound (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t R : ℝ) : Vertex → ℝ :=
  let F := CoreEStress.forces C ab bt td de eh n k l b t
  ![signedSupport R 1 (F H),circleSupport R (F G),signedSupport R 1 (F A),
    signedSupport R (-1) (F B),work (F T) (C.point T),signedSupport R (-1) (F D),
    work (F E) (C.point E)]

def flatDefect (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t R : ℝ) : ℝ :=
  demand C (weights n k l b t)-∑ i,flatBound C ab bt td de eh n k l b t R i

theorem necessary_at_cap {C : SignedCycle} {q : ℝ} {ab bt td de eh : Fin 4}
    {n k l b t : ℝ} (hq : q≤qCap) (hC : C.Necessary q)
    (hn : C.NormalAnchors) (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) :
    flatDefect C ab bt td de eh n k l b t (Real.sqrt qCap)≤0 := by
  have hweight : ∀ i,0≤weights n k l b t i := by
    intro i
    fin_cases i <;> simp [weights] <;>
      linarith [hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2]
  have hc (i : Vertex) : (C.point i).Contained ((Real.sqrt qCap)^2) := by
    rw [Real.sq_sqrt (show 0≤qCap by norm_num [qCap])]
    exact (hC.contained i).trans hq
  have hb : ∀ i,work (CoreEStress.forces C ab bt td de eh n k l b t i) (C.point i)≤
      flatBound C ab bt td de eh n k l b t (Real.sqrt qCap) i := by
    intro i
    fin_cases i
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc H) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.H_nonneg]) _
    · exact work_le_circleSupport (Real.sqrt_nonneg _) (hC.sorted G) (hc G) _
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc A) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.A_nonneg]) _
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc B) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.B_nonpos]) _
    · exact le_rfl
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc D) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.D_nonpos]) _
    · exact le_rfl
  have hh := weighted_separation_le hweight hf hb
  dsimp [flatDefect]
  linarith

theorem flatDefect_as_anchors {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1) (n k l b t R : ℝ) :
    flatDefect C ab bt td de eh n k l b t R=
      demand C (weights n k l b t)+CoreEStress.halfShift C ab bt td de eh n k l b t-
      R*CoreEStress.anchorNorms C ab bt td de eh n k l b t-
      circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t G)-
      work (CoreEStress.forces C ab bt td de eh n k l b t T) (C.point T)-
      work (CoreEStress.forces C ab bt td de eh n k l b t E) (C.point E) := by
  have hid : flatDefect C ab bt td de eh n k l b t R=
      CoreEStress.defect C ab bt td de eh n k l b t R+
      circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t T)-
      work (CoreEStress.forces C ab bt td de eh n k l b t T) (C.point T) := by
    simp [flatDefect,flatBound,CoreEStress.defect,CoreEStress.bound,
      Fin.sum_univ_succ,H,G,A,B,T,D,E]
    ring
  rw [hid,CoreEStress.defect,CoreEStress.sum_bounds C hab hbt htd hde heh]
  ring

theorem negative_TD_decomposition {C : SignedCycle} {ab de eh : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hG : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12) :
    flatDefect C ab 2 2 de eh (tiltedWeight k η (delta C.theta G)) k l c (c/Real.cos s) R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c 1 s+
        CoreEStress.increment C ab 2 2 de eh (tiltedWeight k η (delta C.theta G))
          k l c (c/Real.cos s) R+charge C de eh := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have ho := ordinary_small (de := de) (eh := eh) hsmall
  rw [flatDefect_as_anchors hab (Or.inl rfl) (Or.inr rfl) hde heh,
    CoreEStress.force_G,CoreEStress.force_T,positive_G_support hk hη hG,
    negative_TD_work hcos.ne' hT hflat,CoreEStress.force_E hde heh,demand_eq,
    CoreEStress.DE_width_split hde,CoreEStress.EH_width_split heh]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall B),width_eq ho.1,width_eq ho.2,hT,edgeWidth_negative_formula hs,
    psi_positive hG]
  rcases hab with rfl | rfl <;>
    simp [CoreEStress.increment,CoreEStress.halfShift,secondaryBaseline,secantCharge,
      zeroNorms,primaryCoefficient,primarySupport,tiltedWeight,PositiveAngularEnvelope.phi,
      Real.tan_eq_sin_div_cos,ActualCoreEBlocks.charge,CoreECharge.pairDeficit,work] <;>
    field_simp [hcos.ne'] <;> ring

theorem negative_BT_decomposition {C : SignedCycle} {ab de eh : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hG : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12) :
    flatDefect C ab 3 0 de eh (tiltedWeight k η (delta C.theta G)) k l (c/Real.cos s) c R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c l s+
        CoreEStress.increment C ab 3 0 de eh (tiltedWeight k η (delta C.theta G))
          k l (c/Real.cos s) c R+charge C de eh := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have ho := ordinary_small (de := de) (eh := eh) hsmall
  rw [flatDefect_as_anchors hab (Or.inr rfl) (Or.inl rfl) hde heh,
    CoreEStress.force_G,CoreEStress.force_T,positive_G_support hk hη hG,
    negative_BT_work hcos.ne' hB hflat,CoreEStress.force_E hde heh,demand_eq,
    CoreEStress.DE_width_split hde,CoreEStress.EH_width_split heh]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall T),width_eq ho.1,width_eq ho.2,hB,edgeWidth_negative_formula hs,
    psi_positive hG]
  rcases hab with rfl | rfl <;>
    simp [CoreEStress.increment,CoreEStress.halfShift,secondaryBaseline,secantCharge,
      zeroNorms,primaryCoefficient,primarySupport,tiltedWeight,PositiveAngularEnvelope.phi,
      Real.tan_eq_sin_div_cos,ActualCoreEBlocks.charge,CoreECharge.pairDeficit,work] <;>
    field_simp [hcos.ne'] <;> ring

theorem negative_TD_necessary {C : SignedCycle} {q k l c η s : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hη : 0≤η)
    (hG : 0≤delta C.theta G) (hs : s∈Icc 0 frameCap)
    (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) :
    secondaryBaseline (Real.sqrt qCap) k l c η (delta C.theta G)+
      c*secantGain qCap (1/c) s+
      CoreEStress.increment C ab 2 2 de eh (tiltedWeight k η (delta C.theta G))
        k l c (c/Real.cos s) (Real.sqrt qCap)+charge C de eh≤0 := by
  have hsmall (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hG' : delta C.theta G∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hh := necessary_at_cap hq hC hn
    ⟨tiltedWeight_nonneg hk hη hG',hk,hl,hc.le,div_nonneg hc.le hcos.le⟩ hf
  rw [negative_TD_decomposition hab hde heh hk hη hsmall hG' hs hT hflat,
    secantCharge_eq hc hs] at hh
  exact hh

theorem negative_BT_necessary {C : SignedCycle} {q k l c η s : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hη : 0≤η)
    (hG : 0≤delta C.theta G) (hs : s∈Icc 0 frameCap)
    (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) :
    secondaryBaseline (Real.sqrt qCap) k l c η (delta C.theta G)+
      c*secantGain qCap (l/c) s+
      CoreEStress.increment C ab 3 0 de eh (tiltedWeight k η (delta C.theta G))
        k l (c/Real.cos s) c (Real.sqrt qCap)+charge C de eh≤0 := by
  have hsmall (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hG' : delta C.theta G∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hh := necessary_at_cap hq hC hn
    ⟨tiltedWeight_nonneg hk hη hG',hk,hl,div_nonneg hc.le hcos.le,hc.le⟩ hf
  rw [negative_BT_decomposition hab hde heh hk hη hsmall hG' hs hB hflat,
    secantCharge_eq hc hs] at hh
  exact hh

end SquaresInCircles.Eight.CoreENegativeStress
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CoreEOrdinaryEnvelope
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open PositiveStressCoefficients PositiveOrdinaryParameters PositiveOrdinaryEnvelope
open OrdinaryNegativeEnvelope CorrelatedSameBlock ActualOrdinaryBlocks
open PositiveScalarTransfer (J)

def lower (d l : ℝ) : ℝ :=
  min (V (Real.sqrt qCap) l k d) (J (frameCap-d)+l-87/1250)

theorem coefficient_intervals {d : ℝ} (hd : d∈Icc 0 frameCap) :
    lP d∈Icc (1263/2500) (4/5) ∧ lN d∈Icc (1263/2500) (4/5) := by
  have hd0 : 0≤d := hd.1
  have hd1 : d≤7/10 := hd.2
  have hPlo := mul_nonneg hd0 (show 0≤49/100-(27/250)*d by linarith)
  have hNlo := mul_nonneg hd0 (show 0≤11/20-d/5 by linarith)
  have hPhi := mul_nonneg (sub_nonneg.mpr hd1) (show 0≤49/100-(27/250)*(7/10+d) by linarith)
  have hNhi := mul_nonneg (sub_nonneg.mpr hd1) (show 0≤11/20-(7/10+d)/5 by linarith)
  dsimp [lP,lN]
  constructor <;> constructor <;> linarith

theorem far_lower {d l n b t : ℝ} (h : Bounds d l n b t)
    (hl : l∈Icc (1263/2500) (4/5)) (i : Fin 4) :
    l-87/1250<V (Real.sqrt qCap) (ps n l t i) (qs b t i) frameCap := by
  have hi := domains h i
  have hrough := V_endpoint_lower sqrt_cap_lower hi.1 hi.2.1 hi.2.2.1
  fin_cases i
  · simp only [ps,qs,Fin.zero_eta,Matrix.cons_val] at hrough ⊢
    have hn := h.H_lower
    norm_num [k] at hn
    linarith [hl.2]
  · simpa [ps,qs,k] using CoreEFarEndpoint.rectangle_lower hl
      (show k∈Icc (863/1000) (26/25) by norm_num [k])
  · simpa [ps,qs] using CoreEFarEndpoint.rectangle_lower hl
      (show b∈Icc (863/1000) (26/25) by
        have hb := h.B_lower
        norm_num [k] at hb
        constructor <;> linarith [h.B_upper])
  · have hp : k ≤ min 1 t := le_min (by norm_num [k]) h.D_lower
    simp only [ps,qs,Fin.reduceFinMk,Matrix.cons_val] at hrough ⊢
    have hk : k=863/1000 := rfl
    linarith [hl.2]

theorem endpoint_lower {f : ℝ → ℝ} {a b e : ℝ} {d : ℝ}
    (hd : d∈Icc 0 frameCap) (he : e∈Icc 0 (frameCap-d))
    (hf : ConcaveOn ℝ (Icc 0 (frameCap-d)) f)
    (hzero : a≤f 0) (hfar : b≤f (frameCap-d)) : min a b≤f e := by
  have hh : 0≤frameCap-d := by linarith [hd.2]
  exact (min_le_min hzero hfar).trans
    (hf.min_le_of_mem_Icc ⟨le_rfl,hh⟩ ⟨hh,le_rfl⟩ he)

theorem J_restricted {d : ℝ} (hd : d∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-d)) J :=
  CoreECharge.J_concave.subset
    (Icc_subset_Icc le_rfl (by linarith [hd.1])) (convex_Icc _ _)

theorem pure_lower {d e l n b t : ℝ} (h : Bounds d l n b t)
    (hl : l∈Icc (1263/2500) (4/5)) (he : e∈Icc 0 (frameCap-d)) (j : Fin 4) :
    lower d l≤J e+V (Real.sqrt qCap) (ps n l t j) (qs b t j) (d+e) := by
  have hj := domains h j
  have hV := V_concave (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hj.1 hj.2.1 hj.2.2.1
  have hv := concave_affine_argument hV (a := 1) (b := d)
    (l := 0) (u := frameCap-d)
    (fun u hu => ⟨by linarith [h.angle.1,hu.1],by linarith [hu.2]⟩)
  have hconc : ConcaveOn ℝ (Icc 0 (frameCap-d))
      (fun u => J u+V (Real.sqrt qCap) (ps n l t j) (qs b t j) (d+u)) := by
    refine ((J_restricted h.angle).add hv).congr (fun u _ => ?_)
    simp only [Pi.add_apply,one_mul]
    rw [add_comm u d]
  apply endpoint_lower h.angle he hconc
  · simpa [J] using single_negative_lower h ⟨h.angle.1,le_rfl⟩ j
  · have hf := far_lower h hl j
    simp only [show d+(frameCap-d)=frameCap by ring]
    linarith

theorem same_saturated_lower {d e l n b t : ℝ} (h : Bounds d l n b t)
    (hl : l∈Icc (1263/2500) (4/5)) (he : e∈Icc 0 (frameCap-d)) (i : Fin 4) :
    lower d l≤J e+M (Real.sqrt qCap) (ps n l t i) (qs b t i) (d+e) := by
  have hi := domains h i
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hm := mixedBlock_concave_positive (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hi.1 hi.2.1 hi.2.2.1 hh
  have hm' := concave_affine_argument hm (a := -1) (b := frameCap-d)
    (l := 0) (u := frameCap-d)
    (fun u hu => ⟨by linarith [hu.2],by linarith [hu.1,h.angle.1]⟩)
  have hid (u : ℝ) : mixedBlock (Real.sqrt qCap) (ps n l t i) (qs b t i)
      (-1*u+(frameCap-d)) frameCap=M (Real.sqrt qCap) (ps n l t i) (qs b t i) (d+u) := by
    dsimp [mixedBlock,M]
    congr 1 <;> congr 1 <;> ring
  have hconc : ConcaveOn ℝ (Icc 0 (frameCap-d))
      (fun u => J u+M (Real.sqrt qCap) (ps n l t i) (qs b t i) (d+u)) := by
    exact ((J_restricted h.angle).add hm').congr (fun u _ => by simp only [Pi.add_apply,hid])
  apply endpoint_lower h.angle he hconc
  · have hsame := negative_surplus (R := Real.sqrt qCap)
      (hi.1.trans_le hi.2.1).le hi.2.2.2.1 h.angle
      (show (0:ℝ)∈Icc 0 d from ⟨le_rfl,h.angle.1⟩)
    have hm0 : mixedBlock (Real.sqrt qCap) (ps n l t i) (qs b t i)
        (frameCap-d) frameCap=M (Real.sqrt qCap) (ps n l t i) (qs b t i) d := by
      dsimp [mixedBlock,M]
      rw [show frameCap-d-frameCap= -d by ring]
    simp only [sub_zero,hm0] at hsame
    simpa [J] using (single_negative_lower h ⟨h.angle.1,le_rfl⟩ i).trans hsame
  · have hf := far_lower h hl i
    have heq : M (Real.sqrt qCap) (ps n l t i) (qs b t i) frameCap=
        V (Real.sqrt qCap) (ps n l t i) (qs b t i) frameCap := by
      simp [M,V]
    simp only [show d+(frameCap-d)=frameCap by ring,heq]
    linarith

theorem separated_saturated_lower {d e l n b t : ℝ} (h : Bounds d l n b t)
    (hl : l∈Icc (1263/2500) (4/5)) (he : e∈Icc 0 (frameCap-d)) (i j : Fin 4) :
    lower d l≤J e+U (Real.sqrt qCap) (ps n l t i) (qs b t i) (frameCap-(d+e))+
      V (Real.sqrt qCap) (ps n l t j) (qs b t j) frameCap := by
  have hi := domains h i
  have hU := U_concave (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hi.1 hi.2.1 hi.2.2.1
  have hu := concave_affine_argument hU (a := -1) (b := frameCap-d)
    (l := 0) (u := frameCap-d)
    (fun u hu => ⟨by linarith [hu.2],by linarith [hu.1,h.angle.1]⟩)
  have hconc : ConcaveOn ℝ (Icc 0 (frameCap-d))
      (fun u => J u+U (Real.sqrt qCap) (ps n l t i) (qs b t i) (frameCap-(d+u))+
        V (Real.sqrt qCap) (ps n l t j) (qs b t j) frameCap) := by
    convert ((J_restricted h.angle).add hu).add_const
      (V (Real.sqrt qCap) (ps n l t j) (qs b t j) frameCap) using 1
    funext u
    congr 2
    ring
  apply endpoint_lower h.angle he hconc
  · simpa [J] using PositiveOrdinaryEnvelope.separated_saturated_lower h i j
  · have hf := far_lower h hl j
    simp only [show frameCap-(d+(frameCap-d))=0 by ring,U_zero,add_zero]
    linarith

theorem mixed_sum_lower {d e l n b t : ℝ} (h : Bounds d l n b t)
    (hl : l∈Icc (1263/2500) (4/5)) (he : e∈Icc 0 (frameCap-d))
    (P N : Fin 4 → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d-e)
    (hbalance : (∑ i,N i)=d+e+∑ i,P i) :
    lower d l≤J e+∑ i,mixedBlock (Real.sqrt qCap)
      (ps n l t i) (qs b t i) (P i) (N i) := by
  have hz : d+e∈Icc 0 frameCap := ⟨by linarith [h.angle.1,he.1],by linarith [he.2]⟩
  obtain ⟨i,j,hconc⟩ := ordinary_concentration (Real.sqrt qCap) (ps n l t) (qs b t)
    P N (Real.sqrt_nonneg qCap) (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (fun i => (domains h i).1) (fun i => (domains h i).2.1)
    (fun i => (domains h i).2.2.1) hP hN hz (by linarith) hbalance
  have hpure := pure_lower h hl he j
  have hsat : lower d l≤J e+
      (if i=j then M (Real.sqrt qCap) (ps n l t i) (qs b t i) (d+e)
       else U (Real.sqrt qCap) (ps n l t i) (qs b t i) (frameCap-(d+e))+
         V (Real.sqrt qCap) (ps n l t j) (qs b t j) frameCap) := by
    by_cases hij : i=j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hij)]
      exact same_saturated_lower h hl he i
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hij),← add_assoc]
      exact separated_saturated_lower h hl he i j
  have hh := le_min hpure hsat
  rw [min_add_add_left] at hh
  linarith

/-- The analytic concentration, applied to the original four blocks and the exact charge of
the original core E state. -/
theorem actual_lower {C : SignedCycle} {q l n b t : ℝ} {ab bt td de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core)
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hBT : bt=3 → 0≤delta C.theta B) (hTD : td=2 → 0≤delta C.theta T)
    (he : 0≤ActualCoreEBlocks.eTotal C de eh)
    (h : Bounds (removed C bt td) l n b t) (hl : l∈Icc (1263/2500) (4/5)) :
    lower (removed C bt td) l≤
      CoreEStress.increment C ab bt td de eh n k l b t (Real.sqrt qCap)+
        ActualCoreEBlocks.charge C de eh := by
  let Bs := ActualCoreEBlocks.blocks C ab bt td de eh n k l b t
  have hb := ActualCoreEBlocks.block_budgets hab hbt htd hde heh n k l b t
    hvar hG hBT hTD he
  have hP := fun i => (Bs i).P_nonneg
  have hN := fun i => (Bs i).N_nonneg
  have hsumP : (∑ i,(Bs i).P)≤frameCap := by
    linarith [hb.1.1,hb.2.1.1,hb.2.2.1]
  have hsumN : (∑ i,(Bs i).N)≤frameCap := by
    linarith [hb.2.2.1,hb.2.2.2]
  have hPi (i : Fin 4) : (Bs i).P≤frameCap :=
    (Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)).trans hsumP
  have hNi (i : Fin 4) : (Bs i).N≤frameCap :=
    (Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ i)).trans hsumN
  have hc (i : Fin 4) : (Bs i).p=ps n l t i ∧ (Bs i).q=qs b t i := by
    have ho := PositiveOrdinaryEnvelope.block_coefficients h C ab bt td i
    have he := ActualCoreEBlocks.block_coefficients C ab bt td de eh n k l b t i
    exact ⟨he.1.trans ho.1,he.2.trans ho.2⟩
  have hminor : (∑ i,mixedBlock (Real.sqrt qCap) (ps n l t i) (qs b t i)
      (Bs i).P (Bs i).N)≤∑ i,(Bs i).increment (Real.sqrt qCap) := by
    apply Finset.sum_le_sum
    intro i _
    have hh := (Bs i).minorant (Real.sqrt qCap)
      (by rw [(hc i).1]; exact (domains h i).1.le) (hPi i) (hNi i)
    simpa only [(hc i).1,(hc i).2] using hh
  have henv := mixed_sum_lower h hl hb.2.1 (fun i => (Bs i).P) (fun i => (Bs i).N)
    hP hN hb.2.2.1 hb.2.2.2
  have hcharge := ActualCoreEBlocks.charge_lower hC hcore
    (show ActualCoreEBlocks.eTotal C de eh∈Icc 0 frameCap from
      ⟨he,by linarith [hb.1.1,hb.2.1.2]⟩)
  rw [CoreEStress.increment_eq C hab hbt htd]
  dsimp [Bs] at *
  linarith

end SquaresInCircles.Eight.CoreEOrdinaryEnvelope
end
end
end
