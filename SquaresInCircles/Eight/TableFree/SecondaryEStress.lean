module

public import SquaresInCircles.Eight.TableFree.SignedStress
public import SquaresInCircles.Eight.TableFree.NecessaryCycle
public import SquaresInCircles.Eight.TableFree.TrigonometricReserves

/-!
# The actual positive-GA stress with both E separators secondary

Uncompiled geometric part of
HAND_G5_POSITIVE_GA_OUTER_E_SECONDARY_E_ALL_T_OWNERS.md, Sections 2--4.
The seven separator weights are kept symbolic. Equal DE/EH weights cancel
both E forces identically, with both original E angles still present in
the H/D forces. No sign, radial kind, or containment hypothesis on E is
used by `necessary_stress`.

The positive and negative T force formulas cover secondary BT2/TD0,
positive TD2, positive BT3, and the two genuine negative flat-core cases.
This module proves the necessary analytic inequality. Its strict angular
lower estimate is a distinct remaining proof, not a premise smuggled into
a theorem advertised as an unconditional exclusion.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SecondaryEStress
open Candidate SignedStress

def owners (ab bt td : Fin 4) : Vertex → Fin 4 := ![2,1,ab,bt,td,2,0]

def weights (n k l b t : ℝ) : Vertex → ℝ := ![n,k,l,b,t,1,1]

def forces (C : SignedCycle) (ab bt td : Fin 4) (n k l b t : ℝ) : Vertex → Point :=
  force C (owners ab bt td) (weights n k l b t)

theorem force_H (C : SignedCycle) (ab bt td : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td n k l b t H=
      (n*Real.sin (delta C.theta H)+Real.cos (delta C.theta E),
       n*Real.cos (delta C.theta H)+Real.sin (delta C.theta E)) := by
  simp [forces,force,owners,weights,previous,word,H,E,source,target,add,scale]

theorem force_G (C : SignedCycle) (ab bt td : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td n k l b t G=
      (k*Real.sin (delta C.theta G),k*Real.cos (delta C.theta G)-n) := by
  simp [forces,force,owners,weights,previous,word,G,source,target,add,scale]
  ring

theorem force_A {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (C : SignedCycle) (bt td : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td n k l b t A=
      if ab=0 then (k,l) else
        (k+l*Real.sin (delta C.theta A),l*Real.cos (delta C.theta A)) := by
  rcases hab with rfl | rfl
  · simp [forces,force,owners,weights,previous,word,A,source,target,add,scale]
  · simp [forces,force,owners,weights,previous,word,A,source,target,add,scale]
    ring

theorem force_B {ab bt : Fin 4} (hab : ab=0 ∨ ab=2)
    (hbt : bt=2 ∨ bt=3) (C : SignedCycle) (td : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td n k l b t B=
      add (if bt=2 then
        (b*Real.cos (delta C.theta B),-b*Real.sin (delta C.theta B)) else (b,0))
      (if ab=0 then
        (l*Real.sin (delta C.theta A),-l*Real.cos (delta C.theta A)) else (0,-l)) := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;>
    simp [forces,force,owners,weights,previous,word,A,B,source,target,add,scale]

theorem force_D {td : Fin 4} (htd : td=0 ∨ td=2)
    (C : SignedCycle) (ab bt : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td n k l b t D=
      add (Real.cos (delta C.theta D),-Real.sin (delta C.theta D))
        (if td=0 then
          (t*Real.sin (delta C.theta T),-t*Real.cos (delta C.theta T)) else (0,-t)) := by
  rcases htd with rfl | rfl <;>
    simp [forces,force,owners,weights,previous,word,T,D,source,target,add,scale]

theorem force_T_secondary (C : SignedCycle) (ab : Fin 4) (n k l b t : ℝ) :
    forces C ab 2 0 n k l b t T=(0,t-b) := by
  simp [forces,force,owners,weights,previous,word,T,source,target,add,scale]
  ring

theorem force_T_td_primary (C : SignedCycle) (ab : Fin 4) (n k l b t : ℝ) :
    forces C ab 2 2 n k l b t T=
      (t*Real.sin (delta C.theta T),t*Real.cos (delta C.theta T)-b) := by
  simp [forces,force,owners,weights,previous,word,T,source,target,add,scale]
  ring

theorem force_T_bt_primary (C : SignedCycle) (ab : Fin 4) (n k l b t : ℝ) :
    forces C ab 3 0 n k l b t T=
      (b*Real.sin (delta C.theta B),t-b*Real.cos (delta C.theta B)) := by
  simp [forces,force,owners,weights,previous,word,B,T,source,target,add,scale]
  ring

/-- Neither the primary E coordinate nor its signed tangent enters the
weighted sum. Both E error angles remain in `force_H` and `force_D`. -/
theorem force_E (C : SignedCycle) (ab bt td : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td n k l b t E=(0,0) := by
  simp [forces,force,owners,weights,previous,word,E,source,target,add,scale]

theorem E_coordinates_cancel (C D : SignedCycle) (hθ : C.theta=D.theta)
    (hp : ∀ i,i≠E → C.point i=D.point i)
    (ab bt td : Fin 4) (n k l b t : ℝ) :
    (∑ i,weights n k l b t i*C.edge i (owners ab bt td i))=
      ∑ i,weights n k l b t i*D.edge i (owners ab bt td i) := by
  rw [sum_force_work,sum_force_work]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=E
  · subst i
    change work (forces C ab bt td n k l b t E) (C.point E)=
      work (forces D ab bt td n k l b t E) (D.point E)
    rw [force_E,force_E,work_zero,work_zero]
  · rw [force_independent_of_points C D hθ, hp i hi]

def signedSupport (R sign : ℝ) (v : Point) : ℝ :=
  R*Real.sqrt (v.1^2+v.2^2)-(v.1+sign*v.2)/2

def bound (C : SignedCycle) (ab bt td : Fin 4) (n k l b t R : ℝ) : Vertex → ℝ :=
  let F := forces C ab bt td n k l b t
  ![signedSupport R 1 (F H),circleSupport R (F G),
    signedSupport R 1 (F A),signedSupport R (-1) (F B),
    circleSupport R (F T),signedSupport R (-1) (F D),0]

def angularDefect (C : SignedCycle) (ab bt td : Fin 4) (n k l b t R : ℝ) : ℝ :=
  demand C (weights n k l b t)-∑ i,bound C ab bt td n k l b t R i

/-- Exact geometric input to the angular envelope. E has no geometric
hypotheses at all: its two retained actual weak inequalities suffice. -/
theorem necessary_stress {C : SignedCycle} {ab bt td : Fin 4}
    {n k l b t R : ℝ} (hR : 0≤R)
    (hs : ∀ i,i≠E → (C.point i).Sorted)
    (hc : ∀ i,i≠E → (C.point i).Contained (R^2))
    (hnormal : C.NormalAnchors)
    (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (owners ab bt td i)) :
    angularDefect C ab bt td n k l b t R≤0 := by
  have hweight : ∀ i,0≤weights n k l b t i := by
    intro i
    fin_cases i <;> simp [weights] <;> linarith [hw.1,hw.2.1,hw.2.2.1,
      hw.2.2.2.1,hw.2.2.2.2]
  have hbound : ∀ i,work (forces C ab bt td n k l b t i) (C.point i)≤
      bound C ab bt td n k l b t R i := by
    intro i
    fin_cases i
    · exact work_le_signed_support hR (hc H (by decide)) (Or.inl rfl)
        (by simp [abs_of_nonneg hnormal.H_nonneg]) _
    · exact work_le_circleSupport hR (hs G (by decide)) (hc G (by decide)) _
    · exact work_le_signed_support hR (hc A (by decide)) (Or.inl rfl)
        (by simp [abs_of_nonneg hnormal.A_nonneg]) _
    · exact work_le_signed_support hR (hc B (by decide)) (Or.inr rfl)
        (by simp [abs_of_nonpos hnormal.B_nonpos]) _
    · exact work_le_circleSupport hR (hs T (by decide)) (hc T (by decide)) _
    · exact work_le_signed_support hR (hc D (by decide)) (Or.inr rfl)
        (by simp [abs_of_nonpos hnormal.D_nonpos]) _
    · show work (forces C ab bt td n k l b t E) (C.point E)≤bound C ab bt td n k l b t R E
      rw [force_E,work_zero]
      simp [bound,E]
  have h := weighted_separation_le hweight hf hbound
  unfold angularDefect
  linarith

def tiltedWeight (k η x : ℝ) : ℝ := k*(Real.cos x+η*Real.sin x)

def primarySupport (R k η x : ℝ) : ℝ :=
  k*Real.sin x*(R*Real.sqrt (1+η^2)-(1+η)/2)

theorem scaled_primary_support {R κ η : ℝ} (hκ : 0≤κ) (hη : 0≤η) :
    circleSupport R (κ,-κ*η)=κ*(R*Real.sqrt (1+η^2)-(1+η)/2) ∧
    circleSupport R (κ,κ*η)=κ*(R*Real.sqrt (1+η^2)-(1+η)/2) := by
  have hr : Real.sqrt (κ^2+κ^2*η^2)=κ*Real.sqrt (1+η^2) := by
    rw [show κ^2+κ^2*η^2=κ^2*(1+η^2) by ring,Real.sqrt_mul (sq_nonneg κ),Real.sqrt_sq hκ]
  constructor <;>
    simp [circleSupport,abs_of_nonneg hκ,abs_of_nonneg (mul_nonneg hκ hη),mul_pow,hr] <;>
    ring

theorem positive_G_support {C : SignedCycle} {ab bt td : Fin 4}
    {k l b t R η : ℝ} (hk : 0≤k) (hη : 0≤η)
    (hx : delta C.theta G∈Set.Icc 0 frameCap) :
    circleSupport R
        (forces C ab bt td (tiltedWeight k η (delta C.theta G)) k l b t G)=
      primarySupport R k η (delta C.theta G) := by
  rw [force_G]
  have hs := (transport_trig hx).2.2.1
  have hvec : (k*Real.sin (delta C.theta G),
      k*Real.cos (delta C.theta G)-tiltedWeight k η (delta C.theta G))=
      (k*Real.sin (delta C.theta G),-(k*Real.sin (delta C.theta G))*η) := by
    ext <;> simp [tiltedWeight] <;> ring
  rw [hvec]
  exact (scaled_primary_support (R := R) (mul_nonneg hk hs) hη).1

theorem positive_TD_support {C : SignedCycle} {ab : Fin 4}
    {n k l R η : ℝ} (hk : 0≤k) (hη : 0≤η)
    (hz : delta C.theta T∈Set.Icc 0 frameCap) :
    circleSupport R
        (forces C ab 2 2 n k l (tiltedWeight k η (delta C.theta T)) k T)=
      primarySupport R k η (delta C.theta T) := by
  rw [force_T_td_primary]
  have hs := (transport_trig hz).2.2.1
  have hvec : (k*Real.sin (delta C.theta T),
      k*Real.cos (delta C.theta T)-tiltedWeight k η (delta C.theta T))=
      (k*Real.sin (delta C.theta T),-(k*Real.sin (delta C.theta T))*η) := by
    ext <;> simp [tiltedWeight] <;> ring
  rw [hvec]
  exact (scaled_primary_support (R := R) (mul_nonneg hk hs) hη).1

theorem positive_BT_support {C : SignedCycle} {ab : Fin 4}
    {n k l R η : ℝ} (hk : 0≤k) (hη : 0≤η)
    (hz : delta C.theta B∈Set.Icc 0 frameCap) :
    circleSupport R
        (forces C ab 3 0 n k l k (tiltedWeight k η (delta C.theta B)) T)=
      primarySupport R k η (delta C.theta B) := by
  rw [force_T_bt_primary]
  have hs := (transport_trig hz).2.2.1
  have hvec : (k*Real.sin (delta C.theta B),
      tiltedWeight k η (delta C.theta B)-k*Real.cos (delta C.theta B))=
      (k*Real.sin (delta C.theta B),(k*Real.sin (delta C.theta B))*η) := by
    ext <;> simp [tiltedWeight] <;> ring
  rw [hvec]
  exact (scaled_primary_support (R := R) (mul_nonneg hk hs) hη).2

/-- Negative T primaries cancel the signed T tangent exactly. Its actual
flat-core radial coordinate, rather than a support at another circle, is used. -/
theorem negative_TD_work {C : SignedCycle} {ab : Fin 4} {n k l c s : ℝ}
    (hc : Real.cos s≠0) (hδ : delta C.theta T= -s)
    (hcore : (C.point T).a=7/12) :
    work (forces C ab 2 2 n k l c (c/Real.cos s) T) (C.point T)=
      -(7/12)*c*Real.tan s := by
  rw [force_T_td_primary,hδ]
  simp only [work,Real.sin_neg,Real.cos_neg,hcore,Real.tan_eq_sin_div_cos]
  field_simp [hc]
  ring

theorem negative_BT_work {C : SignedCycle} {ab : Fin 4} {n k l c s : ℝ}
    (hc : Real.cos s≠0) (hδ : delta C.theta B= -s)
    (hcore : (C.point T).a=7/12) :
    work (forces C ab 3 0 n k l (c/Real.cos s) c T) (C.point T)=
      -(7/12)*c*Real.tan s := by
  rw [force_T_bt_primary,hδ]
  simp only [work,Real.sin_neg,Real.cos_neg,hcore,Real.tan_eq_sin_div_cos]
  field_simp [hc]
  ring

end SquaresInCircles.Eight.TableFree.SecondaryEStress
