module

public import SquaresInCircles.Eight.Owners.SecondaryEStress

/-!
# Eight squares: the ordinary-angle blocks of the positive-primary stress

The AB rotation is assigned to its weak owner, and the DE and EH rotations stay the angles of the
cycle, even though the force on E cancels (`anchorNormSum`). The angular defect is the demand plus
the half shifts, minus the norms of the anchor forces and the circle supports of G and T
(`demand_eq`, `defect_as_anchors`). This identifies the baseline and the signed angular increment;
the concentration of the increment and the scalar bounds are proved separately.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.PositiveAngularEnvelope
open Candidate SignedStress SecondaryEStress

def phi (t : ℝ) : ℝ := Real.cos t+Real.sin t

def psi (t : ℝ) : ℝ := Real.cos t+max (Real.sin t) 0-1

def pairNorm (p q t : ℝ) : ℝ :=
  Real.sqrt (p^2+q^2+2*p*q*Real.sin t)

def rotatedPair (p q u v : ℝ) : Point :=
  (p*Real.cos v+q*Real.sin u,p*Real.sin v+q*Real.cos u)

@[simp] theorem phi_zero : phi 0=1 := by simp [phi]
@[simp] theorem psi_zero : psi 0=0 := by simp [psi]

theorem pairNorm_symm (p q t : ℝ) : pairNorm p q t=pairNorm q p t := by
  unfold pairNorm
  congr 1
  ring

@[simp] theorem pairNorm_zero (p q : ℝ) :
    pairNorm p q 0=Real.sqrt (p^2+q^2) := by simp [pairNorm]

/-- The energy of a rotated pair, `p² + q² + 2 p q sin (u + v)`, with both incident angles. -/
theorem rotatedPair_energy (p q u v : ℝ) :
    (rotatedPair p q u v).1^2+(rotatedPair p q u v).2^2=
      p^2+q^2+2*p*q*Real.sin (u+v) := by
  simp only [rotatedPair,Real.sin_add]
  linear_combination p^2*(Real.sin_sq_add_cos_sq v)+
    q^2*(Real.sin_sq_add_cos_sq u)

theorem rotatedPair_norm (p q u v : ℝ) :
    Real.sqrt ((rotatedPair p q u v).1^2+(rotatedPair p q u v).2^2)=
      pairNorm p q (u+v) := by
  rw [rotatedPair_energy]
  rfl

theorem rotatedPair_signedSupport (R p q u v : ℝ) :
    signedSupport R 1 (rotatedPair p q u v)=
      R*pairNorm p q (u+v)-(p*phi v+q*phi u)/2 := by
  unfold signedSupport
  rw [rotatedPair_norm]
  simp only [rotatedPair,phi]
  ring

theorem reflected_rotatedPair_signedSupport (R p q u v : ℝ) :
    signedSupport R (-1)
        ((rotatedPair p q u v).1,-(rotatedPair p q u v).2)=
      R*pairNorm p q (u+v)-(p*phi v+q*phi u)/2 := by
  simpa [signedSupport] using rotatedPair_signedSupport R p q u v

theorem width_add_half_phi {t : ℝ} (ht : |t|≤frameCap) :
    edgeWidth t+phi t/2=3/2+psi t := by
  have hc := transport_cos_pos ht
  by_cases hs : 0≤Real.sin t
  · simp [edgeWidth,pairWidth,phi,psi,abs_of_pos hc,abs_of_nonneg hs,
      max_eq_left hs]
    ring
  · have hs' : Real.sin t≤0 := le_of_lt (lt_of_not_ge hs)
    simp [edgeWidth,pairWidth,phi,psi,abs_of_pos hc,abs_of_nonpos hs',
      max_eq_right hs']
    ring

theorem width_eq {t : ℝ} (ht : |t|≤frameCap) :
    edgeWidth t=3/2+psi t-phi t/2 := by
  linarith [width_add_half_phi ht]

theorem psi_positive {t : ℝ} (ht : t∈Set.Icc 0 frameCap) :
    psi t=phi t-1 := by
  simp [psi,phi,max_eq_left (transport_trig ht).2.2.1]

theorem psi_negative {t : ℝ} (ht : t∈Set.Icc 0 frameCap) :
    psi (-t)=Real.cos t-1 := by
  have hs : -Real.sin t≤0 := neg_nonpos.mpr (transport_trig ht).2.2.1
  simp [psi,Real.sin_neg,Real.cos_neg,max_eq_right hs]

/-- The sum of the norms of the anchor forces. The AB0 rotation belongs to B and the AB2 rotation
to A; a primary BT3 or TD2 contributes no ordinary rotation at its anchor. -/
def anchorNormSum (C : SignedCycle) (ab bt td : Fin 4)
    (n k l b t : ℝ) : ℝ :=
  pairNorm 1 n (delta C.theta H+delta C.theta E)+
  pairNorm k l (if ab=0 then 0 else delta C.theta A)+
  pairNorm l b ((if ab=0 then delta C.theta A else 0)+
    (if bt=2 then delta C.theta B else 0))+
  pairNorm 1 t (delta C.theta D+(if td=0 then delta C.theta T else 0))

def anchorHalfShift (C : SignedCycle) (ab bt td : Fin 4)
    (n k l b t : ℝ) : ℝ :=
  (n*phi (delta C.theta H)+phi (delta C.theta E)+k+
    l*phi (if ab=0 then 0 else delta C.theta A)+
    b*phi (if bt=2 then delta C.theta B else 0)+
    l*phi (if ab=0 then delta C.theta A else 0)+
    phi (delta C.theta D)+t*phi (if td=0 then delta C.theta T else 0))/2

theorem H_support (C : SignedCycle) (ab bt td : Fin 4) (n k l b t R : ℝ) :
    signedSupport R 1 (forces C ab bt td n k l b t H)=
      R*pairNorm 1 n (delta C.theta H+delta C.theta E)-
        (n*phi (delta C.theta H)+phi (delta C.theta E))/2 := by
  rw [force_H]
  have hv : (n*Real.sin (delta C.theta H)+Real.cos (delta C.theta E),
      n*Real.cos (delta C.theta H)+Real.sin (delta C.theta E))=
      rotatedPair 1 n (delta C.theta H) (delta C.theta E) := by
    ext <;> simp [rotatedPair] <;> ring
  rw [hv,rotatedPair_signedSupport]
  ring

theorem A_support {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (C : SignedCycle) (bt td : Fin 4) (n k l b t R : ℝ) :
    signedSupport R 1 (forces C ab bt td n k l b t A)=
      R*pairNorm k l (if ab=0 then 0 else delta C.theta A)-
        (k+l*phi (if ab=0 then 0 else delta C.theta A))/2 := by
  rw [force_A hab]
  rcases hab with rfl | rfl
  · simpa [rotatedPair,phi,signedSupport,pairNorm] using
      rotatedPair_signedSupport R k l 0 0
  · simpa [rotatedPair,phi] using
      rotatedPair_signedSupport R k l (delta C.theta A) 0

theorem B_support {ab bt : Fin 4} (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3)
    (C : SignedCycle) (td : Fin 4) (n k l b t R : ℝ) :
    signedSupport R (-1) (forces C ab bt td n k l b t B)=
      R*pairNorm l b ((if ab=0 then delta C.theta A else 0)+
        (if bt=2 then delta C.theta B else 0))-
        (b*phi (if bt=2 then delta C.theta B else 0)+
         l*phi (if ab=0 then delta C.theta A else 0))/2 := by
  rw [force_B hab hbt]
  have hp := reflected_rotatedPair_signedSupport R b l
    (if ab=0 then delta C.theta A else 0)
    (if bt=2 then delta C.theta B else 0)
  rw [pairNorm_symm b l] at hp
  have hv : add (if bt=2 then
        (b*Real.cos (delta C.theta B),-b*Real.sin (delta C.theta B)) else (b,0))
      (if ab=0 then
        (l*Real.sin (delta C.theta A),-l*Real.cos (delta C.theta A)) else (0,-l))=
      ((rotatedPair b l (if ab=0 then delta C.theta A else 0)
          (if bt=2 then delta C.theta B else 0)).1,
        -(rotatedPair b l (if ab=0 then delta C.theta A else 0)
          (if bt=2 then delta C.theta B else 0)).2) := by
    rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;> ext <;>
      simp [add,rotatedPair] <;> ring
  rw [hv]
  exact hp

theorem D_support {td : Fin 4} (htd : td=0 ∨ td=2)
    (C : SignedCycle) (ab bt : Fin 4) (n k l b t R : ℝ) :
    signedSupport R (-1) (forces C ab bt td n k l b t D)=
      R*pairNorm 1 t (delta C.theta D+(if td=0 then delta C.theta T else 0))-
        (phi (delta C.theta D)+t*phi (if td=0 then delta C.theta T else 0))/2 := by
  rw [force_D htd]
  have hp := reflected_rotatedPair_signedSupport R 1 t
    (if td=0 then delta C.theta T else 0) (delta C.theta D)
  rw [add_comm (if td=0 then delta C.theta T else 0),one_mul] at hp
  have hv : add (Real.cos (delta C.theta D),-Real.sin (delta C.theta D))
        (if td=0 then
          (t*Real.sin (delta C.theta T),-t*Real.cos (delta C.theta T)) else (0,-t))=
      ((rotatedPair 1 t (if td=0 then delta C.theta T else 0) (delta C.theta D)).1,
        -(rotatedPair 1 t (if td=0 then delta C.theta T else 0) (delta C.theta D)).2) := by
    rcases htd with rfl | rfl <;> ext <;> simp [add,rotatedPair] <;> ring
  rw [hv]
  exact hp

theorem sum_bounds {ab bt td : Fin 4} (hab : ab=0 ∨ ab=2)
    (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (C : SignedCycle) (n k l b t R : ℝ) :
    (∑ i,bound C ab bt td n k l b t R i)=
      R*anchorNormSum C ab bt td n k l b t-
        anchorHalfShift C ab bt td n k l b t+
        circleSupport R (forces C ab bt td n k l b t G)+
        circleSupport R (forces C ab bt td n k l b t T) := by
  have hsum : (∑ i,bound C ab bt td n k l b t R i)=
      signedSupport R 1 (forces C ab bt td n k l b t H)+
      circleSupport R (forces C ab bt td n k l b t G)+
      signedSupport R 1 (forces C ab bt td n k l b t A)+
      signedSupport R (-1) (forces C ab bt td n k l b t B)+
      circleSupport R (forces C ab bt td n k l b t T)+
      signedSupport R (-1) (forces C ab bt td n k l b t D) := by
    simp [bound,Fin.sum_univ_succ,H,G,A,B,T,D]
    ring
  rw [hsum,H_support,A_support hab,B_support hab hbt,D_support htd]
  unfold anchorNormSum anchorHalfShift
  ring

theorem demand_eq (C : SignedCycle) (n k l b t : ℝ) :
    demand C (weights n k l b t)=
      n*edgeWidth (delta C.theta H)+k*edgeWidth (delta C.theta G)+
      l*edgeWidth (delta C.theta A)+b*edgeWidth (delta C.theta B)+
      t*edgeWidth (delta C.theta T)+edgeWidth (delta C.theta D)+
      edgeWidth (delta C.theta E) := by
  simp [demand,weights,Fin.sum_univ_succ,H,G,A,B,T,D,E]
  ring

theorem defect_as_anchors {ab bt td : Fin 4} (hab : ab=0 ∨ ab=2)
    (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (C : SignedCycle) (n k l b t R : ℝ) :
    angularDefect C ab bt td n k l b t R=
      demand C (weights n k l b t)+anchorHalfShift C ab bt td n k l b t-
      R*anchorNormSum C ab bt td n k l b t-
      circleSupport R (forces C ab bt td n k l b t G)-
      circleSupport R (forces C ab bt td n k l b t T) := by
  rw [angularDefect,sum_bounds hab hbt htd]
  ring

end SquaresInCircles.Eight.PositiveAngularEnvelope
