module

public import SquaresInCircles.Eight.TableFree.PositiveAngularEnvelope

/-!
# Exact positive-primary baselines for all three nonnegative T regimes

Uncompiled source draft. These are identities in the original seven
angles, followed by necessary inequalities from the actual weak contacts.
The identities retain both weak AB choices and both E rotations. The
secondary-T formula allows the T weight to differ from the G weight.

The baseline at a split `(x,z)` is not identified with the lower endpoint
baseline `B_P(x+z)`: that further step requires a concavity proof.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.PositivePrimaryBaselines
open Candidate SignedStress SecondaryEStress PositiveAngularEnvelope

def primaryCoefficient (R η x : ℝ) : ℝ :=
  1+2*Real.cos x+(1+2*η-R*Real.sqrt (1+η^2))*Real.sin x

def zeroNorms (n k l b t : ℝ) : ℝ :=
  pairNorm 1 n 0+pairNorm k l 0+pairNorm l b 0+pairNorm 1 t 0

def tdBaseline (R k l η x z : ℝ) : ℝ :=
  3+2*l+k*primaryCoefficient R η x+k*primaryCoefficient R η z-
    R*zeroNorms (tiltedWeight k η x) k l (tiltedWeight k η z) k

def btBaseline (R k l η x z : ℝ) : ℝ :=
  3+2*l+k*primaryCoefficient R η x+k*primaryCoefficient R η z-
    R*zeroNorms (tiltedWeight k η x) k l k (tiltedWeight k η z)

def secondaryBaseline (R k l c η x : ℝ) : ℝ :=
  3+2*l+3*c+k*primaryCoefficient R η x-
    R*zeroNorms (tiltedWeight k η x) k l c c

def tdIncrement (C : SignedCycle) (ab : Fin 4) (R k l η : ℝ) : ℝ :=
  let n := tiltedWeight k η (delta C.theta G)
  let m := tiltedWeight k η (delta C.theta T)
  n*psi (delta C.theta H)+l*psi (delta C.theta A)+
    m*psi (delta C.theta B)+psi (delta C.theta D)+psi (delta C.theta E)-
    R*(anchorNormSum C ab 2 2 n k l m k-zeroNorms n k l m k)

def btIncrement (C : SignedCycle) (ab : Fin 4) (R k l η : ℝ) : ℝ :=
  let n := tiltedWeight k η (delta C.theta G)
  let m := tiltedWeight k η (delta C.theta B)
  n*psi (delta C.theta H)+l*psi (delta C.theta A)+
    m*psi (delta C.theta T)+psi (delta C.theta D)+psi (delta C.theta E)-
    R*(anchorNormSum C ab 3 0 n k l k m-zeroNorms n k l k m)

def secondaryIncrement (C : SignedCycle) (ab : Fin 4) (R k l c η : ℝ) : ℝ :=
  let n := tiltedWeight k η (delta C.theta G)
  n*psi (delta C.theta H)+l*psi (delta C.theta A)+
    c*psi (delta C.theta B)+c*psi (delta C.theta T)+
    psi (delta C.theta D)+psi (delta C.theta E)-
    R*(anchorNormSum C ab 2 0 n k l c c-zeroNorms n k l c c)

/-- Positive TD2: its actual BT rotation remains an ordinary B rotation. -/
theorem td_decomposition {C : SignedCycle} {ab : Fin 4} {R k l η : ℝ}
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hη : 0≤η)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Set.Icc 0 frameCap)
    (hz : delta C.theta T∈Set.Icc 0 frameCap) :
    angularDefect C ab 2 2 (tiltedWeight k η (delta C.theta G)) k l
        (tiltedWeight k η (delta C.theta T)) k R=
      tdBaseline R k l η (delta C.theta G) (delta C.theta T)+
        tdIncrement C ab R k l η := by
  rw [defect_as_anchors hab (Or.inl rfl) (Or.inr rfl),
    positive_G_support hk hη hx,positive_TD_support hk hη hz,demand_eq]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall B),width_eq (hsmall T),width_eq (hsmall D),width_eq (hsmall E)]
  rw [psi_positive hx,psi_positive hz]
  rcases hab with rfl | rfl <;>
    simp [anchorHalfShift,tdBaseline,tdIncrement,primaryCoefficient,primarySupport,
      tiltedWeight,PositiveAngularEnvelope.phi] <;> ring

/-- Positive BT3: its actual TD rotation remains an ordinary D rotation. -/
theorem bt_decomposition {C : SignedCycle} {ab : Fin 4} {R k l η : ℝ}
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hη : 0≤η)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Set.Icc 0 frameCap)
    (hz : delta C.theta B∈Set.Icc 0 frameCap) :
    angularDefect C ab 3 0 (tiltedWeight k η (delta C.theta G)) k l k
        (tiltedWeight k η (delta C.theta B)) R=
      btBaseline R k l η (delta C.theta G) (delta C.theta B)+
        btIncrement C ab R k l η := by
  rw [defect_as_anchors hab (Or.inr rfl) (Or.inl rfl),
    positive_G_support hk hη hx,positive_BT_support hk hη hz,demand_eq]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall B),width_eq (hsmall T),width_eq (hsmall D),width_eq (hsmall E)]
  rw [psi_positive hx,psi_positive hz]
  rcases hab with rfl | rfl <;>
    simp [anchorHalfShift,btBaseline,btIncrement,primaryCoefficient,primarySupport,
      tiltedWeight,PositiveAngularEnvelope.phi] <;> ring

/-- BT2/TD0: the T force vanishes, while both of its actual angles remain. -/
theorem secondary_decomposition {C : SignedCycle} {ab : Fin 4} {R k l c η : ℝ}
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hη : 0≤η)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Set.Icc 0 frameCap) :
    angularDefect C ab 2 0 (tiltedWeight k η (delta C.theta G)) k l c c R=
      secondaryBaseline R k l c η (delta C.theta G)+
        secondaryIncrement C ab R k l c η := by
  rw [defect_as_anchors hab (Or.inl rfl) (Or.inl rfl),
    positive_G_support hk hη hx,force_T_secondary,sub_self,circleSupport_zero,demand_eq]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall B),width_eq (hsmall T),width_eq (hsmall D),width_eq (hsmall E)]
  rw [psi_positive hx]
  rcases hab with rfl | rfl <;>
    simp [anchorHalfShift,secondaryBaseline,secondaryIncrement,primaryCoefficient,
      primarySupport,tiltedWeight,PositiveAngularEnvelope.phi] <;> ring

theorem tiltedWeight_nonneg {k η x : ℝ} (hk : 0≤k) (hη : 0≤η)
    (hx : x∈Set.Icc 0 frameCap) : 0≤tiltedWeight k η x := by
  obtain ⟨hc,_,hs,_,_⟩ := transport_trig hx
  unfold tiltedWeight
  exact mul_nonneg hk (add_nonneg (by linarith) (mul_nonneg hη hs))

/-- A larger analytic support radius does not alter any input point or
any actual-q radial label. No E geometry is used in this invocation. -/
theorem necessary_at_cap {C : SignedCycle} {q : ℝ} {ab bt td : Fin 4}
    {n k l b t : ℝ} (hq : q≤qCap)
    (hs : ∀ i,i≠E → (C.point i).Sorted)
    (hc : ∀ i,i≠E → (C.point i).Contained q)
    (hnormal : C.NormalAnchors)
    (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (owners ab bt td i)) :
    angularDefect C ab bt td n k l b t (Real.sqrt qCap)≤0 := by
  apply necessary_stress (Real.sqrt_nonneg _) hs _ hnormal hw hf
  intro i hi
  rw [Real.sq_sqrt (show (0 : ℝ)≤qCap by norm_num [qCap])]
  exact (hc i hi).trans hq

theorem td_necessary {C : SignedCycle} {q k l η : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hl : 0≤l) (hη : 0≤η)
    (hx : 0≤delta C.theta G) (hz : 0≤delta C.theta T)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 i)) :
    tdBaseline (Real.sqrt qCap) k l η (delta C.theta G) (delta C.theta T)+
      tdIncrement C ab (Real.sqrt qCap) k l η≤0 := by
  have hsmall : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hx' : delta C.theta G∈Set.Icc 0 frameCap :=
    ⟨hx,(le_abs_self _).trans (hsmall G)⟩
  have hz' : delta C.theta T∈Set.Icc 0 frameCap :=
    ⟨hz,(le_abs_self _).trans (hsmall T)⟩
  rw [← td_decomposition hab hk hη hsmall hx' hz']
  exact necessary_at_cap hq (fun i _ => hC.sorted i) (fun i _ => hC.contained i)
    hnormal ⟨tiltedWeight_nonneg hk hη hx',hk,hl,tiltedWeight_nonneg hk hη hz',hk⟩ hf

theorem bt_necessary {C : SignedCycle} {q k l η : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hl : 0≤l) (hη : 0≤η)
    (hx : 0≤delta C.theta G) (hz : 0≤delta C.theta B)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 i)) :
    btBaseline (Real.sqrt qCap) k l η (delta C.theta G) (delta C.theta B)+
      btIncrement C ab (Real.sqrt qCap) k l η≤0 := by
  have hsmall : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hx' : delta C.theta G∈Set.Icc 0 frameCap :=
    ⟨hx,(le_abs_self _).trans (hsmall G)⟩
  have hz' : delta C.theta B∈Set.Icc 0 frameCap :=
    ⟨hz,(le_abs_self _).trans (hsmall B)⟩
  rw [← bt_decomposition hab hk hη hsmall hx' hz']
  exact necessary_at_cap hq (fun i _ => hC.sorted i) (fun i _ => hC.contained i)
    hnormal ⟨tiltedWeight_nonneg hk hη hx',hk,hl,hk,tiltedWeight_nonneg hk hη hz'⟩ hf

theorem secondary_necessary {C : SignedCycle} {q k l c η : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hl : 0≤l) (hc : 0≤c) (hη : 0≤η)
    (hx : 0≤delta C.theta G) (hf : ∀ i,C.Feasible i (owners ab 2 0 i)) :
    secondaryBaseline (Real.sqrt qCap) k l c η (delta C.theta G)+
      secondaryIncrement C ab (Real.sqrt qCap) k l c η≤0 := by
  have hsmall : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hx' : delta C.theta G∈Set.Icc 0 frameCap :=
    ⟨hx,(le_abs_self _).trans (hsmall G)⟩
  rw [← secondary_decomposition hab hk hη hsmall hx']
  exact necessary_at_cap hq (fun i _ => hC.sorted i) (fun i _ => hC.contained i)
    hnormal ⟨tiltedWeight_nonneg hk hη hx',hk,hl,hc,hc⟩ hf

end SquaresInCircles.Eight.TableFree.PositivePrimaryBaselines
