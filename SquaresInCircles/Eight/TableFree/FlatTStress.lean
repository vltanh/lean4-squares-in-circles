module

public import SquaresInCircles.Eight.TableFree.PositiveSecondaryEExclusion
public import SquaresInCircles.Eight.TableFree.PositiveSecantGain

/-!
# Exact flat-T stress and its secant gain

Uncompiled source draft. The T work is its original physical work, with
the actual flat radial coordinate `7/12`. In particular, the negative
radial force is not bounded by the full circle support. All other forces
and both E rotations are the same original seven-edge stress.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.FlatTStress
open Candidate SignedStress SecondaryEStress PositiveAngularEnvelope
open PositivePrimaryBaselines ActualOrdinaryBlocks OrdinaryNegativeEnvelope GlobalGA

def flatBound (C : SignedCycle) (ab bt td : Fin 4) (n k l b t R : ℝ) : Vertex → ℝ :=
  let F := forces C ab bt td n k l b t
  ![signedSupport R 1 (F H),circleSupport R (F G),
    signedSupport R 1 (F A),signedSupport R (-1) (F B),
    work (F T) (C.point T),signedSupport R (-1) (F D),0]

def flatDefect (C : SignedCycle) (ab bt td : Fin 4) (n k l b t R : ℝ) : ℝ :=
  demand C (weights n k l b t)-∑ i,flatBound C ab bt td n k l b t R i

theorem necessary_flat_stress {C : SignedCycle} {ab bt td : Fin 4}
    {n k l b t R : ℝ} (hR : 0≤R)
    (hs : ∀ i,i≠E → (C.point i).Sorted)
    (hc : ∀ i,i≠E → (C.point i).Contained (R^2))
    (hnormal : C.NormalAnchors) (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (owners ab bt td i)) :
    flatDefect C ab bt td n k l b t R≤0 := by
  have hweight : ∀ i,0≤weights n k l b t i := by
    intro i
    fin_cases i <;> simp [weights] <;> linarith [hw.1,hw.2.1,hw.2.2.1,
      hw.2.2.2.1,hw.2.2.2.2]
  have hbound : ∀ i,work (forces C ab bt td n k l b t i) (C.point i)≤
      flatBound C ab bt td n k l b t R i := by
    intro i
    fin_cases i
    · exact work_le_signed_support hR (hc H (by decide)) (Or.inl rfl)
        (by simp [abs_of_nonneg hnormal.H_nonneg]) _
    · exact work_le_circleSupport hR (hs G (by decide)) (hc G (by decide)) _
    · exact work_le_signed_support hR (hc A (by decide)) (Or.inl rfl)
        (by simp [abs_of_nonneg hnormal.A_nonneg]) _
    · exact work_le_signed_support hR (hc B (by decide)) (Or.inr rfl)
        (by simp [abs_of_nonpos hnormal.B_nonpos]) _
    · rfl
    · exact work_le_signed_support hR (hc D (by decide)) (Or.inr rfl)
        (by simp [abs_of_nonpos hnormal.D_nonpos]) _
    · change work (forces C ab bt td n k l b t E) (C.point E)≤flatBound C ab bt td n k l b t R E
      rw [force_E]
      simp [work,flatBound,E]
  have h := weighted_separation_le hweight hf hbound
  dsimp [flatDefect]
  linarith

theorem necessary_flat_at_cap {C : SignedCycle} {q : ℝ} {ab bt td : Fin 4}
    {n k l b t : ℝ} (hq : q≤qCap) (hC : C.Necessary q)
    (hnormal : C.NormalAnchors) (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (owners ab bt td i)) :
    flatDefect C ab bt td n k l b t (Real.sqrt qCap)≤0 := by
  apply necessary_flat_stress (Real.sqrt_nonneg _) (fun i _ => hC.sorted i) _ hnormal hw hf
  intro i _
  rw [Real.sq_sqrt (show 0≤qCap by norm_num [qCap])]
  exact (hC.contained i).trans hq

theorem flatDefect_as_anchors {C : SignedCycle} {ab bt td : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (n k l b t R : ℝ) :
    flatDefect C ab bt td n k l b t R=
      demand C (weights n k l b t)+anchorHalfShift C ab bt td n k l b t-
      R*anchorNormSum C ab bt td n k l b t-
      circleSupport R (forces C ab bt td n k l b t G)-
      work (forces C ab bt td n k l b t T) (C.point T) := by
  have hsum : (∑ i,flatBound C ab bt td n k l b t R i)=
      signedSupport R 1 (forces C ab bt td n k l b t H)+
      circleSupport R (forces C ab bt td n k l b t G)+
      signedSupport R 1 (forces C ab bt td n k l b t A)+
      signedSupport R (-1) (forces C ab bt td n k l b t B)+
      work (forces C ab bt td n k l b t T) (C.point T)+
      signedSupport R (-1) (forces C ab bt td n k l b t D) := by
    simp [flatBound,Fin.sum_univ_succ,H,G,A,B,T,D,E]
    ring
  rw [flatDefect,hsum,H_support,A_support hab,B_support hab hbt,D_support htd]
  dsimp [anchorHalfShift,anchorNormSum]
  ring

def secantCharge (R c a s : ℝ) : ℝ :=
  c*(1/Real.cos s-1+(13/12)*Real.tan s)-
    R*(pairNorm a (c/Real.cos s) 0-pairNorm a c 0)

theorem zero_norm_scale {c : ℝ} (hc : 0<c) (a w : ℝ) :
    pairNorm a (c*w) 0=c*Real.sqrt ((a/c)^2+w^2) := by
  have he : c*(a/c)=a := by field_simp [hc.ne']
  simpa only [he,pairNorm_zero] using pairNorm_homogeneous hc.le (a/c) w 0

theorem secantCharge_eq {c s : ℝ} (hc : 0<c) (hs : s∈Icc 0 frameCap) (a : ℝ) :
    secantCharge (Real.sqrt qCap) c a s=c*secantGain qCap (a/c) s := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  rw [secantGain_eq_secant_expression qCap (a/c) hcos]
  have hN : pairNorm a (c/Real.cos s) 0=
      c*Real.sqrt ((1/Real.cos s)^2+(a/c)^2) := by
    simpa only [div_eq_mul_inv,one_mul,add_comm] using zero_norm_scale hc a (1/Real.cos s)
  have hZ : pairNorm a c 0=c*Real.sqrt (1+(a/c)^2) := by
    simpa only [mul_one,one_pow,add_comm] using zero_norm_scale hc a 1
  dsimp [secantCharge]
  rw [hN,hZ]
  ring

def negativeTDIncrement (C : SignedCycle) (ab : Fin 4) (R k l c η s : ℝ) : ℝ :=
  ∑ i,(blocks C ab 2 2 (tiltedWeight k η (delta C.theta G)) k l c (c/Real.cos s) i).increment R

def negativeBTIncrement (C : SignedCycle) (ab : Fin 4) (R k l c η s : ℝ) : ℝ :=
  ∑ i,(blocks C ab 3 0 (tiltedWeight k η (delta C.theta G)) k l (c/Real.cos s) c i).increment R

theorem negative_TD_decomposition {C : SignedCycle} {ab : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hη : 0≤η)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hG : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12) :
    flatDefect C ab 2 2 (tiltedWeight k η (delta C.theta G)) k l c (c/Real.cos s) R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c 1 s+
        negativeTDIncrement C ab R k l c η s := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  rw [flatDefect_as_anchors hab (Or.inl rfl) (Or.inr rfl),
    positive_G_support hk hη hG,negative_TD_work hcos.ne' hT hflat,demand_eq]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall B),width_eq (hsmall D),width_eq (hsmall E),
    hT,edgeWidth_negative_formula hs,psi_positive hG]
  rcases hab with rfl | rfl <;>
    simp [negativeTDIncrement,blocks,Block.increment,Fin.sum_univ_succ,
      anchorHalfShift,anchorNormSum,secondaryBaseline,secantCharge,zeroNorms,
      primaryCoefficient,primarySupport,tiltedWeight,PositiveAngularEnvelope.phi,
      Real.tan_eq_sin_div_cos,pairNorm_symm k l,pairNorm_symm _ 1] <;>
    field_simp [hcos.ne'] <;> ring

theorem negative_BT_decomposition {C : SignedCycle} {ab : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hη : 0≤η)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hG : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12) :
    flatDefect C ab 3 0 (tiltedWeight k η (delta C.theta G)) k l (c/Real.cos s) c R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c l s+
        negativeBTIncrement C ab R k l c η s := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  rw [flatDefect_as_anchors hab (Or.inr rfl) (Or.inl rfl),
    positive_G_support hk hη hG,negative_BT_work hcos.ne' hB hflat,demand_eq]
  rw [width_eq (hsmall H),width_eq (hsmall G),width_eq (hsmall A),
    width_eq (hsmall T),width_eq (hsmall D),width_eq (hsmall E),
    hB,edgeWidth_negative_formula hs,psi_positive hG]
  rcases hab with rfl | rfl <;>
    simp [negativeBTIncrement,blocks,Block.increment,Fin.sum_univ_succ,
      anchorHalfShift,anchorNormSum,secondaryBaseline,secantCharge,zeroNorms,
      primaryCoefficient,primarySupport,tiltedWeight,PositiveAngularEnvelope.phi,
      Real.tan_eq_sin_div_cos,pairNorm_symm k l,pairNorm_symm _ 1] <;>
    field_simp [hcos.ne'] <;> ring

theorem negative_TD_necessary {C : SignedCycle} {q k l c η s : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hη : 0≤η)
    (hG : 0≤delta C.theta G) (hs : s∈Icc 0 frameCap)
    (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (owners ab 2 2 i)) :
    secondaryBaseline (Real.sqrt qCap) k l c η (delta C.theta G)+
      c*secantGain qCap (1/c) s+
      negativeTDIncrement C ab (Real.sqrt qCap) k l c η s≤0 := by
  have hsmall : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hG' : delta C.theta G∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hnec := necessary_flat_at_cap hq hC hnormal
    ⟨tiltedWeight_nonneg hk hη hG',hk,hl,hc.le,div_nonneg hc.le hcos.le⟩ hf
  rw [negative_TD_decomposition hab hk hη hsmall hG' hs hT hflat,secantCharge_eq hc hs] at hnec
  exact hnec

theorem negative_BT_necessary {C : SignedCycle} {q k l c η s : ℝ} {ab : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hnormal : C.NormalAnchors)
    (hab : ab=0 ∨ ab=2) (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hη : 0≤η)
    (hG : 0≤delta C.theta G) (hs : s∈Icc 0 frameCap)
    (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (owners ab 3 0 i)) :
    secondaryBaseline (Real.sqrt qCap) k l c η (delta C.theta G)+
      c*secantGain qCap (l/c) s+
      negativeBTIncrement C ab (Real.sqrt qCap) k l c η s≤0 := by
  have hsmall : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hG' : delta C.theta G∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hcos := transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hnec := necessary_flat_at_cap hq hC hnormal
    ⟨tiltedWeight_nonneg hk hη hG',hk,hl,div_nonneg hc.le hcos.le,hc.le⟩ hf
  rw [negative_BT_decomposition hab hk hη hsmall hG' hs hB hflat,secantCharge_eq hc hs] at hnec
  exact hnec

end SquaresInCircles.Eight.TableFree.FlatTStress
