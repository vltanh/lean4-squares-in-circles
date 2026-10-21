module

public import SquaresInCircles.Eight.TableFree.CoreEStress
public import SquaresInCircles.Eight.TableFree.FlatTStress

/-!
# Original flat-T work with arbitrary normal E witnesses

Uncompiled source draft. Both special points are evaluated at their
original coordinates: T uses its actual flat radial coordinate, and E
contributes its exact signed primary charge. All four ordinary anchors
use their original containment inequalities at the same common radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CoreENegativeStress
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
      zeroNorms,primaryCoefficient,primarySupport,tiltedWeight,phi,Real.tan_eq_sin_div_cos,
      charge,CoreECharge.pairDeficit,work] <;> field_simp [hcos.ne'] <;> ring

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
      zeroNorms,primaryCoefficient,primarySupport,tiltedWeight,phi,Real.tan_eq_sin_div_cos,
      charge,CoreECharge.pairDeficit,work] <;> field_simp [hcos.ne'] <;> ring

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

end SquaresInCircles.Eight.TableFree.CoreENegativeStress
