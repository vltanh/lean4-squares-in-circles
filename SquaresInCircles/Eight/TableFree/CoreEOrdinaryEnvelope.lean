module

public import SquaresInCircles.Eight.TableFree.CoreEStress
public import SquaresInCircles.Eight.TableFree.PositiveOrdinaryEnvelope
public import SquaresInCircles.Eight.TableFree.CoreEFarEndpoint

/-!
# Concentration with the full nonnegative signed E charge

Uncompiled source draft. The stress coefficients are fixed at the actual
positive G/T total. Concavity then varies only the analytic E charge and
the ordinary sign totals. The varying-coefficient comparison is invoked
at E-total zero only; no comparison at an enlarged coefficient parameter
is assumed. Both actual E owners and opposite individual E signs are
retained in the final theorem.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CoreEOrdinaryEnvelope
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open PositiveStressCoefficients PositiveOrdinaryParameters PositiveOrdinaryEnvelope
open OrdinaryNegativeEnvelope CorrelatedSameBlock ActualOrdinaryBlocks
open PositiveScalarTransfer (J)

def lower (d l : ℝ) : ℝ :=
  min (V (Real.sqrt qCap) l k d) (J (frameCap-d)+l-87/1250)

theorem coefficient_intervals {d : ℝ} (hd : d∈Icc 0 frameCap) :
    lP d∈Icc (1263/2500) (4/5) ∧ lN d∈Icc (1263/2500) (4/5) := by
  have hPlo := mul_nonneg hd.1
    (show 0≤49/100-(27/250)*d by dsimp [frameCap] at hd; linarith)
  have hNlo := mul_nonneg hd.1
    (show 0≤11/20-d/5 by dsimp [frameCap] at hd; linarith)
  have hPhi := mul_nonneg (sub_nonneg.mpr hd.2)
    (show 0≤49/100-(27/250)*(frameCap+d) by dsimp [frameCap] at *; linarith)
  have hNhi := mul_nonneg (sub_nonneg.mpr hd.2)
    (show 0≤11/20-(frameCap+d)/5 by dsimp [frameCap] at *; linarith)
  dsimp [lP,lN,frameCap] at *
  constructor <;> constructor <;> nlinarith

theorem far_lower {d l n b t : ℝ} (h : Bounds d l n b t)
    (hl : l∈Icc (1263/2500) (4/5)) (i : Fin 4) :
    l-87/1250<V (Real.sqrt qCap) (ps n l t i) (qs b t i) frameCap := by
  have hi := domains h i
  have hrough := V_endpoint_lower sqrt_cap_lower hi.1 hi.2.1 hi.2.2.1
  fin_cases i
  · simp only [ps,qs,Matrix.cons_val_zero] at *
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
  · have hp : k≤min 1 t := le_min (by norm_num [k]) h.D_lower
    simp [ps,qs] at hrough
    norm_num [k] at hp
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
    simpa only [one_mul,add_comm d] using (J_restricted h.angle).add hv
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
    simpa only [hid] using (J_restricted h.angle).add hm'
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
    · simpa only [if_pos hij] using same_saturated_lower h hl he i
    · simpa only [if_neg hij,add_assoc] using separated_saturated_lower h hl he i j
  apply le_trans _ (add_le_add_left hconc (J e))
  have hh := le_min hpure hsat
  simpa only [min_add_add_left] using hh

/-- This applies the analytic concentration to the original four blocks
and the exact charge of the original core E state. -/
theorem actual_lower {C : SignedCycle} {q l n b t : ℝ} {ab bt td de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core) (hy : (C.point E).y≤0)
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
  have hcharge := ActualCoreEBlocks.charge_lower hC hcore hy
    (show ActualCoreEBlocks.eTotal C de eh∈Icc 0 frameCap from
      ⟨he,by linarith [hb.1.1,hb.2.1.2]⟩)
  rw [CoreEStress.increment_eq C hab hbt htd]
  dsimp [Bs] at *
  linarith

end SquaresInCircles.Eight.TableFree.CoreEOrdinaryEnvelope
