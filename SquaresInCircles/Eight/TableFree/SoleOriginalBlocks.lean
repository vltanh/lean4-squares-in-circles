module

public import SquaresInCircles.Eight.TableFree.SoleEStress
public import SquaresInCircles.Eight.TableFree.SoleLowEnvelope
public import SquaresInCircles.Eight.TableFree.SoleBalancedEnvelope

/-!
# The sole-E envelopes applied to the original signed cycle

Uncompiled source. The actual AB weak owner chooses which block contains
its signed angle. Only the selected positive E primary leaves the
ordinary budget. The coefficient split x,e may vary while the original
ordinary angles and their exact positive/negative totals stay fixed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleOriginalBlocks
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

end SquaresInCircles.Eight.TableFree.SoleOriginalBlocks
