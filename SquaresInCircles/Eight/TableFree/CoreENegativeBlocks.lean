module

public import SquaresInCircles.Eight.TableFree.CoreENegativeEnvelope
public import SquaresInCircles.Eight.TableFree.CoreENegativeStress

/-!
# Actual signed budgets with negative T and either E owner

Uncompiled source draft. Positive and negative removed masses are exact
finite sums of the original angles. No chosen analytic concentration is
interpreted as a geometric change. The E-primary sum may contain an
opposite-signed pair; its common extra variation is discarded only in
the weaker analytic budget.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CoreENegativeBlocks
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PositiveStressCoefficients
open SecondaryEStress PositiveOrdinaryEnvelope NegativeOrdinaryParameters ActualCoreEBlocks

theorem budgets {C : SignedCycle} {ab bt td de eh : Fin 4} {n k l b t d s : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hvar : positiveVariation C.theta≤frameCap)
    (hpos : positivePart (delta C.theta G)+
      (if bt=3 then positivePart (delta C.theta B) else 0)+
      (if td=2 then positivePart (delta C.theta T) else 0)=d)
    (hneg : negativePart (delta C.theta G)+
      (if bt=3 then negativePart (delta C.theta B) else 0)+
      (if td=2 then negativePart (delta C.theta T) else 0)=s)
    (he : 0≤eTotal C de eh) :
    eTotal C de eh≤frameCap-d ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).P)≤frameCap-d-eTotal C de eh ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).N)≤frameCap-s ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
      d+eTotal C de eh-s+∑ i,(blocks C ab bt td de eh n k l b t i).P := by
  have hp := sum_parts C hab hbt htd hde heh n k l b t positivePart positivePart_zero
  have hn := sum_parts C hab hbt htd hde heh n k l b t negativePart negativePart_zero
  have hp' : (∑ i,(blocks C ab bt td de eh n k l b t i).P)=
      positiveVariation C.theta-d-positivePart (primaryDE C de)-positivePart (primaryEH C eh) := by
    change (∑ i,(positivePart (blocks C ab bt td de eh n k l b t i).u+
      positivePart (blocks C ab bt td de eh n k l b t i).v))=_
    rw [hp]
    dsimp [positiveVariation]
    linarith
  have hn' : (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
      negativeVariation C.theta-s-negativePart (primaryDE C de)-negativePart (primaryEH C eh) := by
    change (∑ i,(negativePart (blocks C ab bt td de eh n k l b t i).u+
      negativePart (blocks C ab bt td de eh n k l b t i).v))=_
    rw [hn]
    dsimp [negativeVariation]
    linarith
  have hd := positive_sub_negative (primaryDE C de)
  have hh := positive_sub_negative (primaryEH C eh)
  have hnd := negativePart_nonneg (primaryDE C de)
  have hnh := negativePart_nonneg (primaryEH C eh)
  have heq := variations_equal C.theta
  have hP0 := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => (blocks C ab bt td de eh n k l b t i).P_nonneg)
  dsimp [eTotal] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem actual_lower {C : SignedCycle} {q d s b t : ℝ} {ab bt td de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core)
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hvar : positiveVariation C.theta≤frameCap)
    (hpos : positivePart (delta C.theta G)+
      (if bt=3 then positivePart (delta C.theta B) else 0)+
      (if td=2 then positivePart (delta C.theta T) else 0)=d)
    (hneg : negativePart (delta C.theta G)+
      (if bt=3 then negativePart (delta C.theta B) else 0)+
      (if td=2 then negativePart (delta C.theta T) else 0)=s)
    (he : 0≤eTotal C de eh) (h : Bounds d s b t) (hb : b≤26/25) :
    CoreENegativeEnvelope.lower d≤lambdaN d*s+
      CoreEStress.increment C ab bt td de eh (tiltedWeight k (19/50) d) k (lN d) b t
        (Real.sqrt qCap)+charge C de eh := by
  obtain ⟨Bs,hBs⟩ : ∃ Bs,Bs=blocks C ab bt td de eh (tiltedWeight k (19/50) d) k (lN d) b t :=
    ⟨_,rfl⟩
  have hbud := budgets (n := tiltedWeight k (19/50) d) (k := k) (l := lN d)
    (b := b) (t := t) hab hbt htd hde heh hvar hpos hneg he
  rw [← hBs] at hbud
  have hP := fun i => (Bs i).P_nonneg
  have hN := fun i => (Bs i).N_nonneg
  have hsumP : (∑ i,(Bs i).P)≤frameCap := by linarith [hbud.2.1,h.angle.1]
  have hsumN : (∑ i,(Bs i).N)≤frameCap := by linarith [hbud.2.2.1,h.short.1]
  have hPi (i : Fin 4) : (Bs i).P≤frameCap :=
    (Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)).trans hsumP
  have hNi (i : Fin 4) : (Bs i).N≤frameCap :=
    (Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ i)).trans hsumN
  have hc (i : Fin 4) :
      (Bs i).p=ps (tiltedWeight k (19/50) d) (lN d) t i ∧ (Bs i).q=qs b t i := by
    have h1 := ActualCoreEBlocks.block_coefficients C ab bt td de eh
      (tiltedWeight k (19/50) d) k (lN d) b t i
    have h2 := NegativeOrdinaryParameters.block_coefficients h C ab bt td i
    rw [hBs]
    exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩
  have hminor : (∑ i,mixedBlock (Real.sqrt qCap)
      (ps (tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (Bs i).P (Bs i).N)≤
        ∑ i,(Bs i).increment (Real.sqrt qCap) := by
    apply Finset.sum_le_sum
    intro i _
    have hh := (Bs i).minorant (Real.sqrt qCap)
      (by rw [(hc i).1]; exact (domains h i).1.le) (hPi i) (hNi i)
    simpa only [(hc i).1,(hc i).2] using hh
  have henv := CoreENegativeEnvelope.mixed_sum_lower h hb ⟨he,hbud.1⟩
    (fun i => (Bs i).P) (fun i => (Bs i).N) hP hN hbud.2.1 hbud.2.2.2
  have hcharge := charge_lower hC hcore
    (show eTotal C de eh∈Icc 0 frameCap from ⟨he,by linarith [hbud.1,h.angle.1]⟩)
  rw [CoreEStress.increment_eq C hab hbt htd,← hBs]
  linarith

theorem TD_B_upper {d : ℝ} (hd : d∈Icc 0 frameCap) : cN d≤26/25 := by
  have hh := (PositiveOrdinaryParameters.familyN hd).B_upper
  linarith

theorem BT_B_upper {d s : ℝ} (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 (9/100)) :
    cN d/Real.cos s≤26/25 := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hc : 19919/20000≤Real.cos s := by nlinarith
  have hcp : 0<Real.cos s := by linarith
  apply (div_le_iff₀ hcp).2
  have hh := (PositiveOrdinaryParameters.familyN hd).B_upper
  linarith

theorem TD_lower {C : SignedCycle} {q s : ℝ} {ab de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hvar : positiveVariation C.theta≤frameCap)
    (hd : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 (3/10))
    (hT : delta C.theta T= -s) (he : 0≤eTotal C de eh) :
    CoreENegativeEnvelope.lower (delta C.theta G)≤lambdaN (delta C.theta G)*s+
      CoreEStress.increment C ab 2 2 de eh (tiltedWeight k (19/50) (delta C.theta G))
        k (lN (delta C.theta G)) (cN (delta C.theta G))
        (cN (delta C.theta G)/Real.cos s) (Real.sqrt qCap)+charge C de eh := by
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hd.1
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith [hd.1] : -delta C.theta G≤0)
  have hPT : positivePart (delta C.theta T)=0 := by
    rw [hT]
    exact max_eq_right (by linarith [hs.1] : -s≤0)
  have hNT : negativePart (delta C.theta T)=s := by
    rw [hT]
    simpa [negativePart] using max_eq_left hs.1
  exact actual_lower hC hcore hab (Or.inl rfl) (Or.inr rfl) hde heh hvar
    (by simp [hPG,hPT]) (by simp [hNG,hNT]) he (familyTD hd hs) (TD_B_upper hd)

theorem BT_lower {C : SignedCycle} {q s : ℝ} {ab de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hvar : positiveVariation C.theta≤frameCap)
    (hd : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 (9/100))
    (hB : delta C.theta B= -s) (he : 0≤eTotal C de eh) :
    CoreENegativeEnvelope.lower (delta C.theta G)≤lambdaN (delta C.theta G)*s+
      CoreEStress.increment C ab 3 0 de eh (tiltedWeight k (19/50) (delta C.theta G))
        k (lN (delta C.theta G)) (cN (delta C.theta G)/Real.cos s)
        (cN (delta C.theta G)) (Real.sqrt qCap)+charge C de eh := by
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hd.1
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith [hd.1] : -delta C.theta G≤0)
  have hPB : positivePart (delta C.theta B)=0 := by
    rw [hB]
    exact max_eq_right (by linarith [hs.1] : -s≤0)
  have hNB : negativePart (delta C.theta B)=s := by
    rw [hB]
    simpa [negativePart] using max_eq_left hs.1
  exact actual_lower hC hcore hab (Or.inr rfl) (Or.inl rfl) hde heh hvar
    (by simp [hPG,hPB]) (by simp [hNG,hNB]) he (familyBT hd hs) (BT_B_upper hd hs)

end SquaresInCircles.Eight.TableFree.CoreENegativeBlocks
