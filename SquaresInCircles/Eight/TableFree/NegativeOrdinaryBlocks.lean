module

public import SquaresInCircles.Eight.TableFree.NegativeOrdinaryEnvelope
public import SquaresInCircles.Eight.TableFree.FlatTStress

/-!
# The original seven-angle budgets for negative T

Uncompiled source draft. The positive and negative parts removed from
the four blocks are computed from the original seven edge errors. Both
variation caps and the exact signed balance are then applied to the
actual stress increments, with the original AB owner retained.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.NegativeOrdinaryBlocks
open Candidate PositiveAngularEnvelope PositivePrimaryBaselines PositiveStressCoefficients
open OrdinaryAngleConcavity ActualOrdinaryBlocks PositiveOrdinaryEnvelope
open NegativeOrdinaryParameters FlatTStress

theorem budgets {C : SignedCycle} {ab bt td : Fin 4} {n k l b t d s : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hvar : positiveVariation C.theta≤frameCap)
    (hpos : positivePart (delta C.theta G)+
      (if bt=3 then positivePart (delta C.theta B) else 0)+
      (if td=2 then positivePart (delta C.theta T) else 0)=d)
    (hneg : negativePart (delta C.theta G)+
      (if bt=3 then negativePart (delta C.theta B) else 0)+
      (if td=2 then negativePart (delta C.theta T) else 0)=s) :
    (∑ i,(blocks C ab bt td n k l b t i).P)≤frameCap-d ∧
    (∑ i,(blocks C ab bt td n k l b t i).N)≤frameCap-s ∧
    (∑ i,(blocks C ab bt td n k l b t i).N)=
      d-s+∑ i,(blocks C ab bt td n k l b t i).P := by
  have hp := sum_parts C hab hbt htd n k l b t positivePart positivePart_zero
  have hn := sum_parts C hab hbt htd n k l b t negativePart negativePart_zero
  have hp' : (∑ i,(blocks C ab bt td n k l b t i).P)=positiveVariation C.theta-d := by
    change (∑ i,positivePart (blocks C ab bt td n k l b t i).u+
      positivePart (blocks C ab bt td n k l b t i).v)=_
    rw [hp]
    dsimp [positiveVariation]
    linarith
  have hn' : (∑ i,(blocks C ab bt td n k l b t i).N)=negativeVariation C.theta-s := by
    change (∑ i,negativePart (blocks C ab bt td n k l b t i).u+
      negativePart (blocks C ab bt td n k l b t i).v)=_
    rw [hn]
    dsimp [negativeVariation]
    linarith
  have heq := variations_equal C.theta
  exact ⟨by linarith,by linarith,by linarith⟩

theorem increment_lower {C : SignedCycle} {ab bt td : Fin 4} {d s b t : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hvar : positiveVariation C.theta≤frameCap)
    (hpos : positivePart (delta C.theta G)+
      (if bt=3 then positivePart (delta C.theta B) else 0)+
      (if td=2 then positivePart (delta C.theta T) else 0)=d)
    (hneg : negativePart (delta C.theta G)+
      (if bt=3 then negativePart (delta C.theta B) else 0)+
      (if td=2 then negativePart (delta C.theta T) else 0)=s)
    (h : Bounds d s b t) :
    min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)≤lambdaN d*s+
      ∑ i,(blocks C ab bt td (tiltedWeight k (19/50) d) k (lN d) b t i).increment
        (Real.sqrt qCap) := by
  let Bs := blocks C ab bt td (tiltedWeight k (19/50) d) k (lN d) b t
  have hb := budgets (n := tiltedWeight k (19/50) d) (k := k) (l := lN d)
    (b := b) (t := t) hab hbt htd hvar hpos hneg
  have hP : ∀ i,0≤(Bs i).P := fun i => (Bs i).P_nonneg
  have hN : ∀ i,0≤(Bs i).N := fun i => (Bs i).N_nonneg
  have hsumP : (∑ i,(Bs i).P)≤frameCap := by linarith [hb.1,h.angle.1]
  have hsumN : (∑ i,(Bs i).N)≤frameCap := by linarith [hb.2.1,h.short.1]
  have hPi (i : Fin 4) : (Bs i).P≤frameCap :=
    (Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)).trans hsumP
  have hNi (i : Fin 4) : (Bs i).N≤frameCap :=
    (Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ i)).trans hsumN
  have hsum := NegativeOrdinaryEnvelope.mixed_sum_lower h (fun i => (Bs i).P)
    (fun i => (Bs i).N) hP hN hb.1 hb.2.2
  apply hsum.trans
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  have hc := NegativeOrdinaryParameters.block_coefficients h C ab bt td i
  have hminor := (Bs i).minorant (Real.sqrt qCap)
    (by rw [hc.1]; exact (NegativeOrdinaryParameters.domains h i).1.le) (hPi i) (hNi i)
  simpa only [hc.1,hc.2] using hminor

theorem TD_increment_lower {C : SignedCycle} {ab : Fin 4} {s : ℝ}
    (hab : ab=0 ∨ ab=2) (hvar : positiveVariation C.theta≤frameCap)
    (hd : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 (3/10))
    (hT : delta C.theta T= -s) :
    min (V (Real.sqrt qCap) (lN (delta C.theta G)) k (delta C.theta G))
      (lambdaN (delta C.theta G)*delta C.theta G)≤lambdaN (delta C.theta G)*s+
        negativeTDIncrement C ab (Real.sqrt qCap) k (lN (delta C.theta G))
          (cN (delta C.theta G)) (19/50) s := by
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hd.1
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith [hd.1] : -delta C.theta G≤0)
  have hPT : positivePart (delta C.theta T)=0 := by
    rw [hT]
    exact max_eq_right (by linarith [hs.1] : -s≤0)
  have hNT : negativePart (delta C.theta T)=s := by
    rw [hT]
    simpa [negativePart] using max_eq_left hs.1
  have h := increment_lower hab (Or.inl rfl) (Or.inr rfl) hvar
    (by simp [hPG,hPT]) (by simp [hNG,hNT]) (familyTD hd hs)
  simpa only [negativeTDIncrement] using h

theorem BT_increment_lower {C : SignedCycle} {ab : Fin 4} {s : ℝ}
    (hab : ab=0 ∨ ab=2) (hvar : positiveVariation C.theta≤frameCap)
    (hd : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 (9/100))
    (hB : delta C.theta B= -s) :
    min (V (Real.sqrt qCap) (lN (delta C.theta G)) k (delta C.theta G))
      (lambdaN (delta C.theta G)*delta C.theta G)≤lambdaN (delta C.theta G)*s+
        negativeBTIncrement C ab (Real.sqrt qCap) k (lN (delta C.theta G))
          (cN (delta C.theta G)) (19/50) s := by
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hd.1
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith [hd.1] : -delta C.theta G≤0)
  have hPB : positivePart (delta C.theta B)=0 := by
    rw [hB]
    exact max_eq_right (by linarith [hs.1] : -s≤0)
  have hNB : negativePart (delta C.theta B)=s := by
    rw [hB]
    simpa [negativePart] using max_eq_left hs.1
  have h := increment_lower hab (Or.inr rfl) (Or.inl rfl) hvar
    (by simp [hPG,hPB]) (by simp [hNG,hNB]) (familyBT hd hs)
  simpa only [negativeBTIncrement] using h

end SquaresInCircles.Eight.TableFree.NegativeOrdinaryBlocks
