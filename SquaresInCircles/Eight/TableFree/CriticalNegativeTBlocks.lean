module

public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTStress

/-!
# Original signed blocks for exceptional negative T

Uncompiled source. The three ordinary blocks are extracted directly
from the original seven errors. Both AB weak-owner choices are kept.
The aligned TD0 hypothesis is used only in the BT3 row, where it is the
actual alignment supplied by entry; it removes the otherwise present
D argument and does not alter any source point or frame.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CriticalNegativeTBlocks
open Candidate ActualOrdinaryBlocks ActualCoreEBlocks PositiveAngularEnvelope
open ExceptionalContactStress ExceptionalNegativeTStress
open CriticalECoefficients CriticalNegativeTOrdinaryData
open SingleAngleConcavity CriticalNegativeTContinuation

def blocks (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ) : Fin 3 → Block :=
  ![⟨k*tilt eta x,tilt eta e,delta C.theta H,delta C.theta E⟩,
    ⟨l,k,if ab=0 then 0 else delta C.theta A,0⟩,
    ⟨l,bWeight td c s,if ab=0 then delta C.theta A else 0,if td then delta C.theta B else 0⟩]

theorem sum_parts (C : SignedCycle) {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (td : Bool) (k l c eta s x e : ℝ) (F : ℝ → ℝ) (hF : F 0=0)
    (halign : td=false → delta C.theta T=0) :
    (∑ i,F (blocks C ab td k l c eta s x e i).u+F (blocks C ab td k l c eta s x e i).v)=
      (∑ j,F (delta C.theta j))-F (delta C.theta G)-F (delta C.theta D)-F (primary C td) := by
  rcases hab with rfl | rfl <;> cases td <;>
    simp [blocks,primary,Fin.sum_univ_succ,H,G,A,B,T,D,E,hF,halign] <;> ring

theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (td : Bool) (k l c eta x e : ℝ) {t s : ℝ}
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hs : 0≤s)
    (hsource : primary C td= -s) (htotal : delta C.theta G+delta C.theta D=t)
    (halign : td=false → delta C.theta T=0) :
    (∑i,(blocks C ab td k l c eta s x e i).P)≤frameCap-t ∧
      (∑i,(blocks C ab td k l c eta s x e i).N)=t-s+∑i,(blocks C ab td k l c eta s x e i).P := by
  have hp := sum_parts C hab td k l c eta s x e positivePart positivePart_zero halign
  have hn := sum_parts C hab td k l c eta s x e negativePart negativePart_zero halign
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hG
  have hPD : positivePart (delta C.theta D)=delta C.theta D := max_eq_left hD
  have hPT : positivePart (primary C td)=0 := by rw [hsource]; exact max_eq_right (by linarith)
  have hNG : negativePart (delta C.theta G)=0 := max_eq_right (by linarith)
  have hND : negativePart (delta C.theta D)=0 := max_eq_right (by linarith)
  have hNT : negativePart (primary C td)=s := by simp [hsource,negativePart,max_eq_left hs]
  change (∑i,(blocks C ab td k l c eta s x e i).P)=
    positiveVariation C.theta-positivePart (delta C.theta G)-positivePart (delta C.theta D)-
      positivePart (primary C td) at hp
  change (∑i,(blocks C ab td k l c eta s x e i).N)=
    negativeVariation C.theta-negativePart (delta C.theta G)-negativePart (delta C.theta D)-
      negativePart (primary C td) at hn
  rw [hPG,hPD,hPT] at hp
  rw [hNG,hND,hNT] at hn
  have hv := variations_equal C.theta
  constructor <;> linarith

theorem coefficients (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (i : Fin 3) :
    (blocks C ab td k l c eta s x e i).p=small k l c eta x e s td i ∧
      (blocks C ab td k l c eta s x e i).q=large k l c eta x e s td i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,small,large,alpha,beta,min_comm,max_comm]

theorem single_data (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (i : Fin 3) (hi : single td i=true) :
    (blocks C ab td k l c eta s x e i).v=0 ∧
      (blocks C ab td k l c eta s x e i).alpha=nu k l c eta x e s td i := by
  fin_cases i <;> cases td <;> simp_all [single,blocks,nu]

theorem single_parts (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (i : Fin 3) (hi : single td i=true) :
    (blocks C ab td k l c eta s x e i).P=0 ∨ (blocks C ab td k l c eta s x e i).N=0 := by
  have hv := (single_data C ab td k l c eta s x e i hi).1
  by_cases hu : 0≤(blocks C ab td k l c eta s x e i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right
      (show -(blocks C ab td k l c eta s x e i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]

theorem angles_small {C : SignedCycle} (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 3) :
    |(blocks C ab td k l c eta s x e i).u|≤frameCap ∧
      |(blocks C ab td k l c eta s x e i).v|≤frameCap := by
  have hz : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hA : |if ab=0 then 0 else delta C.theta A|≤frameCap := by
    split_ifs <;> first | exact hz | exact ha A
  have hB : |if ab=0 then delta C.theta A else 0|≤frameCap := by
    split_ifs <;> first | exact hz | exact ha A
  fin_cases i <;> cases td <;> simp [blocks,ha H,ha E,ha B,hA,hB,hz]

theorem increment_eq {C : SignedCycle} {ab : Fin 4} (td : Bool) (R k l c eta s x e : ℝ)
    (hab : ab=0 ∨ ab=2) (halign : td=false → delta C.theta T=0) :
    ExceptionalNegativeTStress.increment C ab td R k l c eta s x e=
      ∑ i,(blocks C ab td k l c eta s x e i).increment R := by
  rcases hab with rfl | rfl <;> cases td <;>
    simp [ExceptionalNegativeTStress.increment,blocks,Block.increment,
      SoleEStress.increment,SoleEStress.anchorNorms,SoleEStress.zeroNorms,
      btOwner,tdOwner,bWeight,tWeight,ordinaryDE,ordinaryEH,halign,
      Fin.sum_univ_succ,pairNorm_symm k l,pairNorm_symm (k*tilt eta x) (tilt eta e)] <;> ring

theorem individual_budgets {C : SignedCycle} {ab : Fin 4} {td : Bool} {k l c eta t s x e : ℝ}
    (ht : 0≤t) (hs : 0≤s)
    (hP : (∑i,(blocks C ab td k l c eta s x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab td k l c eta s x e i).N)=t-s+∑i,(blocks C ab td k l c eta s x e i).P)
    (i : Fin 3) :
    (blocks C ab td k l c eta s x e i).P≤frameCap ∧
      (blocks C ab td k l c eta s x e i).N≤frameCap := by
  have hp := Finset.single_le_sum (fun j _ => (blocks C ab td k l c eta s x e j).P_nonneg)
    (Finset.mem_univ i)
  have hn := Finset.single_le_sum (fun j _ => (blocks C ab td k l c eta s x e j).N_nonneg)
    (Finset.mem_univ i)
  constructor <;> linarith

theorem block_minorant {C : SignedCycle} {ab : Fin 4} {td : Bool} {R k l c eta t s x e : ℝ}
    (ht : 0≤t) (hs : 0≤s) (hp : ∀ i,0≤small k l c eta x e s td i)
    (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab td k l c eta s x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab td k l c eta s x e i).N)=t-s+∑i,(blocks C ab td k l c eta s x e i).P)
    (i : Fin 3) :
    F (single td i) R (small k l c eta x e s td i) (large k l c eta x e s td i)
      (nu k l c eta x e s td i) (blocks C ab td k l c eta s x e i).P
        (blocks C ab td k l c eta s x e i).N≤(blocks C ab td k l c eta s x e i).increment R := by
  obtain ⟨hsmall,hlarge⟩ := coefficients C ab td k l c eta s x e i
  obtain ⟨hbP,hbN⟩ := individual_budgets ht hs hP hN i
  by_cases hi : single td i=true
  · obtain ⟨hv,hn⟩ := single_data C ab td k l c eta s x e i hi
    have hh := SoleOriginalBlocks.one_angle_minorant (blocks C ab td k l c eta s x e i) R hv
      (angles_small ab td k l c eta s x e ha i).1
    simpa only [hi,hsmall,hlarge,hn] using hh
  · have hi' : single td i=false := Bool.eq_false_of_not_eq_true hi
    have hh := (blocks C ab td k l c eta s x e i).minorant R
      (by rw [hsmall]; exact hp i) hbP hbN
    simpa only [F,hi',if_false,hsmall,hlarge] using hh

theorem original_lower {C : SignedCycle} {ab : Fin 4} {td : Bool} {R t k l c eta x e s : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (h : Bounds t k l c eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hsource : primary C td= -s) (htotal : delta C.theta G+delta C.theta D=t)
    (halign : td=false → delta C.theta T=0) :
    lowerEnvelope R k l c t s≤ExceptionalNegativeTStress.increment C ab td R k l c eta s x e := by
  have hs0 := (short_small hs).1
  obtain ⟨hP,hN⟩ := original_budgets hab td k l c eta x e hvar hG hD hs0 hsource htotal halign
  have hlow := CriticalNegativeTEnvelope.ordinary_lower
    (fun i => (blocks C ab td k l c eta s x e i).P)
    (fun i => (blocks C ab td k l c eta s x e i).N) hR hQL hQU h hx he hs
    (fun i => (blocks C ab td k l c eta s x e i).P_nonneg)
    (fun i => (blocks C ab td k l c eta s x e i).N_nonneg) hP hN
    (single_parts C ab td k l c eta s x e)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    block_minorant h.angle.1 hs0 (fun i => (conditions h hx he hs i).1.le) ha hP hN i)
  rw [increment_eq td R k l c eta s x e hab halign]
  exact hlow.trans hsum

end SquaresInCircles.Eight.TableFree.CriticalNegativeTBlocks
