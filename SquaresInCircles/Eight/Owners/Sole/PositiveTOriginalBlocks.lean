module

public import SquaresInCircles.Eight.Owners.Sole.PositiveTEnvelope
public import SquaresInCircles.Eight.Owners.Sole.PositiveTSplitSupport

/-!
# Eight squares: original signed blocks for sole E and positive T

The AB weak owner determines the location of its
ordinary angle. A sole-DE D block is written in the reverse coefficient
order so its one actual ordinary angle has the first coefficient. This
is an algebraic swap of the same block, not a change of physical owner.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTOriginalBlocks
open Candidate SoleTScalarModel SolePositiveTSplitModel SolePositiveTOrdinaryData
open ActualOrdinaryBlocks ActualCoreEBlocks PositiveAngularEnvelope SingleAngleConcavity

def rawBlocks (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) : Fin 4 → Block :=
  SoleEStress.blocks C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family)

def swap (B : Block) : Block := ⟨B.beta,B.alpha,B.v,B.u⟩

def blocks (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) (i : Fin 4) : Block :=
  if i=3 ∧ isDE s.family=true then swap (rawBlocks C ab s t z i) else rawBlocks C ab s t z i

def increment (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (R t z : ℝ) : ℝ :=
  SoleEStress.increment C ab (btOwner s.td) (tdOwner s.td) (deOwner s.family) (ehOwner s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) (p s t z) (lambda s.family) R

theorem btOwner_cases (td : Bool) : btOwner td=2 ∨ btOwner td=3 := by cases td <;> simp [btOwner]
theorem tdOwner_cases (td : Bool) : tdOwner td=0 ∨ tdOwner td=2 := by cases td <;> simp [tdOwner]

theorem swap_data (B : Block) (R : ℝ) :
    (swap B).p=B.p ∧ (swap B).q=B.q ∧ (swap B).P=B.P ∧
    (swap B).N=B.N ∧ (swap B).increment R=B.increment R := by
  simp [swap,Block.p,Block.q,Block.P,Block.N,Block.increment,min_comm,max_comm,
    pairNorm_symm,add_comm]

theorem coefficients (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    (blocks C ab s t z i).p=small s t z i ∧
      (blocks C ab s t z i).q=large s t z i := by
  rcases s with ⟨f,td,atG,j⟩
  fin_cases i <;> cases td <;> cases hD : isDE f <;>
    simp [blocks,rawBlocks,swap,SoleEStress.blocks,Block.p,Block.q,small,large,first,second,
      btWeight,tdWeight,mWeight,m,hD,min_comm,max_comm]

theorem single_data (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ)
    (i : Fin 4) (hi : single s i=true) :
    (blocks C ab s t z i).v=0 ∧ (blocks C ab s t z i).alpha=actualNu s t z i := by
  rcases s with ⟨f,td,atG,j⟩
  fin_cases i <;> cases td <;> cases hD : isDE f <;>
    simp_all [single,blocks,rawBlocks,swap,SoleEStress.blocks,actualNu,
      btOwner,tdOwner,deOwner,ehOwner,ordinaryDE,ordinaryEH,btWeight,tdWeight,mWeight,m]

theorem parts (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    (blocks C ab s t z i).P=
      (ActualCoreEBlocks.blocks C ab (btOwner s.td) (tdOwner s.td)
        (deOwner s.family) (ehOwner s.family) (n s t z) (k s.family t z) (ell s.family t z)
        (btWeight s.family s.td t z) (tdWeight s.family s.td t z) i).P ∧
    (blocks C ab s t z i).N=
      (ActualCoreEBlocks.blocks C ab (btOwner s.td) (tdOwner s.td)
        (deOwner s.family) (ehOwner s.family) (n s t z) (k s.family t z) (ell s.family t z)
        (btWeight s.family s.td t z) (tdWeight s.family s.td t z) i).N := by
  fin_cases i <;> simp only [blocks,rawBlocks,swap,SoleEStress.blocks,ActualCoreEBlocks.blocks] <;>
    split_ifs <;> simp [Block.P,Block.N,add_comm]

theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (s : ScalarCase) (t z : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C s.family) (hT : 0≤tPrimary C s.td)
    (htotal : delta C.theta G+ePrimary C s.family+tPrimary C s.td=t) :
    0≤t ∧ (∑i,(blocks C ab s t z i).P)≤frameCap-t ∧
      (∑i,(blocks C ab s t z i).N)=t+∑i,(blocks C ab s t z i).P := by
  have hBT : btOwner s.td=3 → 0 ≤ delta C.theta B := by
    intro h
    cases htd : s.td
    · simpa [tPrimary,htd] using hT
    · simp [btOwner,htd] at h
  have hTD : tdOwner s.td=2 → 0 ≤ delta C.theta T := by
    intro h
    cases htd : s.td
    · simp [tdOwner,htd] at h
    · simpa [tPrimary,htd] using hT
  have hEtotal : eTotal C (deOwner s.family) (ehOwner s.family)=ePrimary C s.family := by
    cases hD : isDE s.family <;>
      simp [eTotal,primaryDE,primaryEH,deOwner,ehOwner,ePrimary,hD]
  have hremoved : removed C (btOwner s.td) (tdOwner s.td)=delta C.theta G+tPrimary C s.td := by
    cases htd : s.td <;> simp [removed,btOwner,tdOwner,tPrimary]
  have hh := ActualCoreEBlocks.block_budgets hab (btOwner_cases s.td) (tdOwner_cases s.td)
    (SolePositiveTSplitSupport.deOwner_cases s.family) (SolePositiveTSplitSupport.ehOwner_cases s.family)
    (n s t z) (k s.family t z) (ell s.family t z)
    (btWeight s.family s.td t z) (tdWeight s.family s.td t z) hvar hG hBT hTD
    (by rw [hEtotal]; exact hE)
  have hP := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => (parts C ab s t z i).1)
  have hN := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => (parts C ab s t z i).2)
  rw [hEtotal,hremoved] at hh
  obtain ⟨h1,h2,h3,h4⟩ := hh
  refine ⟨by linarith [h1.1,h2.1],?_,?_⟩
  · rw [hP]
    linarith
  · rw [hN,hP]
    linarith

theorem individual_budgets {C : SignedCycle} {ab : Fin 4} {s : ScalarCase} {t z : ℝ}
    (ht : 0≤t) (hP : (∑i,(blocks C ab s t z i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab s t z i).N)=t+∑i,(blocks C ab s t z i).P) (i : Fin 4) :
    (blocks C ab s t z i).P≤frameCap ∧ (blocks C ab s t z i).N≤frameCap := by
  have hp := Finset.single_le_sum (fun j _ => (blocks C ab s t z j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (fun j _ => (blocks C ab s t z j).N_nonneg) (Finset.mem_univ i)
  constructor <;> linarith

theorem single_parts (C : SignedCycle) (ab : Fin 4) (s : ScalarCase) (t z : ℝ)
    (i : Fin 4) (hi : single s i=true) :
    (blocks C ab s t z i).P=0 ∨ (blocks C ab s t z i).N=0 := by
  have hv := (single_data C ab s t z i hi).1
  by_cases hu : 0≤(blocks C ab s t z i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right (show -(blocks C ab s t z i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]

theorem angles_small {C : SignedCycle} (ab : Fin 4) (s : ScalarCase) (t z : ℝ)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 4) :
    |(blocks C ab s t z i).u|≤frameCap ∧ |(blocks C ab s t z i).v|≤frameCap := by
  have hzero : |(0:ℝ)| ≤ frameCap := by norm_num [frameCap]
  have hite : ∀ (P : Prop) [Decidable P] (j : Vertex),
      |(if P then delta C.theta j else 0)| ≤ frameCap := by
    intro P _ j
    split_ifs
    · exact ha j
    · exact hzero
  fin_cases i <;> simp only [blocks,rawBlocks,swap,SoleEStress.blocks] <;> split_ifs <;>
    exact ⟨by first | exact ha _ | exact hzero | exact hite _ _,
      by first | exact ha _ | exact hzero | exact hite _ _⟩

theorem block_minorant {C : SignedCycle} {ab : Fin 4} {s : ScalarCase} {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab s t z i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab s t z i).N)=t+∑i,(blocks C ab s t z i).P) (i : Fin 4) :
    F (single s i) R (small s t z i) (large s t z i) (actualNu s t z i)
      (blocks C ab s t z i).P (blocks C ab s t z i).N≤(blocks C ab s t z i).increment R := by
  obtain ⟨hp,hq⟩ := coefficients C ab s t z i
  have hb := individual_budgets (angle ht).1 hP hN i
  cases hi : single s i
  · have hh := (blocks C ab s t z i).minorant R
      (by rw [hp]; exact (small_pos s ht hz i).le) hb.1 hb.2
    rw [hp,hq] at hh
    simpa only [F,Bool.false_eq_true,↓reduceIte] using hh
  · obtain ⟨hv,hnu⟩ := single_data C ab s t z i hi
    have hh := SoleOriginalBlocks.one_angle_minorant (blocks C ab s t z i) R hv
      (angles_small ab s t z ha i).1
    rw [hp,hq,hnu] at hh
    exact hh

theorem increment_eq {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (s : ScalarCase) (R t z : ℝ) :
    increment C ab s R t z=∑i,(blocks C ab s t z i).increment R := by
  rw [increment,SoleEStress.increment_eq C hab (btOwner_cases s.td) (tdOwner_cases s.td)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [blocks]
  split_ifs
  · exact (swap_data (rawBlocks C ab s t z i) R).2.2.2.2.symm
  · rfl

theorem original_increment {C : SignedCycle} {ab : Fin 4} (s : ScalarCase) {R t z L : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C s.family) (hT : 0≤tPrimary C s.td)
    (htotal : delta C.theta G+ePrimary C s.family+tPrimary C s.td=t)
    (hpure : ∀ i,L≤pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t) :
    L≤ increment C ab s R t z := by
  obtain ⟨ht0,hP,hN⟩ := original_budgets hab s t z hvar hG hE hT htotal
  have henvelope := SolePositiveTEnvelope.ordinary_lower s
    (fun i => (blocks C ab s t z i).P) (fun i => (blocks C ab s t z i).N)
    hR hQL hQU ht hz (fun i => (blocks C ab s t z i).P_nonneg)
    (fun i => (blocks C ab s t z i).N_nonneg) hP hN
    (single_parts C ab s t z) hpure
  have hminor := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => block_minorant (R := R) ht hz ha hP hN i)
  rw [increment_eq hab s R t z]
  exact henvelope.trans hminor

end SquaresInCircles.Eight.SolePositiveTOriginalBlocks
