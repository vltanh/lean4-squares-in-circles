module

public import SquaresInCircles.Eight.TableFree.MiddleBRetreatCycle
public import SquaresInCircles.Eight.TableFree.MiddleClampConstruction
public import SquaresInCircles.Eight.TableFree.HardSplitCycle

/-!
# Clamping an actual common middle frame to the G/T interval

Uncompiled draft.  Both exterior cases invoke the explicit separate-circle
pair construction.  The full hard-cycle replacement keeps the original
H/G/T/D/E data and nonincident physical witnesses.  An exterior source
common frame produces strict losses on both A and B.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate MiddleClampConstruction
namespace SignedCycle

theorem HardInput.aligned_AB_gap {q : ℝ} (I : HardInput q)
    (hcommon : I.cycle.theta A=I.cycle.theta B) :
    1 ≤ (I.cycle.point A).y-(I.cycle.point B).y := by
  have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hw := I.witnesses.feasible A
  rcases hj with hj | hj <;>
    simpa [hj,Feasible,slack,edge,Candidate.word,delta,next,A,B,hcommon,
      zeroProjection,sub_nonneg] using hw

def HardInput.fromClamp {q β : ℝ} (I : HardInput q)
    (hβ : β=I.cycle.theta G ∨ β=I.cycle.theta T)
    (O : PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-β) (β-I.cycle.theta T)) : HardInput q :=
  I.replaceMiddle O.pointA O.pointB β hβ O.sorted_A O.sorted_B O.avoids_A O.avoids_B
    O.normal_A.le O.normal_B.le O.circle_A.le O.circle_B.le
    (by unfold quarterFeasible; simpa only [neg_sub] using O.GA_exact.symm.le)
    (by unfold quarterFeasible; simpa only [neg_sub] using O.BT_exact.symm.le)
    O.AB_zero O.AB_two

theorem HardInput.fromClamp_properties {q β : ℝ} (I : HardInput q)
    (hβ : β=I.cycle.theta G ∨ β=I.cycle.theta T)
    (O : PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-β) (β-I.cycle.theta T)) :
    let J := I.fromClamp hβ O
    J.cycle.theta A=β ∧ J.cycle.theta B=β ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  dsimp only
  refine ⟨rfl,rfl,O.AB_exact,O.circle_A,O.circle_B,?_,?_⟩
  · intro i hi
    by_cases ha : i=A
    · subst i; exact O.circle_A.le
    by_cases hb : i=B
    · subst i; exact O.circle_B.le
    · exact (congrArg SignedPoint.circle (replaceMiddle_unchanged I.cycle O.pointA O.pointB β i ha hb).1).le
  · exact replaceMiddle_unchanged I.cycle O.pointA O.pointB β

theorem HardInput.above_common_pair {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hcommon : I.cycle.theta A=I.cycle.theta B)
    (hG : I.cycle.theta G < I.cycle.theta A) :
    Nonempty (PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      0 (I.cycle.theta G-I.cycle.theta T)) := by
  have hspan : (I.cycle.theta A-I.cycle.theta G)+
      (I.cycle.theta G-I.cycle.theta T) ≤ 7/10 := by
    have hh := I.necessary.spread A T
    have ha := le_abs_self (I.cycle.theta A-I.cycle.theta T)
    dsimp [frameCap] at hh
    linarith
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hBTraw : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta T-I.cycle.theta B) 2 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-((I.cycle.theta A-I.cycle.theta G)+(I.cycle.theta G-I.cycle.theta T))) 2 := by
    rw [show -((I.cycle.theta A-I.cycle.theta G)+(I.cycle.theta G-I.cycle.theta T))=
      I.cycle.theta T-I.cycle.theta A by ring,hcommon]
    exact hBTraw
  exact actual_above_pair (I.necessary.sorted A) ((I.necessary.contained A).trans hq)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyG hyT (sub_pos.mpr hG) (sub_nonneg.mpr hGT)
    hspan (I.aligned_AB_gap hcommon) hGA hBT

theorem HardInput.below_common_pair {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hcommon : I.cycle.theta A=I.cycle.theta B)
    (hT : I.cycle.theta A < I.cycle.theta T) :
    Nonempty (PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta T) 0) := by
  have hspan : (I.cycle.theta T-I.cycle.theta A)+
      (I.cycle.theta G-I.cycle.theta T) ≤ 7/10 := by
    have hh := I.necessary.spread G A
    have ha := le_abs_self (I.cycle.theta G-I.cycle.theta A)
    dsimp [frameCap] at hh
    linarith
  have hGAraw : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-((I.cycle.theta T-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta T))) 0 := by
    rw [show -((I.cycle.theta T-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta T))=
      I.cycle.theta A-I.cycle.theta G by ring]
    exact hGAraw
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta T-I.cycle.theta A) 2 := by
    rw [hcommon]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact actual_below_pair (I.necessary.sorted B) ((I.necessary.contained A).trans hq)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyG hyT (sub_pos.mpr hT) (sub_nonneg.mpr hGT)
    hspan (I.aligned_AB_gap hcommon) hGA hBT

/-- The middle common frame lies in the original intermediate interval.
If it started outside, both source anchor circles strictly decrease. -/
theorem HardInput.clamp_common_middle {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hcommon : I.cycle.theta A=I.cycle.theta B) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta A ∈ Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta A<I.cycle.theta T ∨ I.cycle.theta G<I.cycle.theta A) →
        (J.cycle.point A).circle<(I.cycle.point A).circle ∧
        (J.cycle.point B).circle<(I.cycle.point B).circle) ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  by_cases hupper : I.cycle.theta A ≤ I.cycle.theta G
  · by_cases hlower : I.cycle.theta T ≤ I.cycle.theta A
    · refine ⟨I,hcommon,⟨hlower,hupper⟩,I.aligned_AB_gap hcommon,
        anchorNonincrease_refl _,?_,fun _ _ _ => ⟨rfl,rfl⟩⟩
      rintro (h | h) <;> linarith
    · have hlow : I.cycle.theta A < I.cycle.theta T := lt_of_not_ge hlower
      obtain ⟨O⟩ := I.below_common_pair hq hyG hyT hGT hcommon hlow
      have O' : PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
          (I.cycle.theta G-I.cycle.theta T) (I.cycle.theta T-I.cycle.theta T) := by
        simpa only [sub_self] using O
      let J := I.fromClamp (Or.inr rfl) O'
      obtain ⟨hA,hB,hgap,hCA,hCB,hnon,hfixed⟩ := I.fromClamp_properties (Or.inr rfl) O'
      refine ⟨J,hA.trans hB.symm,?_,hgap.symm.le,hnon,fun _ => ⟨hCA,hCB⟩,hfixed⟩
      rw [hA]
      exact ⟨le_rfl,hGT⟩
  · have hupp : I.cycle.theta G < I.cycle.theta A := lt_of_not_ge hupper
    obtain ⟨O⟩ := I.above_common_pair hq hyG hyT hGT hcommon hupp
    have O' : PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
        (I.cycle.theta G-I.cycle.theta G) (I.cycle.theta G-I.cycle.theta T) := by
      simpa only [sub_self] using O
    let J := I.fromClamp (Or.inl rfl) O'
    obtain ⟨hA,hB,hgap,hCA,hCB,hnon,hfixed⟩ := I.fromClamp_properties (Or.inl rfl) O'
    refine ⟨J,hA.trans hB.symm,?_,hgap.symm.le,hnon,fun _ => ⟨hCA,hCB⟩,hfixed⟩
    rw [hA]
    exact ⟨hGT,le_rfl⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
