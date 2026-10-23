module

public import SquaresInCircles.Eight.TableFree.PairTerminalOwners
public import SquaresInCircles.Eight.TableFree.NegativeSecondaryEExclusion

/-!
# Secondary-E exclusion on the actual pair-preprocessed seven-cycle

Uncompiled source. The global stress theorem is applied to the actual
transported points and frames. A weak aligned TD2 witness is reselected to
the physically equal TD0 projection when required by the negative-BT leaf.
The conclusion is the exact remaining positive T diagonal; no nearest-axis
or wrong-word exclusion is inserted as an assumption.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate

theorem pair_secondary_E_forces_diagonal {q : ℝ}
    (I : SignedCycle.BoundaryInput q) (hq : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hGA : OG.gaOwner=1) (hHG : OG.hgOwner=2)
    (hG : 0≤I.cycle.theta A-OG.theta)
    (hDE : I.cycle.Feasible D 2) (hEH : I.cycle.Feasible E 0) :
    OT.btOwner=3 ∧ OT.tdOwner=2 ∧ OT.point.y=OT.point.a ∧
      0<OT.theta-I.cycle.theta B := by
  let J := I.pairDescendant hq OG OT
  have hcycle : J.cycle=replacePoint (replacePoint I.cycle G OG.point OG.theta)
      T OT.point OT.theta := rfl
  have hδG : delta J.cycle.theta G=I.cycle.theta A-OG.theta := by
    rw [hcycle]
    simp [replacePoint,delta,next,G,A,T]
  have hδB : delta J.cycle.theta B=OT.theta-I.cycle.theta B := by
    rw [hcycle]
    simp [replacePoint,delta,next,B,G,T]
  have hδT : delta J.cycle.theta T=I.cycle.theta D-OT.theta := by
    rw [hcycle]
    simp [replacePoint,delta,next,D,G,T]
  have hTpoint : J.cycle.point T=OT.point := by rw [hcycle]; simp [replacePoint]
  have hwidth : |OT.theta-I.cycle.theta B|≤7/10 := by
    have hh := J.necessary.spread T B
    rw [hcycle] at hh
    simpa [replacePoint,G,T,B,frameCap] using hh
  have hHGactual : J.cycle.Feasible H 2 := by
    rw [hcycle]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,replacePoint,H,G,T,zeroFeasible,sub_nonneg,hHG] using OG.HG
  have hGAactual : J.cycle.Feasible G 1 := by
    rw [hcycle]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,replacePoint,G,A,T,quarterFeasible,sub_nonneg,hGA] using OG.GA
  have hBTactual : J.cycle.Feasible B OT.btOwner := by
    rw [hcycle]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,replacePoint,B,G,T,quarterFeasible,sub_nonneg] using OT.BT
  have hDEactual : J.cycle.Feasible D 2 := by
    rw [hcycle]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,replacePoint,D,E,G,T] using hDE
  have hEHactual : J.cycle.Feasible E 0 := by
    rw [hcycle]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,replacePoint,H,E,G,T] using hEH
  rcases OT.secondary_E_owner_matrix hq (I.necessary.sorted B)
    (I.necessary.core B) (I.necessary.contained B) hwidth with hmatrix | hdiag
  · obtain ⟨td,hTD,hmatrix⟩ := hmatrix
    have hTDactual : J.cycle.Feasible T td := by
      rw [hcycle]
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,delta,next,replacePoint,T,D,G,zeroFeasible,sub_nonneg] using hTD
    have hregime : (OT.btOwner=2 ∧ td=0) ∨ (OT.btOwner=2 ∧ td=2) ∨
        (OT.btOwner=3 ∧ td=0 ∧ (delta J.cycle.theta B<0 → delta J.cycle.theta T=0)) := by
      simpa only [hδB,hδT] using hmatrix
    let ab := J.witnesses.owner A
    have hab : ab=0 ∨ ab=2 := by
      simpa [ab,SignedCycle.normalOwners,A] using J.witnesses.allowed A
    have hf : ∀i, J.cycle.Feasible i (SecondaryEStress.owners ab OT.btOwner td i) := by
      intro i
      fin_cases i
      · simpa [SecondaryEStress.owners,H] using hHGactual
      · simpa [SecondaryEStress.owners,G] using hGAactual
      · simpa [SecondaryEStress.owners,ab,A] using J.witnesses.feasible A
      · simpa [SecondaryEStress.owners,B] using hBTactual
      · simpa [SecondaryEStress.owners,T] using hTDactual
      · simpa [SecondaryEStress.owners,D] using hDEactual
      · simpa [SecondaryEStress.owners,E] using hEHactual
    exact False.elim (NegativeSecondaryEExclusion.preprocessed_secondary_E_false hq
      J.necessary J.anchors_normal J.positive_variation.le hab
      (by rwa [hδG]) (J.radial T) hregime hf)
  · exact hdiag

end SquaresInCircles.Eight.TableFree
