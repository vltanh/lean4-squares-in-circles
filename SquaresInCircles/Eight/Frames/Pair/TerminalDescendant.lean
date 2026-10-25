module

public import SquaresInCircles.Eight.Boundary.Preprocessing
public import SquaresInCircles.Eight.Frames.Pair.TerminalMatrix

/-!
# Eight squares: the terminal matrix after the two pair moves

On the cycle after the two pair moves (`BoundaryInput.pairDescendant`), the terminal alternatives
of the two outputs give the terminal states of G and of T (`states`), except when a moved point
lies on a diagonal of the nearest axes, `yG = -aG` or `yT = aT`; these two cases stay as
hypotheses. Without them, the terminal matrix gives hard owners on the cycle after the moves
(`hard_of_no_diagonal`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.PairTerminalDescendant
open Candidate SignedCycle Stationary GeometricModel PairTerminalMatrix

theorem states {q : ℝ} (I : BoundaryInput q) (hcap : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hGdiag : ((I.pairDescendant hcap OG OT).cycle.point G).y ≠
      -((I.pairDescendant hcap OG OT).cycle.point G).a)
    (hTdiag : ((I.pairDescendant hcap OG OT).cycle.point T).y ≠
      ((I.pairDescendant hcap OG OT).cycle.point T).a) :
    GState (I.pairDescendant hcap OG OT).cycle (I.pairDescendant hcap OG OT).witnesses ∧
    TState (I.pairDescendant hcap OG OT).cycle (I.pairDescendant hcap OG OT).witnesses := by
  let J := I.pairDescendant hcap OG OT
  obtain ⟨hH,hG,hA,hB,hT,hD,hE⟩ := I.pairDescendant_owners hcap OG OT
  have hGp : J.cycle.point G=OG.point := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,G,T]
  have hTp : J.cycle.point T=OT.point := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint]
  have hGt : J.cycle.theta G=OG.theta := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,G,T]
  have hHt : J.cycle.theta H=I.cycle.theta H := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,H,G,T]
  have hTt : J.cycle.theta T=OT.theta := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint]
  have hDt : J.cycle.theta D=I.cycle.theta D := by simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,D,G,T]
  have hdeltaG : delta J.cycle.theta G=I.cycle.theta A-OG.theta := by
    simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,delta,next,G,A,T]
  have hdeltaB : delta J.cycle.theta B=OT.theta-I.cycle.theta B := by
    simp [J,BoundaryInput.pairDescendant_cycle,replacePoint,delta,next,B,G,T]
  change GState J.cycle J.witnesses ∧ TState J.cycle J.witnesses
  constructor
  · rcases OG.terminal with hg | ⟨hg,hh,hpos⟩ | ⟨hg,ha,hneg,hy⟩ | hdiag
    · exact Or.inl (hG.trans hg)
    · exact Or.inr (Or.inl ⟨hG.trans hg,hH.trans hh,by rwa [hdeltaG]⟩)
    · exact Or.inr (Or.inr ⟨hG.trans hg,by rw [hGt,hHt,ha],
        by rwa [hdeltaG],by rwa [hGp]⟩)
    · exact (hGdiag (by change (J.cycle.point G).y= -(J.cycle.point G).a; rwa [hGp])).elim
  · rcases OT.terminal with hb | ⟨hb,ht,hpos⟩ | ⟨hb,ha,hneg,hy⟩ | hdiag
    · exact Or.inl (hB.trans hb)
    · exact Or.inr (Or.inl ⟨hB.trans hb,hT.trans ht,by rwa [hdeltaB]⟩)
    · exact Or.inr (Or.inr ⟨hB.trans hb,by rw [hTt,hDt,ha],
        by rwa [hdeltaB],by rwa [hTp]⟩)
    · exact (hTdiag (by change (J.cycle.point T).y=(J.cycle.point T).a; rwa [hTp])).elim

theorem hard_of_no_diagonal {q : ℝ} (I : NormalizedBoundaryInput q)
    (hQL : qLow≤q) (hq : q≤qStar) (hcap : q≤qCap)
    (OG : GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (OT : TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hGdiag : ((I.pairDescendant hcap OG OT).cycle.point G).y ≠
      -((I.pairDescendant hcap OG OT).cycle.point G).a)
    (hTdiag : ((I.pairDescendant hcap OG OT).cycle.point T).y ≠
      ((I.pairDescendant hcap OG OT).cycle.point T).a) :
    (I.pairDescendant hcap OG OT).cycle.HardOwners := by
  have hs := states I.toBoundaryInput hcap OG OT hGdiag hTdiag
  exact PairTerminalMatrix.hard (I.pairDescendant hcap OG OT) hQL hq hs.1 hs.2

end SquaresInCircles.Eight.PairTerminalDescendant
