module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTSource

/-!
# All original high-GA witnesses excluded in the positive BT3/TD0 sector

Source-only Lean transcription of the source-level positive-T dispatcher.
A putative high GA axis is selected on the *unchanged* BoundaryCycle,
and the other six axes are the actual initially selected weak witnesses.
No A or E owner, radial kind, error sign or total is passed by the caller.

The lower qLow bound is explicit. The fixed-ceiling hand argument handles
smaller working radii before this same-radius high-GA exclusion is used.
No Lean/CI compilation has been run.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA
open Candidate SignedCycle

/-- Every actual high GA witness is impossible if the original BT3 and
TD0 axes are weakly feasible and the actual BT3 error is nonnegative.
This is a theorem about original squares, not about a moved endpoint. -/
theorem high_GA_positive_BT3_TD0_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (hqL : qLow≤q) (hE : C.tangent E≤0)
    (j : Fin 4) (hj : j=2∨j=3)
    (hGA : (forwardAxis j).Feasible (C.square G) (C.square A))
    (hBT : (forwardAxis 3).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D))
    (hz : 0≤delta F.theta B) : False := by
  let I : SourceDomain q (SignedCycle.atFrame F) :=
    sourceDomain F hq hE j hj hGA
  have hBT' : (SignedCycle.atFrame F).Feasible B 3 :=
    (SignedCycle.atFrame_feasible F B 3).2 (by
      simpa [B,T,next] using hBT)
  have hTD' : (SignedCycle.atFrame F).Feasible T 0 :=
    (SignedCycle.atFrame_feasible F T 0).2 (by
      simpa [T,D,next] using hTD)
  have hz' : 0≤delta (SignedCycle.atFrame F).theta B := by
    simpa [SignedCycle.atFrame] using hz
  exact PositiveT.Source.original_false I hqL hq.2 hBT' hTD' hz'

/-- In this entire original physical sector, every feasible GA axis
is low, even when a high and a low axis are simultaneously feasible. -/
theorem all_GA_low_of_positive_BT3_TD0 {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (hqL : qLow≤q) (hE : C.tangent E≤0)
    (hBT : (forwardAxis 3).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D))
    (hz : 0≤delta F.theta B) :
    ∀ j : Fin 4, (forwardAxis j).Feasible (C.square G) (C.square A) →
      j=0∨j=1 := by
  intro j hj
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact (high_GA_positive_BT3_TD0_false F hq hqL hE 2
      (Or.inl rfl) hj hBT hTD hz).elim
  · exact (high_GA_positive_BT3_TD0_false F hq hqL hE 3
      (Or.inr rfl) hj hBT hTD hz).elim

end SquaresInCircles.Eight.TableFree.GlobalGA
