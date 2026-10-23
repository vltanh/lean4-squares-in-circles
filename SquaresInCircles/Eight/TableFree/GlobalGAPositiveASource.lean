module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDSource

/-!
# A positive original A-primary error excludes either original TD owner

Uncompiled source join of the three completed hand-proof branches:
arbitrary original TD0, nonnegative original TD2, and nonpositive
original TD2. The retained original TD witness is classified directly.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA
open Candidate

/-- No TD owner or TD error sign is an input to this original-frame row. -/
theorem frame_one_positive_A_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (atG : Bool)
    (hGA : (forwardAxis (if atG then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if atG then 0 else 2)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H))
    (ha : 0≤TwoPositive.Source.aError (SignedCycle.atFrame F) atG) : False := by
  let j := SignedCycle.retainedOwner F T
  have hf := SignedCycle.retainedOwner_feasible F T
  have hactual := (SignedCycle.atFrame_feasible F T j).1 hf
  rcases GlobalZeroSign.of_frame F hq T (by norm_num [word,T]) j hactual with hlow | hhigh
  · have hTD : (forwardAxis 0).Feasible (C.square T) (C.square D) := by
      simpa [hlow.1,T,D,next] using hactual
    exact PositiveATD0.frame_one_positive_TD0_false F hq hE atG hGA hAB hBT hTD hDE hEH ha
  · have hTD : (forwardAxis 2).Feasible (C.square T) (C.square D) := by
      simpa [hhigh.1,T,D,next] using hactual
    rcases le_total 0 (delta F.theta T) with hz | hz
    · exact TwoPositive.frame_one_positive_TD2_false F hq hE atG hGA hAB hBT hTD hDE hEH ha hz
    · exact PositiveANegativeTD.frame_one_positive_nonpositive_TD2_false F hq hE atG
        hGA hAB hBT hTD hDE hEH ha hz

end SquaresInCircles.Eight.TableFree.GlobalGA
