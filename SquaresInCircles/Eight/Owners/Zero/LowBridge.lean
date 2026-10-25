module

public import SquaresInCircles.Eight.Owners.Zero.LowCycle

/-!
# Eight squares: original-frame sign consequences for the global owner rows

These adapters retain the requested weak axis individually.  In
particular the four signs on the putative high-EH/low-GA path follow
without a restriction on any of the other quarter owners.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalZeroLow

open Candidate

theorem frame_zero_low_source_positive {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=0) (hj : word (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    0<C.tangent i := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact zero_low_source_positive C hq G i hinc hinc' j howner haxis

theorem frame_BT_low_A_positive {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (j : Fin 4) (hj : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square B) (C.square T)) : 0<C.tangent A := by
  simpa [A,B,T,next] using frame_zero_low_source_positive F hq A
    (by norm_num [word,A]) (by norm_num [word,A,next]) j hj
    (by simpa [A,B,T,next] using haxis)

end SquaresInCircles.Eight.GlobalZeroLow
