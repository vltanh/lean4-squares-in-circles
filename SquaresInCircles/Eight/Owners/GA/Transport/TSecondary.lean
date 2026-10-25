module

public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TSource
public import SquaresInCircles.Eight.Owners.GA.Positive.TSource
public import SquaresInCircles.Eight.Owners.GA.Transport.T

/-!
# Eight squares: the full original T reduction reaches an actual BT2 witness

The negative alignment branch is already removed
by reduce_complete. The sole positive BT3/TD0 branch is now excluded for
every A/E source regime. The returned transport is unchanged: it retains
the original radius, source domain and anchor provenance. This is not a
claim that its moved T point equals the original T point.
-/

section
/-!
## The T reduction after the exclusion of the negative alignment

At the negative-BT3 endpoint of the move of T, BT2 is feasible by the A/E dispatch
(`NonpositiveT.Source.aligned_has_BT2`). Only BT2 and a single positive BT3 with TD0 remain
(`reduce_complete`). The TD2 witness used at the negative endpoint comes from the zero-angle owner
tie; no nonzero TD angle is reselected.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.TTransport
open Candidate SignedCycle

structure CompleteResult (q : ℝ) (C : SignedCycle) where
  transport : Result q C
  terminal : (transport.output.cycle C).Feasible B 2 ∨
    ((transport.output.cycle C).Feasible B 3 ∧
      (transport.output.cycle C).Feasible T 0 ∧
      0<delta (transport.output.cycle C).theta B)

theorem reduce_complete {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) : Nonempty (CompleteResult q C) := by
  obtain ⟨O⟩ := reduce I hqL hqU
  have hBT : (O.output.cycle C).Feasible B O.output.btOwner := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,
      TPairOutput.cycle,replacePoint] using O.output.BT
  have hTD : (O.output.cycle C).Feasible T O.output.tdOwner := by
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg,
      TPairOutput.cycle,replacePoint] using O.output.TD
  rcases O.terminal with hb|⟨hb,ht,hpos⟩|⟨hb,ht,he,hneg,hy⟩
  · exact ⟨⟨O,Or.inl (by simpa [hb] using hBT)⟩⟩
  · refine ⟨⟨O,Or.inr ⟨by simpa [hb] using hBT,by simpa [ht] using hTD,?_⟩⟩⟩
    simpa [delta,next,B,T,TPairOutput.cycle,replacePoint] using hpos
  · have hlocal : zeroFeasible O.output.point (C.point D) 0 2 := by
      apply (zero_owner_tie _ _).1
      simpa [he,ht] using O.output.TD
    have hTD2 : (O.output.cycle C).Feasible T 2 := by
      simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg,
        TPairOutput.cycle,replacePoint,he] using hlocal
    have hBT2 := NonpositiveT.Source.aligned_has_BT2 O.source hqL hqU
      (by simpa [hb] using hBT) hTD2
      (by simpa [delta,next,B,T,TPairOutput.cycle,replacePoint] using hneg)
      (by simp [delta,next,T,D,TPairOutput.cycle,replacePoint,he])
      (by simpa [T,TPairOutput.cycle,replacePoint] using hy)
    exact ⟨⟨O,Or.inl hBT2⟩⟩

end SquaresInCircles.Eight.GlobalGA.TTransport
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.TTransport
open Candidate SignedCycle

structure SecondaryResult (q : ℝ) (C : SignedCycle) where
  transport : Result q C
  BT2 : (transport.output.cycle C).Feasible B 2

theorem reduce_secondary {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) : Nonempty (SecondaryResult q C) := by
  obtain ⟨R⟩ := reduce_complete I hqL hqU
  rcases R.terminal with hsecondary|⟨hBT,hTD,hpositive⟩
  · exact ⟨⟨R.transport,hsecondary⟩⟩
  · exact (PositiveT.Source.original_false R.transport.source hqL hqU hBT hTD hpositive.le).elim

end SquaresInCircles.Eight.GlobalGA.TTransport
end
end
end
