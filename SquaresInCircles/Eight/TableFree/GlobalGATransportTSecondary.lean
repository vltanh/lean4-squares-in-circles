module

public import SquaresInCircles.Eight.TableFree.GlobalGATransportTComplete
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTSource

/-!
# The full original T reduction reaches an actual BT2 witness

Uncompiled source join. The negative alignment branch is already removed
by reduce_complete. The sole positive BT3/TD0 branch is now excluded for
every A/E source regime. The returned transport is unchanged: it retains
the original radius, source domain and anchor provenance. This is not a
claim that its moved T point equals the original T point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.TTransport
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

end SquaresInCircles.Eight.TableFree.GlobalGA.TTransport
