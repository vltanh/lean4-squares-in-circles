module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2ReducedANegativeOuterE
public import SquaresInCircles.Eight.TableFree.GlobalGACoreENormalForm

/-!
# Core E is normalized BEFORE A moves (necessary source preservation)

The E-core original high-GA source has genuine physical gap order and
all the other necessary source fields. CoreENormalForm.reduce legitimately
uses these to eliminate the zero-E and paired-negative-E endpoints.
Only then may NegativeANormalForm.cycle_reduce move A to a necessary
(nonpacking) cycle. That second move leaves E, D, H, B and T unchanged,
along with their original errors and axes.

Never apply the E zero-tangent physical-order theorem to the moved-A
necessary cycle. This file keeps the two provenance records separate,
with the same actual q. Source-only Lean transcription, no compilation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle
open GlobalGA.CoreENormalForm
open GlobalGA.NegativeANormalForm

/-- The first transport is a genuine high-GA SourceDomain on the
E-normalized cycle. The second is only a necessary A cycle. -/
structure CoreEFirstResult {q : ℝ} {C : SignedCycle}
    (I : GlobalGA.SourceDomain q C) where
  E : GlobalGA.CoreENormalForm.Result I
  A : GlobalGA.NegativeANormalForm.CycleResult q E.cycle

theorem core_E_then_A {q : ℝ} {C : SignedCycle}
    (I : GlobalGA.SourceDomain q C) (hqL : qLow≤q) (hqU : q≤qCap)
    (hcore : (C.point E).Core) : Nonempty (CoreEFirstResult I) := by
  obtain ⟨P⟩ := GlobalGA.CoreENormalForm.reduce I hqL hqU hcore
  obtain ⟨Q⟩ := A_normalize P.source hqL hqU
  exact ⟨⟨P,Q⟩⟩

namespace CoreEFirstResult
variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

/-- E's original-radius point and true-core kind remain exactly the
E-normalized point and kind after A is normalized. -/
theorem E_point : (R.A.cycle.point Candidate.E)=R.E.cycle.point Candidate.E :=
  ATransport.E_point R.A

theorem E_core : (R.A.cycle.point Candidate.E).Core := by
  rw [E_point R]
  exact R.E.E_core

theorem D_error :
    delta R.A.cycle.theta D=delta R.E.cycle.theta D :=
  ATransport.original_D_error R.A

theorem E_error :
    delta R.A.cycle.theta Candidate.E=delta R.E.cycle.theta Candidate.E :=
  ATransport.original_E_error R.A

/-- The E primary normal form survives A motion exactly: if the E
selected total is negative, there remains one genuine negative flat
core primary (DE3 or EH1), not a hypothetical original witness. -/
theorem E_reduced :
    GlobalGA.CoreENormalForm.Reduced R.A.cycle
      (R.E.source.owner D) (R.E.source.owner Candidate.E) := by
  rcases R.E.reduced with he|⟨hf,hcase⟩
  · left
    simpa [ActualCoreEBlocks.eTotal,ActualCoreEBlocks.primaryDE,
      ActualCoreEBlocks.primaryEH,D_error R,E_error R] using he
  · right
    constructor
    · rw [E_point R]
      exact hf
    · rcases hcase with ⟨hd,he,hneg⟩|⟨hd,he,hneg⟩
      · left
        exact ⟨hd,he,by rw [D_error R]; exact hneg⟩
      · right
        exact ⟨hd,he,by rw [E_error R]; exact hneg⟩

/-- E-first normalization never changes the original radius; and
A-first transport never changes E's D/E owner feasibility. -/
theorem DE : R.A.cycle.Feasible D (R.E.source.owner D) :=
  ATransport.DE R.A _ (R.E.source.feasible D)

theorem EH : R.A.cycle.Feasible Candidate.E (R.E.source.owner Candidate.E) :=
  ATransport.EH R.A _ (R.E.source.feasible Candidate.E)

theorem BT2 (h : R.E.cycle.Feasible B 2) : R.A.cycle.Feasible B 2 :=
  ATransport.BT2 R.A h

theorem TD (j : Fin 4) (h : R.E.cycle.Feasible T j) :
    R.A.cycle.Feasible T j :=
  ATransport.TD R.A j h

end CoreEFirstResult
end SquaresInCircles.Eight.TableFree.HighGABT2
