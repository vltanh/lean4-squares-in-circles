module

public import SquaresInCircles.Eight.Owners.GA.CoreENormalForm
public import SquaresInCircles.Eight.Owners.GA.High.BT2NegativeANormalForm

/-!
# Eight squares: a core E normalized before A moves

A high-GA source domain with E on the core curve has the gap order and the other fields of a
source domain, and `CoreENormalForm.reduce` uses them to remove a zero E error and two negative E
errors. Only then does `A_normalize` (`NegativeANormalForm.cycle_reduce`) move A, to a signed
cycle that satisfies the necessary conditions but need not be a packing. That second move leaves
E, D, H, B and T, their errors and their axes unchanged.

The zero-tangent theorem of E needs the gap order, so it applies to the source domain and not to
the cycle with A moved. A `CoreEFirstResult` keeps the two records apart, at the same `q`
(`core_E_then_A`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.CoreENormalForm
open GlobalGA.NegativeANormalForm

/-- The first transport gives a high-GA source domain on the cycle with E normalized; the second
gives only a signed cycle with A moved that satisfies the necessary conditions. -/
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

/-- After A is normalized, E keeps the point and the core kind it has on the cycle with E
normalized. -/
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

/-- The normal form of the E primaries survives the move of A: if the selected E total is
negative, there is still one negative flat-core primary, DE3 or EH1. -/
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

/-- The normalization of E keeps the radius, and the move of A keeps the DE and EH witnesses of E
feasible. -/
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
end SquaresInCircles.Eight.HighGABT2
