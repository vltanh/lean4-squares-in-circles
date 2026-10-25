module

public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstJointNegative
public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstNegativeNonnegativeE
public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstNonpositiveT
public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstPositiveTD2
public import SquaresInCircles.Eight.Owners.GA.High.BT2ReducedANonpositiveT

/-!
# Eight squares: a core E with a `BT2` witness, for every sign of A and T

`core_E_all_T_false` excludes every high-GA source domain with E on the core curve and a feasible
BT2 witness. E is normalized first, on the source domain, which has the gap order; then A is
normalized, and the result is only a signed cycle at the same `q` that satisfies the necessary
conditions. T, B, H and D and the errors of their witnesses survive both moves.

Two splits cover every case:
  * the selected total of the moved A is nonnegative or negative;
  * T has TD0, TD2 with nonpositive signed error, or TD2 with positive signed error.
The branch with A and E both negative and positive TD2 uses the joint-negative stress on the same
cycle and the entry bound of EH1, or the EH0 secondary when it is feasible at the same state.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle

/-- No high-GA source domain with E on the core curve has a feasible BT2 witness. A moves only
after E, and the cycle with A moved is used only as a signed cycle, not as a packing. -/
theorem core_E_all_T_false
    {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hcore : (C.point E).Core)
    (hBT : C.Feasible B 2) : False := by
  obtain ⟨R⟩ := core_E_then_A I hqL hqU hcore
  have hBT_E : R.E.cycle.Feasible B 2 :=
    (R.E.other_feasible B (by norm_num [B,D,E])
      (by norm_num [B,E]) 2).2 hBT
  by_cases ha : 0≤GlobalGA.NegativeANormalForm.total
      R.A.ga R.A.ab (delta R.A.cycle.theta G)
        (delta R.A.cycle.theta A)
  · -- Nonnegative A: every normal form of a core E is excluded.
    by_cases ht : tdFlag R.E.source=true ∧
        0<delta R.E.cycle.theta T
    · have hTD : R.E.cycle.Feasible T 2 := by
        have howner := tdFlag_true R.E.source ht.1
        simpa [howner] using R.E.source.feasible T
      have hz : 0≤delta R.A.cycle.theta T := by
        rw [ATransport.original_T_error R.A]
        exact ht.2.le
      exact nonnegative_A_positive_TD2_all_E_false R hqU hBT_E
        hTD hz ha
    · have hnonpos : tdFlag R.E.source=true →
          delta R.A.cycle.theta T≤0 := by
        intro hselected
        rw [ATransport.original_T_error R.A]
        by_contra hgt
        exact ht ⟨hselected,lt_of_not_ge hgt⟩
      exact nonnegative_A_nonpositive_T_all_E_false
        R hqU hBT_E ha hnonpos
  · -- Negative A: a nonpositive T error is excluded for every E, and positive TD2 splits into
    -- a nonnegative E total or exactly one negative DE3 or EH1, with every witness tie kept.
    by_cases ht : tdFlag R.E.source=true ∧
        0<delta R.E.cycle.theta T
    · have hTD : R.E.cycle.Feasible T 2 := by
        have howner := tdFlag_true R.E.source ht.1
        simpa [howner] using R.E.source.feasible T
      have hz : 0≤delta R.A.cycle.theta T := by
        rw [ATransport.original_T_error R.A]
        exact ht.2.le
      rcases R.E_reduced with he|⟨hflat,hcase⟩
      · exact negative_A_nonnegative_E_positive_TD2_false R
          hqU hBT_E hTD hz he ha
      · exact negative_A_negative_E_positive_TD2_false R
          hqU hBT_E hTD hz ha hflat hcase
    · have hnonpos : tdFlag R.E.source=true →
          delta R.E.cycle.theta T≤0 := by
        intro hselected
        by_contra hgt
        exact ht ⟨hselected,lt_of_not_ge hgt⟩
      exact negative_reduced_A_nonpositive_T_false
        R.E.source R.A hqL hqU hBT_E hnonpos ha

end SquaresInCircles.Eight.HighGABT2
