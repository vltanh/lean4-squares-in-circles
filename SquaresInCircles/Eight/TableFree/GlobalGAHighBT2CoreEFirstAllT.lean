module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2CoreEFirstJointNegative
public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2CoreEFirstNonpositiveT

/-!
# Complete core-E actual BT2 source across A and T signs

This exhausts the actual high-GA SourceDomain when original E is
true-core, with BT2 genuinely feasible. Normalize E *first* in its
genuine source (with original physical gap order). Then normalize A,
whose result is only a necessary signed cycle at the same q. T/B/H/D
and their originally retained witness errors survive both motions.

The two exhaustive real splits are:
  * selected transported A total nonnegative vs negative;
  * actual original TD0, TD2 with nonpositive signed error, or TD2
    with strictly positive signed error.
The jointly negative E/A, positive TD2 branch is discharged using the
original same-cycle joint-negative stress and the genuine EH1 entry
(or an actually feasible same-state EH0 secondary).

There is no new axiom or owner-capture hypothesis.
Uncompiled source transcription: no Lean, lake, tests or CI.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle

/-- All genuinely true-core original E source records with BT2 are
excluded. A is never moved before E, and the local A cycle is not
asserted to be a new physical packing. -/
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
  · -- Nonnegative A: all true-core E normal forms are already excluded.
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
  · -- Genuine negative A: nonpositive T source is handled for any E,
    -- and positive TD2 splits into nonnegative E or exactly one true
    -- negative DE3/EH1 with all physical witness ties retained.
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

end SquaresInCircles.Eight.TableFree.HighGABT2
