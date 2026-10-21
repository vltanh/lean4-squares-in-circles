module

public import SquaresInCircles.Eight.TableFree.FirstNegativeCycle

/-!
# Exhaustive original-E preparation for the first negative primary

Uncompiled source. EH0 and short EH1 reach the paid first GA0 contact
directly. The long-EH1 branch first moves E on its actual core/circle arc
using the original DE2 or DE3 witness. The original H--D span rules out
the aligned-long alternative. No BT2 availability is required.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace AlignedNegative

theorem aligned_negative_first_entry_of_span {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q) (hqL : qLow≤q) (hqU : q≤qCap)
    (halign : I.cycle.theta G=I.cycle.theta H)
    (ht : I.cycle.theta A<I.cycle.theta H)
    (hyG : (I.cycle.point G).y≤0) (hGA : I.cycle.Feasible G 1)
    (hnot : ¬I.cycle.Feasible G 0)
    (hspan : I.cycle.theta H-I.cycle.theta D≤11/50) :
    Nonempty (FirstGEntry q I.cycle I.witnesses) := by
  let S := sourceOfCycle I.necessary I.anchors_normal I.witnesses halign ht hyG hGA hnot
  by_cases hEH0 : I.cycle.Feasible E 0
  · exact first_negative_g_mixed_entry I.necessary hqU I.anchors_normal I.witnesses
      I.zero_signs I.E_nonpos (I.radial E) halign ht hyG hGA hnot
      (Or.inl rfl) hEH0 (by norm_num)
  have hEH1 : I.cycle.Feasible E 1 := by
    have hj : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [SignedCycle.normalOwners,E] using I.witnesses.allowed E
    rcases hj with hj | hj
    · exact False.elim (hEH0 (by simpa [hj] using I.witnesses.feasible E))
    · simpa [hj] using I.witnesses.feasible E
  have hpwidth : |I.cycle.theta H-I.cycle.theta E|≤7/10 := I.necessary.spread H E
  have hpactual : quarterFeasible (I.cycle.point E) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta E) 1 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH1
  have hppos := S.eh1_error_positive hqU (I.necessary.sorted E) I.E_nonpos hpwidth hpactual
  by_cases hpshort : I.cycle.theta H-I.cycle.theta E≤11/50
  · have hshort : |I.cycle.theta H-I.cycle.theta E|≤11/50 := by
      rwa [abs_of_pos hppos]
    exact first_negative_g_mixed_entry I.necessary hqU I.anchors_normal I.witnesses
      I.zero_signs I.E_nonpos (I.radial E) halign ht hyG hGA hnot
      (Or.inr rfl) hEH1 (fun _ => hshort)
  have hplong := lt_of_not_ge hpshort
  have hn : I.cycle.theta E<I.cycle.theta D := by linarith
  have hcuts := S.cuts hqU
  obtain ⟨O⟩ := OutsideE.cycle_endpoint I hqL hqU hcuts.2.2.2.1 hcuts.2.2.2.2.1
    hn hplong hEH1
  let K := O.boundaryInput I hqU
  have hKH : K.cycle.point H=I.cycle.point H ∧ K.cycle.theta H=I.cycle.theta H :=
    O.unchanged H (by decide)
  have hKG : K.cycle.point G=I.cycle.point G ∧ K.cycle.theta G=I.cycle.theta G :=
    O.unchanged G (by decide)
  have hKA : K.cycle.point A=I.cycle.point A ∧ K.cycle.theta A=I.cycle.theta A :=
    O.unchanged A (by decide)
  have hKal : K.cycle.theta G=K.cycle.theta H := by rw [hKG.2,hKH.2]; exact halign
  have hKt : K.cycle.theta A<K.cycle.theta H := by rw [hKA.2,hKH.2]; exact ht
  have hKyG : (K.cycle.point G).y≤0 := by rw [hKG.1]; exact hyG
  have hKGA : K.cycle.Feasible G 1 := (O.other_feasible G (by decide) (by decide) 1).2 hGA
  have hKnot : ¬K.cycle.Feasible G 0 := fun hh =>
    hnot ((O.other_feasible G (by decide) (by decide) 0).1 hh)
  rcases O.terminal_actual with hstop | hstop | hstop
  · obtain ⟨J⟩ := first_negative_g_mixed_entry K.necessary hqU K.anchors_normal K.witnesses
      K.zero_signs K.E_nonpos (K.radial E) hKal hKt hKyG hKGA hKnot
      (Or.inl rfl) hstop (by norm_num)
    exact ⟨J.prepend_outside I hqU O⟩
  · have hKEH : K.cycle.Feasible E 1 := (O.EH_actual 1).2 O.EH1
    obtain ⟨J⟩ := first_negative_g_mixed_entry K.necessary hqU K.anchors_normal K.witnesses
      K.zero_signs K.E_nonpos (K.radial E) hKal hKt hKyG hKGA hKnot
      (Or.inr rfl) hKEH (fun _ => hstop)
    exact ⟨J.prepend_outside I hqU O⟩
  · exact False.elim ((not_lt_of_ge hspan) hstop.2)

end AlignedNegative
end SquaresInCircles.Eight.TableFree
