module

public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1Assembly
public import SquaresInCircles.Eight.Words.Outside.ECycle

/-!
# Eight squares: aligned-negative H entry at the same q after the outside E move

The mixed owner of EH is 0 or 1. EH0 and short EH1 use their H/G endpoints
(`negative_g_entry_eh0`, `negative_g_entry_short_eh1`); long EH1 first moves E to the DE2 or
DE3 compact endpoint of the original DE owner and then makes one of those same H/G moves
(`NegativeGEntry.prepend_outside`). The assembly `aligned_negative_boundary_entry_of_span`
takes the H--D frame span `θH - θD ≤ 11/50` of the original cycle as a hypothesis.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
namespace AlignedNegative

/-- A hard descendant that keeps the HG normal of the source and a strict loss on the H circle
of the source, for the pullback of the equality case. -/
structure NegativeGEntry (q : ℝ) (C : SignedCycle) (w : C.Witnesses) where
  target : SignedCycle.HardInput q
  ordered : target.cycle.Ordered
  aligned : target.cycle.theta H=target.cycle.theta G
  above_A : C.theta A≤target.cycle.theta H
  H_retreat : target.cycle.theta H<C.theta H
  HG_original : target.cycle.Feasible H (w.owner H)
  H_nondiagonal : |(target.cycle.point H).y|<(target.cycle.point H).a
  G_nondiagonal : |(target.cycle.point G).y|<(target.cycle.point G).a
  H_circle_loss : (target.cycle.point H).circle<(C.point H).circle
  anchor_nonincrease : AnchorNonincrease C target.cycle
  strict_anchor_loss : StrictAnchorLoss C target.cycle
  unchanged : ∀ i, i≠H → i≠G → i≠E →
    target.cycle.point i=C.point i ∧ target.cycle.theta i=C.theta i

theorem negative_g_entry_eh0 {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0)
    (hr : (C.point E).a≤7/12 ∨
      max |(C.point H).y| |(C.point D).y|≤(C.point E).a)
    (halign : C.theta G=C.theta H) (ht : C.theta A<C.theta H)
    (hyG : (C.point G).y≤0) (hGA : C.Feasible G 1)
    (hnot : ¬C.Feasible G 0) (hEH : C.Feasible E 0) (hBT : C.Feasible B 2) :
    Nonempty (NegativeGEntry q C w) := by
  obtain ⟨J,ho,hal,hlo,hhi,hHG,_,hHd,hGd,hHloss,hAN,hSA,hunch⟩ :=
    aligned_negative_eh0_hard_entry hn hq ha w hz hyE hr halign ht hyG hGA hnot hEH hBT
  exact ⟨{
    target := J
    ordered := ho
    aligned := hal
    above_A := hlo
    H_retreat := hhi
    HG_original := hHG
    H_nondiagonal := hHd
    G_nondiagonal := hGd
    H_circle_loss := hHloss
    anchor_nonincrease := hAN
    strict_anchor_loss := hSA
    unchanged := fun i hiH hiG _ => hunch i hiH hiG }⟩

theorem negative_g_entry_short_eh1 {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0)
    (hr : (C.point E).a≤7/12 ∨
      max |(C.point H).y| |(C.point D).y|≤(C.point E).a)
    (halign : C.theta G=C.theta H) (ht : C.theta A<C.theta H)
    (hyG : (C.point G).y≤0) (hGA : C.Feasible G 1)
    (hnot : ¬C.Feasible G 0) (hEH : C.Feasible E 1)
    (hshort : |C.theta H-C.theta E|≤11/50) (hBT : C.Feasible B 2) :
    Nonempty (NegativeGEntry q C w) := by
  obtain ⟨J,ho,hal,hlo,hhi,hHG,_,hHd,hGd,hHloss,hAN,hSA,hunch⟩ :=
    aligned_negative_short_eh1_hard_entry hn hq ha w hz hyE hr halign ht
      hyG hGA hnot hEH hshort hBT
  exact ⟨{
    target := J
    ordered := ho
    aligned := hal
    above_A := hlo
    H_retreat := hhi
    HG_original := hHG
    H_nondiagonal := hHd
    G_nondiagonal := hGd
    H_circle_loss := hHloss
    anchor_nonincrease := hAN
    strict_anchor_loss := hSA
    unchanged := fun i hiH hiG _ => hunch i hiH hiG }⟩

namespace NegativeGEntry

/-- Composing the move of E alone with an entry of the moved cycle keeps the original H loss,
the original HG normal and every retained anchor circle. -/
def prepend_outside {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hq : q≤qCap)
    (O : OutsideE.CycleEndpoint q I.cycle (I.witnesses.owner D))
    (J : NegativeGEntry q (O.boundaryInput I hq).cycle
      (O.boundaryInput I hq).witnesses) : NegativeGEntry q I.cycle I.witnesses where
  target := J.target
  ordered := J.ordered
  aligned := J.aligned
  above_A := by
    have hh := J.above_A
    change O.cycle.theta A≤J.target.cycle.theta H at hh
    rwa [(O.unchanged A (by decide)).2] at hh
  H_retreat := by
    have hh := J.H_retreat
    change J.target.cycle.theta H<O.cycle.theta H at hh
    rwa [(O.unchanged H (by decide)).2] at hh
  HG_original := by
    simpa [OutsideE.CycleEndpoint.boundaryInput,OutsideE.CycleEndpoint.witnesses,H,E]
      using J.HG_original
  H_nondiagonal := J.H_nondiagonal
  G_nondiagonal := J.G_nondiagonal
  H_circle_loss := by
    have hh := J.H_circle_loss
    change (J.target.cycle.point H).circle<(O.cycle.point H).circle at hh
    rwa [(O.unchanged H (by decide)).1] at hh
  anchor_nonincrease := O.anchor_nonincrease.trans J.anchor_nonincrease
  strict_anchor_loss := O.anchor_nonincrease.then_strict J.strict_anchor_loss
  unchanged := by
    intro i hiH hiG hiE
    have hJ := J.unchanged i hiH hiG hiE
    exact ⟨hJ.1.trans (O.unchanged i hiE).1,hJ.2.trans (O.unchanged i hiE).2⟩

end NegativeGEntry

/-- The assembly over the mixed owner and the original DE owner, under the H--D span
`θH - θD ≤ 11/50` of the original cycle. Both long-angle terminal alternatives are constructed,
and the aligned-long one contradicts this span. -/
theorem aligned_negative_boundary_entry_of_span {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q) (hqL : qLow≤q) (hqU : q≤qCap)
    (halign : I.cycle.theta G=I.cycle.theta H)
    (ht : I.cycle.theta A<I.cycle.theta H)
    (hyG : (I.cycle.point G).y≤0) (hGA : I.cycle.Feasible G 1)
    (hnot : ¬I.cycle.Feasible G 0) (hBT : I.cycle.Feasible B 2)
    (hspan : I.cycle.theta H-I.cycle.theta D≤11/50) :
    Nonempty (NegativeGEntry q I.cycle I.witnesses) := by
  let S := sourceOfCycle I.necessary I.anchors_normal I.witnesses halign ht hyG hGA hnot
  have hr := SignedPoint.boundary_radial_alternative (I.necessary.sorted E) (I.radial E)
    (I.necessary.sorted H) (I.necessary.sorted D)
    (I.necessary.contained H) (I.necessary.contained D)
  by_cases hEH0 : I.cycle.Feasible E 0
  · exact negative_g_entry_eh0 I.necessary hqU I.anchors_normal I.witnesses I.zero_signs
      I.E_nonpos hr halign ht hyG hGA hnot hEH0 hBT
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
    exact negative_g_entry_short_eh1 I.necessary hqU I.anchors_normal I.witnesses
      I.zero_signs I.E_nonpos hr halign ht hyG hGA hnot hEH1 hshort hBT
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
  have hKBT : K.cycle.Feasible B 2 := (O.other_feasible B (by decide) (by decide) 2).2 hBT
  have hKr := SignedPoint.boundary_radial_alternative (K.necessary.sorted E) (K.radial E)
    (K.necessary.sorted H) (K.necessary.sorted D)
    (K.necessary.contained H) (K.necessary.contained D)
  rcases O.terminal_actual with hstop | hstop | hstop
  · obtain ⟨J⟩ := negative_g_entry_eh0 K.necessary hqU K.anchors_normal K.witnesses
      K.zero_signs K.E_nonpos hKr hKal hKt hKyG hKGA hKnot hstop hKBT
    exact ⟨J.prepend_outside I hqU O⟩
  · have hKEH : K.cycle.Feasible E 1 := (O.EH_actual 1).2 O.EH1
    obtain ⟨J⟩ := negative_g_entry_short_eh1 K.necessary hqU K.anchors_normal K.witnesses
      K.zero_signs K.E_nonpos hKr hKal hKt hKyG hKGA hKnot hKEH hstop hKBT
    exact ⟨J.prepend_outside I hqU O⟩
  · exact False.elim ((not_lt_of_ge hspan) hstop.2)

end AlignedNegative
end SquaresInCircles.Eight
