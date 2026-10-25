module

public import SquaresInCircles.Eight.Words.FirstNegativeOutsideEntry
public import SquaresInCircles.Eight.Owners.Direct.NegativeTCycle

/-!
# Eight squares: hard entry at the same radius when both primary errors are negative

`BothNegativeEntry` records a hard input at the same `q`, reached from a normalized boundary cycle
with HG and TD aligned: the owners of HG, TD and DE are still feasible, H, G, D, T are off the
diagonal, H and D lie strictly inside their original circles, and A, B are unchanged. The first
conversion, of H and G, stops at its first hard contact and pays a strict loss on the original
circle of H. The second, of D and T, uses the sign and boundary of E and pays a strict loss on the
original circle of D; the cuts near H that it needs come from the first-contact construction.
Given the H–D span `θ_H - θ_D < 21/100`, the entry exists (`both_negative_hard_entry_of_span`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
namespace AlignedNegative

structure BothNegativeEntry (q : ℝ) (C : SignedCycle) (w : C.Witnesses) where
  target : SignedCycle.HardInput q
  ordered : target.cycle.Ordered
  HG_aligned : target.cycle.theta H=target.cycle.theta G
  TD_aligned : target.cycle.theta D=target.cycle.theta T
  HG_original : target.cycle.Feasible H (w.owner H)
  TD_original : target.cycle.Feasible T (w.owner T)
  DE_original : target.cycle.Feasible D (w.owner D)
  H_nondiagonal : |(target.cycle.point H).y|<(target.cycle.point H).a
  G_nondiagonal : |(target.cycle.point G).y|<(target.cycle.point G).a
  D_nondiagonal : |(target.cycle.point D).y|<(target.cycle.point D).a
  T_nondiagonal : |(target.cycle.point T).y|<(target.cycle.point T).a
  H_circle_loss : (target.cycle.point H).circle<(C.point H).circle
  D_circle_loss : (target.cycle.point D).circle<(C.point D).circle
  anchor_nonincrease : AnchorNonincrease C target.cycle
  strict_anchor_loss : StrictAnchorLoss C target.cycle
  middle_unchanged : ∀ i, i=A ∨ i=B →
    target.cycle.point i=C.point i ∧ target.cycle.theta i=C.theta i

theorem both_negative_hard_entry_of_span {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (htG : I.cycle.theta A<I.cycle.theta H)
    (hyG : (I.cycle.point G).y≤0) (hGA : I.cycle.Feasible G 1)
    (hnotGA : ¬I.cycle.Feasible G 0)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (htT : I.cycle.theta D<I.cycle.theta B)
    (hyT : 0≤(I.cycle.point T).y) (hBT : I.cycle.Feasible B 3)
    (hnotBT : ¬I.cycle.Feasible B 2)
    (hspan : I.cycle.theta H-I.cycle.theta D<21/100) :
    Nonempty (BothNegativeEntry q I.cycle I.witnesses) := by
  obtain ⟨J⟩ := aligned_negative_first_entry_of_span I hqL hqU hHG htG hyG hGA hnotGA
    (show I.cycle.theta H-I.cycle.theta D≤11/50 by linarith)
  have hB := J.unchanged B (by decide) (by decide) (by decide)
  have hT := J.unchanged T (by decide) (by decide) (by decide)
  have hD := J.unchanged D (by decide) (by decide) (by decide)
  have hTDJ : J.cycle.theta T=J.cycle.theta D := by rw [hT.2,hD.2]; exact hTD
  have htTJ : J.cycle.theta D<J.cycle.theta B := by rw [hD.2,hB.2]; exact htT
  have hyTJ : 0≤(J.cycle.point T).y := by rw [hT.1]; exact hyT
  have hBTJ : J.cycle.Feasible B 3 := (J.BT_unchanged 3).2 hBT
  have hnotBTJ : ¬J.cycle.Feasible B 2 := fun hh => hnotBT ((J.BT_unchanged 2).1 hh)
  have hspanJ : J.cycle.theta H-J.cycle.theta D<21/100 := by
    rw [hD.2]
    linarith [J.H_retreat]
  obtain ⟨K,ho,hTDK,_,_,hTDo,hDEo,_,hDd,hTd,hDloss,hAN,hSA,hunch⟩ :=
    DirectNegativeT.direct_negative_t_hard_entry J.necessary hqL hqU J.normal
      J.witnesses J.zero_signs J.E_nonpos J.E_boundary J.H_high J.H_primary_lt_one
      hspanJ hTDJ htTJ hyTJ hBTJ hnotBTJ J.GA_hard
  have hKH := hunch H (by decide) (by decide) (by decide)
  have hKG := hunch G (by decide) (by decide) (by decide)
  have hHGslack : K.cycle.slack H (I.witnesses.owner H)=
      J.cycle.slack H (I.witnesses.owner H) := by
    simp only [SignedCycle.slack,SignedCycle.edge,delta,show next H=G from rfl,
      hKH.1,hKH.2,hKG.1,hKG.2]
  exact ⟨{
    target := K
    ordered := ho
    HG_aligned := by rw [hKH.2,hKG.2]; exact J.aligned
    TD_aligned := hTDK
    HG_original := by
      change 0≤K.cycle.slack H (I.witnesses.owner H)
      rw [hHGslack]
      exact J.HG_original
    TD_original := by simpa only [J.right_owners.2.1] using hTDo
    DE_original := by simpa only [J.right_owners.2.2] using hDEo
    H_nondiagonal := by rw [hKH.1]; exact J.H_nondiagonal
    G_nondiagonal := by rw [hKG.1]; exact J.G_nondiagonal
    D_nondiagonal := hDd
    T_nondiagonal := hTd
    H_circle_loss := by rw [hKH.1]; exact J.H_circle_loss
    D_circle_loss := by rwa [hD.1] at hDloss
    anchor_nonincrease := J.anchor_nonincrease.trans hAN
    strict_anchor_loss := J.strict_anchor_loss.then_nonincrease hAN
    middle_unchanged := by
      intro i hi
      have hiD : i≠D := by rcases hi with rfl | rfl <;> decide
      have hiT : i≠T := by rcases hi with rfl | rfl <;> decide
      have hiE : i≠E := by rcases hi with rfl | rfl <;> decide
      have hiH : i≠H := by rcases hi with rfl | rfl <;> decide
      have hiG : i≠G := by rcases hi with rfl | rfl <;> decide
      have hK := hunch i hiD hiT hiE
      have hJ := J.unchanged i hiH hiG hiE
      exact ⟨hK.1.trans hJ.1,hK.2.trans hJ.2⟩ }⟩

end AlignedNegative
end SquaresInCircles.Eight
