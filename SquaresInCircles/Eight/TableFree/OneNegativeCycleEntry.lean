module

public import SquaresInCircles.Eight.TableFree.OneNegativeLocalEntry

/-!
# Same-radius one-negative primary entry, with the exact remaining barrier

Uncompiled source. Every original E position is joined to an actual
necessary, ordered seven-cycle. The successful alternative has GA0 and
BT2 with strict original-D circle loss and H/G/A/B unchanged. The other
alternative is a complete original-witness negative-T state with H≤D,
ready for the separate anchor-order exclusion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace DirectNegativeT

structure HardTEntry (q : ℝ) (C : SignedCycle) (w : C.Witnesses) where
  input : SignedCycle.HardInput q
  ordered : input.cycle.Ordered
  TD_aligned : input.cycle.theta T=input.cycle.theta D
  D_advance : C.theta D<input.cycle.theta D
  D_below_B : input.cycle.theta D≤C.theta B
  original_TD : input.cycle.Feasible T (w.owner T)
  original_DE : input.cycle.Feasible D (w.owner D)
  original_EH : input.cycle.Feasible E (w.owner E)
  D_nondiagonal : |(input.cycle.point D).y|<(input.cycle.point D).a
  T_nondiagonal : |(input.cycle.point T).y|<(input.cycle.point T).a
  D_circle_loss : (input.cycle.point D).circle<(C.point D).circle
  anchor_nonincrease : AnchorNonincrease C input.cycle
  strict_anchor_loss : StrictAnchorLoss C input.cycle
  unchanged : ∀ i, i≠D → i≠T → i≠E →
    input.cycle.point i=C.point i ∧ input.cycle.theta i=C.theta i

def LocalEndpoint.hardTEntry {q : ℝ} {C : SignedCycle}
    {I : Source q (C.theta B-C.theta D) (C.point D) (C.point T) (C.point B)}
    (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (hz : C.ZeroSignImplications w) (hGA : C.Feasible G 0) : HardTEntry q C w where
  input := O.hardInput w hn ha hz hGA
  ordered := O.ordered w hn hq ha hz
  TD_aligned := by simp [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
  D_advance := by
    have hh : C.theta D<C.theta B-O.angle := by linarith [O.angle_mem.2]
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E] using hh
  D_below_B := by
    have hh : C.theta B-O.angle≤C.theta B := by linarith [O.angle_mem.1]
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E] using hh
  original_TD := (O.witnesses w).feasible T
  original_DE := (O.witnesses w).feasible D
  original_EH := (O.witnesses w).feasible E
  D_nondiagonal := by
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.D_nondiagonal
  T_nondiagonal := by
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.T_nondiagonal
  D_circle_loss := by
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.D_circle_loss
  anchor_nonincrease := O.anchor_nonincrease
  strict_anchor_loss := O.strict_anchor_loss
  unchanged := O.unchanged

/-- The only scalar span input is the original .22 upper bound. The
construction itself exposes any failure of positive H--D order as an
actual same-radius barrier, including a failure at the original state. -/
theorem one_negative_t_entry_of_span {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hqL : qLow≤q) (hqU : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q)
    (hspan : C.theta H-C.theta D<11/50)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3)
    (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0) :
    Nonempty (HardTEntry q C w) ∨ Nonempty (NegativeTBarrier q) := by
  by_cases horder : C.theta D<C.theta H
  · let I := sourceOfCycle hn ha w halign ht hyT hBT hnot
    have hDEwidth : |(C.theta E-C.theta B)+(C.theta B-C.theta D)|≤7/10 := by
      rw [show (C.theta E-C.theta B)+(C.theta B-C.theta D)=C.theta E-C.theta D by ring]
      exact hn.spread E D
    have hEHwidth : |(C.theta H-C.theta B)-(C.theta E-C.theta B)|≤7/10 := by
      rw [show (C.theta H-C.theta B)-(C.theta E-C.theta B)=C.theta H-C.theta E by ring]
      exact hn.spread H E
    have hspan' : (C.theta H-C.theta B)+(C.theta B-C.theta D)∈Ioc 0 (11/50 : ℝ) := by
      constructor <;> linarith
    have hjDE : w.owner D=2 ∨ w.owner D=3 := by
      simpa [SignedCycle.normalOwners,D] using w.allowed D
    have hjEH : w.owner E=0 ∨ w.owner E=1 := by
      simpa [SignedCycle.normalOwners,E] using w.allowed E
    have hDE : quarterFeasible (C.point D) (C.point E)
        ((C.theta E-C.theta B)+(C.theta B-C.theta D)) (w.owner D) := by
      rw [show (C.theta E-C.theta B)+(C.theta B-C.theta D)=C.theta E-C.theta D by ring]
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,delta,next,D,E,quarterFeasible,sub_nonneg] using w.feasible D
    have hEH : quarterFeasible (C.point E) (C.point H)
        ((C.theta H-C.theta B)-(C.theta E-C.theta B)) (w.owner E) := by
      rw [show (C.theta H-C.theta B)-(C.theta E-C.theta B)=C.theta H-C.theta E by ring]
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,delta,next,H,E,quarterFeasible,sub_nonneg] using w.feasible E
    rcases I.one_negative_endpoint_or_barrier hqL hqU
      (hn.sorted H) (hn.core H) (hn.contained H) ha.H_nonneg
      (hn.sorted E) (hn.contained E) (hn.core E) hrE hyE
      hDEwidth hEHwidth hspan' (w.owner D) (w.owner E) hjDE hjEH hDE hEH with ⟨O⟩ | ⟨O⟩
    · exact Or.inl ⟨O.hardTEntry w hn hqU ha hz hGA⟩
    · exact Or.inr ⟨O.barrier w hn ha hz hGA⟩
  · exact Or.inr ⟨{
      cycle := C
      necessary := hn
      anchors_normal := ha
      E_nonpos := hyE
      witnesses := w
      zero_signs := hz
      GA_hard := hGA
      BT_secondary := hBT
      BT_unavailable := hnot
      TD_aligned := halign
      negative_BT := ht
      T_nonneg := hyT
      H_not_above := le_of_not_gt horder }⟩

end DirectNegativeT
end SquaresInCircles.Eight.TableFree
