module

public import SquaresInCircles.Eight.TableFree.FirstNegativeEndpoint
public import SquaresInCircles.Eight.TableFree.OutsideECycle

/-!
# First negative-primary conversion without a BT2 premise

Uncompiled source. The resulting actual cycle retains a high H anchor,
the original right-hand centers and frames, and all original BT axes. Its
E point remains on its actual circle or core boundary. Thus a second
negative-primary conversion can consume this endpoint directly.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace AlignedNegative

structure FirstGEntry (q : ℝ) (C : SignedCycle) (w : C.Witnesses) where
  cycle : SignedCycle
  necessary : cycle.Necessary q
  normal : cycle.NormalAnchors
  witnesses : cycle.Witnesses
  zero_signs : cycle.ZeroSignImplications witnesses
  ordered : cycle.Ordered
  E_nonpos : (cycle.point E).y≤0
  E_boundary : (cycle.point E).Boundary q
  GA_hard : cycle.Feasible G 0
  H_high : 211/250<(cycle.point H).y
  H_primary_lt_one : (cycle.point H).a<1
  aligned : cycle.theta H=cycle.theta G
  above_A : C.theta A≤cycle.theta H
  H_retreat : cycle.theta H<C.theta H
  HG_original : cycle.Feasible H (w.owner H)
  H_nondiagonal : |(cycle.point H).y|<(cycle.point H).a
  G_nondiagonal : |(cycle.point G).y|<(cycle.point G).a
  H_circle_loss : (cycle.point H).circle<(C.point H).circle
  anchor_nonincrease : AnchorNonincrease C cycle
  strict_anchor_loss : StrictAnchorLoss C cycle
  right_owners : witnesses.owner B=w.owner B ∧ witnesses.owner T=w.owner T ∧
    witnesses.owner D=w.owner D
  unchanged : ∀ i, i≠H → i≠G → i≠E →
    cycle.point i=C.point i ∧ cycle.theta i=C.theta i

namespace FirstMixedEndpoint

variable {q : ℝ} {C : SignedCycle} {j : Fin 4}
variable {I : Source q (C.theta H-C.theta A) (C.point H) (C.point G) (C.point A)}

def cycle (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j) : SignedCycle :=
  replaceHG C O.Hpoint O.Gpoint O.angle

theorem unchanged (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (i : Vertex) (hiH : i≠H) (hiG : i≠G) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i :=
  replaceHG_unchanged C O.Hpoint O.Gpoint O.angle i hiH hiG

theorem necessary (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (hn : C.Necessary q) : O.cycle.Necessary q :=
  replaceHG_necessary hn O.H_sorted (O.H_circle_loss.le.trans (hn.contained H))
    O.H_core O.G_sorted O.G_inside.le O.G_core.ge
    ⟨O.angle_mem.1,O.angle_mem.2.le⟩

theorem normal (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (ha : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · have hh : 0≤O.Hpoint.y := by linarith [O.H_high]
    simpa [cycle,replaceHG,replacePoint,H,G] using hh
  · simpa [cycle,replaceHG,replacePoint,H,G,A] using ha.A_nonneg
  · simpa [cycle,replaceHG,replacePoint,H,G,B] using ha.B_nonpos
  · simpa [cycle,replaceHG,replacePoint,H,G,D] using ha.D_nonpos

def witnesses (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (hj : j=0 ∨ j=1) (w : C.Witnesses) : O.cycle.Witnesses where
  owner := ![w.owner H,0,w.owner A,w.owner B,w.owner T,w.owner D,j]
  feasible i := by
    fin_cases i
    · apply (replaceHG_HG C O.Hpoint O.Gpoint O.angle _).2
      have hh : w.owner H=0 ∨ w.owner H=2 := by
        simpa [SignedCycle.normalOwners,H] using w.allowed H
      rcases hh with hh | hh
      · simpa [hh] using O.HG0
      · simpa [hh] using O.HG2
    · exact (replaceHG_GA C O.Hpoint O.Gpoint O.angle 0).2 O.GA0
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle A
        (by decide) _).2 (w.feasible A)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle B
        (by decide) _).2 (w.feasible B)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle T
        (by decide) _).2 (w.feasible T)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle D
        (by decide) _).2 (w.feasible D)
    · exact (replaceHG_EH C O.Hpoint O.Gpoint O.angle j).2 O.EH
  allowed i := by
    fin_cases i
    · simpa [H] using w.allowed H
    · norm_num [SignedCycle.normalOwners,G]
    · simpa [A] using w.allowed A
    · simpa [B] using w.allowed B
    · simpa [T] using w.allowed T
    · simpa [D] using w.allowed D
    · simpa [SignedCycle.normalOwners,E] using hj

theorem zero_signs (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (hj : j=0 ∨ j=1) (w : C.Witnesses) (hz : C.ZeroSignImplications w) :
    O.cycle.ZeroSignImplications (O.witnesses hj w) := by
  constructor
  · intro _
    simpa [cycle,replaceHG,replacePoint] using O.G_negative
  · intro hh
    have hT : w.owner T=0 := by simpa [witnesses,T] using hh
    rw [(O.unchanged T (by decide) (by decide)).1]
    exact hz.TD_canceling hT

theorem anchor_nonincrease
    (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j) :
    AnchorNonincrease C O.cycle := by
  intro i hi
  by_cases hH : i=H
  · subst i
    simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss.le
  · have hG : i≠G := by
      rintro rfl
      simp [anchorVertices,H,A,B,D,E,G] at hi
    rw [(O.unchanged i hH hG).1]

theorem strict_anchor_loss
    (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j) :
    StrictAnchorLoss C O.cycle := by
  refine ⟨H,by simp [anchorVertices],?_⟩
  simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss

def entry (O : FirstMixedEndpoint I (C.point E) (C.theta A-C.theta E) j)
    (hj : j=0 ∨ j=1) (hn : C.Necessary q) (hq : q≤qCap)
    (ha : C.NormalAnchors) (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q) : FirstGEntry q C w where
  cycle := O.cycle
  necessary := O.necessary hn
  normal := O.normal ha
  witnesses := O.witnesses hj w
  zero_signs := O.zero_signs hj w hz
  ordered := SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses hj w) (O.zero_signs hj w hz)
  E_nonpos := by rw [(O.unchanged E (by decide) (by decide)).1]; exact hyE
  E_boundary := by rw [(O.unchanged E (by decide) (by decide)).1]; exact hrE
  GA_hard := (replaceHG_GA C O.Hpoint O.Gpoint O.angle 0).2 O.GA0
  H_high := by simpa [cycle,replaceHG,replacePoint,H,G] using O.H_high
  H_primary_lt_one := by simpa [cycle,replaceHG,replacePoint,H,G] using O.H_primary_lt_one
  aligned := by simp [cycle,replaceHG,replacePoint,H,G]
  above_A := by
    have hh : C.theta A≤C.theta A+O.angle := by linarith [O.angle_mem.1]
    simpa [cycle,replaceHG,replacePoint,H,G] using hh
  H_retreat := by
    have hh : C.theta A+O.angle<C.theta H := by linarith [O.angle_mem.2]
    simpa [cycle,replaceHG,replacePoint,H,G] using hh
  HG_original := (O.witnesses hj w).feasible H
  H_nondiagonal := by simpa [cycle,replaceHG,replacePoint,H,G] using O.H_nondiagonal
  G_nondiagonal := by simpa [cycle,replaceHG,replacePoint] using O.G_nondiagonal
  H_circle_loss := by simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss
  anchor_nonincrease := O.anchor_nonincrease
  strict_anchor_loss := O.strict_anchor_loss
  right_owners := ⟨rfl,rfl,rfl⟩
  unchanged := fun i hiH hiG _ => O.unchanged i hiH hiG

end FirstMixedEndpoint

theorem first_negative_g_mixed_entry {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q)
    (halign : C.theta G=C.theta H) (ht : C.theta A<C.theta H)
    (hyG : (C.point G).y≤0) (hGA : C.Feasible G 1)
    (hnot : ¬C.Feasible G 0) {j : Fin 4} (hj : j=0 ∨ j=1)
    (hEH : C.Feasible E j) (hshort : j=1 → |C.theta H-C.theta E|≤11/50) :
    Nonempty (FirstGEntry q C w) := by
  let I := sourceOfCycle hn ha w halign ht hyG hGA hnot
  have heq : (C.theta A-C.theta E)+(C.theta H-C.theta A)=C.theta H-C.theta E := by ring
  have he : |(C.theta A-C.theta E)+(C.theta H-C.theta A)|≤7/10 := by
    rw [heq]
    exact hn.spread H E
  have hf : quarterFeasible (C.point E) (C.point H)
      ((C.theta A-C.theta E)+(C.theta H-C.theta A)) j := by
    rw [heq]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  obtain ⟨O⟩ := I.first_mixed_endpoint hq (hn.sorted E) (hn.contained E) hyE hj he
    (by intro hj1; rw [heq]; exact hshort hj1) hf
  exact ⟨O.entry hj hn hq ha w hz hyE hrE⟩

namespace FirstGEntry

variable {q : ℝ} {C : SignedCycle} {w : C.Witnesses}

theorem BT_unchanged (J : FirstGEntry q C w) (j : Fin 4) :
    J.cycle.Feasible B j ↔ C.Feasible B j := by
  have hB := J.unchanged B (by decide) (by decide) (by decide)
  have hT := J.unchanged T (by decide) (by decide) (by decide)
  have hn : next B=T := by decide
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,delta,hn,
    hB.1,hB.2,hT.1,hT.2]

def prepend_outside (I : SignedCycle.NormalizedBoundaryInput q) (hq : q≤qCap)
    (O : OutsideE.CycleEndpoint q I.cycle (I.witnesses.owner D))
    (J : FirstGEntry q (O.boundaryInput I hq).cycle (O.boundaryInput I hq).witnesses) :
    FirstGEntry q I.cycle I.witnesses where
  cycle := J.cycle
  necessary := J.necessary
  normal := J.normal
  witnesses := J.witnesses
  zero_signs := J.zero_signs
  ordered := J.ordered
  E_nonpos := J.E_nonpos
  E_boundary := J.E_boundary
  GA_hard := J.GA_hard
  H_high := J.H_high
  H_primary_lt_one := J.H_primary_lt_one
  aligned := J.aligned
  above_A := by
    have hh := J.above_A
    change O.cycle.theta A≤J.cycle.theta H at hh
    rwa [(O.unchanged A (by decide)).2] at hh
  H_retreat := by
    have hh := J.H_retreat
    change J.cycle.theta H<O.cycle.theta H at hh
    rwa [(O.unchanged H (by decide)).2] at hh
  HG_original := by
    simpa [OutsideE.CycleEndpoint.boundaryInput,OutsideE.CycleEndpoint.witnesses,H,E]
      using J.HG_original
  H_nondiagonal := J.H_nondiagonal
  G_nondiagonal := J.G_nondiagonal
  H_circle_loss := by
    have hh := J.H_circle_loss
    change (J.cycle.point H).circle<(O.cycle.point H).circle at hh
    rwa [(O.unchanged H (by decide)).1] at hh
  anchor_nonincrease := O.anchor_nonincrease.trans J.anchor_nonincrease
  strict_anchor_loss := O.anchor_nonincrease.then_strict J.strict_anchor_loss
  right_owners := by
    simpa [OutsideE.CycleEndpoint.boundaryInput,OutsideE.CycleEndpoint.witnesses,B,T,D,E]
      using J.right_owners
  unchanged := by
    intro i hiH hiG hiE
    have hJ := J.unchanged i hiH hiG hiE
    exact ⟨hJ.1.trans (O.unchanged i hiE).1,hJ.2.trans (O.unchanged i hiE).2⟩

end FirstGEntry

end AlignedNegative
end SquaresInCircles.Eight.TableFree
