module

public import SquaresInCircles.Eight.TableFree.OutsideDE2Endpoint
public import SquaresInCircles.Eight.TableFree.AlignedNegativeEH1Assembly

/-!
# Actual seven-cycle insertion of the two outside-E endpoints

Uncompiled source. The compact DE2 and DE3 constructions change only E.
This file inserts their point at its proved physical frame, retains the
original DE axis and every nonincident witness, proves physical order, and
computes the exact decrease of both signed variation budgets. In particular
the output is again an actual boundary input at the same working radius.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace OutsideE

/-- Common geometric output of the two proved compact constructions. The
parameter j is the original DE owner, rather than a newly selected axis. -/
structure CycleEndpoint (q : ℝ) (C : SignedCycle) (j : Fin 4) where
  point : SignedPoint
  movement : ℝ
  movement_nonneg : 0≤movement
  movement_le_n : movement≤C.theta D-C.theta E
  error_positive : 0<C.theta H-C.theta E-movement
  sorted : point.Sorted
  contained : point.Contained q
  core : point.AvoidsCore
  radial : point.Boundary q
  nonpos : point.y≤0
  tangent_nonincrease : |point.y|≤|(C.point E).y|
  circle_nonincrease : point.circle≤(C.point E).circle
  DE : quarterFeasible (C.point D) point (-(C.theta D-C.theta E-movement)) j
  EH1 : quarterFeasible point (C.point H) (C.theta H-C.theta E-movement) 1
  terminal : quarterFeasible point (C.point H) (C.theta H-C.theta E-movement) 0 ∨
    C.theta H-C.theta E-movement≤11/50 ∨
      (C.theta D-C.theta E-movement=0 ∧ 11/50<C.theta H-C.theta E-movement)

def DE2Endpoint.toCycle {q : ℝ} {C : SignedCycle}
    (O : DE2Endpoint q (C.point D) (C.point E) (C.point H)
      (C.theta D-C.theta E) (C.theta H-C.theta E)) : CycleEndpoint q C 2 where
  point := O.point
  movement := O.movement
  movement_nonneg := O.movement_nonneg
  movement_le_n := O.movement_le_n
  error_positive := O.error_positive
  sorted := O.sorted
  contained := O.contained
  core := O.core
  radial := O.radial
  nonpos := O.nonpos
  tangent_nonincrease := O.tangent_nonincrease
  circle_nonincrease := O.circle_nonincrease
  DE := O.DE2
  EH1 := O.EH1
  terminal := O.terminal

def DE3Endpoint.toCycle {q : ℝ} {C : SignedCycle}
    (O : DE3Endpoint q (C.point D) (C.point E) (C.point H)
      (C.theta D-C.theta E) (C.theta H-C.theta E)) : CycleEndpoint q C 3 where
  point := O.point
  movement := O.movement
  movement_nonneg := O.movement_nonneg
  movement_le_n := O.movement_le_n
  error_positive := O.error_positive
  sorted := O.sorted
  contained := O.contained
  core := O.core
  radial := O.radial
  nonpos := O.nonpos
  tangent_nonincrease := O.tangent_nonincrease
  circle_nonincrease := O.circle_nonincrease
  DE := O.DE3
  EH1 := O.EH1
  terminal := O.terminal

namespace CycleEndpoint

variable {q : ℝ} {C : SignedCycle} {j : Fin 4}

def cycle (O : CycleEndpoint q C j) : SignedCycle :=
  replacePoint C E O.point (C.theta E+O.movement)

theorem unchanged (O : CycleEndpoint q C j) (i : Vertex) (hi : i≠E) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i := by
  simp [cycle,replacePoint,hi]

theorem DE_actual (O : CycleEndpoint q C j) : O.cycle.Feasible D j := by
  have heq : C.theta E+O.movement-C.theta D=
      -(C.theta D-C.theta E-O.movement) := by ring
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using O.DE

theorem EH_actual (O : CycleEndpoint q C j) (k : Fin 4) :
    O.cycle.Feasible E k ↔
      quarterFeasible O.point (C.point H) (C.theta H-C.theta E-O.movement) k := by
  have heq : C.theta H-(C.theta E+O.movement)=
      C.theta H-C.theta E-O.movement := by ring
  simp [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,E,quarterFeasible,sub_nonneg,heq]

theorem other_feasible (O : CycleEndpoint q C j) (i : Vertex)
    (hiD : i≠D) (hiE : i≠E) (k : Fin 4) :
    O.cycle.Feasible i k ↔ C.Feasible i k := by
  have hn : next i≠E := by fin_cases i <;> norm_num [next,D,E] at hiD ⊢
  exact SignedCycle.replacePoint_other_feasible hiE hn

theorem frame_range (O : CycleEndpoint q C j) :
    C.theta E+O.movement∈Icc (min (C.theta E) (C.theta D))
      (max (C.theta E) (C.theta D)) := by
  have hED : C.theta E≤C.theta D := by
    linarith [O.movement_nonneg,O.movement_le_n]
  rw [min_eq_left hED,max_eq_right hED]
  constructor <;> linarith [O.movement_nonneg,O.movement_le_n]

theorem necessary (O : CycleEndpoint q C j) (hn : C.Necessary q) :
    O.cycle.Necessary q :=
  SignedCycle.necessary_replace_clamped (v := E) (a := E) (b := D)
    hn O.sorted O.contained O.core (Or.inr O.frame_range)

theorem normal (O : CycleEndpoint q C j) (ha : C.NormalAnchors) :
    O.cycle.NormalAnchors := by
  constructor
  · rw [(O.unchanged H (by decide)).1]; exact ha.H_nonneg
  · rw [(O.unchanged A (by decide)).1]; exact ha.A_nonneg
  · rw [(O.unchanged B (by decide)).1]; exact ha.B_nonpos
  · rw [(O.unchanged D (by decide)).1]; exact ha.D_nonpos

def witnesses (w : C.Witnesses) (O : CycleEndpoint q C (w.owner D)) :
    O.cycle.Witnesses where
  owner := Function.update w.owner E 1
  feasible i := by
    by_cases hiE : i=E
    · subst i
      simpa using (O.EH_actual 1).2 O.EH1
    · by_cases hiD : i=D
      · subst i
        simpa [E,D] using O.DE_actual
      · simpa [Function.update_of_ne hiE] using
          (O.other_feasible i hiD hiE (w.owner i)).2 (w.feasible i)
  allowed i := by
    by_cases hiE : i=E
    · subst i
      norm_num [SignedCycle.normalOwners,E]
    · simpa [Function.update_of_ne hiE] using w.allowed i

theorem zero_signs (w : C.Witnesses) (O : CycleEndpoint q C (w.owner D))
    (hz : C.ZeroSignImplications w) : O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hj
    have hj' : w.owner H=2 := by simpa [witnesses,H,E] using hj
    rw [(O.unchanged G (by decide)).1]
    exact hz.HG_canceling hj'
  · intro hj
    have hj' : w.owner T=0 := by simpa [witnesses,T,E] using hj
    rw [(O.unchanged T (by decide)).1]
    exact hz.TD_canceling hj'

theorem ordered (w : C.Witnesses) (O : CycleEndpoint q C (w.owner D))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (hz : C.ZeroSignImplications w) : O.cycle.Ordered :=
  SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses w) (O.zero_signs w hz)

theorem strict_spread (O : CycleEndpoint q C j) (hs : C.StrictSpread) :
    O.cycle.StrictSpread :=
  SignedCycle.strictSpread_replace_clamped (v := E) (a := E) (b := D)
    (p := O.point) hs (Or.inr O.frame_range)

theorem variations (O : CycleEndpoint q C j) :
    positiveVariation C.theta-positiveVariation O.cycle.theta=O.movement ∧
      negativeVariation C.theta-negativeVariation O.cycle.theta=O.movement := by
  have hDEold : positivePart (C.theta E-C.theta D)=0 :=
    max_eq_right (by linarith [O.movement_nonneg,O.movement_le_n])
  have hDEnew : positivePart (C.theta E+O.movement-C.theta D)=0 :=
    max_eq_right (by linarith [O.movement_le_n])
  have hEHold : positivePart (C.theta H-C.theta E)=C.theta H-C.theta E :=
    max_eq_left (by linarith [O.error_positive,O.movement_nonneg])
  have hEHnew : positivePart (C.theta H-(C.theta E+O.movement))=
      C.theta H-(C.theta E+O.movement) :=
    max_eq_left (by linarith [O.error_positive])
  have hp : positiveVariation C.theta-positiveVariation O.cycle.theta=O.movement := by
    simp [positiveVariation,Fin.sum_univ_succ,delta,next,cycle,replacePoint,
      H,G,A,B,T,D,E,Function.update_apply,hDEold,hDEnew,hEHold,hEHnew]
    ring
  exact ⟨hp,by
    simpa only [← variations_equal C.theta,← variations_equal O.cycle.theta] using hp⟩

theorem anchor_nonincrease (O : CycleEndpoint q C j) :
    AnchorNonincrease C O.cycle := by
  intro i hi
  by_cases hiE : i=E
  · subst i
    simpa [cycle,replacePoint] using O.circle_nonincrease
  · rw [(O.unchanged i hiE).1]

theorem radial_all (O : CycleEndpoint q C j) (hr : ∀ i, (C.point i).Boundary q) :
    ∀ i, (O.cycle.point i).Boundary q := by
  intro i
  by_cases hiE : i=E
  · subst i
    simpa [cycle,replacePoint] using O.radial
  · rw [(O.unchanged i hiE).1]
    exact hr i

theorem terminal_actual (O : CycleEndpoint q C j) :
    O.cycle.Feasible E 0 ∨
      |O.cycle.theta H-O.cycle.theta E|≤11/50 ∨
      (O.cycle.theta E=O.cycle.theta D ∧ 11/50<C.theta H-C.theta D) := by
  rcases O.terminal with hh | hh | ⟨hn,hp⟩
  · exact Or.inl ((O.EH_actual 0).2 hh)
  · right; left
    have heq : O.cycle.theta H-O.cycle.theta E=
        C.theta H-C.theta E-O.movement := by
      simp [cycle,replacePoint,H,E]
      ring
    rw [heq,abs_of_pos O.error_positive]
    exact hh
  · right; right
    constructor
    · simp [cycle,replacePoint,D,E]
      linarith
    · linarith

/-- All original outer anchors are literally retained; the new E point is
on its original radial arc. The lower signed budgets are proved above. -/
def boundaryInput (I : SignedCycle.NormalizedBoundaryInput q) (hq : q≤qCap)
    (O : CycleEndpoint q I.cycle (I.witnesses.owner D)) :
    SignedCycle.NormalizedBoundaryInput q where
  cycle := O.cycle
  necessary := O.necessary I.necessary
  ordered := O.ordered I.witnesses I.necessary hq I.anchors_normal I.zero_signs
  strict_spread := O.strict_spread I.strict_spread
  positive_variation := by
    have hvar := O.variations.1
    linarith [I.positive_variation,O.movement_nonneg]
  negative_variation := by
    have hvar := O.variations.2
    linarith [I.negative_variation,O.movement_nonneg]
  radial := O.radial_all I.radial
  anchors_outer := by
    intro i hi
    have hiE : i≠E := by fin_cases i <;> norm_num [H,A,B,D,E] at hi ⊢
    rw [(O.unchanged i hiE).1]
    exact I.anchors_outer i hi
  anchors_normal := O.normal I.anchors_normal
  witnesses := O.witnesses I.witnesses
  zero_signs := O.zero_signs I.witnesses I.zero_signs
  E_nonpos := by simpa [cycle,replacePoint] using O.nonpos

end CycleEndpoint

/-- The original owner matrix has exactly its two genuine compact leaves.
No terminal event or feasible intermediate path is assumed. -/
theorem cycle_endpoint {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<(I.cycle.point H).y) (hHa : (I.cycle.point H).a<1)
    (hn : I.cycle.theta E<I.cycle.theta D)
    (hp : 11/50<I.cycle.theta H-I.cycle.theta E)
    (hEH : I.cycle.Feasible E 1) :
    Nonempty (CycleEndpoint q I.cycle (I.witnesses.owner D)) := by
  have hnrange : I.cycle.theta D-I.cycle.theta E∈Ioc 0 (7/10 : ℝ) :=
    ⟨sub_pos.mpr hn,(le_abs_self _).trans (I.necessary.spread D E)⟩
  have hprange : I.cycle.theta H-I.cycle.theta E∈Ioc (11/50 : ℝ) (7/10 : ℝ) :=
    ⟨hp,(le_abs_self _).trans (I.necessary.spread H E)⟩
  have hHouter := I.anchors_outer H (by simp)
  have hDouter := I.anchors_outer D (by simp)
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta E) 1 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  have hDE' : quarterFeasible (I.cycle.point D) (I.cycle.point E)
      (-(I.cycle.theta D-I.cycle.theta E)) (I.witnesses.owner D) := by
    have heq : -(I.cycle.theta D-I.cycle.theta E)=
        I.cycle.theta E-I.cycle.theta D := by ring
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using I.witnesses.feasible D
  have hj : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
    simpa [SignedCycle.normalOwners,D] using I.witnesses.allowed D
  rcases hj with hj | hj
  · rw [hj]
    obtain ⟨O⟩ := de2_endpoint hqL hqU (I.necessary.sorted H) hHy hHa hHouter
      (I.necessary.sorted D) I.anchors_normal.D_nonpos hDouter
      (I.necessary.sorted E) I.E_nonpos (I.radial E) hnrange hprange
      (by simpa [hj] using hDE') hEH'
    exact ⟨O.toCycle⟩
  · rw [hj]
    obtain ⟨O⟩ := de3_endpoint hqL hqU (I.necessary.sorted H) hHy hHa hHouter
      (I.necessary.sorted E) I.E_nonpos (I.radial E) hnrange hprange
      (by simpa [hj] using hDE') hEH'
    exact ⟨O.toCycle⟩

end OutsideE
end SquaresInCircles.Eight.TableFree
