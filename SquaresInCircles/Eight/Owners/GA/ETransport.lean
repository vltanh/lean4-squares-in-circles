module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SmallHigh
public import SquaresInCircles.Eight.Owners.GA.EZero
public import SquaresInCircles.Eight.Owners.GA.Transport.T

/-!
# Eight squares: the high-GA source domain after a move of a flat-core E

A `Move` puts E at a point of the flat part `a = 7/12` of the core curve, with a frame angle
between two frame angles of the cycle and new witnesses on DE and EH. Both changing edges are
quarter edges: their sorted local angles and their witnesses put their gaps on the positive
winding branch by the central-band theorem `TTransport.positive_gap`, and the other five gaps are
the original gaps (`Move.ordered`). `Move.source` is then a high-GA source domain at the same
`q`, with the data and owners of G, A, B and T unchanged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.ETransport
open Candidate SignedCycle

structure Move (q : ℝ) (C : SignedCycle) where
  point : SignedPoint
  theta : ℝ
  sorted : point.Sorted
  contained : point.Contained q
  core : point.Core
  flat : point.a=7/12
  nonpos : point.y≤0
  frame_range : ∃a b : Vertex,
    theta∈Icc (min (C.theta a) (C.theta b)) (max (C.theta a) (C.theta b))
  de : Fin 4
  eh : Fin 4
  de_allowed : de=2 ∨ de=3
  eh_allowed : eh=0 ∨ eh=1
  DE : quarterFeasible (C.point D) point (theta-C.theta D) de
  EH : quarterFeasible point (C.point H) (C.theta H-theta) eh
  positive_nonincrease : positiveVariation (Function.update C.theta E theta)≤
    positiveVariation C.theta

namespace Move
variable {q : ℝ} {C : SignedCycle}

def cycle (O : Move q C) : SignedCycle := replacePoint C E O.point O.theta

theorem unchanged (O : Move q C) (i : Vertex) (hi : i≠E) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i := by
  simp [cycle,replacePoint,hi]

theorem other_delta (O : Move q C) (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
    delta O.cycle.theta i=delta C.theta i := by
  have hn : next i≠E := by revert hiD; fin_cases i <;> decide
  simp [delta,(O.unchanged i hiE).2,(O.unchanged (next i) hn).2]

theorem other_feasible (O : Move q C) (i : Vertex) (hiD : i≠D) (hiE : i≠E)
    (j : Fin 4) : O.cycle.Feasible i j ↔ C.Feasible i j := by
  have hn : next i≠E := by revert hiD; fin_cases i <;> decide
  exact SignedCycle.replacePoint_other_feasible hiE hn

theorem DE_actual (O : Move q C) : O.cycle.Feasible D O.de := by
  simpa [cycle,replacePoint,Feasible,slack,edge,word,delta,next,D,E,
    quarterFeasible,sub_nonneg] using O.DE

theorem EH_actual (O : Move q C) : O.cycle.Feasible E O.eh := by
  simpa [cycle,replacePoint,Feasible,slack,edge,word,delta,next,H,E,
    quarterFeasible,sub_nonneg] using O.EH

theorem necessary (O : Move q C) (hn : C.Necessary q) : O.cycle.Necessary q := by
  obtain ⟨a,b,hr⟩ := O.frame_range
  exact necessary_replace_clamped (v:=E) (a:=a) (b:=b)
    hn O.sorted O.contained O.core.ge (Or.inr hr)

theorem strict_spread (O : Move q C) (hs : C.StrictSpread) : O.cycle.StrictSpread := by
  obtain ⟨a,b,hr⟩ := O.frame_range
  exact strictSpread_replace_clamped (v:=E) (a:=a) (b:=b)
    (p:=O.point) hs (Or.inr hr)

theorem negative_nonincrease (O : Move q C) :
    negativeVariation O.cycle.theta≤negativeVariation C.theta := by
  rw [←variations_equal O.cycle.theta,←variations_equal C.theta]
  exact O.positive_nonincrease

def owner (O : Move q C) (w : Vertex → Fin 4) : Vertex → Fin 4 :=
  Function.update (Function.update w D O.de) E O.eh

theorem other_owner (O : Move q C) (w : Vertex → Fin 4) (i : Vertex)
    (hiD : i≠D) (hiE : i≠E) : O.owner w i=w i := by simp [owner,hiD,hiE]

theorem feasible (O : Move q C) (w : Vertex → Fin 4)
    (hf : ∀i,C.Feasible i (w i)) : ∀i,O.cycle.Feasible i (O.owner w i) := by
  intro i
  by_cases hiE : i=E
  · subst i; simpa [owner] using O.EH_actual
  by_cases hiD : i=D
  · subst i; simpa [owner,D,E] using O.DE_actual
  · rw [O.other_owner w i hiD hiE]
    exact (O.other_feasible i hiD hiE _).2 (hf i)

theorem allowed (O : Move q C) (w : Vertex → Fin 4)
    (hw : ∀i,w i∈highGAOwners i) : ∀i,O.owner w i∈highGAOwners i := by
  intro i
  by_cases hiE : i=E
  · subst i
    simpa [owner,highGAOwners,E] using O.eh_allowed
  by_cases hiD : i=D
  · subst i
    simpa [owner,highGAOwners,D,E] using O.de_allowed
  · rw [O.other_owner w i hiD hiE]
    exact hw i

/-- The geometry of the two quarter edges gives the winding after the move. No sign of A and no
low GA owner is used. -/
theorem ordered (O : Move q C) (hn : C.Necessary q) (ho : C.Ordered)
    (hq : q≤qCap) (w : Vertex → Fin 4) (hf : ∀i,C.Feasible i (w i)) :
    O.cycle.Ordered := by
  have hn' := O.necessary hn
  have hf' := O.feasible w hf
  have hang := localAngle_mem hn'.sorted
  have hdelta (i : Vertex) : -(7/10:ℝ)≤delta O.cycle.theta i :=
    (abs_le.mp (hn'.spread (next i) i)).1
  have hlo (i : Vertex) : -(19/25:ℝ)<O.cycle.physicalGap i := by
    by_cases hi : i=D ∨ i=E
    · have hw : word i=1 := by rcases hi with rfl | rfl <;> decide
      have he : O.cycle.physicalGap i=Real.pi/2+delta O.cycle.theta i+
          O.cycle.localAngle i-O.cycle.localAngle (next i) := by
        simp [physicalGap,hw]
      rw [he]
      linarith [(hang i).1,(hang (next i)).2,hdelta i]
    · have hiD : i≠D := fun hh => hi (Or.inl hh)
      have hiE : i≠E := fun hh => hi (Or.inr hh)
      have he : O.cycle.physicalGap i=C.physicalGap i := by
        fin_cases i <;>
          simp [cycle,replacePoint,physicalGap,localAngle,word,delta,next,D,E]
            at hiD hiE ⊢
      rw [he]
      linarith [ho.gap_pos i]
  have hgap (i : Vertex) : 19/25<O.cycle.physicalGap i :=
    TTransport.positive_gap hn' hq i (O.owner w i) (hf' i) (hlo i)
  have hupper := seven_gaps_three_quarters O.cycle.polarAngle (fun i => by
    rw [polarAngle_gap]
    exact hgap i)
  constructor
  · intro i; linarith [hgap i]
  · intro i
    have hh := hupper i
    rw [polarAngle_gap] at hh
    linarith [Real.pi_pos]

def source (O : Move q C) (I : SourceDomain q C) (hq : q≤qCap) :
    SourceDomain q O.cycle where
  owner := O.owner I.owner
  feasible := O.feasible I.owner I.feasible
  allowed := O.allowed I.owner I.allowed
  necessary := O.necessary I.necessary
  ordered := O.ordered I.necessary I.ordered hq I.owner I.feasible
  strict_spread := O.strict_spread I.strict_spread
  positive_variation := lt_of_le_of_lt O.positive_nonincrease I.positive_variation
  negative_variation := lt_of_le_of_lt O.negative_nonincrease I.negative_variation
  radial i := by
    by_cases hi : i=E
    · subst i; exact Or.inr O.core
    · rw [(O.unchanged i hi).1]; exact I.radial i
  outer i hi := by
    have hiE : i≠E := by rintro rfl; exact absurd hi (by decide)
    rw [(O.unchanged i hiE).1]
    exact I.outer i hi
  H_positive := by rw [(O.unchanged H (by decide)).1]; exact I.H_positive
  G_negative := by rw [(O.unchanged G (by decide)).1]; exact I.G_negative
  B_negative := by rw [(O.unchanged B (by decide)).1]; exact I.B_negative
  D_negative := by rw [(O.unchanged D (by decide)).1]; exact I.D_negative
  E_nonpos := O.nonpos
  A_upper := by rw [(O.unchanged A (by decide)).1]; exact I.A_upper
  A_nonpos_outer := by
    rw [(O.unchanged A (by decide)).1]
    exact I.A_nonpos_outer
  internal_sorted i hi := by
    by_cases hiE : i=E
    · subst i
      have hy := CoreENegativeTotal.flat_tangent O.core O.flat O.nonpos
      change |O.point.y|<O.point.a
      rw [abs_of_nonpos O.nonpos,O.flat]
      linarith [hy.1]
    · rw [(O.unchanged i hiE).1]
      exact I.internal_sorted i hi

end Move

def ofMixed {q : ℝ} {C : SignedCycle} (O : NegativeCoreE.CycleMove q C)
    (hf : O.point.a=7/12) : Move q C where
  point := O.point
  theta := O.theta
  sorted := O.sorted
  contained := O.contained
  core := O.core
  flat := hf
  nonpos := O.nonpos
  frame_range := ⟨E,D,O.frame_range⟩
  de := O.de
  eh := O.eh
  de_allowed := O.de_allowed
  eh_allowed := O.eh_allowed
  DE := O.DE
  EH := O.EH
  positive_nonincrease := O.positive_nonincrease

/-- The move that keeps E at its state and reselects feasible DE and EH witnesses at the same
radius. -/
def identity {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hc : (C.point E).Core) (hf : (C.point E).a=7/12)
    (de eh : Fin 4) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hDE : C.Feasible D de) (hEH : C.Feasible E eh) : Move q C where
  point := C.point E
  theta := C.theta E
  sorted := I.necessary.sorted E
  contained := I.necessary.contained E
  core := hc
  flat := hf
  nonpos := I.E_nonpos
  frame_range := ⟨E,E,by simp⟩
  de := de
  eh := eh
  de_allowed := hde
  eh_allowed := heh
  DE := by
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg] using hDE
  EH := by
    simpa [Feasible,slack,edge,word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  positive_nonincrease := by simp

end SquaresInCircles.Eight.GlobalGA.ETransport
