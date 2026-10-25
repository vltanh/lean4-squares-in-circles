module

public import SquaresInCircles.Eight.TableFree.PositiveECycle

/-!
# Positive outer E reaches actual EH contact at its original frame

Uncompiled source. The original common q-circle is used throughout.
Decreasing the nonnegative E tangent improves DE3 and preserves EH0.
Only E's point is changed; all seven frames, both variations, and every
nonincident weak witness are retained. The output is either E.y=0 or
the actual EH0 contact, with its original possibly nonzero error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveEContact
open Candidate PairedPrimary

def demand (H : SignedPoint) (rho : ℝ) : ℝ :=
  edgeWidth rho-H.a*Real.cos rho-H.y*Real.sin rho

structure Replacement (q : ℝ) (C : SignedCycle) where
  point : SignedPoint
  sorted : point.Sorted
  outer : point.Outer q
  core : point.AvoidsCore
  nonnegative : 0≤point.y
  tangent_le : point.y≤(C.point E).y
  DE : quarterFeasible (C.point D) point (delta C.theta D) 3
  EH : quarterFeasible point (C.point H) (delta C.theta E) 0
  terminal : point.y=0 ∨ point.y=demand (C.point H) (delta C.theta E)

theorem replace {q : ℝ} {C : SignedCycle} (hQL : qLow≤q)
    (hC : C.Necessary q) (hE : (C.point E).Outer q) (hy : 0≤(C.point E).y)
    (hd : 0≤delta C.theta D) (hDE : C.Feasible D 3) (hEH : C.Feasible E 0) :
    Nonempty (Replacement q C) := by
  let y := max 0 (demand (C.point H) (delta C.theta E))
  have hDE' : edgeWidth (delta C.theta D)≤(C.point D).a+
      (C.point E).a*Real.sin (delta C.theta D)-(C.point E).y*Real.cos (delta C.theta D) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,quarterProjection,
      D,E,next,sub_nonneg] using hDE
  have hEH' : demand (C.point H) (delta C.theta E)≤(C.point E).y := by
    have hwE : word E≠0 := by decide
    have hnE : next E=H := rfl
    have hh := hEH
    simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,hwE,↓reduceIte,hnE,
      quarterProjection,Matrix.cons_val] at hh
    dsimp [demand]
    linarith
  have hy0 : 0≤y := le_max_left _ _
  have hyle : y≤(C.point E).y := max_le hy hEH'
  have hdiag := SignedPoint.contained_minor_le_diagonal (hC.sorted E) (hC.contained E)
  have hyarc : |y|≤diagonalCoordinate q := by
    rw [abs_of_nonneg hy0]
    exact hyle.trans (by simpa [abs_of_nonneg hy] using hdiag)
  obtain ⟨hps,hpo,hpc⟩ := SignedPoint.outerAt_spec hQL hyarc
  have hdI : delta C.theta D∈Icc 0 (7/10:ℝ) :=
    ⟨hd,(le_abs_self _).trans (hC.spread (next D) D)⟩
  have hcircle := eq_outerAt_of_outer (hC.sorted E) hE
  have hold : 0≤contact q (C.point D).a (delta C.theta D) (C.point E).y := by
    have ha : (C.point E).a=(arc q (C.point E).y).a := congrArg SignedPoint.a hcircle
    dsimp [contact]
    rw [← ha]
    linarith
  have hnew := (contact_strictAnti (B := (C.point D).a) hQL hdI).antitoneOn
    (abs_le.mp hyarc) (abs_le.mp hdiag) hyle
  refine ⟨{
    point := arc q y
    sorted := hps
    outer := hpo
    core := hpc
    nonnegative := hy0
    tangent_le := hyle
    DE := ?_
    EH := ?_
    terminal := ?_ }⟩
  · dsimp [contact,arc,SignedPoint.outerAt] at hold hnew
    simp only [quarterFeasible,quarterProjection,arc,SignedPoint.outerAt,Matrix.cons_val]
    linarith
  · have hh : demand (C.point H) (delta C.theta E)≤y := le_max_right _ _
    dsimp [demand] at hh
    simp only [quarterFeasible,quarterProjection,arc,SignedPoint.outerAt,Matrix.cons_val]
    linarith
  · by_cases hh : demand (C.point H) (delta C.theta E)≤0
    · left
      exact max_eq_left hh
    · right
      exact max_eq_right (lt_of_not_ge hh).le

namespace Replacement
variable {q : ℝ} {C : SignedCycle}

def cycle (O : Replacement q C) : SignedCycle := replacePoint C E O.point (C.theta E)

@[simp] theorem theta_eq (O : Replacement q C) : O.cycle.theta=C.theta := by
  simp [cycle,replacePoint]

theorem unchanged (O : Replacement q C) (i : Vertex) (hi : i≠E) :
    O.cycle.point i=C.point i := by simp [cycle,replacePoint,hi]

theorem DE_actual (O : Replacement q C) : O.cycle.Feasible D 3 := by
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
    word,delta,next,D,E,quarterFeasible,sub_nonneg] using O.DE

theorem EH_actual (O : Replacement q C) : O.cycle.Feasible E 0 := by
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
    word,delta,next,H,E,quarterFeasible,sub_nonneg] using O.EH

theorem other_feasible (O : Replacement q C) (i : Vertex) (hiD : i≠D) (hiE : i≠E)
    (j : Fin 4) : O.cycle.Feasible i j ↔ C.Feasible i j := by
  have hn : next i≠E := by revert hiD; fin_cases i <;> decide
  exact SignedCycle.replacePoint_other_feasible hiE hn


theorem necessary (O : Replacement q C) (hC : C.Necessary q) : O.cycle.Necessary q :=
  SignedCycle.necessary_replace_clamped (a := E) (b := E)
    hC O.sorted O.outer.le O.core (Or.inl rfl)

theorem normal (O : Replacement q C) (hn : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · rw [O.unchanged H (by decide)]; exact hn.H_nonneg
  · rw [O.unchanged A (by decide)]; exact hn.A_nonneg
  · rw [O.unchanged B (by decide)]; exact hn.B_nonpos
  · rw [O.unchanged D (by decide)]; exact hn.D_nonpos

def witnesses (O : Replacement q C) (w : C.Witnesses) : O.cycle.Witnesses where
  owner := Function.update (Function.update w.owner D 3) E 0
  feasible i := by
    by_cases hiE : i=E
    · subst i; simpa using O.EH_actual
    · by_cases hiD : i=D
      · subst i; simpa [D,E] using O.DE_actual
      · simpa [hiD,hiE] using (O.other_feasible i hiD hiE (w.owner i)).2 (w.feasible i)
  allowed i := by
    by_cases hiE : i=E
    · subst i; simp [SignedCycle.normalOwners,E]
    · by_cases hiD : i=D
      · subst i; simp [SignedCycle.normalOwners,D,E]
      · simpa [hiD,hiE] using w.allowed i

theorem zero_signs (O : Replacement q C) (w : C.Witnesses) (hz : C.ZeroSignImplications w) :
    O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hh
    rw [O.unchanged G (by decide)]
    exact hz.HG_canceling (by simpa [witnesses,H,D,E] using hh)
  · intro hh
    rw [O.unchanged T (by decide)]
    exact hz.TD_canceling (by simpa [witnesses,T,D,E] using hh)

def boundaryInput (I : SignedCycle.BoundaryInput q) (hq : q≤qCap)
    (O : Replacement q I.cycle) : SignedCycle.BoundaryInput q where
  cycle := O.cycle
  necessary := O.necessary I.necessary
  ordered := SignedCycle.normal_necessary_ordered (O.necessary I.necessary) hq
    (O.normal I.anchors_normal) (O.witnesses I.witnesses) (O.zero_signs I.witnesses I.zero_signs)
  strict_spread := by simpa only [SignedCycle.StrictSpread,O.theta_eq] using I.strict_spread
  positive_variation := by simpa only [O.theta_eq] using I.positive_variation
  negative_variation := by simpa only [O.theta_eq] using I.negative_variation
  radial := by
    intro i
    by_cases hi : i=E
    · subst i; exact Or.inl O.outer
    · rw [O.unchanged i hi]; exact I.radial i
  anchors_outer := by
    intro i hi
    have hiE : i≠E := by rintro rfl; exact absurd hi (by decide)
    rw [O.unchanged i hiE]
    exact I.anchors_outer i hi
  anchors_normal := O.normal I.anchors_normal
  witnesses := O.witnesses I.witnesses
  zero_signs := O.zero_signs I.witnesses I.zero_signs

end Replacement
end SquaresInCircles.Eight.TableFree.PositiveEContact
