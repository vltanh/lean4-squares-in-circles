module

public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly
public import SquaresInCircles.Eight.Owners.E.DiagonalExclusion
public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain
public import SquaresInCircles.Eight.Owners.Positive.TDSpanScalars
public import SquaresInCircles.Eight.Words.Core.ESignedExclusion

/-!
# Eight squares: reducing a positive GA terminal to the two sole-E families

The reduction covers the three preprocessed rows of T (`TRegime`), both signs of every ordinary
error, both owners of AB, the four selected pairs of owners at E, and either sign of the tangent
and radial kind of E.

A core E and both secondary axes at E are excluded by the stress theorems at the points of the
cycle (`secondary_false`). Nonpositive primaries of an outer E are selected again on the same
points (`reselect_E`). A pair of positive primaries at E is transported at the same radius up to an
alignment of E, whose possible diagonal is excluded geometrically (`paired`). The six points other
than E, their frames, the selected owners of the edges away from E and both signed variation
budgets stay.

The conclusion is a sole-positive-E state (`Sole`, `Output`, `original`); the scalar exclusions of
its TD2 and BT3 families are proved separately.
-/

section
/-!
## A positive outer E reaches the EH contact at its frame

On the common circle of `q`, decreasing the nonnegative tangent of an outer E improves DE3 and
keeps EH0 (`replace`). Only the point of E changes: the seven frames, both variations and every
witness away from E stay (`Replacement.cycle`, `Replacement.boundaryInput`). The new point has
`E.y = 0` or lies at the EH0 contact, whose error may be nonzero (`Replacement`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveEContact
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
end SquaresInCircles.Eight.PositiveEContact
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveGAOuterSoleReduction
open Candidate SignedCycle PositiveEPair

/-- The rows of T after the preprocessing of the primary pair: BT2 with TD0 or TD2, or BT3 with
TD0, aligned at TD when the BT error is negative. -/
def TRegime {q : ℝ} (I : BoundaryInput q) : Prop :=
  (I.witnesses.owner B=2 ∧ I.witnesses.owner T=0) ∨
  (I.witnesses.owner B=2 ∧ I.witnesses.owner T=2) ∨
  (I.witnesses.owner B=3 ∧ I.witnesses.owner T=0 ∧
    (delta I.cycle.theta B<0 → delta I.cycle.theta T=0))

/-- A sole positive primary at E: DE2 and EH1 with positive E error, or DE3 and EH0 with positive D
error, as feasible axes of the cycle. A nonpositive primary is not kept once its secondary is
feasible on the same points. -/
def Sole (C : SignedCycle) : Prop :=
  (C.Feasible D 2 ∧ C.Feasible E 1 ∧ 0<delta C.theta E) ∨
  (C.Feasible D 3 ∧ C.Feasible E 0 ∧ 0<delta C.theta D)

structure Output {q : ℝ} (I : BoundaryInput q) where
  boundary : BoundaryInput q
  E_outer : (boundary.cycle.point E).Outer q
  HG : boundary.witnesses.owner H=2
  GA : boundary.witnesses.owner G=1
  G_positive : 0<delta boundary.cycle.theta G
  T_regime : TRegime boundary
  sole : Sole boundary.cycle
  unchanged : ∀ i,i≠E → boundary.cycle.point i=I.cycle.point i ∧
    boundary.cycle.theta i=I.cycle.theta i
  unchanged_errors : ∀ i,i≠D → i≠E →
    delta boundary.cycle.theta i=delta I.cycle.theta i
  unchanged_owners : ∀ i,i≠D → i≠E →
    boundary.witnesses.owner i=I.witnesses.owner i
  positive_variation : positiveVariation boundary.cycle.theta=
    positiveVariation I.cycle.theta
  negative_variation : negativeVariation boundary.cycle.theta=
    negativeVariation I.cycle.theta

theorem reselect_E {C : SignedCycle} {ab bt td de eh de' eh' : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i))
    (hDE : C.Feasible D de') (hEH : C.Feasible E eh') :
    ∀ i,C.Feasible i (CoreEStress.owners ab bt td de' eh' i) := by
  intro i
  fin_cases i
  · have h : C.Feasible 0 2 := hf 0
    exact h
  · have h : C.Feasible 1 1 := hf 1
    exact h
  · have h : C.Feasible 2 ab := hf 2
    exact h
  · have h : C.Feasible 3 bt := hf 3
    exact h
  · have h : C.Feasible 4 td := hf 4
    exact h
  · have h : C.Feasible 5 de' := hDE
    exact h
  · have h : C.Feasible 6 eh' := hEH
    exact h

theorem secondary_false {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G) (hT : TRegime I)
    (hDE : I.cycle.Feasible D 2) (hEH : I.cycle.Feasible E 0) : False := by
  have hab : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hf := reselect_E (CoreESignedExclusion.original_owners I hHG hGA) hDE hEH
  exact NegativeSecondaryEExclusion.preprocessed_secondary_E_false hq I.necessary
    I.anchors_normal I.positive_variation.le hab hG (I.radial T) hT
    (by simpa only [CoreEStress.owners,SecondaryEStress.owners] using hf)

def originalOutput {q : ℝ} (I : BoundaryInput q)
    (hE : (I.cycle.point E).Outer q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hT : TRegime I)
    (hsole : Sole I.cycle) : Output I where
  boundary := I
  E_outer := hE
  HG := hHG
  GA := hGA
  G_positive := hG
  T_regime := hT
  sole := hsole
  unchanged := fun _ _ => ⟨rfl,rfl⟩
  unchanged_errors := fun _ _ _ => rfl
  unchanged_owners := fun _ _ _ => rfl
  positive_variation := rfl
  negative_variation := rfl

theorem TRegime.endpoint {q : ℝ} {I : BoundaryInput q} (hT : TRegime I)
    (hq : q≤qCap)
    (F : Endpoint q (I.cycle.point D) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta D))
    (hD : 0≤delta I.cycle.theta D) (hE : 0≤delta I.cycle.theta E) :
    TRegime (F.boundaryInput I hq hD hE) := by
  change (F.witnesses I.witnesses).owner B=2 ∧
      (F.witnesses I.witnesses).owner T=0 ∨
    (F.witnesses I.witnesses).owner B=2 ∧
      (F.witnesses I.witnesses).owner T=2 ∨
    (F.witnesses I.witnesses).owner B=3 ∧
      (F.witnesses I.witnesses).owner T=0 ∧
      (delta F.cycle.theta B<0 → delta F.cycle.theta T=0)
  rw [F.other_owner I.witnesses B (by decide) (by decide),
    F.other_owner I.witnesses T (by decide) (by decide),
    F.other_delta B (by decide) (by decide),
    F.other_delta T (by decide) (by decide)]
  exact hT

def endpointOutput {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (F : Endpoint q (I.cycle.point D) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta D))
    (hD : 0≤delta I.cycle.theta D) (hE : 0≤delta I.cycle.theta E)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hT : TRegime I)
    (hsole : Sole F.cycle) : Output I where
  boundary := F.boundaryInput I hq hD hE
  E_outer := by
    change (F.cycle.point E).Outer q
    simpa only [Endpoint.cycle,replacePoint,Function.update_self] using F.outer
  HG := by
    change (F.witnesses I.witnesses).owner H=2
    rw [F.other_owner I.witnesses H (by decide) (by decide)]
    exact hHG
  GA := by
    change (F.witnesses I.witnesses).owner G=1
    rw [F.other_owner I.witnesses G (by decide) (by decide)]
    exact hGA
  G_positive := by
    change 0<delta F.cycle.theta G
    rw [F.other_delta G (by decide) (by decide)]
    exact hG
  T_regime := hT.endpoint hq F hD hE
  sole := hsole
  unchanged := F.unchanged
  unchanged_errors := F.other_delta
  unchanged_owners := F.other_owner I.witnesses
  positive_variation := F.positive_variation_eq hD hE
  negative_variation := F.negative_variation_eq hD hE

/-- A pair of positive primaries at E gives one of the two sole-primary states. -/
theorem paired {q : ℝ} (I : BoundaryInput q) (hQL : qLow≤q) (hQU : q≤qCap)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hT : TRegime I)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1)
    (hD : 0<delta I.cycle.theta D) (hE : 0<delta I.cycle.theta E) :
    Nonempty (Output I) := by
  have htotal : 0<I.cycle.theta H-I.cycle.theta D := by
    have heq : delta I.cycle.theta D+delta I.cycle.theta E=
        I.cycle.theta H-I.cycle.theta D := by
      simp only [delta,show next D=E by decide,show next E=H by decide]
      ring
    linarith
  obtain ⟨F⟩ := PositiveEPair.original_candidate I hQL hQU hDE hEH hD.le hE.le htotal
  rcases F.terminal with halignD | halignE | hdiag
  · have hDE' : F.cycle.Feasible D 2 := by
      simpa [Endpoint.deOwner,halignD] using F.DE_actual
    have hE' : 0<delta F.cycle.theta E := by
      rw [F.delta_EH,halignD,sub_zero]
      exact htotal
    exact ⟨endpointOutput I hQU F hD.le hE.le hHG hGA hG hT
      (Or.inl ⟨hDE',F.EH_primary,hE'⟩)⟩
  · have hEH' : F.cycle.Feasible E 0 := by
      simpa [Endpoint.ehOwner,halignE] using F.EH_actual
    have hD' : 0<delta F.cycle.theta D := by
      rw [F.delta_DE,halignE]
      exact htotal
    exact ⟨endpointOutput I hQU F hD.le hE.le hHG hGA hG hT
      (Or.inr ⟨F.DE_primary,hEH',hD'⟩)⟩
  · let J := F.boundaryInput I hQU hD.le hE.le
    have hq : q∈Icc (5/2:ℝ) qCap :=
      ⟨uniform_radius_order.1.le.trans hQL,hQU⟩
    have hj : |(J.cycle.point E).y|=(J.cycle.point E).a := by
      simpa [J,Endpoint.boundaryInput,Endpoint.cycle,replacePoint] using hdiag
    exact (J.E_not_diagonal hq hj).elim

/-- Every positive GA terminal reduces to a sole-positive-E state at the same radius, with the
coordinates of the points other than E; the output carries the geometric facts that the sole-E
scalar families need. -/
theorem original {q : ℝ} (I : BoundaryInput q) (hQL : qLow≤q) (hQU : q≤qCap)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hT : TRegime I) :
    Nonempty (Output I) := by
  rcases I.radial E with houter | hcore
  · have hde : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
      simpa [normalOwners,D] using I.witnesses.allowed D
    have heh : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [normalOwners,E] using I.witnesses.allowed E
    have hD : I.cycle.Feasible D 2 ∨
        (I.cycle.Feasible D 3 ∧ 0<delta I.cycle.theta D) := by
      rcases hde with hj | hj
      · exact Or.inl (by simpa [hj] using I.witnesses.feasible D)
      · have hf : I.cycle.Feasible D 3 := by simpa [hj] using I.witnesses.feasible D
        by_cases hz : delta I.cycle.theta D≤0
        · exact Or.inl (OuterEPrimaryComparison.cycle_DE I.necessary I.anchors_normal hQU houter hz hf)
        · exact Or.inr ⟨hf,lt_of_not_ge hz⟩
    have hE : I.cycle.Feasible E 0 ∨
        (I.cycle.Feasible E 1 ∧ 0<delta I.cycle.theta E) := by
      rcases heh with hj | hj
      · exact Or.inl (by simpa [hj] using I.witnesses.feasible E)
      · have hf : I.cycle.Feasible E 1 := by simpa [hj] using I.witnesses.feasible E
        by_cases hz : delta I.cycle.theta E≤0
        · exact Or.inl (OuterEPrimaryComparison.cycle_EH I.necessary I.anchors_normal hQU houter hz hf)
        · exact Or.inr ⟨hf,lt_of_not_ge hz⟩
    rcases hD with hD | ⟨hD,hd⟩ <;> rcases hE with hE | ⟨hE,he⟩
    · exact (secondary_false I hQU hHG hGA hG.le hT hD hE).elim
    · exact ⟨originalOutput I houter hHG hGA hG hT (Or.inl ⟨hD,hE,he⟩)⟩
    · exact ⟨originalOutput I houter hHG hGA hG hT (Or.inr ⟨hD,hE,hd⟩)⟩
    · exact paired I hQL hQU hHG hGA hG hT hD hE hd he
  · exact (CoreESignedExclusion.positive_GA_false I hQL hQU hcore hHG hGA hG.le hT).elim

end SquaresInCircles.Eight.PositiveGAOuterSoleReduction
end
end
end
