module

public import SquaresInCircles.Eight.TableFree.CoreESignedExclusion
public import SquaresInCircles.Eight.TableFree.NegativeSecondaryEExclusion
public import SquaresInCircles.Eight.TableFree.OuterEPrimaryComparison
public import SquaresInCircles.Eight.TableFree.PositiveECycle
public import SquaresInCircles.Eight.TableFree.EDiagonalExclusion

/-!
# Complete positive-GA reduction to the two actual sole-E families

Uncompiled source draft. The theorem covers all three preprocessed T-owner
rows, both signs of every ordinary error, both AB owners, all four selected
E-owner pairs, and either E tangent sign and radial kind.

Core E and both secondary E axes are excluded by the existing original-point
stress theorems. Nonpositive outer-E primaries are reselected on the same
points. A pair of positive E primaries is transported at the original radius
until an actual E alignment; its possible diagonal is excluded geometrically.
The six non-E points, their frames, their nonincident selected owners and
both signed variation budgets remain unchanged.

The conclusion is an actual sole-positive-E state. Its TD2/BT3 scalar
exclusions remain separate obligations; no such exclusion is assumed here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveGAOuterSoleReduction
open Candidate SignedCycle PositiveEPair

/-- The exhaustive T rows after primary-pair preprocessing. In the negative
BT row, TD alignment is a property of the actual endpoint. -/
def TRegime {q : ℝ} (I : BoundaryInput q) : Prop :=
  (I.witnesses.owner B=2 ∧ I.witnesses.owner T=0) ∨
  (I.witnesses.owner B=2 ∧ I.witnesses.owner T=2) ∨
  (I.witnesses.owner B=3 ∧ I.witnesses.owner T=0 ∧
    (delta I.cycle.theta B<0 → delta I.cycle.theta T=0))

/-- These are actual feasible axes on the output cycle; an originally
selected nonpositive primary need not be retained when its secondary has
just been proved feasible on those same points. -/
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

/-- A genuine paired-E input yields one of the two actual sole-primary
states, never an assumed endpoint or a diagonal exception. -/
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

/-- Full original-boundary reduction of every positive GA terminal. The
output carries every geometric fact needed by the remaining sole-E scalar
families at this same radius and with the original non-E coordinates. -/
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

end SquaresInCircles.Eight.TableFree.PositiveGAOuterSoleReduction
