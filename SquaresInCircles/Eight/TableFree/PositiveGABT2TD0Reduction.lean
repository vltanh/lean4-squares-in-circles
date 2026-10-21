module

public import SquaresInCircles.Eight.TableFree.PositiveEContactExclusion
public import SquaresInCircles.Eight.TableFree.CoreEPositiveComplete
public import SquaresInCircles.Eight.TableFree.CoreESignedExclusion
public import SquaresInCircles.Eight.TableFree.PositiveSecondaryEExclusion
public import SquaresInCircles.Eight.TableFree.OuterEPrimaryComparison

/-!
# Positive GA with arbitrary original E owners reaches a genuine E tie

Uncompiled source. All core-E cases, nonpositive primary reselections,
secondary/sole E owners and aligned paired endpoints are discharged.
The only returned alternative is an actual same-radius boundary cycle
whose E point lies on the diagonal. The six other points and all five
nonincident errors and selected owners remain literal. Global quarter-
word recoding can therefore consume this output without a hypothetical
tie-exclusion premise or a change of the original common radius.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveGABT2TD0Reduction
open Candidate SignedCycle PositiveEPair

structure DiagonalOutput {q : ℝ} (I : BoundaryInput q) where
  boundary : BoundaryInput q
  diagonal : |(boundary.cycle.point E).y|=(boundary.cycle.point E).a
  unchanged_points : ∀ i,i≠E → boundary.cycle.point i=I.cycle.point i
  unchanged_errors : ∀ i,i≠D → i≠E → delta boundary.cycle.theta i=delta I.cycle.theta i
  unchanged_owners : ∀ i,i≠D → i≠E → boundary.witnesses.owner i=I.witnesses.owner i
  positive_variation : positiveVariation boundary.cycle.theta=positiveVariation I.cycle.theta
  negative_variation : negativeVariation boundary.cycle.theta=negativeVariation I.cycle.theta

def diagonal_output {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (F : Endpoint q (I.cycle.point D) (I.cycle.point H) (I.cycle.theta H-I.cycle.theta D))
    (hD : 0≤delta I.cycle.theta D) (hE : 0≤delta I.cycle.theta E)
    (hdiag : |F.point.y|=F.point.a) : DiagonalOutput I where
  boundary := F.boundaryInput I hq hD hE
  diagonal := by simpa [Endpoint.boundaryInput,Endpoint.cycle,replacePoint] using hdiag
  unchanged_points i hi := (F.unchanged i hi).1
  unchanged_errors := F.other_delta
  unchanged_owners := F.other_owner I.witnesses
  positive_variation := F.positive_variation_eq hD hE
  negative_variation := F.negative_variation_eq hD hE

theorem reselect_E {C : SignedCycle} {ab de eh de' eh' : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i))
    (hDE : C.Feasible D de') (hEH : C.Feasible E eh') :
    ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de' eh' i) := by
  intro i
  fin_cases i <;> first
    | simpa [CoreEStress.owners,H,G,A,B,T,D,E] using hf (0:Vertex)
    | simpa [CoreEStress.owners,H,G,A,B,T,D,E] using hf (1:Vertex)
    | simpa [CoreEStress.owners,H,G,A,B,T,D,E] using hf (2:Vertex)
    | simpa [CoreEStress.owners,H,G,A,B,T,D,E] using hf (3:Vertex)
    | simpa [CoreEStress.owners,H,G,A,B,T,D,E] using hf (4:Vertex)
    | simpa [CoreEStress.owners,H,G,A,B,T,D,E] using hDE
    | simpa [CoreEStress.owners,H,G,A,B,T,D,E] using hEH

theorem moved_E_owners {q : ℝ} {C : SignedCycle}
    (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) {ab de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 1 i))
    (hDE : F.cycle.Feasible D de) (hEH : F.cycle.Feasible E eh) :
    ∀ i,F.cycle.Feasible i (CoreEStress.owners ab 2 0 de eh i) := by
  intro i
  by_cases hiD : i=D
  · subst i; simpa [CoreEStress.owners,D] using hDE
  · by_cases hiE : i=E
    · subst i; simpa [CoreEStress.owners,E] using hEH
    · apply (F.other_feasible i hiD hiE _).2
      have hh := hf i
      fin_cases i <;> norm_num [D,E] at hiD hiE ⊢ <;> simpa [CoreEStress.owners] using hh

theorem positive_pair_diagonal {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {q : ℝ} (I : BoundaryInput q) {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hab : ab=0 ∨ ab=2)
    (hG : 0<delta I.cycle.theta G) (hD : 0<delta I.cycle.theta D)
    (hE : 0<delta I.cycle.theta E)
    (hf : ∀ i,I.cycle.Feasible i (CoreEStress.owners ab 2 0 3 1 i)) :
    Nonempty (DiagonalOutput I) := by
  have hcap : q≤qCap := (hq.trans hsharp.2).trans uniform_radius_order.2.2.1.le
  have hDE : I.cycle.Feasible D 3 := by simpa [CoreEStress.owners,D] using hf D
  have hEH : I.cycle.Feasible E 1 := by simpa [CoreEStress.owners,E] using hf E
  have htotal : 0<I.cycle.theta H-I.cycle.theta D := by
    have heq : delta I.cycle.theta D+delta I.cycle.theta E=I.cycle.theta H-I.cycle.theta D := by
      simp [delta,next,D,E,H]
      ring
    linarith
  obtain ⟨F⟩ := PositiveEPair.original_candidate I hQL hcap hDE hEH hD.le hE.le htotal
  have hnec := F.necessary I.necessary
  have hn := F.normal I.anchors_normal
  have hvar : positiveVariation F.cycle.theta≤frameCap := by
    rw [F.positive_variation_eq hD.le hE.le]
    exact I.positive_variation.le
  have hG' : 0<delta F.cycle.theta G := by rw [F.other_delta G (by decide) (by decide)]; exact hG
  have hD' : 0≤delta F.cycle.theta D := by rw [F.delta_DE]; exact F.de_mem.1
  have hE' : 0≤delta F.cycle.theta E := by rw [F.delta_EH]; linarith [F.de_mem.2]
  rcases F.terminal with halignedD | halignedE | hdiag
  · have hDE' : F.cycle.Feasible D 2 := by simpa [Endpoint.deOwner,halignedD] using F.DE_actual
    have hf' := moved_E_owners F hf hDE' F.EH_primary
    exact (SolePositiveExclusion.sole_EH_false hQL (hq.trans hsharp.2) hnec hn hvar
      hab hG'.le hE' hf').elim
  · have hEH' : F.cycle.Feasible E 0 := by simpa [Endpoint.ehOwner,halignedE] using F.EH_actual
    have hf' := moved_E_owners F hf F.DE_primary hEH'
    have houter : (F.cycle.point E).Outer q := by simpa [Endpoint.cycle,replacePoint] using F.outer
    exact (PositiveEContactExclusion.sole_DE_false hd hsharp hQL hq hnec hn hvar
      hab hG' hD' houter hf').elim
  · exact ⟨diagonal_output I hcap F hD.le hE.le hdiag⟩

/-- Every original E sign is admitted. In the sole-DE case the actual
same-radius contact theorem treats the positive-E alternative; the
sign-symmetric core theorem treats the other radial kind. -/
theorem original_boundary {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {q : ℝ} (I : BoundaryInput q)
    (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hBT : I.witnesses.owner B=2) (hTD : I.witnesses.owner T=0)
    (hG : 0<delta I.cycle.theta G) : Nonempty (DiagonalOutput I) := by
  have hcap : q≤qCap := (hq.trans hsharp.2).trans uniform_radius_order.2.2.1.le
  have hab : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hde : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
    simpa [normalOwners,D] using I.witnesses.allowed D
  have heh : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
    simpa [normalOwners,E] using I.witnesses.allowed E
  have hf := CoreESignedExclusion.original_owners I hHG hGA
  rw [hBT,hTD] at hf
  rcases I.radial E with houter | hcore
  · have hD : I.cycle.Feasible D 2 ∨
        (I.cycle.Feasible D 3 ∧ 0<delta I.cycle.theta D) := by
      rcases hde with he | he
      · exact Or.inl (by simpa [he] using I.witnesses.feasible D)
      · have hh : I.cycle.Feasible D 3 := by simpa [he] using I.witnesses.feasible D
        by_cases hz : delta I.cycle.theta D≤0
        · exact Or.inl (OuterEPrimaryComparison.cycle_DE I.necessary I.anchors_normal hcap houter hz hh)
        · exact Or.inr ⟨hh,lt_of_not_ge hz⟩
    have hE : I.cycle.Feasible E 0 ∨
        (I.cycle.Feasible E 1 ∧ 0<delta I.cycle.theta E) := by
      rcases heh with he | he
      · exact Or.inl (by simpa [he] using I.witnesses.feasible E)
      · have hh : I.cycle.Feasible E 1 := by simpa [he] using I.witnesses.feasible E
        by_cases hz : delta I.cycle.theta E≤0
        · exact Or.inl (OuterEPrimaryComparison.cycle_EH I.necessary I.anchors_normal hcap houter hz hh)
        · exact Or.inr ⟨hh,lt_of_not_ge hz⟩
    rcases hD with hD | ⟨hD,hd'⟩ <;> rcases hE with hE | ⟨hE,he'⟩
    · have hf' := reselect_E hf hD hE
      have hh := PositiveSecondaryEExclusion.secondary_T_false hcap I.necessary I.anchors_normal
        I.positive_variation.le hab hG.le
        (by simpa [SecondaryEStress.owners,CoreEStress.owners] using hf')
      exact hh.elim
    · exact (SolePositiveExclusion.sole_EH_false hQL (hq.trans hsharp.2) I.necessary
        I.anchors_normal I.positive_variation.le hab hG.le he'.le (reselect_E hf hD hE)).elim
    · exact (PositiveEContactExclusion.sole_DE_false hd hsharp hQL hq I.necessary
        I.anchors_normal I.positive_variation.le hab hG hd'.le houter
        (reselect_E hf hD hE)).elim
    · exact positive_pair_diagonal hd hsharp I hQL hq hab hG hd' he'
        (reselect_E hf hD hE)
  · exact (CoreESignedExclusion.positive_GA_false I hQL hcap hcore hHG hGA hG.le
      (Or.inl ⟨hBT,hTD⟩)).elim

/-- The normalized source is a direct specialization of the sign-free
original-boundary theorem; no E normalization is performed in its proof. -/
theorem original {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {q : ℝ} (I : NormalizedBoundaryInput q)
    (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hBT : I.witnesses.owner B=2) (hTD : I.witnesses.owner T=0)
    (hG : 0<delta I.cycle.theta G) : Nonempty (DiagonalOutput I.toBoundaryInput) :=
  original_boundary hd hsharp I.toBoundaryInput hQL hq hHG hGA hBT hTD hG

end SquaresInCircles.Eight.TableFree.PositiveGABT2TD0Reduction
