module

public import SquaresInCircles.Eight.TableFree.OuterEPrimaryComparison
public import SquaresInCircles.Eight.TableFree.CoreESignedExclusion

/-!
# Same-state selection of the actual outer-E secondary witnesses

Uncompiled source. Every selected nonpositive E primary is replaced by
the secondary proved at the same original point, angle, and common radius.
The two-secondary case is then excluded for the complete preprocessed T
union. The remaining alternatives contain only strictly positive retained
E primaries; no endpoint or missing exclusion is supplied as a premise.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.OuterESelection
open Candidate SignedCycle

def deOwner {C : SignedCycle} (w : C.Witnesses) : Fin 4 :=
  if delta C.theta D≤0 then 2 else w.owner D

def ehOwner {C : SignedCycle} (w : C.Witnesses) : Fin 4 :=
  if delta C.theta E≤0 then 0 else w.owner E

theorem de_allowed {C : SignedCycle} (w : C.Witnesses) : deOwner w=2 ∨ deOwner w=3 := by
  by_cases hd : delta C.theta D≤0
  · exact Or.inl (by simp [deOwner,hd])
  · simpa [deOwner,hd,normalOwners,D] using w.allowed D

theorem eh_allowed {C : SignedCycle} (w : C.Witnesses) : ehOwner w=0 ∨ ehOwner w=1 := by
  by_cases he : delta C.theta E≤0
  · exact Or.inl (by simp [ehOwner,he])
  · simpa [ehOwner,he,normalOwners,E] using w.allowed E

theorem de_feasible {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (hE : (I.cycle.point E).Outer q) : I.cycle.Feasible D (deOwner I.witnesses) := by
  by_cases hd : delta I.cycle.theta D≤0
  · rw [deOwner,if_pos hd]
    have ha : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
      simpa [normalOwners,D] using I.witnesses.allowed D
    rcases ha with ha | ha
    · simpa [ha] using I.witnesses.feasible D
    · exact OuterEPrimaryComparison.cycle_DE I.necessary I.anchors_normal hq hE hd
        (by simpa [ha] using I.witnesses.feasible D)
  · simpa [deOwner,hd] using I.witnesses.feasible D

theorem eh_feasible {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (hE : (I.cycle.point E).Outer q) : I.cycle.Feasible E (ehOwner I.witnesses) := by
  by_cases he : delta I.cycle.theta E≤0
  · rw [ehOwner,if_pos he]
    have ha : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [normalOwners,E] using I.witnesses.allowed E
    rcases ha with ha | ha
    · simpa [ha] using I.witnesses.feasible E
    · exact OuterEPrimaryComparison.cycle_EH I.necessary I.anchors_normal hq hE he
        (by simpa [ha] using I.witnesses.feasible E)
  · simpa [ehOwner,he] using I.witnesses.feasible E

def witnesses {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (hE : (I.cycle.point E).Outer q) : I.cycle.Witnesses where
  owner := Function.update (Function.update I.witnesses.owner D (deOwner I.witnesses))
    E (ehOwner I.witnesses)
  feasible i := by
    by_cases hiE : i=E
    · subst i; simpa using eh_feasible I hq hE
    · by_cases hiD : i=D
      · subst i; simpa [D,E] using de_feasible I hq hE
      · simpa [hiD,hiE] using I.witnesses.feasible i
  allowed i := by
    by_cases hiE : i=E
    · subst i; simpa [normalOwners,E] using eh_allowed I.witnesses
    · by_cases hiD : i=D
      · subst i; simpa [normalOwners,D,E] using de_allowed I.witnesses
      · simpa [hiD,hiE] using I.witnesses.allowed i

theorem other_owner {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (hE : (I.cycle.point E).Outer q) (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
    (witnesses I hq hE).owner i=I.witnesses.owner i := by
  simp [witnesses,hiD,hiE]

def boundary {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (hE : (I.cycle.point E).Outer q) : BoundaryInput q :=
  { I with
    witnesses := witnesses I hq hE
    zero_signs := by
      constructor
      · intro h
        apply I.zero_signs.HG_canceling
        simpa [witnesses,H,D,E] using h
      · intro h
        apply I.zero_signs.TD_canceling
        simpa [witnesses,T,D,E] using h }

theorem DE_positive {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (hE : (I.cycle.point E).Outer q)
    (hj : (boundary I hq hE).witnesses.owner D=3) : 0<delta I.cycle.theta D := by
  by_contra h
  have hd := le_of_not_gt h
  simp [boundary,witnesses,deOwner,hd,D,E] at hj

theorem EH_positive {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (hE : (I.cycle.point E).Outer q)
    (hj : (boundary I hq hE).witnesses.owner E=1) : 0<delta I.cycle.theta E := by
  by_contra h
  have he := le_of_not_gt h
  simp [boundary,witnesses,ehOwner,he,E] at hj

/-- The two-secondary exclusion removes that branch after actual
same-state selection, leaving precisely the three positive-primary cases. -/
theorem positive_GA_alternatives {q : ℝ} (I : BoundaryInput q) (hq : q≤qCap)
    (hE : (I.cycle.point E).Outer q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G)
    (hT : (I.witnesses.owner B=2 ∧ I.witnesses.owner T=0) ∨
      (I.witnesses.owner B=2 ∧ I.witnesses.owner T=2) ∨
      (I.witnesses.owner B=3 ∧ I.witnesses.owner T=0 ∧
        (delta I.cycle.theta B<0 → delta I.cycle.theta T=0))) :
    let J := boundary I hq hE
    (J.witnesses.owner D=2 ∧ J.witnesses.owner E=1 ∧ 0<delta I.cycle.theta E) ∨
    (J.witnesses.owner D=3 ∧ J.witnesses.owner E=0 ∧ 0<delta I.cycle.theta D) ∨
    (J.witnesses.owner D=3 ∧ J.witnesses.owner E=1 ∧
      0<delta I.cycle.theta D ∧ 0<delta I.cycle.theta E) := by
  let J := boundary I hq hE
  have hHG' : J.witnesses.owner H=2 := by simpa [J,boundary,witnesses,H,D,E] using hHG
  have hGA' : J.witnesses.owner G=1 := by simpa [J,boundary,witnesses,G,D,E] using hGA
  have ha : J.witnesses.owner A=0 ∨ J.witnesses.owner A=2 := by
    simpa [normalOwners,A] using J.witnesses.allowed A
  have hd : J.witnesses.owner D=2 ∨ J.witnesses.owner D=3 := by
    simpa [normalOwners,D] using J.witnesses.allowed D
  have he : J.witnesses.owner E=0 ∨ J.witnesses.owner E=1 := by
    simpa [normalOwners,E] using J.witnesses.allowed E
  have ht : (J.witnesses.owner B=2 ∧ J.witnesses.owner T=0) ∨
      (J.witnesses.owner B=2 ∧ J.witnesses.owner T=2) ∨
      (J.witnesses.owner B=3 ∧ J.witnesses.owner T=0 ∧
        (delta J.cycle.theta B<0 → delta J.cycle.theta T=0)) := by
    simpa [J,boundary,witnesses,B,T,D,E] using hT
  rcases hd with hd | hd <;> rcases he with he | he
  · exfalso
    have hf := CoreESignedExclusion.original_owners J hHG' hGA'
    have hf' : ∀ i,J.cycle.Feasible i
        (SecondaryEStress.owners (J.witnesses.owner A) (J.witnesses.owner B)
          (J.witnesses.owner T) i) := by
      simpa [hd,he,CoreEStress.owners,SecondaryEStress.owners] using hf
    exact NegativeSecondaryEExclusion.preprocessed_secondary_E_false hq J.necessary
      J.anchors_normal J.positive_variation.le ha hG (J.radial T) ht hf'
  · exact Or.inl ⟨hd,he,EH_positive I hq hE he⟩
  · exact Or.inr (Or.inl ⟨hd,he,DE_positive I hq hE hd⟩)
  · exact Or.inr (Or.inr ⟨hd,he,DE_positive I hq hE hd,EH_positive I hq hE he⟩)

end SquaresInCircles.Eight.TableFree.OuterESelection
