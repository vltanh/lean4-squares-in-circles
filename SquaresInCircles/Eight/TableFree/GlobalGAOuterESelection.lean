module

public import SquaresInCircles.Eight.TableFree.GlobalGASourceDomain
public import SquaresInCircles.Eight.TableFree.OuterEPrimaryComparison
public import SquaresInCircles.Eight.TableFree.GlobalGAPairedECharge

/-!
# Same-state outer-E owner selection in the high-GA domain

Uncompiled source join of `HAND_G3_OUTER_E_NEGATIVE_PRIMARY_WITNESS_COMPARISON.md`.
The pointwise original-radius comparison needs only the adjacent H/D signs;
it places no sign restriction on A. Every nonpositive outer-E primary is
reselected to its actual secondary at the same point and frame.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.OuterE
open Candidate SignedCycle

theorem DE_secondary {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q≤qCap) (hE : (C.point E).Outer q) (hd : delta C.theta D≤0)
    (hf : C.Feasible D 3) : C.Feasible D 2 := by
  have hlocal : quarterFeasible (C.point D) (C.point E) (delta C.theta D) 3 := by
    simpa [Feasible,slack,edge,word,next,D,E,quarterFeasible,sub_nonneg] using hf
  have hh := OuterEPrimaryComparison.DE_nonpositive
    (I.necessary.sorted E) hE (I.necessary.sorted D) (I.necessary.contained D)
    hq I.D_negative.le hd (I.necessary.spread (next D) D) hlocal
  simpa [Feasible,slack,edge,word,next,D,E,quarterFeasible,sub_nonneg] using hh

theorem EH_secondary {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q≤qCap) (hE : (C.point E).Outer q) (he : delta C.theta E≤0)
    (hf : C.Feasible E 1) : C.Feasible E 0 := by
  have hlocal : quarterFeasible (C.point E) (C.point H) (delta C.theta E) 1 := by
    simpa [Feasible,slack,edge,word,next,E,H,quarterFeasible,sub_nonneg] using hf
  have hh := OuterEPrimaryComparison.EH_nonpositive
    (I.necessary.sorted E) hE (I.necessary.sorted H) (I.necessary.contained H)
    hq I.H_positive.le he (I.necessary.spread (next E) E) hlocal
  simpa [Feasible,slack,edge,word,next,E,H,quarterFeasible,sub_nonneg] using hh

structure Selection {q : ℝ} {C : SignedCycle} (I : SourceDomain q C) where
  de : Bool
  eh : Bool
  DE : C.Feasible D (if de then 3 else 2)
  EH : C.Feasible E (if eh then 1 else 0)
  DE_positive : de=true→0<delta C.theta D
  EH_positive : eh=true→0<delta C.theta E

def select {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q≤qCap) (hE : (C.point E).Outer q) : Selection I := by
  have hd : I.owner D=2∨I.owner D=3 := by simpa [highGAOwners,D] using I.allowed D
  have he : I.owner E=0∨I.owner E=1 := by simpa [highGAOwners,E] using I.allowed E
  obtain ⟨de,hDE,hdep⟩ : ∃de : Bool,C.Feasible D (if de then 3 else 2) ∧
      (de=true→0<delta C.theta D) := by
    rcases hd with hd|hd
    · exact ⟨false,by simpa [hd] using I.feasible D,by intro h; cases h⟩
    · have hf : C.Feasible D 3 := by simpa [hd] using I.feasible D
      by_cases hnonpos : delta C.theta D≤0
      · exact ⟨false,DE_secondary I hq hE hnonpos hf,by intro h; cases h⟩
      · exact ⟨true,hf,fun _ => lt_of_not_ge hnonpos⟩
  obtain ⟨eh,hEH,hehp⟩ : ∃eh : Bool,C.Feasible E (if eh then 1 else 0) ∧
      (eh=true→0<delta C.theta E) := by
    rcases he with he|he
    · exact ⟨false,by simpa [he] using I.feasible E,by intro h; cases h⟩
    · have hf : C.Feasible E 1 := by simpa [he] using I.feasible E
      by_cases hnonpos : delta C.theta E≤0
      · exact ⟨false,EH_secondary I hq hE hnonpos hf,by intro h; cases h⟩
      · exact ⟨true,hf,fun _ => lt_of_not_ge hnonpos⟩
  exact ⟨de,eh,hDE,hEH,hdep,hehp⟩

namespace Selection
variable {q : ℝ} {C : SignedCycle} {I : SourceDomain q C}

theorem total_nonneg (S : Selection I) : 0≤PairedE.cycleTotal C S.de S.eh := by
  have hD : 0≤PairedE.selected S.de (delta C.theta D) := by
    cases hd : S.de
    · simp [PairedE.selected]
    · simpa [PairedE.selected] using (S.DE_positive hd).le
  have hE : 0≤PairedE.selected S.eh (delta C.theta E) := by
    cases he : S.eh
    · simp [PairedE.selected]
    · simpa [PairedE.selected] using (S.EH_positive he).le
  exact add_nonneg hD hE

def owner (S : Selection I) : Vertex→Fin 4 :=
  Function.update (Function.update I.owner D (if S.de then 3 else 2))
    E (if S.eh then 1 else 0)

theorem other_owner (S : Selection I) (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
    S.owner i=I.owner i := by simp [owner,hiD,hiE]

def source (S : Selection I) : SourceDomain q C :=
  { I with
    owner := S.owner
    feasible := by
      intro i
      by_cases hiE : i=E
      · subst i; simpa [owner] using S.EH
      by_cases hiD : i=D
      · subst i; simpa [owner,D,E] using S.DE
      simpa [S.other_owner i hiD hiE] using I.feasible i
    allowed := by
      intro i
      by_cases hiE : i=E
      · subst i; cases S.eh <;> simp [owner,highGAOwners,E]
      by_cases hiD : i=D
      · subst i; cases S.de <;> simp [owner,highGAOwners,D,E]
      simpa [S.other_owner i hiD hiE] using I.allowed i }

end Selection
end SquaresInCircles.Eight.TableFree.GlobalGA.OuterE
