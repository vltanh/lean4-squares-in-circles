module

public import SquaresInCircles.Eight.Owners.GA.Paired.ECharge
public import SquaresInCircles.Eight.Owners.GA.Paired.NegativeECycle
public import SquaresInCircles.Eight.Owners.GA.EZero
public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain

/-!
# Eight squares: same-state outer-E owner selection in the high-GA domain

The pointwise original-radius comparison needs only the adjacent H/D signs;
it places no sign restriction on A. Every nonpositive outer-E primary is
reselected to its actual secondary at the same point and frame.
-/

section
/-!
## The owner and signed-total normal form of a core E

For a source domain with E on the core curve, `reduce` moves E alone, at the same `q`, to a
`Result` that is `Reduced`: every selection DE2/3, EH0/1 ends with a nonnegative selected E total
`eTotal`, or with E on the flat part `a = 7/12` of the core curve and exactly one negative E
primary, DE3 with EH0 or EH1 with DE2, the secondary on the other edge. Mixed signs use the compact
core-arc or the flat-gap move of `CoreENegativeTotal.reduce_negative_total`. In
`reduce_nonpositive` a zero primary error is a tie that makes the secondary of its edge feasible,
and two negative errors use the intrinsic concavity endpoint of `PairedNegativeE.reduce` and the
E-zero obstruction. Every point and frame angle other than those of E is unchanged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.CoreENormalForm
open Candidate SignedCycle ActualCoreEBlocks ETransport

def Reduced (C : SignedCycle) (de eh : Fin 4) : Prop :=
  0≤eTotal C de eh ∨
    ((C.point E).a=7/12 ∧
      ((de=3 ∧ eh=0 ∧ delta C.theta D<0) ∨
       (de=2 ∧ eh=1 ∧ delta C.theta E<0)))

structure Result {q : ℝ} {C : SignedCycle} (I : SourceDomain q C) where
  cycle : SignedCycle
  source : SourceDomain q cycle
  E_core : (cycle.point E).Core
  point_other : ∀i,i≠E → cycle.point i=C.point i
  theta_other : ∀i,i≠E → cycle.theta i=C.theta i
  owner_other : ∀i,i≠D → i≠E → source.owner i=I.owner i
  positive_nonincrease : positiveVariation cycle.theta≤positiveVariation C.theta
  reduced : Reduced cycle (source.owner D) (source.owner E)

namespace Result
variable {q : ℝ} {C : SignedCycle} {I : SourceDomain q C}

theorem other_delta (R : Result I) (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
    delta R.cycle.theta i=delta C.theta i := by
  have hn : next i≠E := by revert hiD; fin_cases i <;> decide
  simp [delta,R.theta_other i hiE,R.theta_other (next i) hn]

theorem other_feasible (R : Result I) (i : Vertex) (hiD : i≠D) (hiE : i≠E)
    (j : Fin 4) : R.cycle.Feasible i j ↔ C.Feasible i j := by
  have hn : next i≠E := by revert hiD; fin_cases i <;> decide
  simp [Feasible,slack,edge,R.other_delta i hiD hiE,
    R.point_other i hiE,R.point_other (next i) hn]

theorem negative_nonincrease (R : Result I) :
    negativeVariation R.cycle.theta≤negativeVariation C.theta := by
  rw [←variations_equal R.cycle.theta,←variations_equal C.theta]
  exact R.positive_nonincrease

def unchanged (I : SourceDomain q C) (hc : (C.point E).Core)
    (hr : Reduced C (I.owner D) (I.owner E)) : Result I where
  cycle := C
  source := I
  E_core := hc
  point_other _ _ := rfl
  theta_other _ _ := rfl
  owner_other _ _ _ := rfl
  positive_nonincrease := le_rfl
  reduced := hr

def ofMove (I : SourceDomain q C) (hq : q≤qCap) (O : Move q C)
    (hr : Reduced O.cycle O.de O.eh) : Result I where
  cycle := O.cycle
  source := O.source I hq
  E_core := O.core
  point_other i hi := (O.unchanged i hi).1
  theta_other i hi := (O.unchanged i hi).2
  owner_other i hiD hiE := O.other_owner I.owner i hiD hiE
  positive_nonincrease := O.positive_nonincrease
  reduced := by simpa [Move.source,Move.owner,D,E] using hr

/-- A `Move` of E followed by a `Result` for the moved source domain is a `Result` for `I`: the
radius, the data outside E and every selected A and T error stay those of `I`. -/
def prependMove (I : SourceDomain q C) (hq : q≤qCap) (O : Move q C)
    (R : Result (O.source I hq)) : Result I where
  cycle := R.cycle
  source := R.source
  E_core := R.E_core
  point_other i hi := (R.point_other i hi).trans (O.unchanged i hi).1
  theta_other i hi := (R.theta_other i hi).trans (O.unchanged i hi).2
  owner_other i hiD hiE := (R.owner_other i hiD hiE).trans (O.other_owner I.owner i hiD hiE)
  positive_nonincrease := R.positive_nonincrease.trans O.positive_nonincrease
  reduced := R.reduced

end Result

theorem aligned_DE_secondary {C : SignedCycle}
    (hd : delta C.theta D=0) (hf : C.Feasible D 3) : C.Feasible D 2 := by
  have hd' : delta C.theta 5=0 := hd
  have hh : quarterFeasible (C.point D) (C.point E) (delta C.theta D) 3 := by
    simpa [Feasible,slack,edge,word,next,D,E,quarterFeasible,sub_nonneg] using hf
  rw [hd] at hh
  have hs := (quarter_high_tie (C.point D) (C.point E)).2 hh
  simpa [Feasible,slack,edge,word,next,D,E,hd',quarterFeasible,sub_nonneg] using hs

theorem aligned_EH_secondary {C : SignedCycle}
    (he : delta C.theta E=0) (hf : C.Feasible E 1) : C.Feasible E 0 := by
  have he' : delta C.theta 6=0 := he
  have hh : quarterFeasible (C.point E) (C.point H) (delta C.theta E) 1 := by
    simpa [Feasible,slack,edge,word,next,H,E,quarterFeasible,sub_nonneg] using hf
  rw [he] at hh
  have hs := (quarter_low_tie (C.point E) (C.point H)).2 hh
  simpa [Feasible,slack,edge,word,next,H,E,he',quarterFeasible,sub_nonneg] using hs

/-- A negative E total on the flat core with no positive E primary: a zero primary error is a tie
that makes the secondary of its edge feasible, and two negative errors use the paired endpoint. -/
theorem reduce_nonpositive {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) (hc : (C.point E).Core)
    (hf : (C.point E).a=7/12)
    (hneg : eTotal C (I.owner D) (I.owner E)<0)
    (hd : I.owner D=3 → delta C.theta D≤0)
    (he : I.owner E=1 → delta C.theta E≤0) : Nonempty (Result I) := by
  have hde : I.owner D=2 ∨ I.owner D=3 := by
    simpa [highGAOwners,D] using I.allowed D
  have heh : I.owner E=0 ∨ I.owner E=1 := by
    simpa [highGAOwners,E] using I.allowed E
  rcases hde with hde | hde
  · have heh : I.owner E=1 := by
      rcases heh with heh | heh
      · simp [eTotal,primaryDE,primaryEH,hde,heh] at hneg
      · exact heh
    have hr : delta C.theta E<0 := by
      simpa [eTotal,primaryDE,primaryEH,hde,heh] using hneg
    exact ⟨Result.unchanged I hc (Or.inr ⟨hf,Or.inr ⟨hde,heh,hr⟩⟩)⟩
  · rcases heh with heh | heh
    · have hr : delta C.theta D<0 := by
        simpa [eTotal,primaryDE,primaryEH,hde,heh] using hneg
      exact ⟨Result.unchanged I hc (Or.inr ⟨hf,Or.inl ⟨hde,heh,hr⟩⟩)⟩
    · have hDE : C.Feasible D 3 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 1 := by simpa [heh] using I.feasible E
      have hsum : delta C.theta D+delta C.theta E<0 := by
        simpa [eTotal,primaryDE,primaryEH,hde,heh] using hneg
      by_cases hzD : delta C.theta D=0
      · have hr : delta C.theta E<0 := by linarith
        let O := ETransport.identity I hc hf 2 1 (Or.inl rfl) (Or.inr rfl)
          (aligned_DE_secondary hzD hDE) hEH
        refine ⟨Result.ofMove I hqU O (Or.inr ⟨?_,Or.inr ⟨rfl,rfl,?_⟩⟩)⟩
        · exact hf
        · simpa [O,ETransport.identity,Move.cycle,replacePoint] using hr
      by_cases hzE : delta C.theta E=0
      · have hr : delta C.theta D<0 := by linarith
        let O := ETransport.identity I hc hf 3 0 (Or.inr rfl) (Or.inl rfl)
          hDE (aligned_EH_secondary hzE hEH)
        refine ⟨Result.ofMove I hqU O (Or.inr ⟨?_,Or.inl ⟨rfl,rfl,?_⟩⟩)⟩
        · exact hf
        · simpa [O,ETransport.identity,Move.cycle,replacePoint] using hr
      have hd' : delta C.theta D<0 := lt_of_le_of_ne (hd hde) hzD
      have he' : delta C.theta E<0 := lt_of_le_of_ne (he heh) hzE
      obtain ⟨R⟩ := PairedNegativeE.reduce I hqL hqU hc hDE hEH hd' he'
      exact ⟨Result.ofMove I hqU R.move (Or.inr ⟨R.move.flat,R.single⟩)⟩

/-- Every source domain with E on the core curve has a `Result`, for every sign of A and T. -/
theorem reduce {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) (hc : (C.point E).Core) :
    Nonempty (Result I) := by
  by_cases htotal : 0≤eTotal C (I.owner D) (I.owner E)
  · exact ⟨Result.unchanged I hc (Or.inl htotal)⟩
  let J : CoreENegativeTotal.Input q :=
    { cycle := C
      necessary := I.necessary
      E_nonpos := I.E_nonpos
      H_nonneg := I.H_positive.le
      D_outer := I.outer D (by simp)
      H_outer := I.outer H (by simp)
      de := I.owner D
      eh := I.owner E
      de_allowed := by simpa [highGAOwners,D] using I.allowed D
      eh_allowed := by simpa [highGAOwners,E] using I.allowed E
      DE := I.feasible D
      EH := I.feasible E }
  obtain ⟨R⟩ := CoreENegativeTotal.reduce_negative_total J hqL hqU hc (lt_of_not_ge htotal)
  let O := ETransport.ofMixed R.move R.flat
  let I' := O.source I hqU
  have hc' : (O.cycle.point E).Core := O.core
  have hf' : (O.cycle.point E).a=7/12 := O.flat
  by_cases hnew : 0≤eTotal O.cycle O.de O.eh
  · exact ⟨Result.ofMove I hqU O (Or.inl hnew)⟩
  have hneg' : eTotal O.cycle (I'.owner D) (I'.owner E)<0 := by
    simpa [I',Move.source,Move.owner,D,E] using lt_of_not_ge hnew
  have hnonpos : primaryDE O.cycle O.de≤0 ∧ primaryEH O.cycle O.eh≤0 := by
    rcases R.normal_form with hpos | ⟨hflat,hd,he⟩
    · exact (hnew (by simpa [O,ofMixed,Move.cycle,NegativeCoreE.CycleMove.cycle] using hpos)).elim
    · exact ⟨hd,he⟩
  have hd' : I'.owner D=3 → delta O.cycle.theta D≤0 := by
    intro hh
    have hh' : O.de=3 := by simpa [I',Move.source,Move.owner,D,E] using hh
    simpa [primaryDE,hh'] using hnonpos.1
  have he' : I'.owner E=1 → delta O.cycle.theta E≤0 := by
    intro hh
    have hh' : O.eh=1 := by simpa [I',Move.source,Move.owner,E] using hh
    simpa [primaryEH,hh'] using hnonpos.2
  obtain ⟨S⟩ := reduce_nonpositive I' hqL hqU hc' hf' hneg' hd' he'
  exact ⟨Result.prependMove I hqU O S⟩

end SquaresInCircles.Eight.GlobalGA.CoreENormalForm
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.OuterE
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

theorem exists_selection {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q≤qCap) (hE : (C.point E).Outer q) : Nonempty (Selection I) := by
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
  exact ⟨⟨de,eh,hDE,hEH,hdep,hehp⟩⟩

def select {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q≤qCap) (hE : (C.point E).Outer q) : Selection I :=
  Classical.choice (exists_selection I hq hE)

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
end SquaresInCircles.Eight.GlobalGA.OuterE
end
end
end
