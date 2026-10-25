module

public import SquaresInCircles.Eight.Owners.GA.OuterESelection
public import SquaresInCircles.Eight.Owners.GA.Negative.ACycle
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SmallHigh
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD0Source
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD0Source
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAStress
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDSource
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsSourceData
public import SquaresInCircles.Eight.Owners.GA.EZero

/-!
# Eight squares: a core E, E first and A second, with nonnegative A and nonpositive T

E is normalized while the cycle is an ordered boundary cycle. The move of A that follows gives a
signed cycle that is used only through the seven circle inequalities of the necessary conditions,
not as a packing. The cases are: a nonnegative selected E total, or a single negative DE3 or EH1
on the flat core; a selected A total in `[0, 1/6]` or in `[1/6, frameCap]`; and TD0, or TD2 with
nonpositive error (`nonnegative_A_nonpositive_T_all_E_false`). The scalar stresses for the low and
the high A totals, with TD0 or TD2, apply with the weak witnesses of the cycle. For EH1, a feasible
EH0 is reselected on the same cycle; otherwise the geometry of E and H gives the short cut of the
angle of E.
-/

section
/-!
## The owner flags of a high-GA source domain

The stress of nonnegative A and E totals `NonnegativeTotals.all_TD_false` is a single scalar proof
for TD0, positive TD2 and negative TD2, with four Boolean owner flags. Here the flags `gaFlag`,
`abFlag`, `deFlag` and `ehFlag` are read off the seven chosen weak axes of a `SourceDomain`
(`ga_owner`, `ab_owner`, `de_owner`, `eh_owner`), and `aTotal` and `eTotal` are the signed totals of
the selected A and E primaries. No GA, AB, DE or EH witness is changed. Neither the signs of the
single A and E errors nor the radial kind of T are restricted.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate SignedCycle
namespace HighGABT2

variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

/-- The primary flags are the owners of the source domain itself: GA3, AB2, DE3 and EH1. -/
def gaFlag : Bool := decide (I.owner G=3)
def abFlag : Bool := decide (I.owner A=2)
def deFlag : Bool := decide (I.owner D=3)
def ehFlag : Bool := decide (I.owner E=1)

theorem ga_owner :
    I.owner G=(if gaFlag I then 3 else 2) := by
  have h : I.owner G=2∨I.owner G=3 := by
    simpa [GlobalGA.highGAOwners,G] using I.allowed G
  rcases h with h|h
  · simp [gaFlag,h]
  · simp [gaFlag,h]

theorem ab_owner :
    I.owner A=(if abFlag I then 2 else 0) := by
  have h : I.owner A=0∨I.owner A=2 := by
    simpa [GlobalGA.highGAOwners,A] using I.allowed A
  rcases h with h|h
  · simp [abFlag,h]
  · simp [abFlag,h]

theorem de_owner :
    I.owner D=(if deFlag I then 3 else 2) := by
  have h : I.owner D=2∨I.owner D=3 := by
    simpa [GlobalGA.highGAOwners,D] using I.allowed D
  rcases h with h|h
  · simp [deFlag,h]
  · simp [deFlag,h]

theorem eh_owner :
    I.owner E=(if ehFlag I then 1 else 0) := by
  have h : I.owner E=0∨I.owner E=1 := by
    simpa [GlobalGA.highGAOwners,E] using I.allowed E
  rcases h with h|h
  · simp [ehFlag,h]
  · simp [ehFlag,h]

/-- The signed totals of the selected A and E primaries. An unselected primary contributes zero,
even when the error of its secondary is nonzero; the two primaries may have errors of opposite
signs. -/
def aTotal : ℝ :=
  GlobalGA.NonnegativeTotals.Source.aTotal C (gaFlag I) (abFlag I)
def eTotal : ℝ :=
  GlobalGA.NonnegativeTotals.Source.eTotal C (deFlag I) (ehFlag I)

include I in
theorem original_HG : C.Feasible H 0∨C.Feasible H 2 := by
  have h : I.owner H=0∨I.owner H=2 := by
    simpa [GlobalGA.highGAOwners,H] using I.allowed H
  rcases h with h|h
  · exact Or.inl (by simpa [h] using I.feasible H)
  · exact Or.inr (by simpa [h] using I.feasible H)

include I in
theorem original_TD : C.Feasible T 0∨C.Feasible T 2 := by
  have h : I.owner T=0∨I.owner T=2 := by
    simpa [GlobalGA.highGAOwners,T] using I.allowed T
  rcases h with h|h
  · exact Or.inl (by simpa [h] using I.feasible T)
  · exact Or.inr (by simpa [h] using I.feasible T)

end HighGABT2
end SquaresInCircles.Eight
end
end
end

section
/-!
## The normalization of the A primaries in a high-GA source domain

`A_normalize` is the only move of A in the negative-A BT2 case. At the radius of the source
domain, `NegativeANormalForm.cycle_reduce` gives either a nonnegative selected A total or one
negative primary on a flat-core A with positive `y`. A itself moves, so the result is a signed
cycle that satisfies the necessary conditions; it need not be a packing, be ordered or be a source
domain. Every other square and the five witnesses on the edges away from A are unchanged.

The BT2, TD, HG, DE and EH witnesses of the source domain stay feasible (`ATransport`), by the
equivalences on the unchanged edges, and so do the T, D and E errors and the points of E, H, G, B
and D.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle

variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

include I in
theorem A_normalize (hqL : qLow≤q) (hqU : q≤qCap) :
    Nonempty (GlobalGA.NegativeANormalForm.CycleResult q C) := by
  have hQL : (5/2:ℝ)≤q := by
    have hlow : (5/2:ℝ)≤qLow := by norm_num [qLow]
    exact hlow.trans hqL
  have hGA : C.Feasible G (if gaFlag I then 3 else 2) := by
    rw [←ga_owner I]
    exact I.feasible G
  have hAB : C.Feasible A (if abFlag I then 2 else 0) := by
    rw [←ab_owner I]
    exact I.feasible A
  exact GlobalGA.NegativeANormalForm.cycle_reduce
    (gaFlag I) (abFlag I) hQL hqU I.necessary I.radial
    I.G_negative.le (I.outer B (by simp [H,G,B,D]))
    I.B_negative.le I.A_upper I.A_nonpos_outer I.strict_spread hGA hAB

namespace ATransport
open GlobalGA.NegativeANormalForm
variable {q : ℝ} {C : SignedCycle} (O : CycleResult q C)

/-- A BT2 witness stays feasible when A moves. -/
theorem BT2 (hBT : C.Feasible B 2) : O.cycle.Feasible B 2 :=
  (O.other_edges B (by norm_num [B,G,A]) 2).2 hBT

/-- A TD witness stays feasible when A moves. -/
theorem TD (j : Fin 4) (hTD : C.Feasible T j) : O.cycle.Feasible T j :=
  (O.other_edges T (by norm_num [T,G,A]) j).2 hTD

theorem HG (j : Fin 4) (hHG : C.Feasible H j) : O.cycle.Feasible H j :=
  (O.other_edges H (by norm_num [H,G,A]) j).2 hHG

theorem DE (j : Fin 4) (hDE : C.Feasible D j) : O.cycle.Feasible D j :=
  (O.other_edges D (by norm_num [D,G,A]) j).2 hDE

theorem EH (j : Fin 4) (hEH : C.Feasible E j) : O.cycle.Feasible E j :=
  (O.other_edges E (by norm_num [E,G,A]) j).2 hEH

theorem original_T_error :
    delta O.cycle.theta T=delta C.theta T := by
  have h4 : O.cycle.theta 4=C.theta 4 := O.theta_other T (by decide)
  have h5 : O.cycle.theta 5=C.theta 5 := O.theta_other D (by decide)
  simp [delta,next,T,h4,h5]

theorem original_D_error :
    delta O.cycle.theta D=delta C.theta D := by
  have h5 : O.cycle.theta 5=C.theta 5 := O.theta_other D (by decide)
  have h6 : O.cycle.theta 6=C.theta 6 := O.theta_other E (by decide)
  simp [delta,next,D,h5,h6]

theorem original_E_error :
    delta O.cycle.theta E=delta C.theta E := by
  have h6 : O.cycle.theta 6=C.theta 6 := O.theta_other E (by decide)
  have h0 : O.cycle.theta 0=C.theta 0 := O.theta_other H (by decide)
  simp [delta,next,E,h6,h0]

theorem E_point : O.cycle.point E=C.point E :=
  O.point_other E (by norm_num [E,A])

theorem H_point : O.cycle.point H=C.point H :=
  O.point_other H (by norm_num [H,A])

theorem G_point : O.cycle.point G=C.point G :=
  O.point_other G (by norm_num [G,A])

theorem B_point : O.cycle.point B=C.point B :=
  O.point_other B (by norm_num [B,A])

theorem D_point : O.cycle.point D=C.point D :=
  O.point_other D (by norm_num [D,A])

end ATransport
end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## A core E normalized before A moves

A high-GA source domain with E on the core curve has the gap order and the other fields of a
source domain, and `CoreENormalForm.reduce` uses them to remove a zero E error and two negative E
errors. Only then does `A_normalize` (`NegativeANormalForm.cycle_reduce`) move A, to a signed
cycle that satisfies the necessary conditions but need not be a packing. That second move leaves
E, D, H, B and T, their errors and their axes unchanged.

The zero-tangent theorem of E needs the gap order, so it applies to the source domain and not to
the cycle with A moved. A `CoreEFirstResult` keeps the two records apart, at the same `q`
(`core_E_then_A`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.CoreENormalForm
open GlobalGA.NegativeANormalForm

/-- The first transport gives a high-GA source domain on the cycle with E normalized; the second
gives only a signed cycle with A moved that satisfies the necessary conditions. -/
structure CoreEFirstResult {q : ℝ} {C : SignedCycle}
    (I : GlobalGA.SourceDomain q C) where
  E : GlobalGA.CoreENormalForm.Result I
  A : GlobalGA.NegativeANormalForm.CycleResult q E.cycle

theorem core_E_then_A {q : ℝ} {C : SignedCycle}
    (I : GlobalGA.SourceDomain q C) (hqL : qLow≤q) (hqU : q≤qCap)
    (hcore : (C.point E).Core) : Nonempty (CoreEFirstResult I) := by
  obtain ⟨P⟩ := GlobalGA.CoreENormalForm.reduce I hqL hqU hcore
  obtain ⟨Q⟩ := A_normalize P.source hqL hqU
  exact ⟨⟨P,Q⟩⟩

namespace CoreEFirstResult
variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

/-- After A is normalized, E keeps the point and the core kind it has on the cycle with E
normalized. -/
theorem E_point : (R.A.cycle.point Candidate.E)=R.E.cycle.point Candidate.E :=
  ATransport.E_point R.A

theorem E_core : (R.A.cycle.point Candidate.E).Core := by
  rw [E_point R]
  exact R.E.E_core

theorem D_error :
    delta R.A.cycle.theta D=delta R.E.cycle.theta D :=
  ATransport.original_D_error R.A

theorem E_error :
    delta R.A.cycle.theta Candidate.E=delta R.E.cycle.theta Candidate.E :=
  ATransport.original_E_error R.A

/-- The normal form of the E primaries survives the move of A: if the selected E total is
negative, there is still one negative flat-core primary, DE3 or EH1. -/
theorem E_reduced :
    GlobalGA.CoreENormalForm.Reduced R.A.cycle
      (R.E.source.owner D) (R.E.source.owner Candidate.E) := by
  rcases R.E.reduced with he|⟨hf,hcase⟩
  · left
    simpa [ActualCoreEBlocks.eTotal,ActualCoreEBlocks.primaryDE,
      ActualCoreEBlocks.primaryEH,D_error R,E_error R] using he
  · right
    constructor
    · rw [E_point R]
      exact hf
    · rcases hcase with ⟨hd,he,hneg⟩|⟨hd,he,hneg⟩
      · left
        exact ⟨hd,he,by rw [D_error R]; exact hneg⟩
      · right
        exact ⟨hd,he,by rw [E_error R]; exact hneg⟩

/-- The normalization of E keeps the radius, and the move of A keeps the DE and EH witnesses of E
feasible. -/
theorem DE : R.A.cycle.Feasible D (R.E.source.owner D) :=
  ATransport.DE R.A _ (R.E.source.feasible D)

theorem EH : R.A.cycle.Feasible Candidate.E (R.E.source.owner Candidate.E) :=
  ATransport.EH R.A _ (R.E.source.feasible Candidate.E)

theorem BT2 (h : R.E.cycle.Feasible B 2) : R.A.cycle.Feasible B 2 :=
  ATransport.BT2 R.A h

theorem TD (j : Fin 4) (h : R.E.cycle.Feasible T j) :
    R.A.cycle.Feasible T j :=
  ATransport.TD R.A j h

end CoreEFirstResult
end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## Normalizing E first and A second, with nonnegative A and E totals

Once E is normalized on a source domain, A moves, and the moved cycle need not be a source domain.
The selected DE and EH normals of E, the HG and TD normals, the four sign anchors of H, G, B and D
and the selected E total carry over to the moved cycle, which satisfies the necessary conditions.
The signed stress of nonnegative totals `NonnegativeTotals.all_TD_false` then excludes both T
owners and both signs of the TD2 error, zero included (`reduced_nonnegative_AE_false`). The cycle
with A moved is used only as a signed cycle, not as a packing.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

/-- On the cycle with E then A moved, the owners of the source domain on the edges other than GA
and AB stay feasible. -/
private theorem witness_HG :
    R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
  (original_HG R.E.source).imp
    (ATransport.HG R.A 0) (ATransport.HG R.A 2)

private theorem witness_TD :
    R.A.cycle.Feasible T 0∨R.A.cycle.Feasible T 2 :=
  (original_TD R.E.source).imp
    (ATransport.TD R.A 0) (ATransport.TD R.A 2)

/-- With E then A normalized, nonnegative selected A and E totals and a BT2 witness are impossible,
for both TD owners and every sign of the T error. -/
theorem reduced_nonnegative_AE_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (ha : 0≤GlobalGA.NegativeANormalForm.total R.A.ga R.A.ab
      (delta R.A.cycle.theta G) (delta R.A.cycle.theta A))
    (he : 0≤GlobalGA.NonnegativeTotals.Source.eTotal R.A.cycle
      (deFlag R.E.source) (ehFlag R.E.source)) : False := by
  have hA : 0≤GlobalGA.NonnegativeTotals.Source.aTotal R.A.cycle
      R.A.ga R.A.ab := by
    simpa [GlobalGA.NegativeANormalForm.total,
      GlobalGA.NonnegativeTotals.Source.aTotal,GlobalGA.PairedE.total,
      GlobalGA.PairedE.selected] using ha
  have hDE : R.A.cycle.Feasible D (if deFlag R.E.source then 3 else 2) := by
    rw [←de_owner R.E.source]
    exact R.DE
  have hEH : R.A.cycle.Feasible E (if ehFlag R.E.source then 1 else 0) := by
    rw [←eh_owner R.E.source]
    exact R.EH
  have hH : 0≤(R.A.cycle.point H).y := by
    rw [ATransport.H_point R.A]
    exact R.E.source.H_positive.le
  have hG : (R.A.cycle.point G).y≤0 := by
    rw [ATransport.G_point R.A]
    exact R.E.source.G_negative.le
  have hB : (R.A.cycle.point B).y≤0 := by
    rw [ATransport.B_point R.A]
    exact R.E.source.B_negative.le
  have hD : (R.A.cycle.point D).y≤0 := by
    rw [ATransport.D_point R.A]
    exact R.E.source.D_negative.le
  exact GlobalGA.NonnegativeTotals.all_TD_false
    R.A.ga R.A.ab (deFlag R.E.source) (ehFlag R.E.source)
    R.A.necessary.sorted R.A.necessary.contained
    (R.A.necessary.core T) hqU hH hG hB hD
    (R.A.variation.trans R.E.source.positive_variation.le) hA he
    (witness_HG R) R.A.GA R.A.AB (R.BT2 hBT)
    (witness_TD R) hDE hEH

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## A core E with both secondary owners at the same state

If DE2 and EH0 are feasible on the cycle with E then A moved, E is reselected on them at the same
state, without moving. The selected E charge is then zero, and with a nonnegative selected A total
the stress `NonnegativeTotals.all_TD_false` excludes the cycle for every T owner and every T error
(`nonnegative_A_secondary_E_all_T_false`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

theorem nonnegative_A_secondary_E_all_T_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (ha : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab)
    (hDE : R.A.cycle.Feasible D 2)
    (hEH : R.A.cycle.Feasible E 0) : False := by
  have hE : 0≤GlobalGA.NonnegativeTotals.Source.eTotal
      R.A.cycle false false := by
    simp [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected]
  have hHG : R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
    (original_HG R.E.source).imp
      (ATransport.HG R.A 0) (ATransport.HG R.A 2)
  have hTD : R.A.cycle.Feasible T 0∨R.A.cycle.Feasible T 2 :=
    (original_TD R.E.source).imp
      (ATransport.TD R.A 0) (ATransport.TD R.A 2)
  have hH : 0≤(R.A.cycle.point H).y := by
    rw [ATransport.H_point R.A]
    exact R.E.source.H_positive.le
  have hG : (R.A.cycle.point G).y≤0 := by
    rw [ATransport.G_point R.A]
    exact R.E.source.G_negative.le
  have hB : (R.A.cycle.point B).y≤0 := by
    rw [ATransport.B_point R.A]
    exact R.E.source.B_negative.le
  have hD : (R.A.cycle.point D).y≤0 := by
    rw [ATransport.D_point R.A]
    exact R.E.source.D_negative.le
  exact GlobalGA.NonnegativeTotals.all_TD_false
    R.A.ga R.A.ab false false
    R.A.necessary.sorted R.A.necessary.contained
    (R.A.necessary.core T) hqU hH hG hB hD
    (R.A.variation.trans R.E.source.positive_variation.le)
    ha hE hHG R.A.GA R.A.AB (R.BT2 hBT) hTD hDE hEH

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## A BT2 witness with nonpositive selected A and T primary errors, for every E

`tdFlag` records whether the TD witness of a source domain is TD2 (`td_owner`, `tdFlag_true`).
The owner flags of the source domain are used as they are: if an A primary is selected, its own
angular error is nonpositive, and an unselected primary has no sign restriction. The T primary is
treated in the same way.

When E is on the core curve, the core-E negative-total contradiction covers both signs of E and
all its owner alternatives. When E is outer, reselecting E at the same state makes its selected
total nonnegative, and the signed stress of the A and E totals excludes the source domain. No point
of A, T or E moves in this branch. Weak ties are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle

variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

def tdFlag : Bool := decide (I.owner T=2)

theorem td_owner : I.owner T=(if tdFlag I then 2 else 0) := by
  have h : I.owner T=0∨I.owner T=2 := by
    simpa [GlobalGA.highGAOwners,T] using I.allowed T
  rcases h with h|h
  · simp [tdFlag,h]
  · simp [tdFlag,h]

theorem tdFlag_true (h : tdFlag I=true) : I.owner T=2 := by
  simpa [tdFlag] using h

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## A normalized negative A and a nonpositive T, for every E

The normalization of A gives a signed cycle that satisfies the necessary conditions; the moved A
need not form a packing, keep the order of its neighbors or have a selected normal of its own.
The owners of an outer E are selected on the source domain `I` only, and the stress lemmas on the
seven circle inequalities apply to the moved cycle (`reduced_A_nonpositive_T_false`).

This excludes a single negative A primary with a nonpositive T primary
(`negative_reduced_A_nonpositive_T_false`) for both radial kinds of E, all selected DE and EH signs
and weak ties.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle}
  (I : GlobalGA.SourceDomain q C)
  (O : CycleResult q C)

include I in
/-- The separators of the source domain on the edges away from A stay feasible on the cycle of
`O`, at the same radius. -/
private theorem reduced_HG :
    O.cycle.Feasible H 0∨O.cycle.Feasible H 2 :=
  (original_HG I).imp (ATransport.HG O 0) (ATransport.HG O 2)

private theorem reduced_TD :
    O.cycle.Feasible T (if tdFlag I then 2 else 0) := by
  apply ATransport.TD O
  rw [←td_owner I]
  exact I.feasible T

private theorem reduced_DE :
    O.cycle.Feasible D (if deFlag I then 3 else 2) := by
  apply ATransport.DE O
  rw [←de_owner I]
  exact I.feasible D

private theorem reduced_EH :
    O.cycle.Feasible E (if ehFlag I then 1 else 0) := by
  apply ATransport.EH O
  rw [←eh_owner I]
  exact I.feasible E

/-- A cycle with A moved whose selected A primaries and selected T primary are nonpositive has no
BT2 witness. Every regime of E is covered, negative E totals included, and the moved A is used
without any order. -/
theorem reduced_A_nonpositive_T_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hBT : C.Feasible B 2)
    (hga : O.ga=true→delta O.cycle.theta G≤0)
    (hab : O.ab=true→delta O.cycle.theta A≤0)
    (htd : tdFlag I=true→delta C.theta T≤0) : False := by
  have hBT' := ATransport.BT2 O hBT
  have hTD' := reduced_TD I O
  have hHG' := reduced_HG I O
  have hT : tdFlag I=true→delta O.cycle.theta T≤0 := by
    intro ht
    rw [ATransport.original_T_error O]
    exact htd ht
  have hH : 0≤(O.cycle.point H).y := by
    rw [ATransport.H_point O]
    exact I.H_positive.le
  have hG : (O.cycle.point G).y≤0 := by
    rw [ATransport.G_point O]
    exact I.G_negative.le
  have hB : (O.cycle.point B).y≤0 := by
    rw [ATransport.B_point O]
    exact I.B_negative.le
  have hD : (O.cycle.point D).y≤0 := by
    rw [ATransport.D_point O]
    exact I.D_negative.le
  have hv : positiveVariation O.cycle.theta≤frameCap :=
    O.variation.trans I.positive_variation.le
  rcases I.radial E with houter|hcore
  · -- The owners of an outer E are selected on E, D and H of the source domain, which stay put.
    let S := GlobalGA.OuterE.select I hqU houter
    have hDE := ATransport.DE O _ S.DE
    have hEH := ATransport.EH O _ S.EH
    have he : 0≤GlobalGA.PairedE.cycleTotal O.cycle S.de S.eh := by
      simpa [GlobalGA.PairedE.cycleTotal,GlobalGA.PairedE.total,
        GlobalGA.PairedE.selected,ATransport.original_D_error O,
        ATransport.original_E_error O] using S.total_nonneg
    exact GlobalGA.PairedE.Negative.actual_false
      O.ga O.ab (tdFlag I) S.de S.eh
      O.necessary.sorted O.necessary.contained O.necessary.core hqU
      hH hG hB hD hv hHG' O.GA O.AB hBT' hTD' hDE hEH
      hga hab hT he
  · -- A core E: the negative-total contradiction needs no order of the cycle with A moved,
    -- only its seven circle inequalities.
    have hEc : (O.cycle.point E).Core := by
      rw [ATransport.E_point O]
      exact hcore
    have hEy : (O.cycle.point E).y≤0 := by
      rw [ATransport.E_point O]
      exact I.E_nonpos
    have hHo : (O.cycle.point H).Outer q := by
      rw [ATransport.H_point O]
      exact I.outer H (by simp)
    have hDo : (O.cycle.point D).Outer q := by
      rw [ATransport.D_point O]
      exact I.outer D (by simp)
    exact GlobalGA.CoreENegativeTotal.actual_false
      O.ga O.ab (tdFlag I) (deFlag I) (ehFlag I)
      O.necessary hqL hqU hH hG hB hD hHo hDo hEy hEc
      hv hHG' O.GA O.AB hBT' hTD' (reduced_DE I O) (reduced_EH I O)
      hga hab hT

/-- In the two negative branches of the A normal form exactly one selected primary is negative.
The positivity and flatness bounds of `O.reduced` are not needed for a nonpositive T. -/
theorem negative_reduced_A_nonpositive_T_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hBT : C.Feasible B 2)
    (htd : tdFlag I=true→delta C.theta T≤0)
    (hnegative : ¬ 0≤
      GlobalGA.NegativeANormalForm.total O.ga O.ab
        (delta O.cycle.theta G) (delta O.cycle.theta A)) : False := by
  rcases O.reduced with hnonneg|⟨hg,ha,hflat,hy,hu⟩|⟨hg,ha,hflat,hy,hv⟩
  · exact hnegative hnonneg
  · exact reduced_A_nonpositive_T_false I O hqL hqU hBT
      (by intro _; simpa [hg] using hu.2.le)
      (by intro hab; cases ha.symm.trans hab)
      htd
  · exact reduced_A_nonpositive_T_false I O hqL hqU hBT
      (by intro hga; cases hg.symm.trans hga)
      (by intro _; simpa [ha] using hv.2.le)
      htd

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

/-- After A moves, the total of the selected A primaries, not the sum of both A angles, stays in
the signed-variation window `[0, frameCap]` of the source domain. -/
private theorem a_total_domain
    (ha : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab) :
    GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab∈
      Icc 0 frameCap := by
  have hp : positiveVariation R.A.cycle.theta≤frameCap :=
    R.A.variation.trans R.E.source.positive_variation.le
  have hn : negativeVariation R.A.cycle.theta≤frameCap := by
    rw [←variations_equal]
    exact hp
  have hpair := GlobalGA.Secondary.original_pair_budgets (i:=G) (j:=A)
    hp hn (by norm_num [G,A])
  exact GlobalGA.PairedE.total_bounds R.A.ga R.A.ab hpair.1 hpair.2
    (by simpa [GlobalGA.PairedE.LowA.aTotal,
      GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.total] using ha)

/-- The signs of H, G, B and D used by the A, E and T stresses, after the move of A. -/
private theorem anchor_signs :
    0≤(R.A.cycle.point H).y ∧
      (R.A.cycle.point G).y≤0 ∧
      (R.A.cycle.point B).y≤0 ∧
      (R.A.cycle.point D).y≤0 := by
  constructor
  · rw [ATransport.H_point R.A]; exact R.E.source.H_positive.le
  constructor
  · rw [ATransport.G_point R.A]; exact R.E.source.G_negative.le
  constructor
  · rw [ATransport.B_point R.A]; exact R.E.source.B_negative.le
  · rw [ATransport.D_point R.A]; exact R.E.source.D_negative.le

private theorem H_witness :
    R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
  (original_HG R.E.source).imp (ATransport.HG R.A 0) (ATransport.HG R.A 2)

/-- A nonnegative selected A total, a nonpositive selected T primary and a negative DE3 with the
secondary EH0 are impossible. -/
theorem nonnegative_A_negative_DE_nonpositive_T_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hA : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab)
    (hTD : R.A.cycle.Feasible T (if tdFlag R.E.source then 2 else 0))
    (ht : tdFlag R.E.source=true→delta R.A.cycle.theta T≤0)
    (hflat : (R.A.cycle.point E).a=7/12)
    (hd : delta R.A.cycle.theta D<0)
    (hDE : R.A.cycle.Feasible D 3)
    (hEH : R.A.cycle.Feasible E 0) : False := by
  obtain ⟨hH,hG,hB,hD⟩ := anchor_signs R
  have hEy : (R.A.cycle.point E).y≤0 := by
    rw [R.E_point]; exact R.E.source.E_nonpos
  have ha := a_total_domain R hA
  have hv : positiveVariation R.A.cycle.theta≤frameCap :=
    R.A.variation.trans R.E.source.positive_variation.le
  by_cases hsmall : GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab ≤ 1/6
  · exact GlobalGA.NegativeELowA.actual_false
      R.A.ga R.A.ab (tdFlag R.E.source) true false
      R.A.necessary.sorted R.A.necessary.contained
      (R.A.necessary.core T) hqU hH hG hB hD hflat hv
      (H_witness R) R.A.GA R.A.AB (R.BT2 hBT)
      hTD hDE hEH ⟨ha.1,hsmall⟩ ht
      (fun _=>hd.le) (by intro h; cases h)
  · have hhigh : GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab∈
        Icc (1/6:ℝ) frameCap := ⟨(lt_of_not_ge hsmall).le,ha.2⟩
    cases htflag : tdFlag R.E.source
    · have hTD0 : R.A.cycle.Feasible T 0 := by simpa [htflag] using hTD
      exact GlobalGA.NegativeDETD0.original_high_false
        R.A.ga R.A.ab R.A.necessary.sorted R.A.necessary.contained
        hqU hH hG hB hD hEy R.E_core hv hhigh hd.le
        (H_witness R) R.A.GA R.A.AB (R.BT2 hBT) hTD0
        hDE hEH
    · have hTD2 : R.A.cycle.Feasible T 2 := by simpa [htflag] using hTD
      exact GlobalGA.NegativeELargeA.Source.actual_false
        R.A.ga R.A.ab true false
        R.A.necessary.sorted R.A.necessary.contained
        (R.A.necessary.core T) hqU hH hG hB hD hflat hv
        (H_witness R) R.A.GA R.A.AB (R.BT2 hBT) hTD2 hDE hEH
        hhigh (ht htflag) (fun _=>hd.le) (by intro h; cases h)

/-- A single negative EH1 has a quarter entry, so the flat tangent and angle cut of E hold on this
cycle. The cyclic order of the moved A is not used. -/
theorem nonnegative_A_negative_EH_nonpositive_T_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hA : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab)
    (hTD : R.A.cycle.Feasible T (if tdFlag R.E.source then 2 else 0))
    (ht : tdFlag R.E.source=true→delta R.A.cycle.theta T≤0)
    (hEneg : delta R.A.cycle.theta E<0)
    (hDE : R.A.cycle.Feasible D 2)
    (hEH : R.A.cycle.Feasible E 1) : False := by
  by_cases hEH0 : R.A.cycle.Feasible E 0
  · exact nonnegative_A_secondary_E_all_T_false R hqU hBT hA hDE hEH0
  have hv : positiveVariation R.A.cycle.theta≤frameCap :=
    R.A.variation.trans R.E.source.positive_variation.le
  have hEy : (R.A.cycle.point E).y≤0 := by
    rw [R.E_point]; exact R.E.source.E_nonpos
  have hHy : 0≤(R.A.cycle.point H).y := by
    rw [ATransport.H_point R.A]
    exact R.E.source.H_positive.le
  obtain ⟨hflat,hb,hmag⟩ :=
    GlobalGA.NegativeEHPositiveTD.Source.genuine_domain
      R.A.necessary.sorted R.A.necessary.contained hqU hHy hEy
      R.E_core hv hEneg hEH hEH0
  have hang : -delta R.A.cycle.theta E∈Icc (0:ℝ) (1/4) := by
    constructor
    · linarith
    · simpa [GlobalGA.NegativeEHPositiveTD.Source.magnitude] using hmag
  obtain ⟨hH,hG,hB,hD⟩ := anchor_signs R
  have ha := a_total_domain R hA
  by_cases hsmall : GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab ≤ 1/6
  · exact GlobalGA.NegativeELowA.actual_false
      R.A.ga R.A.ab (tdFlag R.E.source) false true
      R.A.necessary.sorted R.A.necessary.contained
      (R.A.necessary.core T) hqU hH hG hB hD hflat hv
      (H_witness R) R.A.GA R.A.AB (R.BT2 hBT)
      hTD hDE hEH ⟨ha.1,hsmall⟩ ht
      (by intro h; cases h) (fun _=>hang)
  · have hhigh : GlobalGA.PairedE.LowA.aTotal R.A.cycle R.A.ga R.A.ab∈
        Icc (1/6:ℝ) frameCap := ⟨(lt_of_not_ge hsmall).le,ha.2⟩
    cases htflag : tdFlag R.E.source
    · have hTD0 : R.A.cycle.Feasible T 0 := by simpa [htflag] using hTD
      exact GlobalGA.NegativeEHTD0.original_high_false
        R.A.ga R.A.ab R.A.necessary.sorted R.A.necessary.contained
        hqU hH hG hB hD hEy R.E_core hv hhigh hEneg hEH0
        (H_witness R) R.A.GA R.A.AB (R.BT2 hBT) hTD0
        hDE hEH
    · have hTD2 : R.A.cycle.Feasible T 2 := by simpa [htflag] using hTD
      exact GlobalGA.NegativeELargeA.Source.actual_false
        R.A.ga R.A.ab false true
        R.A.necessary.sorted R.A.necessary.contained
        (R.A.necessary.core T) hqU hH hG hB hD hflat hv
        (H_witness R) R.A.GA R.A.AB (R.BT2 hBT) hTD2 hDE hEH
        hhigh (ht htflag)
        (by intro h; cases h) (fun _=>⟨hang,hb.2⟩)

/-- Every E normal form with a nonnegative selected A total and a nonpositive selected T primary
is impossible, including a TD0 error of either sign, a zero TD2 error and simultaneous weak
owners. -/
theorem nonnegative_A_nonpositive_T_all_E_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (ha : 0≤GlobalGA.NegativeANormalForm.total
      R.A.ga R.A.ab (delta R.A.cycle.theta G)
        (delta R.A.cycle.theta A))
    (ht : tdFlag R.E.source=true→delta R.A.cycle.theta T≤0) : False := by
  have ha' : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab := by
    simpa [GlobalGA.NegativeANormalForm.total,
      GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected] using ha
  have hTD : R.A.cycle.Feasible T (if tdFlag R.E.source then 2 else 0) := by
    apply R.TD
    rw [←td_owner R.E.source]
    exact R.E.source.feasible T
  rcases R.E_reduced with he|⟨hflat,hcase⟩
  · have he' : 0≤GlobalGA.NonnegativeTotals.Source.eTotal R.A.cycle
        (deFlag R.E.source) (ehFlag R.E.source) := by
      simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
        GlobalGA.PairedE.total,GlobalGA.CoreENegativeTotal.selected_total,
        GlobalGA.PairedE.cycleTotal,de_owner R.E.source,eh_owner R.E.source]
        using he
    exact reduced_nonnegative_AE_false R hqU hBT ha he'
  · rcases hcase with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · exact nonnegative_A_negative_DE_nonpositive_T_false
        R hqU hBT ha' hTD ht hflat hd
        (by simpa [hde] using R.DE)
        (by simpa [heh] using R.EH)
    · exact nonnegative_A_negative_EH_nonpositive_T_false
        R hqU hBT ha' hTD ht he
        (by simpa [hde] using R.DE)
        (by simpa [heh] using R.EH)

end SquaresInCircles.Eight.HighGABT2
end
end
end
