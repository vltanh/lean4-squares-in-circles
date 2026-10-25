module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly
public import SquaresInCircles.Eight.Owners.E.ZeroCapEndpoints
public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars
public import SquaresInCircles.Eight.Owners.ScalarRadicalTransfer
public import SquaresInCircles.Eight.Owners.TD0Span

/-!
# Eight squares: positive-TD2 span: the four intrinsic boundaries of the scalar domain

The continuous weight depends on the unchanged A--T
frame difference. At fixed difference the scalar is concave in the short
negative-GA error. Its two endpoints are four intrinsic polygon edges.
One follows from the fixed-weight span reserve; the other three use their
explicit whole-interval polynomials, with every Taylor direction proved.
-/

section
/-!
## Actual same-radius E candidates for two nonnegative primaries

The larger of the original H/D primary coordinates
is chosen only for the scalar contact construction. Reversing that
choice reflects the local E tangent and then restores the original
DE/EH edges. The output includes both quarter-gap guards and an explicit
diagonal alternative; the global tie theorem is not assumed here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveEPair
open EPairOrderedEndpoint

structure Endpoint (q : ℝ) (D H : SignedPoint) (t : ℝ) where
  point : SignedPoint
  deError : ℝ
  de_mem : deError∈Icc 0 t
  sorted : point.Sorted
  outer : point.Outer q
  core : point.AvoidsCore
  DE : quarterFeasible D point deError 3
  EH : quarterFeasible point H (t-deError) 1
  de_guard : 0<deError ∨ point.y<point.a
  eh_guard : 0<t-deError ∨ -point.a<point.y
  terminal : deError=0 ∨ deError=t ∨ |point.y|=point.a

theorem candidate {q u v : ℝ} {D E H : SignedPoint}
    (hQL : qLow≤q) (hQU : q≤qCap)
    (hDs : D.Sorted) (hDo : D.Outer q) (hHs : H.Sorted) (hHo : H.Outer q)
    (hEs : E.Sorted) (hEc : E.Contained q)
    (hu : 0≤u) (hv : 0≤v) (ht0 : 0<u+v) (ht : u+v≤7/10)
    (hDE : quarterFeasible D E u 3) (hEH : quarterFeasible E H v 1) :
    Nonempty (Endpoint q D H (u+v)) := by
  have hDb := SignedPoint.outer_bounds hDs hDo
  have hHb := SignedPoint.outer_bounds hHs hHo
  by_cases horder : H.a≤D.a
  · obtain ⟨F⟩ := ordered_endpoint hQL hQU ⟨hDb.1,hDb.2.2⟩ horder
      hu hv ht0 ht hEs hEc
      (by simpa [quarterFeasible,quarterProjection] using hDE)
      (by simpa [quarterFeasible,quarterProjection,add_comm,add_left_comm,add_assoc] using hEH)
    refine ⟨{
      point := F.point
      deError := F.firstError
      de_mem := F.first_mem
      sorted := F.sorted
      outer := F.outer
      core := F.avoids_core
      DE := by simpa [quarterFeasible,quarterProjection] using F.first_feasible
      EH := by simpa [quarterFeasible,quarterProjection,add_comm,add_left_comm,add_assoc] using F.second_feasible
      de_guard := ?_
      eh_guard := Or.inr F.lower_strict
      terminal := ?_ }⟩
    · by_cases hz : F.firstError=0
      · exact Or.inr (F.aligned_upper_strict hz)
      · exact Or.inl (lt_of_le_of_ne F.first_mem.1 (Ne.symm hz))
    · rcases F.endpoint with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (by rw [hh,abs_of_pos F.sorted.1]))
  · have horder' : D.a≤H.a := (lt_of_not_ge horder).le
    obtain ⟨F⟩ := ordered_endpoint (p := E.reflect) (u := v) (v := u)
      hQL hQU ⟨hHb.1,hHb.2.2⟩ horder' hv hu (by simpa [add_comm] using ht0)
      (by simpa [add_comm] using ht)
      ((SignedPoint.reflect_sorted E).mpr hEs) ((SignedPoint.reflect_contained E q).mpr hEc)
      (by simpa [quarterFeasible,quarterProjection,SignedPoint.reflect,
        add_comm,add_left_comm,add_assoc] using hEH)
      (by simpa [quarterFeasible,quarterProjection,SignedPoint.reflect,
        add_comm,add_left_comm,add_assoc,sub_eq_add_neg] using hDE)
    let d := u+v-F.firstError
    have hr : u+v-d=F.firstError := by dsimp [d]; ring
    have hother : v+u-F.firstError=d := by dsimp [d]; ring
    refine ⟨{
      point := F.point.reflect
      deError := d
      de_mem := ⟨by dsimp [d]; linarith [F.first_mem.2],by dsimp [d]; linarith [F.first_mem.1]⟩
      sorted := (SignedPoint.reflect_sorted F.point).mpr F.sorted
      outer := (SignedPoint.reflect_outer F.point q).mpr F.outer
      core := (SignedPoint.reflect_avoidsCore F.point).mpr F.avoids_core
      DE := ?_
      EH := ?_
      de_guard := Or.inr (by dsimp [SignedPoint.reflect]; linarith [F.lower_strict])
      eh_guard := ?_
      terminal := ?_ }⟩
    · have hh := F.second_feasible
      rw [hother] at hh
      simpa [quarterFeasible,quarterProjection,SignedPoint.reflect,
        add_comm,add_left_comm,add_assoc,sub_eq_add_neg] using hh
    · rw [hr]
      simpa [quarterFeasible,quarterProjection,SignedPoint.reflect,
        add_comm,add_left_comm,add_assoc,sub_eq_add_neg] using F.first_feasible
    · by_cases hz : F.firstError=0
      · right
        have hh := F.aligned_upper_strict hz
        dsimp [SignedPoint.reflect]
        linarith
      · left
        rw [hr]
        exact lt_of_le_of_ne F.first_mem.1 (Ne.symm hz)
    · rcases F.endpoint with hh | hh | hh
      · right; left
        dsimp [d]
        linarith
      · left
        dsimp [d]
        linarith
      · right; right
        simp [SignedPoint.reflect,hh,abs_of_pos F.sorted.1]

theorem DE_aligned {q t : ℝ} {D H : SignedPoint} (F : Endpoint q D H t)
    (hd : F.deError=0) : quarterFeasible D F.point 0 2 := by
  have hh := F.DE
  simpa [hd,quarterFeasible,quarterProjection] using hh

theorem EH_aligned {q t : ℝ} {D H : SignedPoint} (F : Endpoint q D H t)
    (he : F.deError=t) : quarterFeasible F.point H 0 0 := by
  have hh := F.EH
  simp only [he,sub_self,quarterFeasible,quarterProjection] at hh ⊢
  norm_num at hh ⊢
  linarith

end SquaresInCircles.Eight.PositiveEPair
end
end
end

section
/-!
## Inserting a positive E-pair endpoint into the seven-cycle

Only E is replaced, at the same radius (`Endpoint.cycle`): the other six coordinates and frames and
the owners of the five edges away from E stay. Both signed variations are unchanged, since the two
original and the two new errors at E are nonnegative with the same sum (`positive_variation_eq`,
`negative_variation_eq`). The winding follows from the geometry of the normal owners, and the
output is a boundary input with no sign condition on E (`Endpoint.boundaryInput`). A positive
DE3/EH1 pair has such an endpoint (`original_candidate`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.PositiveEPair
open Candidate

namespace Endpoint
variable {q : ℝ} {C : SignedCycle}

def cycle (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) : SignedCycle :=
  replacePoint C E F.point (C.theta D+F.deError)

def deOwner (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) : Fin 4 :=
  if F.deError=0 then 2 else 3

def ehOwner (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) : Fin 4 :=
  if F.deError=C.theta H-C.theta D then 0 else 1

theorem unchanged (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (i : Vertex) (hi : i≠E) : F.cycle.point i=C.point i ∧ F.cycle.theta i=C.theta i := by
  simp [cycle,replacePoint,hi]

theorem delta_DE (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    delta F.cycle.theta D=F.deError := by simp [cycle,replacePoint,delta,next,D,E]

theorem delta_EH (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    delta F.cycle.theta E=C.theta H-C.theta D-F.deError := by
  simp [cycle,replacePoint,delta,next,H,D,E]
  ring

theorem other_delta (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (i : Vertex) (hiD : i≠D) (hiE : i≠E) : delta F.cycle.theta i=delta C.theta i := by
  have hn : next i≠E := by revert hiD; fin_cases i <;> decide
  simp [delta,(F.unchanged i hiE).2,(F.unchanged (next i) hn).2]


theorem other_feasible (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (i : Vertex) (hiD : i≠D) (hiE : i≠E) (j : Fin 4) :
    F.cycle.Feasible i j ↔ C.Feasible i j := by
  have hn : next i≠E := by revert hiD; fin_cases i <;> decide
  exact SignedCycle.replacePoint_other_feasible hiE hn


private theorem r47_feasD (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (j : Fin 4) : F.cycle.Feasible D j ↔
      quarterFeasible (C.point D) F.point (delta F.cycle.theta D) j := by
  have hw : word D≠0 := by decide
  have hn : next D=E := rfl
  have hDE : D≠E := by decide
  have hE : F.cycle.point E=F.point := by simp [cycle,replacePoint]
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,hw,↓reduceIte,hn,
    quarterFeasible,sub_nonneg,hE,(F.unchanged D hDE).1]

private theorem r47_feasE (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (j : Fin 4) : F.cycle.Feasible E j ↔
      quarterFeasible F.point (C.point H) (delta F.cycle.theta E) j := by
  have hw : word E≠0 := by decide
  have hn : next E=H := rfl
  have hHE : H≠E := by decide
  have hE : F.cycle.point E=F.point := by simp [cycle,replacePoint]
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,hw,↓reduceIte,hn,
    quarterFeasible,sub_nonneg,hE,(F.unchanged H hHE).1]

theorem DE_primary (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    F.cycle.Feasible D 3 := by
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
    word,delta,next,D,E,quarterFeasible,sub_nonneg] using F.DE

theorem EH_primary (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    F.cycle.Feasible E 1 := by
  refine (r47_feasE F 1).2 ?_
  rw [F.delta_EH]
  exact F.EH


theorem DE_actual (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    F.cycle.Feasible D F.deOwner := by
  by_cases hz : F.deError=0
  · have hh := DE_aligned F hz
    have ho : F.deOwner=2 := by simp [deOwner,hz]
    rw [ho]
    refine (r47_feasD F 2).2 ?_
    rw [F.delta_DE,hz]
    exact hh
  · simpa [deOwner,hz] using F.DE_primary


theorem EH_actual (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    F.cycle.Feasible E F.ehOwner := by
  by_cases hz : F.deError=C.theta H-C.theta D
  · have hh := EH_aligned F hz
    have ho : F.ehOwner=0 := by simp [ehOwner,hz]
    rw [ho]
    refine (r47_feasE F 0).2 ?_
    rw [F.delta_EH,hz,sub_self]
    exact hh
  · simpa [ehOwner,hz] using F.EH_primary


theorem frame_range (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    C.theta D+F.deError∈Icc (min (C.theta D) (C.theta H)) (max (C.theta D) (C.theta H)) := by
  have hDH : C.theta D≤C.theta H := by linarith [F.de_mem.1,F.de_mem.2]
  rw [min_eq_left hDH,max_eq_right hDH]
  constructor <;> linarith [F.de_mem.1,F.de_mem.2]

theorem necessary (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (hn : C.Necessary q) : F.cycle.Necessary q :=
  SignedCycle.necessary_replace_clamped (v := E) (a := D) (b := H)
    hn F.sorted F.outer.le F.core (Or.inr F.frame_range)

theorem normal (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (hn : C.NormalAnchors) : F.cycle.NormalAnchors := by
  constructor
  · rw [(F.unchanged H (by decide)).1]; exact hn.H_nonneg
  · rw [(F.unchanged A (by decide)).1]; exact hn.A_nonneg
  · rw [(F.unchanged B (by decide)).1]; exact hn.B_nonpos
  · rw [(F.unchanged D (by decide)).1]; exact hn.D_nonpos

def witnesses (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (w : C.Witnesses) : F.cycle.Witnesses where
  owner := Function.update (Function.update w.owner D F.deOwner) E F.ehOwner
  feasible i := by
    by_cases hiE : i=E
    · subst i; simpa using F.EH_actual
    · by_cases hiD : i=D
      · subst i; simpa [D,E] using F.DE_actual
      · simpa [Function.update_of_ne hiE,Function.update_of_ne hiD] using
          (F.other_feasible i hiD hiE (w.owner i)).2 (w.feasible i)
  allowed i := by
    by_cases hiE : i=E
    · subst i
      simp [SignedCycle.normalOwners,E,ehOwner]
      exact em _
    · by_cases hiD : i=D
      · subst i
        simp [SignedCycle.normalOwners,D,E,deOwner]
        exact em _
      · simpa [Function.update_of_ne hiE,Function.update_of_ne hiD] using w.allowed i

theorem other_owner (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (w : C.Witnesses) (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
    (F.witnesses w).owner i=w.owner i := by simp [witnesses,hiD,hiE]

theorem zero_signs (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) :
    F.cycle.ZeroSignImplications (F.witnesses w) := by
  constructor
  · intro hj
    rw [(F.unchanged G (by decide)).1]
    apply hz.HG_canceling
    simpa [witnesses,H,D,E] using hj
  · intro hj
    rw [(F.unchanged T (by decide)).1]
    apply hz.TD_canceling
    simpa [witnesses,T,D,E] using hj

theorem positive_variation_eq (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (hDE : 0≤delta C.theta D) (hEH : 0≤delta C.theta E) :
    positiveVariation F.cycle.theta=positiveVariation C.theta := by
  have hd : 0≤C.theta 6-C.theta 5 := hDE
  have he : 0≤C.theta 0-C.theta 6 := hEH
  have hm := F.de_mem
  have h5 : C.theta 5=C.theta D := rfl
  have h0 : C.theta 0=C.theta H := rfl
  have e1 : positivePart (C.theta D+F.deError-C.theta 5)=C.theta D+F.deError-C.theta 5 :=
    max_eq_left (by linarith [hm.1])
  have e2 : positivePart (C.theta 0-(C.theta D+F.deError))=C.theta 0-(C.theta D+F.deError) :=
    max_eq_left (by linarith [hm.2])
  have e3 : positivePart (C.theta 6-C.theta 5)=C.theta 6-C.theta 5 := max_eq_left hd
  have e4 : positivePart (C.theta 0-C.theta 6)=C.theta 0-C.theta 6 := max_eq_left he
  simp [positiveVariation,Fin.sum_univ_succ,delta,next,cycle,replacePoint,
    E,Function.update_apply]
  linarith


theorem negative_variation_eq (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (hDE : 0≤delta C.theta D) (hEH : 0≤delta C.theta E) :
    negativeVariation F.cycle.theta=negativeVariation C.theta := by
  rw [← variations_equal F.cycle.theta,← variations_equal C.theta]
  exact F.positive_variation_eq hDE hEH

def boundaryInput (I : SignedCycle.BoundaryInput q) (hq : q≤qCap)
    (F : Endpoint q (I.cycle.point D) (I.cycle.point H) (I.cycle.theta H-I.cycle.theta D))
    (hDE : 0≤delta I.cycle.theta D) (hEH : 0≤delta I.cycle.theta E) :
    SignedCycle.BoundaryInput q where
  cycle := F.cycle
  necessary := F.necessary I.necessary
  ordered := SignedCycle.normal_necessary_ordered (F.necessary I.necessary) hq
    (F.normal I.anchors_normal) (F.witnesses I.witnesses) (F.zero_signs I.witnesses I.zero_signs)
  strict_spread := SignedCycle.strictSpread_replace_clamped (v := E) (a := D) (b := H)
    (p := F.point) I.strict_spread (Or.inr F.frame_range)
  positive_variation := by rw [F.positive_variation_eq hDE hEH]; exact I.positive_variation
  negative_variation := by rw [F.negative_variation_eq hDE hEH]; exact I.negative_variation
  radial := by
    intro i
    by_cases hi : i=E
    · subst i; exact Or.inl F.outer
    · rw [(F.unchanged i hi).1]; exact I.radial i
  anchors_outer := by
    intro i hi
    have hiE : i≠E := by rintro rfl; exact absurd hi (by decide)
    rw [(F.unchanged i hiE).1]
    exact I.anchors_outer i hi
  anchors_normal := F.normal I.anchors_normal
  witnesses := F.witnesses I.witnesses
  zero_signs := F.zero_signs I.witnesses I.zero_signs

end Endpoint

theorem original_candidate {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hQL : qLow≤q) (hQU : q≤qCap)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1)
    (hd : 0≤delta I.cycle.theta D) (he : 0≤delta I.cycle.theta E)
    (ht0 : 0<I.cycle.theta H-I.cycle.theta D) :
    Nonempty (Endpoint q (I.cycle.point D) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta D)) := by
  have hsum : delta I.cycle.theta D+delta I.cycle.theta E=I.cycle.theta H-I.cycle.theta D := by
    simp [delta,next,D,E,H]
  have ht : I.cycle.theta H-I.cycle.theta D≤7/10 :=
    (le_abs_self _).trans (I.necessary.spread H D)
  have hDE' : quarterFeasible (I.cycle.point D) (I.cycle.point E) (delta I.cycle.theta D) 3 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,D,E,next,
      quarterFeasible,sub_nonneg] using hDE
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H) (delta I.cycle.theta E) 1 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,E,H,next,
      quarterFeasible,sub_nonneg] using hEH
  have hh := candidate hQL hQU (I.necessary.sorted D) (I.anchors_outer D (by simp))
    (I.necessary.sorted H) (I.anchors_outer H (by simp))
    (I.necessary.sorted E) (I.necessary.contained E) hd he
    (by rwa [hsum]) (by rwa [hsum]) hDE' hEH'
  simpa only [hsum] using hh


end SquaresInCircles.Eight.PositiveEPair
end
end
end

section
/-!
## Continuous boundary certificates for the positive-TD2 long-span exclusion

The three intervals are the intrinsic edges of the feasible (t,v) polygon;
they do not subdivide an angle search. Polynomial identities and coefficient
reserves are specified for kernel reduction and have not been executed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.PositiveTDSpanPolynomials
open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

inductive Edge where | zero | short | spread

def lo : Edge → ℚ | .zero => 11/50 | .short => 13/100 | .spread => 61/100
def hi : Edge → ℚ | .zero => 7/10 | .short => 61/100 | .spread => 7/10
def degree : Edge → ℕ | .zero => 10 | .short => 10 | .spread => 11
def reserve : Edge → ℚ | .zero => 11/500 | .short => 4/125 | .spread => 33/500
def center : Edge → ℚ | .zero => 23/50 | .short => 37/100 | .spread => 131/200

def Rbar : ℚ := 494697/250000
def cbar : ℚ := 179843/200000
def kbar : ℚ := 114322/125000
def lambda : ℚ[X] := C (59/100)+C (47/100)*X
def t : Edge → ℚ[X] | .zero => 0 | .short => C (9/100) | .spread => C (7/10)-X
def w : Edge → ℚ[X] | .zero => X-C (11/50) | .short => X-C (13/100) | .spread => C (12/25)
def S5 (x : ℚ[X]) : ℚ[X] := x-C (1/6)*x^3+C (1/120)*x^5
def S7 (x : ℚ[X]) : ℚ[X] := S5 x-C (1/5040)*x^7
def C6 (x : ℚ[X]) : ℚ[X] := 1-C (1/2)*x^2+C (1/24)*x^4-C (1/720)*x^6
def delta (i : Edge) : ℚ[X] := X-C (center i)
def mass0 (i : Edge) : ℚ[X] :=
  match i with
  | .zero => C (1284507/1000000)+C (73747/250000)*delta i+C (26057/500000)*(delta i)^2
  | .short => C (1258389/1000000)+C (8916/31250)*delta i+C (55427/1000000)*(delta i)^2
  | .spread => C (53757/40000)+C (156999/500000)*delta i+C (45503/1000000)*(delta i)^2
def mass1 (i : Edge) : ℚ[X] :=
  match i with
  | .zero => C (966507/1000000)-C (571273/1000000)*delta i-C (61027/200000)*(delta i)^2
  | .short => C (203083/200000)-C (51519/100000)*delta i-C (158721/500000)*(delta i)^2
  | .spread => C (843959/1000000)-C (170729/250000)*delta i-C (263049/1000000)*(delta i)^2
def demand (i : Edge) : ℚ[X] :=
  C (2-cbar)+2*lambda+C (3/2-cbar)*C6 (t i)+C (13/12)*S7 (t i)+C6 X-
    C kbar*S5 (w i)+C (1/2)*C6 (w i)
def radicand0 : ℚ[X] := 1+lambda^2
def radicand1 : ℚ[X] := 1+lambda^2-2*lambda*S7 X
def certificate (i : Edge) : ℚ[X] :=
  2*mass0 i*mass1 i*demand i-C Rbar*
    (mass1 i*(radicand0+(mass0 i)^2)+mass0 i*(radicand1+(mass1 i)^2))

/-- On each edge `certificate i - reserve i` has positive Bernstein coefficients of its degree:
it is a positive combination of the products `(v - lo)^k (hi - v)^(n-k)`, which `linarith`
finds. -/
local macro "edge_positive" a:term:max b:term:max : tactic => `(tactic| (
  intro v hv
  have h0 : 0≤v-$a := sub_nonneg.2 hv.1
  have h1 : 0≤$b-v := sub_nonneg.2 hv.2
  have hb (k l : ℕ) : 0≤(v-$a)^k*($b-v)^l := mul_nonneg (pow_nonneg h0 k) (pow_nonneg h1 l)
  simp only [certificate,mass0,mass1,demand,radicand0,radicand1,lambda,t,w,S5,S7,C6,delta,center,
    Rbar,cbar,kbar,map_add,map_sub,map_mul,map_pow,map_one,map_zero,map_ofNat,aeval_C,aeval_X,
    eq_ratCast]
  push_cast
  linarith [hb 11 0,hb 10 1,hb 9 2,hb 8 3,hb 7 4,hb 6 5,hb 5 6,hb 4 7,hb 3 8,hb 2 9,hb 1 10,
    hb 0 11,hb 10 0,hb 9 1,hb 8 2,hb 7 3,hb 6 4,hb 5 5,hb 4 6,hb 3 7,hb 2 8,hb 1 9,hb 0 10]))

private theorem certificate_positive_zero :
    ∀ {v : ℝ},v∈Set.Icc (11/50:ℝ) (7/10) → (11/500:ℝ)<aeval v (certificate .zero) := by
  edge_positive (11/50) (7/10)
private theorem certificate_positive_short :
    ∀ {v : ℝ},v∈Set.Icc (13/100:ℝ) (61/100) → (4/125:ℝ)<aeval v (certificate .short) := by
  edge_positive (13/100) (61/100)
private theorem certificate_positive_spread :
    ∀ {v : ℝ},v∈Set.Icc (61/100:ℝ) (7/10) → (33/500:ℝ)<aeval v (certificate .spread) := by
  edge_positive (61/100) (7/10)

theorem certificate_positive (i : Edge) {v : ℝ} (hv : v∈Set.Icc (lo i:ℝ) (hi i:ℝ)) :
    (reserve i:ℝ)<aeval v (certificate i) := by
  cases i <;> norm_num [lo,hi,reserve] at hv ⊢
  · exact certificate_positive_zero hv
  · exact certificate_positive_short hv
  · exact certificate_positive_spread hv

theorem masses_positive (i : Edge) {v : ℝ} (hv : v∈Set.Icc (lo i:ℝ) (hi i:ℝ)) :
    0<aeval v (mass0 i) ∧ 0<aeval v (mass1 i) := by
  have h1 : 0≤v-lo i := sub_nonneg.2 hv.1
  have h2 : 0≤(hi i:ℝ)-v := sub_nonneg.2 hv.2
  have h12 := mul_nonneg h1 h2
  have h11 := mul_nonneg h1 h1
  cases i <;>
    simp only [lo,hi,mass0,mass1,delta,center,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,
      eq_ratCast] at h1 h2 h12 h11 ⊢ <;>
    push_cast at h1 h2 h12 h11 ⊢ <;>
    constructor <;> linarith

theorem radical_transfer (i : Edge) {v D R p0 p1 : ℝ}
    (hv : v∈Set.Icc (lo i:ℝ) (hi i:ℝ))
    (hD : aeval v (demand i)≤D) (hR : 0≤R) (hRu : R≤(Rbar:ℝ))
    (hp0 : 0≤p0) (hp1 : 0≤p1)
    (hp0u : p0≤aeval v radicand0) (hp1u : p1≤aeval v radicand1) :
    0<D-R*(Real.sqrt p0+Real.sqrt p1) := by
  obtain ⟨hm0,hm1⟩ := masses_positive i hv
  have hs0 := ScalarRadicalTransfer.sqrt_le_mass_majorant hp0 hm0
  have hs1 := ScalarRadicalTransfer.sqrt_le_mass_majorant hp1 hm1
  have hquot0 := div_le_div_of_nonneg_right
    (add_le_add hp0u (le_refl ((aeval v (mass0 i))^2))) (by positivity : 0≤2*aeval v (mass0 i))
  have hquot1 := div_le_div_of_nonneg_right
    (add_le_add hp1u (le_refl ((aeval v (mass1 i))^2))) (by positivity : 0≤2*aeval v (mass1 i))
  have hsum := add_le_add (hs0.trans hquot0) (hs1.trans hquot1)
  have hmul := mul_le_mul hRu hsum (by positivity) (hR.trans hRu)
  have hpoly := certificate_positive i hv
  have hreserve : (0:ℝ)<(reserve i:ℝ) := by cases i <;> norm_num [reserve]
  have hpolypos : 0<aeval v (certificate i) := hreserve.trans hpoly
  have hid : aeval v (certificate i)/(2*aeval v (mass0 i)*aeval v (mass1 i))=
      aeval v (demand i)-(Rbar:ℝ)*
        ((aeval v radicand0+(aeval v (mass0 i))^2)/(2*aeval v (mass0 i))+
         (aeval v radicand1+(aeval v (mass1 i))^2)/(2*aeval v (mass1 i))) := by
    simp only [certificate,map_sub,map_add,map_mul,map_pow,map_ofNat,aeval_C,eq_ratCast]
    field_simp [hm0.ne',hm1.ne']
  have hpos := div_pos hpolypos (by positivity : 0<2*aeval v (mass0 i)*aeval v (mass1 i))
  rw [hid] at hpos
  linarith

@[simp] theorem lambda_eval (v : ℝ) : aeval v lambda=59/100+(47/100)*v := by simp [lambda]
@[simp] theorem S5_eval (p : ℚ[X]) (v : ℝ) :
    aeval v (S5 p)=aeval v p-(aeval v p)^3/6+(aeval v p)^5/120 := by simp [S5]; ring
@[simp] theorem S7_eval (p : ℚ[X]) (v : ℝ) :
    aeval v (S7 p)=aeval v p-(aeval v p)^3/6+(aeval v p)^5/120-(aeval v p)^7/5040 := by simp [S7]; ring
@[simp] theorem C6_eval (p : ℚ[X]) (v : ℝ) :
    aeval v (C6 p)=1-(aeval v p)^2/2+(aeval v p)^4/24-(aeval v p)^6/720 := by simp [C6]; ring

end SquaresInCircles.Eight.PositiveTDSpanPolynomials
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveTDSpanScalars
open SpanNormBounds PositiveAngularEnvelope

abbrev k : ℝ := EndpointBudgetScalars.k0

def weight (v : ℝ) : ℝ := 59/100+(47/100)*v
def base (t v l : ℝ) : ℝ :=
  TD0Span.f t+2+2*l+Real.cos v-c-R*(N l 0+N l (-v))
def F (t v w : ℝ) : ℝ := base t v (weight v)-EndpointBudgetScalars.positiveGain w

theorem N_formula (l z : ℝ) : N l z=Real.sqrt (1+l^2+2*l*Real.sin z) := by
  unfold N pairNorm
  congr 1
  ring

theorem weight_bounds {v : ℝ} (hv : v∈Icc (13/100:ℝ) frameCap) :
    weight v∈Icc (13/20:ℝ) (23/25) := by
  dsimp [weight,frameCap] at *
  constructor <;> linarith [hv.1,hv.2]

theorem base_as_stress (t v l : ℝ) :
    base t v l=TD0Span.f t+3+2*l-c-2*R*N l 0+V l v := by
  simp [base,SpanNormBounds.V,OrdinaryAngleConcavity.V,SpanNormBounds.N]
  ring

theorem base_fixed (t v : ℝ) :
    base t v TD0Span.lambda=TD0Span.f t+3+2*TD0Span.lambda-c-
      2*R*N TD0Span.lambda 0+V TD0Span.lambda v := base_as_stress t v TD0Span.lambda

theorem norm_weight_deriv {l z : ℝ} (hl : 0<l) (hz : |z|≤frameCap) :
    HasDerivAt (fun a => N a z) ((l+Real.sin z)/N l z) l := by
  have hr := PairNormCalculus.pair_radicand_pos hl (show (0:ℝ)<1 by norm_num) hz
  have hN0 := N_pos hl hz
  have hr0 : 1+l^2+2*l*Real.sin z≠0 := by
    have : 0<1+l^2+2*l*Real.sin z := by nlinarith [hr]
    exact this.ne'
  have h1 : HasDerivAt (fun a : ℝ => a^2) (2*l) l := by simpa using hasDerivAt_pow 2 l
  have h2 : HasDerivAt (fun a : ℝ => 1+a^2+2*a*Real.sin z) (2*l+2*Real.sin z) l := by
    have h := (h1.const_add 1).add ((hasDerivAt_id' l).mul_const (2*Real.sin z))
    have hf : (fun a : ℝ => 1+a^2+2*a*Real.sin z)=fun a => 1+a^2+a*(2*Real.sin z) := by
      funext a; ring
    rw [hf]
    exact h.congr_deriv (by ring)
  have h3 := h2.sqrt hr0
  have hf : (fun a => N a z)=fun a => Real.sqrt (1+a^2+2*a*Real.sin z) := by
    funext a; exact N_formula a z
  rw [hf]
  refine h3.congr_deriv ?_
  have hs : Real.sqrt (1+l^2+2*l*Real.sin z)≠0 := by rw [← N_formula]; exact hN0.ne'
  rw [N_formula]
  field_simp

theorem base_weight_deriv {t v l : ℝ} (hl : 0<l) (hv : |v|≤frameCap) :
    HasDerivAt (base t v)
      (2-R*(l/N l 0+(l-Real.sin v)/N l (-v))) l := by
  have hd0 := norm_weight_deriv hl (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hdv := norm_weight_deriv hl (show |-v|≤frameCap by simpa using hv)
  have hlin : HasDerivAt (fun a : ℝ => TD0Span.f t+2+2*a+Real.cos v-c) (2*1) l :=
    ((((hasDerivAt_id' l).const_mul (2:ℝ)).const_add (TD0Span.f t+2)).add_const
      (Real.cos v)).sub_const c
  have h := hlin.sub ((hd0.add hdv).const_mul R)
  rw [Real.sin_zero,add_zero,Real.sin_neg,← sub_eq_add_neg] at h
  show HasDerivAt (fun a => TD0Span.f t+2+2*a+Real.cos v-c-R*(N a 0+N a (-v))) _ l
  exact h.congr_deriv (by ring)

/-- Positive-square ratio bounds on the whole coefficient rectangle.
They retain the actual norm denominators and have no sampled premise. -/
theorem aligned_ratio_bounds {l v : ℝ}
    (hl : l∈Icc (13/20:ℝ) (7/10)) (hv : v∈Icc (13/100:ℝ) (11/50)) :
    l/N l 0≤1147/2000 ∧ (l-Real.sin v)/N l (-v)≤4987/10000 := by
  have hl0 : 0<l := by linarith [hl.1]
  have hvi : v∈Icc 0 frameCap := ⟨by linarith [hv.1],by norm_num [frameCap] at *; linarith [hv.2]⟩
  have hvabs : |v|≤frameCap := by rw [abs_of_nonneg hvi.1]; exact hvi.2
  have hN0 := N_pos hl0 (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hNv := N_pos hl0 (show |-v|≤frameCap by simpa using hvabs)
  have hZ := N_sq hl0 (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hM := N_sq hl0 (show |-v|≤frameCap by simpa using hvabs)
  simp only [Real.sin_zero,Real.sin_neg] at hZ hM
  have hl2 := pow_le_pow_left₀ hl0.le hl.2 2
  have hs0 : (12963/100000:ℝ)≤Real.sin v := by
    have hs13 := sin_lower_seven (show (0:ℝ)≤13/100 by norm_num)
    have hm := CorrelatedSameBlock.sin_mono
      (show (13/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hvi hv.1
    norm_num at hs13
    linarith
  have hsu : Real.sin v≤11/50 := (Real.sin_le hvi.1).trans hv.2
  have hfirst : l≤(1147/2000)*N l 0 := by
    nlinarith
  have hz0 : 0≤l-Real.sin v := by linarith [hl.1]
  let r : ℝ := 4987/10000
  let z := Real.sin v
  have hfactorA := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hl.2) (show 0≤1-r^2 by norm_num [r]))
    (show 0≤7/10+l-2*z by dsimp [z]; linarith [hl.1])
  have hfactorZ := mul_nonneg (show 0≤z-12963/100000 by exact sub_nonneg.mpr hs0)
    (show 0≤2*(7/10)*(1-r^2)-z-12963/100000 by dsimp [r,z]; linarith)
  have hidA : r^2*(1+l^2-2*l*z)-(l-z)^2-
      (r^2*(1+(7/10:ℝ)^2-2*(7/10)*z)-(7/10-z)^2)=
      (7/10-l)*(1-r^2)*(7/10+l-2*z) := by ring
  have hidZ : r^2*(1+(7/10:ℝ)^2-2*(7/10)*z)-(7/10-z)^2-
      (r^2*(1+(7/10:ℝ)^2-2*(7/10)*(12963/100000))-(7/10-12963/100000)^2)=
      (z-12963/100000)*(2*(7/10)*(1-r^2)-z-12963/100000) := by ring
  have hpoly : 0≤r^2*(1+l^2-2*l*z)-(l-z)^2 := by
    norm_num [r] at hidA hidZ hfactorA hfactorZ ⊢
    linarith
  have hsecond : l-Real.sin v≤(4987/10000)*N l (-v) := by
    apply le_of_sq_le_sq _ (mul_pos (by norm_num) hNv).le
    rw [mul_pow,hM]
    dsimp [r,z] at hpoly
    linarith
  exact ⟨(div_le_iff₀ hN0).2 hfirst,(div_le_iff₀ hNv).2 hsecond⟩

theorem base_weight_lower {l v : ℝ}
    (hl : l∈Icc (13/20:ℝ) (7/10)) (hv : v∈Icc (13/100:ℝ) (11/50)) :
    -(61/500:ℝ)≤2-R*(l/N l 0+(l-Real.sin v)/N l (-v)) := by
  obtain ⟨h0,h1⟩ := aligned_ratio_bounds hl hv
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hm := mul_le_mul_of_nonneg_left (add_le_add h0 h1) hR0
  have hR := radius_bounds.2
  have hmul := mul_le_mul_of_nonneg_right hR.le
    (show (0:ℝ)≤1147/2000+4987/10000 by norm_num)
  linarith

theorem aligned_boundary {v : ℝ} (hv : v∈Icc (13/100:ℝ) (11/50)) :
    0<F (11/50-v) v 0 := by
  have hti : 11/50-v∈Icc 0 (9/100:ℝ) := ⟨by linarith [hv.2],by linarith [hv.1]⟩
  have hvi : v∈Icc 0 frameCap := ⟨by linarith [hv.1],by norm_num [frameCap] at *; linarith [hv.2]⟩
  have hl : weight v∈Icc (13/20:ℝ) (7/10) := by
    dsimp [weight]
    constructor <;> linarith [hv.1,hv.2]
  have hx : (13/20:ℝ)∈Icc (13/20:ℝ) (7/10) := by norm_num
  have hd (l : ℝ) (hl : l∈Icc (13/20:ℝ) (7/10)) :=
    base_weight_deriv (t := 11/50-v) (show 0<l by linarith [hl.1])
      (show |v|≤frameCap by rw [abs_of_nonneg hvi.1]; exact hvi.2)
  have hg := derivative_reserve
    (fun l hl => (hd l hl).continuousAt.continuousWithinAt)
    (fun l hl => hd l (Ioo_subset_Icc_self hl))
    (fun l hl => base_weight_lower (Ioo_subset_Icc_self hl) hv) hx hl hl.1
  have hfixed := TD0Span.scalar_reserve hti hvi (by linarith)
  rw [← base_fixed] at hfixed
  have hdiff : weight v-13/20≤217/5000 := by dsimp [weight]; linarith [hv.2]
  simp [F,EndpointBudgetScalars.positiveGain]
  dsimp [TD0Span.lambda] at hfixed
  linarith

theorem boundary_data (i : PositiveTDSpanPolynomials.Edge) {v : ℝ}
    (hv : v∈Icc (PositiveTDSpanPolynomials.lo i:ℝ) (PositiveTDSpanPolynomials.hi i:ℝ)) :
    Polynomial.aeval v (PositiveTDSpanPolynomials.t i)∈Icc 0 (9/100:ℝ) ∧
      Polynomial.aeval v (PositiveTDSpanPolynomials.w i)∈Icc 0 (12/25:ℝ) ∧
      v∈Icc (13/100:ℝ) frameCap := by
  obtain ⟨h1,h2⟩ := hv
  cases i <;>
  · simp only [PositiveTDSpanPolynomials.lo,PositiveTDSpanPolynomials.hi,
      PositiveTDSpanPolynomials.t,PositiveTDSpanPolynomials.w,map_zero,map_sub,
      Polynomial.aeval_X,Polynomial.aeval_C,eq_ratCast,frameCap,Set.mem_Icc] at h1 h2 ⊢
    push_cast at h1 h2 ⊢
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_,?_⟩ <;> linarith

theorem polynomial_boundary (i : PositiveTDSpanPolynomials.Edge) {v : ℝ}
    (hv : v∈Icc (PositiveTDSpanPolynomials.lo i:ℝ) (PositiveTDSpanPolynomials.hi i:ℝ)) :
    0<F (Polynomial.aeval v (PositiveTDSpanPolynomials.t i)) v
      (Polynomial.aeval v (PositiveTDSpanPolynomials.w i)) := by
  obtain ⟨ht,hw,hvi⟩ := boundary_data i hv
  obtain ⟨T,hT⟩ : ∃ T, Polynomial.aeval v (PositiveTDSpanPolynomials.t i)=T := ⟨_,rfl⟩
  obtain ⟨W,hW⟩ : ∃ W, Polynomial.aeval v (PositiveTDSpanPolynomials.w i)=W := ⟨_,rfl⟩
  rw [hT] at ht
  rw [hW] at hw
  rw [hT,hW]
  have hv0 : 0≤v := by linarith [hvi.1]
  have hl := weight_bounds hvi
  have hl0 : 0<weight v := by linarith [hl.1]
  have hsT := sin_lower_seven ht.1
  have hcT := cos_lower_six ht.1
  have hcV := cos_lower_six hv0
  have hsV := sin_lower_seven hv0
  have hsW := sin_upper_five hw.1
  have hcW := cos_lower_six hw.1
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have ht6 := pow_le_pow_left₀ ht.1 ht.2 6
  norm_num at ht2 ht6
  have hct0 : 0≤1-T^2/2+T^4/24-T^6/720 := by
    linarith [pow_nonneg ht.1 4]
  have hc := diagonal_bounds.2
  have hcoef := mul_le_mul
    (show (3/2-179843/200000:ℝ)≤3/2-c by linarith) hcT hct0 (show (0:ℝ)≤3/2-c by linarith)
  have hsW0 : 0≤Real.sin W :=
    Real.sin_nonneg_of_nonneg_of_le_pi hw.1 (by linarith [hw.2,Real.pi_gt_three])
  have hk := EndpointBudgetScalars.radical_bounds.2.1
  have hkS := mul_le_mul hk.le hsW hsW0 (by norm_num : (0:ℝ)≤914576/1000000)
  have hdem : Polynomial.aeval v (PositiveTDSpanPolynomials.demand i)=
      (2-179843/200000)+2*(59/100+(47/100)*v)
      +(3/2-179843/200000)*(1-T^2/2+T^4/24-T^6/720)
      +(13/12)*(T-T^3/6+T^5/120-T^7/5040)
      +(1-v^2/2+v^4/24-v^6/720)
      -(114322/125000)*(W-W^3/6+W^5/120)
      +(1/2)*(1-W^2/2+W^4/24-W^6/720) := by
    simp only [PositiveTDSpanPolynomials.demand,map_add,map_sub,map_mul,map_ofNat,
      Polynomial.aeval_C,eq_ratCast,PositiveTDSpanPolynomials.lambda_eval,
      PositiveTDSpanPolynomials.C6_eval,PositiveTDSpanPolynomials.S5_eval,
      PositiveTDSpanPolynomials.S7_eval,Polynomial.aeval_X,hT,hW,
      PositiveTDSpanPolynomials.cbar,PositiveTDSpanPolynomials.kbar]
    push_cast
    ring
  have hD : Polynomial.aeval v (PositiveTDSpanPolynomials.demand i)≤
      TD0Span.f T+2+2*weight v+Real.cos v-c-EndpointBudgetScalars.positiveGain W := by
    rw [hdem]
    simp only [TD0Span.f,EndpointBudgetScalars.positiveGain,weight]
    linarith only [hc,hcoef,hsT,hcV,hkS,hcW]
  have hp0 : 0≤1+(weight v)^2 := by positivity
  have hp1 : 0≤1+(weight v)^2-2*weight v*Real.sin v := by
    have hp := PairNormCalculus.pair_radicand_pos hl0 (show (0:ℝ)<1 by norm_num)
      (show |-v|≤frameCap by rw [abs_neg,abs_of_nonneg hv0]; exact hvi.2)
    simp only [one_pow,Real.sin_neg] at hp
    linarith
  have hp0u : 1+(weight v)^2≤Polynomial.aeval v PositiveTDSpanPolynomials.radicand0 := by
    simp [PositiveTDSpanPolynomials.radicand0,weight]
  have hp1u : 1+(weight v)^2-2*weight v*Real.sin v≤
      Polynomial.aeval v PositiveTDSpanPolynomials.radicand1 := by
    have hm := mul_le_mul_of_nonneg_left hsV (show 0≤2*weight v by positivity)
    have he : Polynomial.aeval v PositiveTDSpanPolynomials.radicand1=
        1+(weight v)^2-2*weight v*(v-v^3/6+v^5/120-v^7/5040) := by
      simp only [PositiveTDSpanPolynomials.radicand1,map_sub,map_add,map_one,map_pow,map_mul,
        map_ofNat,PositiveTDSpanPolynomials.lambda_eval,PositiveTDSpanPolynomials.S7_eval,
        Polynomial.aeval_X,weight]
    rw [he]
    linarith only [hm]
  have hRu : R≤((PositiveTDSpanPolynomials.Rbar:ℚ):ℝ) := by
    rw [show ((PositiveTDSpanPolynomials.Rbar:ℚ):ℝ)=494697/250000 by
      norm_num [PositiveTDSpanPolynomials.Rbar]]
    exact radius_bounds.2.le
  have hpos := PositiveTDSpanPolynomials.radical_transfer i hv hD
    (show (0:ℝ)≤R from Real.sqrt_nonneg qCap) hRu hp0 hp1 hp0u hp1u
  have hN0 : N (weight v) 0=Real.sqrt (1+(weight v)^2) := by
    rw [N_formula,Real.sin_zero]; congr 1; ring
  have hNv : N (weight v) (-v)=Real.sqrt (1+(weight v)^2-2*weight v*Real.sin v) := by
    rw [N_formula,Real.sin_neg]; congr 1; ring
  simp only [F,base,hN0,hNv]
  linarith only [hpos]

theorem gain_deriv (w : ℝ) :
    HasDerivAt EndpointBudgetScalars.positiveGain
      (k*Real.cos w+(1/2)*Real.sin w) w := by
  have h1 : HasDerivAt (fun x => k*Real.sin x) (k*Real.cos w) w :=
    (Real.hasDerivAt_sin w).const_mul _
  have h2 : HasDerivAt (fun x => (1-Real.cos x)/2) ((0- -Real.sin w)/2) w :=
    ((hasDerivAt_const w (1:ℝ)).sub (Real.hasDerivAt_cos w)).div_const 2
  have hfun : EndpointBudgetScalars.positiveGain=fun x => k*Real.sin x+(1-Real.cos x)/2 := by
    funext x; rfl
  rw [hfun]
  exact (h1.add h2).congr_deriv (by ring)

theorem gain_monotone : MonotoneOn EndpointBudgetScalars.positiveGain (Icc 0 (12/25:ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
  · unfold EndpointBudgetScalars.positiveGain
    fun_prop
  · exact fun w _ => gain_deriv w
  · intro w hw
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig
      (show w∈Icc 0 frameCap by constructor <;> norm_num [frameCap] at * <;> linarith [hw.1,hw.2])
    have hk0 : 0≤k := by linarith [EndpointBudgetScalars.radical_bounds.1]
    exact add_nonneg (mul_nonneg hk0 (by linarith)) (mul_nonneg (by norm_num) hs0)

theorem gain_curvature {w : ℝ} (hw : w∈Icc 0 (12/25:ℝ)) :
    0≤(1/2)*Real.cos w-k*Real.sin w := by
  have hwi : w∈Icc 0 frameCap := ⟨hw.1,by norm_num [frameCap] at *; linarith [hw.2]⟩
  have he : (12/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hcos := CorrelatedSameBlock.cos_anti hwi he hw.2
  have hsin := CorrelatedSameBlock.sin_mono hwi he hw.2
  have hc48 := cos_lower_six (show (0:ℝ)≤12/25 by norm_num)
  have hs48 := sin_upper_five (show (0:ℝ)≤12/25 by norm_num)
  have hm := mul_le_mul EndpointBudgetScalars.radical_bounds.2.1.le (hsin.trans hs48)
    (transport_trig hwi).2.2.1 (by norm_num : (0:ℝ)≤914576/1000000)
  norm_num at hc48 hm
  linarith

/-- Concavity is in the short negative-GA error with v fixed. The weight
therefore stays fixed throughout this analytic comparison. -/
theorem fixed_v_concave {v : ℝ} (_hv : v∈Icc (13/100:ℝ) frameCap) :
    ConcaveOn ℝ (Icc (max 0 (11/50-v)) (min (9/100) (frameCap-v)))
      (fun t => F t v (t+v-11/50)) := by
  have hd1 : ∀ x, HasDerivAt (fun t => F t v (t+v-11/50))
      (-(3/2-c)*Real.sin x+(13/12)*Real.cos x-
        (k*Real.cos (x+v-11/50)+(1/2)*Real.sin (x+v-11/50))) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => t+v-11/50) 1 x :=
      ((hasDerivAt_id' x).add_const v).sub_const (11/50)
    have hg0 := (gain_deriv (x+v-11/50)).comp x hlin
    have hg : HasDerivAt (fun t => EndpointBudgetScalars.positiveGain (t+v-11/50))
        ((k*Real.cos (x+v-11/50)+(1/2)*Real.sin (x+v-11/50))*1) x := hg0
    have hf : HasDerivAt (fun t => TD0Span.f t+2+2*weight v+Real.cos v-c-
        R*(N (weight v) 0+N (weight v) (-v)))
        (-(3/2-c)*Real.sin x+(13/12)*Real.cos x) x :=
      (((((TD0Span.f_deriv x).add_const 2).add_const (2*weight v)).add_const
        (Real.cos v)).sub_const c).sub_const _
    exact (hf.sub hg).congr_deriv (by ring)
  have hd2 : ∀ x, HasDerivAt (fun x => -(3/2-c)*Real.sin x+(13/12)*Real.cos x-
        (k*Real.cos (x+v-11/50)+(1/2)*Real.sin (x+v-11/50)))
      (-(3/2-c)*Real.cos x-(13/12)*Real.sin x+k*Real.sin (x+v-11/50)-
        (1/2)*Real.cos (x+v-11/50)) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => t+v-11/50) 1 x :=
      ((hasDerivAt_id' x).add_const v).sub_const (11/50)
    have hs : HasDerivAt (fun t => Real.sin (t+v-11/50)) (Real.cos (x+v-11/50)*1) x :=
      (Real.hasDerivAt_sin _).comp x hlin
    have hc : HasDerivAt (fun t => Real.cos (t+v-11/50)) (-Real.sin (x+v-11/50)*1) x :=
      (Real.hasDerivAt_cos _).comp x hlin
    have h := (((Real.hasDerivAt_sin x).const_mul (-(3/2-c))).add
      ((Real.hasDerivAt_cos x).const_mul (13/12:ℝ))).sub
      ((hc.const_mul k).add (hs.const_mul (1/2:ℝ)))
    exact h.congr_deriv (by ring)
  apply concave_of_deriv2 (fun x _ => hd1 x) (fun x _ => hd2 x)
  intro t ht
  have ht0 : 0≤t := (le_max_left _ _).trans ht.1
  have ht9 : t≤9/100 := ht.2.trans (min_le_left _ _)
  have hw0 : 0≤t+v-11/50 := by linarith [(le_max_right (0:ℝ) (11/50-v)).trans ht.1]
  have hw48 : t+v-11/50≤12/25 := by
    have h := ht.2.trans (min_le_right (9/100:ℝ) (frameCap-v))
    norm_num [frameCap] at h
    linarith
  have hcurv := gain_curvature ⟨hw0,hw48⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig
    (show t∈Icc 0 frameCap by constructor <;> norm_num [frameCap] at * <;> linarith)
  have hm := mul_nonneg (show 0≤3/2-c by linarith [diagonal_bounds.2])
    (show 0≤Real.cos t by linarith)
  nlinarith

/-- Strict positivity on the entire original scalar polygon, including
its four intrinsic boundary faces and all weak frame ties. -/
theorem domain_positive {t v w : ℝ}
    (ht : t∈Icc 0 (9/100:ℝ)) (hv : v∈Icc (13/100:ℝ) frameCap)
    (htv : 11/50≤t+v ∧ t+v≤frameCap)
    (hw : w∈Icc 0 (t+v-11/50)) : 0<F t v w := by
  let l := max 0 (11/50-v)
  let r := min (9/100) (frameCap-v)
  have htr : t∈Icc l r := by
    constructor
    · exact max_le ht.1 (by linarith [htv.1])
    · exact le_min ht.2 (by linarith [htv.2])
  have hlr : l≤r := htr.1.trans htr.2
  have hleft : 0<F l v (l+v-11/50) := by
    by_cases h : 11/50≤v
    · have hl : l=0 := max_eq_left (by linarith)
      rw [hl]
      have hb := polynomial_boundary PositiveTDSpanPolynomials.Edge.zero
        (show v∈Icc (PositiveTDSpanPolynomials.lo .zero:ℝ) (PositiveTDSpanPolynomials.hi .zero:ℝ) by
          simpa [PositiveTDSpanPolynomials.lo,PositiveTDSpanPolynomials.hi,frameCap] using And.intro h hv.2)
      simpa [PositiveTDSpanPolynomials.t,PositiveTDSpanPolynomials.w] using hb
    · have hl : l=11/50-v := max_eq_right (by linarith)
      rw [hl]
      have hzero : (11/50-v)+v-11/50=0 := by ring
      rw [hzero]
      exact aligned_boundary ⟨hv.1,by linarith⟩
  have hright : 0<F r v (r+v-11/50) := by
    by_cases h : v≤61/100
    · have hr : r=9/100 := min_eq_left (by dsimp [frameCap]; linarith)
      rw [hr]
      have hb := polynomial_boundary PositiveTDSpanPolynomials.Edge.short
        (show v∈Icc (PositiveTDSpanPolynomials.lo .short:ℝ) (PositiveTDSpanPolynomials.hi .short:ℝ) by
          simpa [PositiveTDSpanPolynomials.lo,PositiveTDSpanPolynomials.hi] using And.intro hv.1 h)
      convert hb using 1
      simp [PositiveTDSpanPolynomials.t,PositiveTDSpanPolynomials.w]
      ring
    · have hr : r=frameCap-v := min_eq_right (by dsimp [frameCap]; linarith)
      rw [hr]
      have hb := polynomial_boundary PositiveTDSpanPolynomials.Edge.spread
        (show v∈Icc (PositiveTDSpanPolynomials.lo .spread:ℝ) (PositiveTDSpanPolynomials.hi .spread:ℝ) by
          simpa [PositiveTDSpanPolynomials.lo,PositiveTDSpanPolynomials.hi,frameCap] using
            And.intro (by linarith : (61/100:ℝ)≤v) hv.2)
      convert hb using 1
      simp [PositiveTDSpanPolynomials.t,PositiveTDSpanPolynomials.w,frameCap]
      ring
  have hconc := fixed_v_concave hv
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr hlr) (right_mem_Icc.mpr hlr) htr
  have hp : 0<F t v (t+v-11/50) := (lt_min hleft hright).trans_le hmin
  have hlarge : t+v-11/50∈Icc 0 (12/25:ℝ) := by
    constructor <;> norm_num [frameCap] at * <;> linarith [htv.1,htv.2]
  have hsmall : w∈Icc 0 (12/25:ℝ) := ⟨hw.1,hw.2.trans hlarge.2⟩
  have hm := gain_monotone hsmall hlarge hw.2
  dsimp [F] at hp ⊢
  linarith

end SquaresInCircles.Eight.PositiveTDSpanScalars
end
end
end
