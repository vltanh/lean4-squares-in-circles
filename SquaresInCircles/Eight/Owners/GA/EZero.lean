module

public import SquaresInCircles.Eight.Owners.OriginalOwners
public import SquaresInCircles.Eight.Owners.GA.Owners
public import SquaresInCircles.Eight.Owners.GA.Target.SmallTangent

/-!+# The zero-E boundary is impossible in the actual high-GA domain

Reflection and reversal send each original high GA separator to an actual
low BT separator.  At E=0 the reflected E chart is still nonpositive, so
the already proved complete BT exclusion applies to a realization of the
same signed boundary-neighbor system.  No nonneighbor separator and no
normal-source owner assumption is introduced.
-/

section
/-!
## The source domain of a high GA witness

A `SourceDomain` keeps a putative high GA witness, GA2 or GA3, as it is, and the separating axes
selected by the frame on the other six edges (`sourceOwner`). `sourceDomain` derives on the boundary
cycle, at the same `q`, every radial, sign, variation, sorting and A-target hypothesis that the
high-GA scalar arguments use.

`normal_owners_of_GA_low` gives the normal owner of every edge once every feasible GA witness is
one of the two low axes.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight
open Candidate

namespace GlobalGA

/-- The high-GA data of a signed cycle at the boundary radius `q`: one feasible owner per edge, the
necessary conditions, the order and spread, the variation budgets, the radial kinds, and the signs
and sortings of the points. The owners serve directly in the signed-total dispatch. -/
structure SourceDomain (q : ℝ) (C : SignedCycle) where
  owner : Vertex → Fin 4
  feasible : ∀i,C.Feasible i (owner i)
  allowed : ∀i,owner i∈highGAOwners i
  necessary : C.Necessary q
  ordered : C.Ordered
  strict_spread : C.StrictSpread
  positive_variation : positiveVariation C.theta<frameCap
  negative_variation : negativeVariation C.theta<frameCap
  radial : ∀i,(C.point i).Boundary q
  outer : ∀i∈({H,G,B,D} : Finset Vertex),(C.point i).Outer q
  H_positive : 0<(C.point H).y
  G_negative : (C.point G).y<0
  B_negative : (C.point B).y<0
  D_negative : (C.point D).y<0
  E_nonpos : (C.point E).y≤0
  A_upper : (C.point A).y<1/2
  A_nonpos_outer : (C.point A).y≤0 → (C.point A).Outer q
  internal_sorted : ∀i,i=G∨i=A∨i=B∨i=T∨i=E → |(C.point i).y|<(C.point i).a

/-- The owners with the GA index set to `j`. Every other edge keeps the forward-axis index selected
by the frame, weak ties included. -/
def sourceOwner {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (j : Fin 4) (i : Vertex) : Fin 4 :=
  if i=G then j else SignedCycle.retainedOwner F i

@[simp] theorem sourceOwner_G {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (j : Fin 4) : sourceOwner F j G=j := by
  simp [sourceOwner]

theorem sourceOwner_other {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (j : Fin 4) {i : Vertex} (hi : i≠G) :
    sourceOwner F j i=SignedCycle.retainedOwner F i := by
  simp [sourceOwner,hi]

theorem sourceOwner_feasible {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (j : Fin 4)
    (hGA : (forwardAxis j).Feasible (C.square G) (C.square A)) :
    ∀i,(SignedCycle.atFrame F).Feasible i (sourceOwner F j i) := by
  intro i
  by_cases hi : i=G
  · subst i
    rw [sourceOwner_G]
    exact (SignedCycle.atFrame_feasible F G j).2 (by simpa [G,A,next] using hGA)
  · rw [sourceOwner_other F j hi]
    exact SignedCycle.retainedOwner_feasible F i

theorem sourceOwner_allowed {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (j : Fin 4) (hj : j=2∨j=3) :
    ∀i,sourceOwner F j i∈highGAOwners i := by
  intro i
  by_cases hi : i=G
  · subst i
    rcases hj with rfl|rfl <;> simp [sourceOwner,highGAOwners,G]
  · rw [highGAOwners_eq_normal hi,sourceOwner_other F j hi]
    exact GlobalOriginalOwners.frame_other_owners F hq hE i hi
      (SignedCycle.retainedOwner F i)
      ((SignedCycle.atFrame_feasible F i _).1 (SignedCycle.retainedOwner_feasible F i))

/-- The source domain of a frame with a feasible high GA witness. All four outer equations use `q`;
the auxiliary ceiling inside the cited obstructions gives only impossibility and never takes the
place of the circle equality. -/
def sourceDomain {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (j : Fin 4) (hj : j=2∨j=3)
    (hGA : (forwardAxis j).Feasible (C.square G) (C.square A)) :
    SourceDomain q (SignedCycle.atFrame F) := by
  obtain ⟨hH,hHy,hB,hBy,hD,hDy⟩ := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G
    (by norm_num [word,G]) j hj (by simpa [G,A,next] using hGA)
  have hGo := SignedCycle.atFrame_outer_of_kind F G hG.1
  have hv := FramePhysicalTransport.candidate_variations F hq
  refine {
    owner := sourceOwner F j
    feasible := sourceOwner_feasible F j hGA
    allowed := sourceOwner_allowed F hq hE j hj
    necessary := SignedCycle.atFrame_necessary F
    ordered := SignedCycle.atFrame_ordered F
    strict_spread := SignedCycle.atFrame_strictSpread F
    positive_variation := hv.1
    negative_variation := hv.2
    radial := SignedCycle.atFrame_boundary F
    outer := ?_
    H_positive := hHy
    G_negative := (SignedCycle.atFrame_y_neg_iff F G).2 hG.2
    B_negative := hBy
    D_negative := hDy
    E_nonpos := (SignedCycle.atFrame_y_nonpos_iff F E).2 hE
    A_upper := Target.frame_target_small F hq hE j hj hGA
    A_nonpos_outer := ?_
    internal_sorted := ?_ }
  · intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hH
    · exact hGo
    · exact hB
    · exact hD
  · intro hA
    exact SignedCycle.atFrame_outer_of_kind F A
      (GlobalZeroSourceOuter.frame_nonpositive_source_outer F hq A
        (by norm_num [word,A]) ((SignedCycle.atFrame_y_nonpos_iff F A).1 hA))
  · intro i hi
    rcases hi with hG|hA|hB|hT|hE
    · simpa only [SignedCycle.atFrame,Candidate.signed_b_abs] using
        BinaryDiagonalExclusion.of_frame F hq i (Or.inl hG)
    · simpa only [SignedCycle.atFrame,Candidate.signed_b_abs] using
        BinaryDiagonalExclusion.of_frame F hq i (Or.inr (Or.inl hA))
    · simpa only [SignedCycle.atFrame,Candidate.signed_b_abs] using
        BinaryDiagonalExclusion.of_frame F hq i (Or.inr (Or.inr (Or.inl hB)))
    · simpa only [SignedCycle.atFrame,Candidate.signed_b_abs] using
        BinaryDiagonalExclusion.of_frame F hq i (Or.inr (Or.inr (Or.inr hT)))
    · subst i
      simpa only [SignedCycle.atFrame,Candidate.signed_b_abs] using
        EDiagonalExclusion.of_frame F hq

end GlobalGA

namespace GlobalOriginalOwners

/-- The owners of the other six edges are restricted by `frame_other_owners`; with every feasible
GA witness low, every edge has its normal owner. -/
theorem normal_owners_of_GA_low {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hGA : ∀j : Fin 4,(forwardAxis j).Feasible (C.square G) (C.square A) → j=0∨j=1) :
    Candidate.OwnerRestriction C SignedCycle.normalOwners := by
  intro i j hj
  by_cases hi : i=G
  · subst i
    have hh := hGA j (by simpa [G,A,next] using hj)
    rcases hh with rfl|rfl <;> simp [SignedCycle.normalOwners,G]
  · exact frame_other_owners F hq hE i hi j hj

end GlobalOriginalOwners
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA
open Candidate SignedCycle

/-- This statement applies to actual transported boundary neighbors as
well as to the original cycle.  The reflected A frame is identically zero,
so realization preserves the reflected real frames exactly. -/
theorem zero_E_false {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ho : C.Ordered) (hs : C.StrictSpread)
    (hr : ∀i,(C.point i).Boundary q)
    (owner : Vertex → Fin 4) (hf : ∀i,C.Feasible i (owner i))
    (hq : q∈Icc (5/2:ℝ) Q0) (hE : (C.point E).y=0)
    (j : Fin 4) (hj : j=2 ∨ j=3) (hGA : C.Feasible G j) : False := by
  let owner' : Vertex → Fin 4 := fun i => reflectedOwner (owner (reflectedIndex (next i)))
  have hf' (i : Vertex) : C.reflected.Feasible i (owner' i) :=
    (reflected_feasible C i _).2 (hf _)
  have hr' (i : Vertex) : (C.reflected.point i).Boundary q := by
    simpa [reflected] using hr (reflectedIndex i)
  have hs' : C.reflected.StrictSpread := by
    intro i k
    have hh := hs (reflectedIndex k) (reflectedIndex i)
    simpa [reflected,show C.theta B-C.theta (reflectedIndex i)-
      (C.theta B-C.theta (reflectedIndex k))=
      C.theta (reflectedIndex k)-C.theta (reflectedIndex i) by ring] using hh
  have hA' : C.reflected.theta A=0 := by simp [reflected,reflectedIndex,A,B]
  let K := C.reflected.realizeBoundary hn.reflected ho.reflected hr' owner' hf'
  let F : Candidate.Frame K := C.reflected.realizedFrame hn.reflected ho.reflected
    hr' owner' hf' hq.2 hs' hA'
  have hE6 : (C.point 6).y=0 := hE
  have hE' : K.tangent E≤0 := by
    simp [K,BoundaryCycle.tangent,realizeBoundary,reflected,reflectedIndex,E,
      SignedPoint.reflect,hE6]
  have hBT : C.reflected.Feasible B (reflectedOwner j) := by
    have hh := (reflected_feasible C B j).2
      (by simpa [reflectedIndex,next,B,T,G] using hGA)
    exact hh
  have hBT' : (forwardAxis (reflectedOwner j)).Feasible (K.square B) (K.square T) := by
    have hh := (C.reflected.realizeBoundary_feasible_iff hn.reflected ho.reflected
      hr' owner' hf' B (reflectedOwner j)).2 hBT
    simpa [K,next,B,T] using hh
  have hclass := GlobalBT.frame_BT_high F hq hE' (reflectedOwner j) hBT'
  rcases hj with rfl | rfl <;> norm_num [reflectedOwner] at hclass

theorem SourceDomain.E_negative {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q∈Icc (5/2:ℝ) Q0) : (C.point E).y<0 := by
  apply lt_of_le_of_ne I.E_nonpos
  intro he
  have hj : I.owner G=2 ∨ I.owner G=3 := by
    simpa [highGAOwners,G] using I.allowed G
  exact zero_E_false I.necessary I.ordered I.strict_spread I.radial I.owner I.feasible
    hq he (I.owner G) hj (I.feasible G)

end SquaresInCircles.Eight.GlobalGA
end
end
end
