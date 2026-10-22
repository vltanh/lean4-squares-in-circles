module

public import SquaresInCircles.Eight.TableFree.GlobalGATargetSmallTangent
public import SquaresInCircles.Eight.TableFree.GlobalGAOwners
public import SquaresInCircles.Eight.TableFree.BinaryDiagonalExclusion

/-!
# The actual source domain for the complete high-GA owner matrix

Uncompiled transcription of Section 2 of
`HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md`. A putative original high GA witness
is retained exactly. The other six witnesses are the initially selected
physical axes. Every radial, sign, variation, sorting and A-target premise
used by the high-GA scalar matrix is derived on the unchanged source.

The final theorem assembles the original normal-owner restriction once
the remaining GA restriction has been proved. It does not assert that
the still-unfinished high-GA sign matrix has already been excluded.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree
open Candidate

namespace GlobalGA

/-- Necessary high-GA data at the original boundary radius. The retained
owners can be used directly by the signed-total dispatch; the record has
no exclusion, scalar reserve, or hard-owner conclusion as a field. -/
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

/-- Replace the chosen GA index only. Every other edge keeps its literal
originally selected forward-axis index, including weak ties. -/
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

/-- Exact source construction. All four outer equations use q; the
auxiliary ceiling inside the cited obstructions supplies only impossibility
and is never substituted for the original circle equality. -/
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

/-- No physical normal on a non-GA edge is changed by selecting the
putative high witness used in the contradiction. -/
theorem sourceDomain_original_normal {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (j : Fin 4) (hj : j=2∨j=3)
    (hGA : (forwardAxis j).Feasible (C.square G) (C.square A))
    (i : Vertex) (hi : i≠G) :
    (forwardAxis ((sourceDomain F hq hE j hj hGA).owner i)).normal
      ((SignedCycle.atFrame F).actualSquare i) ((SignedCycle.atFrame F).actualSquare (next i))=
      (C.selected i).normal (C.square i) (C.square (next i)) := by
  change (forwardAxis (sourceOwner F j i)).normal _ _=_
  rw [sourceOwner_other F j hi]
  exact SignedCycle.retainedOwner_normal F i

end GlobalGA

namespace GlobalOriginalOwners

/-- The other six original owner classes have already been proved.
This joins the remaining all-witness GA restriction to the exact
normal-owner predicate consumed by original-source recovery. -/
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
end SquaresInCircles.Eight.TableFree
