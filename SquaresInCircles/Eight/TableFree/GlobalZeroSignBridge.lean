module

public import SquaresInCircles.Eight.TableFree.GlobalZeroSignCycle
public import SquaresInCircles.Eight.TableFree.EDiagonalExclusion

/-!
# Original candidate and signed-cycle zero-owner classification

These adapters retain the actual radius, points, real frame angles and
feasible axes.  They infer the HG and TD canceling sign implications
from geometry, including on boundary transport descendants before A
has been rotated to zero.  Normal-owner or anchor-sign hypotheses are
not used in the geometric classification.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree
open Candidate

namespace GlobalZeroSign

theorem offset_increment (i : Vertex) : integerQuarterIncrement offsets i=word i := by
  fin_cases i <;> norm_num [integerQuarterIncrement,offsets,word,next]

theorem of_offsetLift {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets)
    (i : Vertex) (hi : word i=0) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (j=0 ∧ 0<C.tangent i) ∨ (j=2 ∧ C.tangent (next i)<0) := by
  have hinc : integerQuarterIncrement F.quarter i=0 := by
    rw [hm,offset_increment,hi]
  exact classify C hq F i hinc j haxis

/-- All three zero edges and all feasible original axes are quantified;
the frame has no middle-order or outer-sign requirement. -/
theorem of_frame {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=0) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (j=0 ∧ 0<C.tangent i) ∨ (j=2 ∧ C.tangent (next i)<0) := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  exact of_offsetLift C hq G hGquarter i hi j haxis

theorem frame_source_positive {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=0)
    (haxis : (forwardAxis 0).Feasible (C.square i) (C.square (next i))) :
    0<C.tangent i := by
  rcases of_frame F hq i hi 0 haxis with ⟨_,hh⟩ | ⟨hn,_⟩
  · exact hh
  · norm_num at hn

theorem frame_target_negative {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=0)
    (haxis : (forwardAxis 2).Feasible (C.square i) (C.square (next i))) :
    C.tangent (next i)<0 := by
  rcases of_frame F hq i hi 2 haxis with ⟨hn,_⟩ | ⟨_,hh⟩
  · norm_num at hn
  · exact hh

end GlobalZeroSign

namespace SignedCycle

/-- The signed source has the same original-axis classification.  This
statement needs no chosen normal-owner family and no A-frame alignment. -/
theorem zero_owner_classification {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex→Fin 4) (hf : ∀ i,C.Feasible i (owner i))
    (i : Vertex) (hi : word i=0) (j : Fin 4) (hj : C.Feasible i j) :
    (j=0 ∧ 0<(C.point i).y) ∨ (j=2 ∧ (C.point (next i)).y<0) := by
  let K := C.realizeBoundary hn ho hr owner hf
  obtain ⟨F,hFtheta,hFquarter⟩ := EDiagonalExclusion.offsetLift_exists K C.theta
    (by simpa only [StrictSpread,frameCap] using hs)
    (by
      intro k
      change (C.realizeBoundary hn ho hr owner hf).canonicalAngle k=_
      simpa only [actualAngle,mul_div_assoc] using
        C.realizeBoundary_canonicalAngle hn ho hr owner hf k)
  have haxis : (forwardAxis j).Feasible (K.square i) (K.square (next i)) :=
    (C.realizeBoundary_feasible_iff hn ho hr owner hf i j).2 hj
  have htangent (k : Vertex) : K.tangent k=(C.point k).y/(C.point k).a := by
    simp only [K,BoundaryCycle.tangent,realizeBoundary,SignedPoint.canonicalSign_mul_abs]
  rcases GlobalZeroSign.of_offsetLift K (by simpa only [qCap,Q0] using hq)
      F hFquarter i hi j haxis with ⟨hj0,hy⟩ | ⟨hj2,hy⟩
  · refine Or.inl ⟨hj0,?_⟩
    rw [htangent] at hy
    have hh := (lt_div_iff₀ (hn.sorted i).1).1 hy
    simpa only [zero_mul] using hh
  · refine Or.inr ⟨hj2,?_⟩
    rw [htangent] at hy
    have hh := (div_lt_iff₀ (hn.sorted (next i)).1).1 hy
    simpa only [zero_mul] using hh

/-- The two zero-owner implications in the sharp source record are
consequences of the original geometry, not extra source hypotheses. -/
theorem zero_signs_of_boundary {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀ i,(C.point i).Boundary q)
    (w : C.Witnesses) : C.ZeroSignImplications w := {
  HG_canceling h := by
    have hf : C.Feasible H 2 := by simpa only [h] using w.feasible H
    have hh := C.zero_owner_classification hq hn ho hs hr w.owner w.feasible
      H (by norm_num [word,H]) 2 hf
    rcases hh with ⟨hn,_⟩ | ⟨_,hy⟩
    · norm_num at hn
    · simpa [H,G,next] using hy
  TD_canceling h := by
    have hf : C.Feasible T 0 := by simpa only [h] using w.feasible T
    have hh := C.zero_owner_classification hq hn ho hs hr w.owner w.feasible
      T (by norm_num [word,T]) 0 hf
    rcases hh with ⟨_,hy⟩ | ⟨hn,_⟩
    · exact hy
    · norm_num at hn }

theorem atFrame_zero_signs {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (w : (atFrame F).Witnesses) :
    (atFrame F).ZeroSignImplications w :=
  (atFrame F).zero_signs_of_boundary (by simpa only [qCap,Q0] using hq)
    (atFrame_necessary F) (atFrame_ordered F) (atFrame_strictSpread F)
    (atFrame_boundary F) w

end SignedCycle
end SquaresInCircles.Eight.TableFree
