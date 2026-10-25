module

public import SquaresInCircles.Eight.Frames.PhysicalTransport
public import SquaresInCircles.Eight.Owners.E.DiagonalExclusion
public import SquaresInCircles.Eight.Owners.Zero.SignSupport
public import SquaresInCircles.Eight.Words.Zero.PrimaryCycle

/-!
# Eight squares: original candidate and signed-cycle zero-owner classification

These adapters retain the actual radius, points, real frame angles and
feasible axes.  They infer the HG and TD canceling sign implications
from geometry, including on boundary transport descendants before A
has been rotated to zero.  Normal-owner or anchor-sign hypotheses are
not used in the geometric classification.
-/

section
/-!
## Strict signs for every original zero-quarter secondary owner

A wrong-sign secondary owner costs more than `1` after the original
common vertex markers and the frame return allowance are included.
The six other actual edges cost more than `6*.8833`; the same closed
frame tour pays the return allowance.  The resulting total exceeds
`2*pi`.

The conclusion quantifies over every originally feasible weak axis.
Radius expansion is used only inside this contradiction and preserves
the original tangent and integer quarter increment.  No other owner,
anchor sign, vertex order, or frame-error sign is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalZeroSign

open FramePair QuarterWordGeometry

theorem closed_boost_impossible (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hboost : 1<phaseValue F hgap i+(stateOf C i).signedLabel-
      (stateOf C (next i)).signedLabel+(9/50)*frameCost |difference F i|) : False := by
  let g : Vertex → ℝ := fun k => phaseValue F hgap k+
    (stateOf C k).signedLabel-(stateOf C (next k)).signedLabel
  let v : Vertex → ℝ := fun k => frameCost |difference F k|
  have hb : 1<g i+(9/50)*v i := hboost
  have hother (k : Vertex) : (8833/10000:ℝ)<g k-(9/50)*v k := by
    have hh := (ZeroPrimary.handGamma_lower (branchOf C k).type
      (branchOf C (next k)).type).trans_lt (FrameAllPairs.all_pair C k)
    simpa only [ZeroPrimary.frame_pair_cost C F hgap k,g,v] using hh
  have hc : (Finset.univ.erase i : Finset Vertex).card=6 := by simp
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ.erase i : Finset Vertex))
    (Finset.card_pos.1 (by omega))
    (fun k _ => hother k)
  have hcost : (∑k,g k)=2*Real.pi := marker_budget C F hgap
    (fun k => (stateOf C k).signedLabel)
  have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := g) (Finset.mem_univ i)
  have hreturn : v i≤∑k∈(Finset.univ.erase i : Finset Vertex),v k :=
    ZeroPrimary.frame_edge_le_return F i
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,hc,nsmul_eq_mul] at hsum
  rw [hcost] at hsplit
  push_cast at hsum
  linarith [Arithmetic.two_pi_lt_710_over_113]

private theorem zero_word (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hi : integerQuarterIncrement F.quarter i=0) :
    F.word hgap pi_lt_22_over_7 i=0 := by
  apply Fin.ext
  have hh := F.word_cast hgap pi_lt_22_over_7 i
  rw [hi] at hh
  omega

theorem ceiling_source_positive (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (haxis : (forwardAxis 0).Feasible (C.square i) (C.square (next i))) :
    0<C.tangent i := by
  by_contra! hbad
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  have hz : phaseValue F hgap i=difference F i := by
    simp [phaseValue,zero_word C F hgap i hi]
  have hp : pairAngle C i=difference F i := by
    have hh := phase_gap C F hgap i
    rw [hz] at hh
    linarith [pairAngle_gap C i]
  have hm := stateOf_feasible C i 0 haxis
  rw [hp] at hm
  have hy : sign (stateOf C i).positive*(stateOf C i).b≤0 := by
    have hn : C.sigma i*C.b i≤0 := by
      have hh := (div_le_iff₀ (C.a_pos i)).1 hbad
      simpa only [zero_mul] using hh
    simpa only [stateOf,signOf_spec] using hn
  have hb := source_secondary_boost (stateOf C i) (stateOf C (next i))
    (by simpa only [frameCap] using (difference_small F i).le) hy hm
  apply closed_boost_impossible C F hgap i
  simpa only [hz] using hb

theorem ceiling_target_negative (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (haxis : (forwardAxis 2).Feasible (C.square i) (C.square (next i))) :
    C.tangent (next i)<0 := by
  by_contra! hbad
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  have hz : phaseValue F hgap i=difference F i := by
    simp [phaseValue,zero_word C F hgap i hi]
  have hp : pairAngle C i=difference F i := by
    have hh := phase_gap C F hgap i
    rw [hz] at hh
    linarith [pairAngle_gap C i]
  have hm := stateOf_feasible C i 2 haxis
  rw [hp] at hm
  have hy : 0≤ sign (stateOf C (next i)).positive*(stateOf C (next i)).b := by
    have hn : 0≤C.sigma (next i)*C.b (next i) := by
      have hh := (le_div_iff₀ (C.a_pos (next i))).1 hbad
      simpa only [zero_mul] using hh
    simpa only [stateOf,signOf_spec] using hn
  have hb := target_secondary_boost (stateOf C i) (stateOf C (next i))
    (by simpa only [frameCap] using (difference_small F i).le) hy hm
  apply closed_boost_impossible C F hgap i
  simpa only [hz] using hb

/-- The original source tangent is strictly positive for every weak
source-secondary zero-quarter owner, at every permitted radius. -/
theorem source_positive {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (haxis : (forwardAxis 0).Feasible (C.square i) (C.square (next i))) :
    0<C.tangent i := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hinc : integerQuarterIncrement G.quarter i=0 := hi
  have hh := ceiling_source_positive D G i hinc
    (hR.preserves_all_axes i (forwardAxis 0) haxis)
  simpa only [hR.same_tangents] using hh

/-- The original target tangent is strictly negative for every weak
target-secondary zero-quarter owner.  A zero transverse coordinate is
excluded by the same strict cycle reserve. -/
theorem target_negative {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (haxis : (forwardAxis 2).Feasible (C.square i) (C.square (next i))) :
    C.tangent (next i)<0 := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hinc : integerQuarterIncrement G.quarter i=0 := hi
  have hh := ceiling_target_negative D G i hinc
    (hR.preserves_all_axes i (forwardAxis 2) haxis)
  simpa only [hR.same_tangents] using hh

/-- Primary exclusion also concerns every original weak axis and uses
the concrete full-domain common-quarter bound on all six return edges. -/
theorem secondary {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    j=0 ∨ j=2 := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  let hgap : ∀k,19/25<angleGap D.beta k := boundary_gap_lower D le_rfl
  have hinc : integerQuarterIncrement G.quarter i=0 := hi
  exact ZeroPrimary.original_zero_secondary D G hgap (FrameAllPairs.all_pair D)
    i (zero_word D G hgap i hinc) j (hR.preserves_all_axes i (forwardAxis j) haxis)

/-- Complete original-axis classification on a zero-quarter edge.
Simultaneous weak owners retain both of their strict sign consequences. -/
theorem classify {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (j=0 ∧ 0<C.tangent i) ∨ (j=2 ∧ C.tangent (next i)<0) := by
  rcases secondary C hq F i hi j haxis with rfl | rfl
  · exact Or.inl ⟨rfl,source_positive C hq F i hi haxis⟩
  · exact Or.inr ⟨rfl,target_negative C hq F i hi haxis⟩

end SquaresInCircles.Eight.GlobalZeroSign
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight
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
end SquaresInCircles.Eight
end
end
end
