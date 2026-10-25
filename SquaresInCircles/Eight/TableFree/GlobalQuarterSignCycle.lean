module

public import SquaresInCircles.Eight.TableFree.GlobalQuarterSignSupport
public import SquaresInCircles.Eight.TableFree.GlobalZeroSignBridge

/-!
# Original quarter-owner signs and the global DE restriction

The complete local boosts are joined to six unchanged original G1 pair
bounds and the physical frame return path.  Fixed-ray expansion preserves
every retained weak axis and both source signs.  The final statements
therefore concern the original radius and original physical normals.

For a quarter edge, every original owner in `{0,1}` forces a strictly
positive target; every owner in `{2,3}` forces a strictly negative source.
In particular a nonpositive E forces the original DE owners and strict
D sign without any other owner, anchor, or frame-order input.  Uncompiled
source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree
open Candidate

namespace GlobalQuarterSign

open FramePair TableFreeWordGeometry

private theorem one_word (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hi : integerQuarterIncrement F.quarter i=1) :
    F.word hgap pi_lt_22_over_7 i=1 := by
  apply Fin.ext
  have hh := F.word_cast hgap pi_lt_22_over_7 i
  rw [hi] at hh
  omega

theorem ceiling_target_positive (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4) (hj : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    0<C.tangent (next i) := by
  by_contra! hbad
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  have hz : phaseValue F hgap i=Real.pi/2+difference F i := by
    simp [phaseValue,one_word C F hgap i hi,add_comm]
  have hp : pairAngle C i=Real.pi/2+difference F i := by
    have hh := phase_gap C F hgap i
    rw [hz] at hh
    linarith [pairAngle_gap C i]
  have hm := stateOf_feasible C i j haxis
  rw [hp] at hm
  have hy : sign (stateOf C (next i)).positive*(stateOf C (next i)).b≤0 := by
    have hn : C.sigma (next i)*C.b (next i)≤0 := by
      have hh := (div_le_iff₀ (C.a_pos (next i))).1 hbad
      simpa only [zero_mul] using hh
    simpa only [stateOf,signOf_spec] using hn
  have hb := target_nonpos_boost (stateOf C i) (stateOf C (next i))
    (by simpa only [frameCap] using (difference_small F i).le) hy j hj hm
  apply GlobalZeroSign.closed_boost_impossible C F hgap i
  simpa only [hz] using hb

theorem ceiling_source_negative (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.tangent i<0 := by
  by_contra! hbad
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  have hz : phaseValue F hgap i=Real.pi/2+difference F i := by
    simp [phaseValue,one_word C F hgap i hi,add_comm]
  have hp : pairAngle C i=Real.pi/2+difference F i := by
    have hh := phase_gap C F hgap i
    rw [hz] at hh
    linarith [pairAngle_gap C i]
  have hm := stateOf_feasible C i j haxis
  rw [hp] at hm
  have hy : 0≤ sign (stateOf C i).positive*(stateOf C i).b := by
    have hn : 0≤C.sigma i*C.b i := by
      have hh := (le_div_iff₀ (C.a_pos i)).1 hbad
      simpa only [zero_mul] using hh
    simpa only [stateOf,signOf_spec] using hn
  have hb := source_nonneg_boost (stateOf C i) (stateOf C (next i))
    (by simpa only [frameCap] using (difference_small F i).le) hy j hj hm
  apply GlobalZeroSign.closed_boost_impossible C F hgap i
  simpa only [hz] using hb

theorem target_positive {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4) (hj : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    0<C.tangent (next i) := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hinc : integerQuarterIncrement G.quarter i=1 := hi
  have hh := ceiling_target_positive D G i hinc j hj
    (hR.preserves_all_axes i (forwardAxis j) haxis)
  simpa only [hR.same_tangents] using hh

theorem source_negative {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.tangent i<0 := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hinc : integerQuarterIncrement G.quarter i=1 := hi
  have hh := ceiling_source_negative D G i hinc j hj
    (hR.preserves_all_axes i (forwardAxis j) haxis)
  simpa only [hR.same_tangents] using hh

/-- Every original quarter owner, including each member of a weak tie. -/
theorem classify {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ((j=0 ∨ j=1) ∧ 0<C.tangent (next i)) ∨
      ((j=2 ∨ j=3) ∧ C.tangent i<0) := by
  fin_cases j
  · exact Or.inl ⟨Or.inl rfl,target_positive C hq F i hi 0 (Or.inl rfl) haxis⟩
  · exact Or.inl ⟨Or.inr rfl,target_positive C hq F i hi 1 (Or.inr rfl) haxis⟩
  · exact Or.inr ⟨Or.inl rfl,source_negative C hq F i hi 2 (Or.inl rfl) haxis⟩
  · exact Or.inr ⟨Or.inr rfl,source_negative C hq F i hi 3 (Or.inr rfl) haxis⟩

theorem of_offsetLift {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets)
    (i : Vertex) (hi : word i=1) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ((j=0 ∨ j=1) ∧ 0<C.tangent (next i)) ∨
      ((j=2 ∨ j=3) ∧ C.tangent i<0) := by
  have hinc : integerQuarterIncrement F.quarter i=1 := by
    rw [hm,GlobalZeroSign.offset_increment,hi]
  exact classify C hq F i hinc j haxis

theorem of_frame {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ((j=0 ∨ j=1) ∧ 0<C.tangent (next i)) ∨
      ((j=2 ∨ j=3) ∧ C.tangent i<0) := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  exact of_offsetLift C hq G hGquarter i hi j haxis

/-- A weakly nonpositive quarter target determines all original owners
and the strict source sign, with no prescribed sign at the source. -/
theorem frame_target_nonpos {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (ht : C.tangent (next i)≤0) :
    C.tangent i<0 ∧ ∀j : Fin 4,
      (forwardAxis j).Feasible (C.square i) (C.square (next i)) → j=2 ∨ j=3 := by
  have heach (j : Fin 4)
      (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
      (j=2 ∨ j=3) ∧ C.tangent i<0 := by
    rcases of_frame F hq i hi j hj with ⟨_,hn⟩ | hh
    · exact (not_lt_of_ge ht hn).elim
    · exact hh
  obtain ⟨j,hj⟩ := F.forward_complete i (C.selected i) (C.feasible i)
  have haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [hj] using C.feasible i
  exact ⟨(heach j haxis).2,fun j hj => (heach j hj).1⟩

theorem frame_DE {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0) :
    C.tangent D<0 ∧ ∀j : Fin 4,
      (forwardAxis j).Feasible (C.square D) (C.square E) → j=2 ∨ j=3 := by
  simpa [D,E,next] using frame_target_nonpos F hq D (by norm_num [word,D])
    (by simpa [D,E,next] using hE)

end GlobalQuarterSign

namespace SignedCycle

theorem quarter_owner_classification {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex→Fin 4) (hf : ∀ i,C.Feasible i (owner i))
    (i : Vertex) (hi : word i=1) (j : Fin 4) (hj : C.Feasible i j) :
    ((j=0 ∨ j=1) ∧ 0<(C.point (next i)).y) ∨
      ((j=2 ∨ j=3) ∧ (C.point i).y<0) := by
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
  rcases GlobalQuarterSign.of_offsetLift K (by simpa only [qCap,Q0] using hq)
      F hFquarter i hi j haxis with ⟨hj0,hy⟩ | ⟨hj2,hy⟩
  · refine Or.inl ⟨hj0,?_⟩
    rw [htangent] at hy
    have hh := (lt_div_iff₀ (hn.sorted (next i)).1).1 hy
    simpa only [zero_mul] using hh
  · refine Or.inr ⟨hj2,?_⟩
    rw [htangent] at hy
    have hh := (div_lt_iff₀ (hn.sorted i).1).1 hy
    simpa only [zero_mul] using hh

/-- Global D negativity and DE classification on an actual signed
boundary source, before all-normal-owner or anchor classification. -/
theorem DE_owners_and_sign {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex→Fin 4) (hf : ∀ i,C.Feasible i (owner i))
    (hE : (C.point E).y≤0) :
    (C.point D).y<0 ∧ ∀j : Fin 4,C.Feasible D j → j=2 ∨ j=3 := by
  have heach (j : Fin 4) (hj : C.Feasible D j) :
      (j=2 ∨ j=3) ∧ (C.point D).y<0 := by
    rcases C.quarter_owner_classification hq hn ho hs hr owner hf D
        (by norm_num [word,D]) j hj with ⟨_,hy⟩ | hh
    · have hbad : 0<(C.point E).y := by simpa [D,E,next] using hy
      exact (not_lt_of_ge hE hbad).elim
    · exact hh
  exact ⟨(heach (owner D) (hf D)).2,fun j hj => (heach j hj).1⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
