module

public import SquaresInCircles.Eight.TableFree.NearestAxisRecode
public import SquaresInCircles.Eight.TableFree.FramePhysicalTransport
public import SquaresInCircles.Eight.TableFree.QuarterDoubleExclusion
public import SquaresInCircles.Eight.TableFree.BoundaryRealization

/-!
# An actual candidate-word E point is strictly sorted

Both nearest-axis representations at E are genuine boundary cycles.  At
positive tangent the other representation puts a double on EH; at negative
tangent it puts a double on DE.  The complete common-quarter inequalities
exclude those words.  No binary wrong-word exclusion, E-owner assumption,
or E-sign normalization is used.

The argument applies to every original radius between 5/2 and Q0 and to
transport descendants before any frame normalization at A.  Uncompiled
source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate

namespace EDiagonalExclusion

/-- Strict spread supplies a lift with the displayed candidate integers.
There is no extra normalization of the given real angles. -/
theorem offsetLift_exists {q : ℝ} (C : BoundaryCycle q) (theta : Vertex→ℝ)
    (hs : ∀ i j,|theta i-theta j|<7/10)
    (hr : ∀ i,C.canonicalAngle i=theta i+(offsets i:ℝ)*(Real.pi/2)) :
    ∃ F : QuarterLift C,F.theta=theta ∧ F.quarter=offsets := by
  classical
  obtain ⟨l,hlmem,hl⟩ := Finset.exists_min_image Finset.univ theta Finset.univ_nonempty
  obtain ⟨u,humem,hu⟩ := Finset.exists_max_image Finset.univ theta Finset.univ_nonempty
  have hlo (i : Vertex) : theta l≤theta i := hl i (Finset.mem_univ _)
  have hhi (i : Vertex) : theta i≤theta u := hu i (Finset.mem_univ _)
  refine ⟨{
    theta := theta
    quarter := offsets
    left := theta l
    diameter := theta u-theta l
    small := (abs_lt.mp (hs u l)).2
    theta_range := fun i => ⟨hlo i,by linarith [hhi i]⟩
    represents := hr },rfl,rfl⟩

/-- Expansion is used solely to invoke the actual common-quarter proof
at its fixed ceiling.  It keeps the source's integer lift unchanged. -/
theorem increment_ne_two {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C) (i : Vertex) :
    integerQuarterIncrement F.quarter i≠2 := by
  intro hi
  let D := FramePhysicalTransport.auxiliary C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F
    (FramePhysicalTransport.auxiliary_expansion C hq)
  have hg : ∀ j,19/25<angleGap D.beta j := boundary_gap_lower D le_rfl
  have hword : G.word hg pi_lt_22_over_7 i=2 := by
    apply Fin.ext
    have hc := G.word_cast hg pi_lt_22_over_7 i
    have he : integerQuarterIncrement G.quarter i=2 := hi
    rw [he] at hc
    omega
  exact TableFreeWordGeometry.no_double D G hg ⟨i,hword⟩

/-- At E either tangent sign creates an actual double increment after
the other nearest-axis choice. -/
theorem of_offsetLift {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C)
    (hm : F.quarter=offsets) : C.b E<C.a E := by
  by_contra! hbad
  have hd : C.b E=C.a E := le_antisymm (C.b_le_a E) hbad
  let J := NearestAxisRecode.cycle C E hd
  let H := NearestAxisRecode.lift F E hd
  rcases C.sigma_sign E with hs | hs
  · have hh : integerQuarterIncrement H.quarter D=2 := by
      change integerQuarterIncrement (NearestAxisRecode.lift F E hd).quarter D=2
      rw [NearestAxisRecode.increment,hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,D,E,next,hs]
    exact increment_ne_two J hq H D hh
  · have hh : integerQuarterIncrement H.quarter E=2 := by
      change integerQuarterIncrement (NearestAxisRecode.lift F E hd).quarter E=2
      rw [NearestAxisRecode.increment,hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,E,next,hs]
    exact increment_ne_two J hq H E hh

theorem of_frame {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) : C.b E<C.a E := by
  obtain ⟨G,hGtheta,hGquarter⟩ := offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro i; simpa only [mul_div_assoc] using F.canonical_eq i)
  exact of_offsetLift C hq G hGquarter

end EDiagonalExclusion

namespace SignedCycle

/-- This version needs just physical boundary geometry and one genuine
weak owner per edge.  The normal-owner and anchor records are not used. -/
theorem E_strictly_sorted {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀ i,(C.point i).Boundary q)
    (owner : Vertex→Fin 4) (hf : ∀ i,C.Feasible i (owner i)) :
    |(C.point E).y|<(C.point E).a := by
  let K := C.realizeBoundary hn ho hr owner hf
  obtain ⟨F,hFtheta,hFquarter⟩ := EDiagonalExclusion.offsetLift_exists K C.theta
    (by simpa only [StrictSpread,frameCap] using hs)
    (by
      intro i
      change (C.realizeBoundary hn ho hr owner hf).canonicalAngle i=_
      simpa only [actualAngle,mul_div_assoc] using
        C.realizeBoundary_canonicalAngle hn ho hr owner hf i)
  exact EDiagonalExclusion.of_offsetLift K
    (by simpa only [qCap,Q0] using hq) F hFquarter

namespace BoundaryInput

theorem E_strictly_sorted {q : ℝ} (I : BoundaryInput q)
    (hq : q∈Icc (5/2:ℝ) qCap) :
    |(I.cycle.point E).y|<(I.cycle.point E).a :=
  I.cycle.E_strictly_sorted hq I.necessary I.ordered I.strict_spread I.radial
    I.witnesses.owner I.witnesses.feasible

/-- A same-radius transport endpoint with an E diagonal is therefore
impossible even when its incident E owners differ from those of its source. -/
theorem E_not_diagonal {q : ℝ} (I : BoundaryInput q)
    (hq : q∈Icc (5/2:ℝ) qCap) :
    |(I.cycle.point E).y|≠(I.cycle.point E).a :=
  ne_of_lt (I.E_strictly_sorted hq)

end BoundaryInput
end SignedCycle
end SquaresInCircles.Eight.TableFree
