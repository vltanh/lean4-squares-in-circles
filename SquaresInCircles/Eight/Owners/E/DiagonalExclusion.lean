module

public import SquaresInCircles.Eight.Frames.NearestAxisRecode
public import SquaresInCircles.Eight.Frames.PhysicalTransport
public import SquaresInCircles.Eight.Words.QuarterDoubleExclusion
public import SquaresInCircles.Eight.Boundary.Realization

/-!
# Eight squares: the point E is strictly sorted

A point E on its diagonal has two nearest-axis representations, and both give boundary cycles. At
positive tangent the other representation puts a double increment on EH, at negative tangent on
DE (`of_offsetLift`); the common-quarter inequalities exclude these words (`increment_ne_two`).
So E is strictly sorted (`SignedCycle.E_strictly_sorted`), with no assumption on the owners at E
or on the sign of E.

The argument applies at every radius between `5/2` and `Q0`, and to the endpoints of transports
before any normalization of the frame at A (`BoundaryInput.E_not_diagonal`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate

namespace EDiagonalExclusion

/-- Real angles of spread below `7/10` that represent the canonical angles with the offsets
`offsets` give a quarter lift with these angles and offsets. -/
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

/-- No quarter increment of a lift of a boundary cycle at a radius in `[5/2, Q0]` is `2`.
Expansion to `Q0` brings the common-quarter inequalities to their ceiling and keeps the integer
lift. -/
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
  exact QuarterWordGeometry.no_double D G hg ⟨i,hword⟩

/-- A lift with the offsets `offsets` has `C.b E < C.a E`: at E either sign of the tangent creates
a double increment for the other nearest-axis choice. -/
theorem of_offsetLift {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C)
    (hm : F.quarter=offsets) : C.b E<C.a E := by
  by_contra! hbad
  have hd : C.b E=C.a E := le_antisymm (C.b_le_a E) hbad
  let J := NearestAxisRecode.cycle C E hd
  let H := NearestAxisRecode.lift F E hd
  rcases C.sigma_sign E with hs | hs
  all_goals have hs6 : C.sigma 6=_ := hs
  · have hh : integerQuarterIncrement H.quarter D=2 := by
      change integerQuarterIncrement (NearestAxisRecode.lift F E hd).quarter D=2
      rw [NearestAxisRecode.increment,hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,D,E,next,hs6]
    exact increment_ne_two J hq H D hh
  · have hh : integerQuarterIncrement H.quarter E=2 := by
      change integerQuarterIncrement (NearestAxisRecode.lift F E hd).quarter E=2
      rw [NearestAxisRecode.increment,hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,E,next,hs6]
    exact increment_ne_two J hq H E hh

theorem of_frame {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) : C.b E<C.a E := by
  obtain ⟨G,hGtheta,hGquarter⟩ := offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro i; simpa only [mul_div_assoc] using F.canonical_eq i)
  exact of_offsetLift C hq G hGquarter

end EDiagonalExclusion

namespace SignedCycle

/-- A necessary ordered cycle with strict spread, points on the boundary and one weak owner per
edge has `|E.y| < E.a`. -/
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

/-- The point E of a boundary input is off its diagonal, whatever the owners of the edges at E. -/
theorem E_not_diagonal {q : ℝ} (I : BoundaryInput q)
    (hq : q∈Icc (5/2:ℝ) qCap) :
    |(I.cycle.point E).y|≠(I.cycle.point E).a :=
  ne_of_lt (I.E_strictly_sorted hq)

end BoundaryInput
end SignedCycle
end SquaresInCircles.Eight
