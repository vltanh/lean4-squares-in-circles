module

public import SquaresInCircles.Eight.Boundary.Reduction
public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Words.Basic

/-!
# Eight squares: the squares of a signed cycle

A signed cycle describes seven squares (`actualSquare`): the square of a vertex has the centre of
its signed point and the frame angle `actualAngle`. Consecutive frame angles differ by the
quarter of the candidate word plus the frame step, less a full turn on the last edge
(`actualAngle_difference`); the full turn disappears in the sine and the cosine of the relative
angle (`actualSquare_relative_trig`). The slack of a forward axis `j` on an edge is the
separating-axis slack of the two squares along that axis (`actualSquare_margin`,
`actualSquare_feasible`), and a square lies in the disk of squared radius `q` exactly when its
point is contained (`actualSquare_contained_iff`). These identities hold for every signed cycle,
also one that is not a boundary cycle, with no condition on the signs of the transverse
coordinates.
-/

section
/-!
## The other nearest axis at a diagonal

When the square `v` of a boundary cycle lies on the diagonal, `b v = a v`, its two nearest axes
give two canonical frames of the same square (`choice`). Recoding `v` with the other axis gives a
boundary cycle at the same level, on the same radial curves, with the same centres, radial kinds
and centre directions (`cycle`, `center`, `radial_kind`, `rays`); every witness is carried over
with its normal, not chosen again. The canonical angle of `v` changes by a quarter turn
(`canonicalAngle`), and a quarter lift of the cycle gives one of the recoded cycle with the same
real frames, only the integer quarters changing (`lift`). The quarter word of the recoded cycle
follows from that of `C` by an equality of quarter increments (`increment`, `word_cast`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.NearestAxisRecode

def turn {q : ℝ} (C : BoundaryCycle q) (v i : Vertex) : Fin 4 :=
  if i=v then if C.sigma v=1 then 3 else 1 else 0

def shift {q : ℝ} (C : BoundaryCycle q) (v i : Vertex) : ℤ :=
  if i=v then if C.sigma v=1 then -1 else 1 else 0

def sign {q : ℝ} (C : BoundaryCycle q) (v i : Vertex) : ℝ :=
  if i=v then -C.sigma i else C.sigma i

/-- The canonical frames with the other nearest axis at `v`; the equality `b v = a v` serves only
to exchange the two equal coordinates of `v`. -/
def choice {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) (i : Vertex) : CanonicalSquare (C.square i) where
  quarter := turn C v i
  a := C.a i
  b := C.b i
  sigma := sign C v i
  a_pos := C.a_pos i
  b_nonneg := C.b_nonneg i
  b_le_a := C.b_le_a i
  sigma_sign := by
    by_cases hi : i=v
    · subst i
      rcases C.sigma_sign v with hs | hs
      · exact Or.inr (by simp [sign,hs])
      · exact Or.inl (by simp [sign,hs])
    · simpa [sign,hi] using C.sigma_sign i
  center_eq := by
    rw [C.center_eq i]
    by_cases hi : i=v
    · subst i
      have h1 : (-1:ℝ) ≠ 1 := by norm_num
      rcases C.sigma_sign v with hs | hs <;>
        apply Prod.ext <;>
        simp [turn,sign,hs,turnSquare,rotate,hd,h1] <;> ring
    · simp [turn,sign,hi,turnSquare]

/-- The boundary cycle recoded at `v`: the same squares, at the same level and on the same radial
curves. -/
def cycle {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) : BoundaryCycle q where
  square i := turnSquare (turn C v i) (C.square i)
  contained i := by
    change phi (alpha (turnSquare (turn C v i) (C.square i)) (0,0))
      (beta (turnSquare (turn C v i) (C.square i)) (0,0))≤q
    rw [turnSquare_phi]
    exact C.contained i
  core i p hp := C.core i p
    ((turnSquare_sameSquare (turn C v i) (C.square i)).2 p |>.mp hp)
  selected i := transportQuarterAxis (turn C v i) (turn C v (next i)) (C.selected i)
  feasible i := transportQuarterAxis_feasible (C.feasible i)
  kind := C.kind
  a := C.a
  b := C.b
  sigma := sign C v
  a_pos := C.a_pos
  b_nonneg := C.b_nonneg
  b_le_a := C.b_le_a
  sigma_sign i := (choice C v hd i).sigma_sign
  center_eq i := (choice C v hd i).center_eq
  boundary := C.boundary
  beta := C.beta
  center_cos := C.center_cos
  center_sin := C.center_sin
  frame_cos i := by
    have hx : (C.square i).center.1=
        Real.sqrt (normSq (C.square i).center)*Real.cos (C.beta i) := by
      rw [(choice C v hd i).radius_sq]
      exact C.center_cos i
    have hy : (C.square i).center.2=
        Real.sqrt (normSq (C.square i).center)*Real.sin (C.beta i) := by
      rw [(choice C v hd i).radius_sq]
      exact C.center_sin i
    exact ((choice C v hd i).frame_polar hx hy).1
  frame_sin i := by
    have hx : (C.square i).center.1=
        Real.sqrt (normSq (C.square i).center)*Real.cos (C.beta i) := by
      rw [(choice C v hd i).radius_sq]
      exact C.center_cos i
    have hy : (C.square i).center.2=
        Real.sqrt (normSq (C.square i).center)*Real.sin (C.beta i) := by
      rw [(choice C v hd i).radius_sq]
      exact C.center_sin i
    exact ((choice C v hd i).frame_polar hx hy).2
  gap_pos := C.gap_pos
  gap_lt_pi := C.gap_lt_pi

@[simp] theorem center {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) (i : Vertex) :
    ((cycle C v hd).square i).center=(C.square i).center := rfl

@[simp] theorem radial_kind {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) : (cycle C v hd).kind=C.kind := rfl

@[simp] theorem rays {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) : (cycle C v hd).beta=C.beta := rfl

theorem canonicalAngle {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) (i : Vertex) :
    (cycle C v hd).canonicalAngle i=
      C.canonicalAngle i+(shift C v i:ℝ)*(Real.pi/2) := by
  by_cases hi : i=v
  · subst i
    have ha : C.a v≠0 := ne_of_gt (C.a_pos v)
    have h1 : (-1:ℝ) ≠ 1 := by norm_num
    rcases C.sigma_sign v with hs | hs <;>
      simp [BoundaryCycle.canonicalAngle,BoundaryCycle.alpha,BoundaryCycle.tangent,
        cycle,sign,shift,hs,hd,ha,h1,Real.arctan_neg,Real.arctan_one] <;> ring
  · simp [BoundaryCycle.canonicalAngle,BoundaryCycle.alpha,BoundaryCycle.tangent,
      cycle,sign,shift,hi]

/-- The quarter lift of the recoded cycle: the same real lift, with the same diameter and
differences; only the integer representative changes. -/
def lift {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (v : Vertex) (hd : C.b v=C.a v) : QuarterLift (cycle C v hd) where
  theta := F.theta
  quarter i := F.quarter i+shift C v i
  left := F.left
  diameter := F.diameter
  small := F.small
  theta_range := F.theta_range
  represents i := by
    change (cycle C v hd).canonicalAngle i=_
    rw [canonicalAngle]
    change C.beta i+C.alpha i+_=_
    rw [F.represents]
    simp only [Int.cast_add]
    ring

theorem increment {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (v : Vertex) (hd : C.b v=C.a v) (i : Vertex) :
    integerQuarterIncrement (lift F v hd).quarter i=
      integerQuarterIncrement F.quarter i+shift C v (next i)-shift C v i := by
  simp only [integerQuarterIncrement,lift]
  ring

theorem word_cast {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C)
    (v : Vertex) (hd : C.b v=C.a v)
    (hg : ∀ i,19/25<angleGap C.beta i) (hp : Real.pi<22/7) (i : Vertex) :
    (((lift F v hd).word hg hp i).val:ℤ)=
      ((F.word hg hp i).val:ℤ)+shift C v (next i)-shift C v i := by
  rw [QuarterLift.word_cast (lift F v hd) hg hp i,QuarterLift.word_cast F hg hp i,increment]

end SquaresInCircles.Eight.NearestAxisRecode
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
namespace SignedCycle
open Candidate

def actualAngle (C : SignedCycle) (i : Vertex) : ℝ :=
  C.theta i+(Candidate.offsets i : ℝ)*Real.pi/2

theorem actualAngle_difference (C : SignedCycle) (i : Vertex) :
    C.actualAngle (next i)-C.actualAngle i =
      Candidate.phi C.theta i-(if i=6 then 2*Real.pi else 0) := by
  fin_cases i <;>
    simp [actualAngle,Candidate.phi,Candidate.word,Candidate.delta,
      Candidate.offsets,next] <;> ring

theorem actualSquare_relative_trig (C : SignedCycle) (i : Vertex) :
    relativeC (C.actualSquare i) (C.actualSquare (next i)) =
        Real.cos (Candidate.phi C.theta i) ∧
      relativeS (C.actualSquare i) (C.actualSquare (next i)) =
        Real.sin (Candidate.phi C.theta i) := by
  have hc : relativeC (C.actualSquare i) (C.actualSquare (next i)) =
      Real.cos (C.actualAngle (next i)-C.actualAngle i) := by
    simp [relativeC,actualSquare,SignedPoint.square,actualAngle,Real.cos_sub]
    ring
  have hs : relativeS (C.actualSquare i) (C.actualSquare (next i)) =
      Real.sin (C.actualAngle (next i)-C.actualAngle i) := by
    simp [relativeS,actualSquare,SignedPoint.square,actualAngle,Real.sin_sub]
    ring
  rw [actualAngle_difference] at hc hs
  by_cases hi : i=6
  · simpa [hi,Real.cos_sub,Real.sin_sub] using And.intro hc hs
  · simpa [hi] using And.intro hc hs

/-- The projection on the forward axis `j` less the separation threshold is the slack
`C.slack i j`: the signed transverse coordinates are the local coordinates of the squares, so
the signs in `forwardMargin` are both `1`. -/
theorem actualSquare_margin (C : SignedCycle) (i : Vertex) (j : Fin 4) :
    (forwardAxis j).projection (C.actualSquare i) (C.actualSquare (next i)) -
      SAT.threshold (C.actualSquare i) (C.actualSquare (next i)) = C.slack i j := by
  obtain ⟨hc,hs⟩ := C.actualSquare_relative_trig i
  have hK : (C.actualSquare i).center =
      rotate (C.actualSquare i) ((C.point i).a,-1*(C.point i).y) := by
    simp [actualSquare]
  have hL : (C.actualSquare (next i)).center =
      rotate (C.actualSquare (next i))
        ((C.point (next i)).a,-1*(C.point (next i)).y) := by
    simp [actualSquare]
  have h := canonical_margin_identity j (C.actualSquare i)
    (C.actualSquare (next i)) (C.point i).a (C.point i).y
    (C.point (next i)).a (C.point (next i)).y 1 1
    (Candidate.phi C.theta i) hK hL hc hs
  rw [h]
  fin_cases i <;> fin_cases j <;>
    simp [forwardMargin,Candidate.phi,Candidate.word,slack,edge,
      zeroProjection,quarterProjection,edgeWidth,pairWidth,
      Real.sin_add,Real.cos_add] <;> ring

theorem actualSquare_feasible (C : SignedCycle) (i : Vertex) (j : Fin 4) :
    (forwardAxis j).Feasible (C.actualSquare i) (C.actualSquare (next i)) ↔
      C.Feasible i j := by
  change SAT.threshold (C.actualSquare i) (C.actualSquare (next i)) ≤
      (forwardAxis j).projection (C.actualSquare i) (C.actualSquare (next i)) ↔
      0 ≤ C.slack i j
  rw [← actualSquare_margin]
  exact sub_nonneg.symm

theorem actualSquare_contained_iff (C : SignedCycle)
    (hs : ∀ i, (C.point i).Sorted) (q : ℝ) (i : Vertex) :
    SqContained q (C.actualSquare i) ↔ (C.point i).Contained q :=
  SignedPoint.square_contained_iff (hs i) q
    (C.theta i+(Candidate.offsets i : ℝ)*Real.pi/2)

theorem actualSquare_contained {q : ℝ} {C : SignedCycle}
    (hs : ∀ i, (C.point i).Sorted) (hc : ∀ i, (C.point i).Contained q)
    (i : Vertex) : SqContained q (C.actualSquare i) := by
  exact (SignedPoint.square_contained_iff (hs i) q
    (C.theta i+(Candidate.offsets i : ℝ)*Real.pi/2)).2 (hc i)

theorem actualSquare_points_contained {q : ℝ} {C : SignedCycle}
    (hs : ∀ i, (C.point i).Sorted) (hc : ∀ i, (C.point i).Contained q) :
    ∀ i p, closedSquare (C.actualSquare i) p → normSq p ≤ q := by
  have hq0 : 0 ≤ q := (C.point 0).circle_nonneg.trans (hc 0)
  exact fun i => (SqContained.iff_points hq0 _).1
    (actualSquare_contained hs hc i)

end SignedCycle
end SquaresInCircles.Eight
end
end
end
