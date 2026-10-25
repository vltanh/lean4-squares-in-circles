module

public import SquaresInCircles.Eight.BoundaryReduction
public import SquaresInCircles.Eight.QuarterWords

/-!
# The other nearest axis at an actual diagonal

At a sorted diagonal the two nearest directed square axes give two canonical
records of precisely the same physical square.  The new record keeps the
center, true radial state and center-angle lift.  Every original weak axis
is transported by its exact normal, rather than reselected after the move.

The real frame lift is unchanged; only its integer representative changes.
Thus the word calculation below is an equality of actual quarter increments.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.NearestAxisRecode

def turn {q : ℝ} (C : BoundaryCycle q) (v i : Vertex) : Fin 4 :=
  if i=v then if C.sigma v=1 then 3 else 1 else 0

def shift {q : ℝ} (C : BoundaryCycle q) (v i : Vertex) : ℤ :=
  if i=v then if C.sigma v=1 then -1 else 1 else 0

def sign {q : ℝ} (C : BoundaryCycle q) (v i : Vertex) : ℝ :=
  if i=v then -C.sigma i else C.sigma i

/-- The canonical data at the alternate nearest axis.  The equality
`b v=a v` is used only to exchange the two equal local coordinates. -/
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

/-- Literal physical recoding at the same radius and on the same radial
boundary branch.  In particular it does not perform a radial expansion. -/
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

theorem sameSquare {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) (i : Vertex) :
    SameSquare ((cycle C v hd).square i) (C.square i) :=
  turnSquare_sameSquare _ _

theorem samePhysicalFrame {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) (i : Vertex) :
    SamePhysicalFrame ((cycle C v hd).square i) (C.square i) :=
  turnSquare_physical _ _

@[simp] theorem radial_kind {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) : (cycle C v hd).kind=C.kind := rfl

@[simp] theorem rays {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) : (cycle C v hd).beta=C.beta := rfl

theorem axis_normal {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) (i : Vertex) (axis : SignedAxis) :
    (transportQuarterAxis (turn C v i) (turn C v (next i)) axis).normal
      ((cycle C v hd).square i) ((cycle C v hd).square (next i))=
        axis.normal (C.square i) (C.square (next i)) :=
  transportQuarterAxis_normal _ _ _ _ _

theorem axis_projection {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) (i : Vertex) (axis : SignedAxis) :
    (transportQuarterAxis (turn C v i) (turn C v (next i)) axis).projection
      ((cycle C v hd).square i) ((cycle C v hd).square (next i))=
        axis.projection (C.square i) (C.square (next i)) := by
  simp only [SignedAxis.projection,axis_normal,center]

/-- Exact slack preservation includes every simultaneous weak tie. -/
theorem axis_slack {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) (i : Vertex) (axis : SignedAxis) :
    (transportQuarterAxis (turn C v i) (turn C v (next i)) axis).projection
        ((cycle C v hd).square i) ((cycle C v hd).square (next i))-
        SAT.threshold ((cycle C v hd).square i) ((cycle C v hd).square (next i))=
      axis.projection (C.square i) (C.square (next i))-
        SAT.threshold (C.square i) (C.square (next i)) := by
  rw [axis_projection]
  change _-SAT.threshold (turnSquare _ _) (turnSquare _ _)=_
  rw [turnSquare_threshold]

theorem all_axes {q : ℝ} (C : BoundaryCycle q) (v : Vertex)
    (hd : C.b v=C.a v) (i : Vertex) (axis : SignedAxis)
    (ha : axis.Feasible (C.square i) (C.square (next i))) :
    (transportQuarterAxis (turn C v i) (turn C v (next i)) axis).Feasible
      ((cycle C v hd).square i) ((cycle C v hd).square (next i)) :=
  transportQuarterAxis_feasible ha

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

/-- Only the representative integer changes.  The very same real lift,
diameter and all its signed differences are retained. -/
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

end SquaresInCircles.Eight.TableFree.NearestAxisRecode
