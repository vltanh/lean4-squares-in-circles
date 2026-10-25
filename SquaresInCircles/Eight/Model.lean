module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic
public import SquaresInCircles.Common.SeparatingAxes

/-!
# Eight squares: radius levels, signed axes and cycles

The squared radii of the proof are the levels `qMinus < Q1 < Q0` (`radius_levels`), and the
core disk has radius `coreRadius = 1/12`. Containment and packings are stated with squared
radii (`SqContained`, `SqPacking`); `SqPacking` is `Packing` with the radius squared
(`sqPacking_iff_packing`), so boundary contacts are allowed. All distances are squared
Euclidean distances (`normSq`).

Two squares are separated along one of eight signed axes, an axis of either square with a sign
(`SignedAxis`); `SignedAxis.Feasible` says that the projection of the difference of the centres
on it reaches the threshold of the separating-axis theorem. A `NeighborCycle` is seven squares in
the disk that avoid the core disk, with a separating signed axis, the witness, on each pair of
consecutive squares. A `BoundaryCycle` adds a canonical frame, a state `(a, b)` on the outer or
the core curve (`BoundaryState`) and a real centre direction for each square. `RadiusExpansion`
and `BoundaryReduction` record the two ways in which a cycle is moved.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight

def qMinus : ℝ := 7831 / 2000
def Q1 : ℝ := 1957767069 / 500000000
def Q0 : ℝ := 9789 / 2500
def coreRadius : ℝ := 1 / 12

theorem radius_levels : (5 : ℝ) / 2 < qMinus ∧ qMinus < Q1 ∧ Q1 < Q0 ∧ Q0 < 4 := by
  norm_num [qMinus, Q1, Q0]

/-- Containment of a square in the closed disk of squared radius `q` about the origin. -/
def SqContained (q : ℝ) (K : UnitSquare) : Prop :=
  phi (alpha K (0, 0)) (beta K (0, 0)) ≤ q

/-- `Packing` with the squared radius `q`: the closed squares lie in the closed disk of squared
radius `q` about `o` and have disjoint interiors. -/
def SqPacking {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (q : ℝ) : Prop :=
  0 ≤ q ∧ (∀ i p, closedSquare (S i) p → normSq (sub p o) ≤ q) ∧
    InteriorDisjoint S

theorem sqPacking_iff_packing {n : ℕ} (S : Fin n → UnitSquare) (o : Point)
    {q : ℝ} (hq : 0 ≤ q) :
    SqPacking S o q ↔ Packing S o (Real.sqrt q) := by
  simp only [SqPacking, Packing, InteriorDisjoint, inDisk, Real.sq_sqrt hq]
  exact ⟨fun h => ⟨Real.sqrt_nonneg _, h.2⟩, fun h => ⟨hq, h.2⟩⟩

theorem packing_sq {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (h : Packing S o R) : SqPacking S o (R ^ 2) :=
  ⟨sq_nonneg _, h.2.1, h.2.2⟩

theorem SqContained.iff_points {q : ℝ} (hq : 0 ≤ q) (K : UnitSquare) :
    SqContained q K ↔ ∀ p, closedSquare K p → normSq p ≤ q := by
  constructor
  · intro h p hp
    have hh := inDisk_of_phi_le (R := Real.sqrt q)
      (by simpa [SqContained, Real.sq_sqrt hq] using h) hp
    simpa [inDisk, sub, Real.sq_sqrt hq] using hh
  · intro h
    have hh := phi_le_of_contained K (0, 0) (Real.sqrt q) (fun p hp => by
      simpa [inDisk, sub, Real.sq_sqrt hq] using h p hp)
    simpa [SqContained, Real.sq_sqrt hq] using hh

theorem SqContained.mono {q r : ℝ} {K : UnitSquare}
    (h : SqContained q K) (hqr : q ≤ r) : SqContained r K := h.trans hqr

/-- The closed square avoids the open core disk. -/
def CoreAvoiding (K : UnitSquare) : Prop :=
  ∀ p, closedSquare K p → coreRadius ^ 2 ≤ normSq p

/-- The closed square avoids the closed core disk. The exterior squares of a packing do, by
the core theorem `central_core_and_exteriors`. -/
def StrictCoreAvoiding (K : UnitSquare) : Prop :=
  ∀ p, closedSquare K p → coreRadius ^ 2 < normSq p

def ContainsCore (K : UnitSquare) : Prop :=
  ∀ p, normSq p ≤ coreRadius ^ 2 → openSquare K p

theorem StrictCoreAvoiding.weak {K : UnitSquare} (h : StrictCoreAvoiding K) :
    CoreAvoiding K := fun p hp => (h p hp).le

def e (K : UnitSquare) : Point := (K.cosine, K.sine)
def f (K : UnitSquare) : Point := (-K.sine, K.cosine)

theorem e_unit (K : UnitSquare) : normSq (e K) = 1 := K.unit

def SameFrame (K L : UnitSquare) : Prop := K.cosine = L.cosine ∧ K.sine = L.sine

/-- The frames of the two squares agree up to a quarter turn: the squares have the same axes. -/
def SamePhysicalFrame (K L : UnitSquare) : Prop :=
  (K.cosine = L.cosine ∧ K.sine = L.sine) ∨
  (K.cosine = -L.sine ∧ K.sine = L.cosine) ∨
  (K.cosine = -L.cosine ∧ K.sine = -L.sine) ∨
  (K.cosine = L.sine ∧ K.sine = -L.cosine)

def SameSquare (K L : UnitSquare) : Prop :=
  (∀ p, openSquare K p ↔ openSquare L p) ∧
  (∀ p, closedSquare K p ↔ closedSquare L p)

def moveCenter (K : UnitSquare) (p : Point) : UnitSquare := { K with center := p }

theorem moveCenter_sameFrame (K : UnitSquare) (p : Point) :
    SameFrame (moveCenter K p) K := ⟨rfl, rfl⟩

/-- Four axes, independently of their two orientations. -/
inductive AxisOwner | sourceX | sourceY | targetX | targetY

def AxisOwner.normal (a : AxisOwner) (K L : UnitSquare) : Point :=
  match a with
  | .sourceX => e K | .sourceY => f K | .targetX => e L | .targetY => f L

inductive AxisSign | positive | negative

def AxisSign.value : AxisSign → ℝ | .positive => 1 | .negative => -1
def AxisSign.flip : AxisSign → AxisSign | .positive => .negative | .negative => .positive

structure SignedAxis where
  owner : AxisOwner
  sign : AxisSign

def SignedAxis.normal (a : SignedAxis) (K L : UnitSquare) : Point :=
  scale a.sign.value (a.owner.normal K L)

def SignedAxis.projection (a : SignedAxis) (K L : UnitSquare) : ℝ :=
  dot (a.normal K L) (sub L.center K.center)

/-- The signed axis separates `K` and `L`: the projection of `L.center - K.center` on it is at
least the threshold `SAT.threshold K L`. Several axes may separate the same pair. -/
def SignedAxis.Feasible (a : SignedAxis) (K L : UnitSquare) : Prop :=
  SAT.threshold K L ≤ a.projection K L

abbrev Vertex := Fin 7
def next (i : Vertex) : Vertex := i + 1
def prev (i : Vertex) : Vertex := i - 1

def angleGap (β : Vertex → ℝ) (i : Vertex) : ℝ :=
  β (next i) - β i + if i = 6 then 2 * Real.pi else 0

inductive RadialKind | outer | coreSide | coreCorner
  deriving DecidableEq

/-- The two radial curves, with the core side/corner junction kept weak. -/
def BoundaryState (q : ℝ) (k : RadialKind) (a b : ℝ) : Prop :=
  match k with
  | .outer => phi a b = q
  | .coreSide => a = 7 / 12 ∧ b ≤ 1 / 2
  | .coreCorner => 1 / 2 ≤ b ∧
      (a - 1 / 2) ^ 2 + (b - 1 / 2) ^ 2 = (1 / 12 : ℝ) ^ 2

/-- Seven squares in the disk that avoid the core disk, with a separating signed axis, the
witness, on each pair of consecutive squares. Nonconsecutive squares may overlap. -/
structure NeighborCycle (q : ℝ) where
  square : Vertex → UnitSquare
  contained : ∀ i, SqContained q (square i)
  core : ∀ i, CoreAvoiding (square i)
  selected : Vertex → SignedAxis
  feasible : ∀ i, (selected i).Feasible (square i) (square (next i))

/-- A neighbour cycle in which every square is given a canonical frame, with its centre at
`a e - σ b f`, `0 ≤ b ≤ a`, a state `(a, b)` on one of the radial curves and a real centre
direction `beta`, the gaps between consecutive directions lying in `(0, π)`. Each of the seven
squares may lie on the outer or on the core curve, in any of the 128 combinations. -/
structure BoundaryCycle (q : ℝ) extends NeighborCycle q where
  kind : Vertex → RadialKind
  a : Vertex → ℝ
  b : Vertex → ℝ
  sigma : Vertex → ℝ
  a_pos : ∀ i, 0 < a i
  b_nonneg : ∀ i, 0 ≤ b i
  b_le_a : ∀ i, b i ≤ a i
  sigma_sign : ∀ i, sigma i = -1 ∨ sigma i = 1
  center_eq : ∀ i, (square i).center = rotate (square i) (a i, -sigma i * b i)
  boundary : ∀ i, BoundaryState q (kind i) (a i) (b i)
  beta : Vertex → ℝ
  center_cos : ∀ i, (square i).center.1 = Real.sqrt (a i ^ 2 + b i ^ 2) * Real.cos (beta i)
  center_sin : ∀ i, (square i).center.2 = Real.sqrt (a i ^ 2 + b i ^ 2) * Real.sin (beta i)
  frame_cos : ∀ i, (square i).cosine = Real.cos (beta i + Real.arctan (sigma i * b i / a i))
  frame_sin : ∀ i, (square i).sine = Real.sin (beta i + Real.arctan (sigma i * b i / a i))
  gap_pos : ∀ i, 0 < angleGap beta i
  gap_lt_pi : ∀ i, angleGap beta i < Real.pi

def BoundaryCycle.tangent {q : ℝ} (C : BoundaryCycle q) (i : Vertex) : ℝ :=
  C.sigma i * C.b i / C.a i

def BoundaryCycle.alpha {q : ℝ} (C : BoundaryCycle q) (i : Vertex) : ℝ :=
  Real.arctan (C.tangent i)

def BoundaryCycle.canonicalAngle {q : ℝ} (C : BoundaryCycle q) (i : Vertex) : ℝ :=
  C.beta i + C.alpha i

theorem BoundaryCycle.tangent_mem {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    -1 ≤ C.tangent i ∧ C.tangent i ≤ 1 := by
  have ha := C.a_pos i
  have hb := C.b_nonneg i
  have hab := C.b_le_a i
  rcases C.sigma_sign i with h | h
  · simp only [BoundaryCycle.tangent, h, neg_one_mul]
    exact ⟨(le_div_iff₀ ha).2 (by linarith), (div_le_iff₀ ha).2 (by linarith)⟩
  · simp only [BoundaryCycle.tangent, h, one_mul]
    exact ⟨(le_div_iff₀ ha).2 (by linarith), (div_le_iff₀ ha).2 (by linarith)⟩

/-- `D` is an expansion of `C` to a larger level: the same radial kinds, frames, centre
directions and tangents, and every signed axis that separates two consecutive squares of `C`,
not only the witness, separates them in `D`. -/
structure RadiusExpansion {q r : ℝ} (C : BoundaryCycle q) (D : BoundaryCycle r) : Prop where
  same_kind : D.kind = C.kind
  same_frames : ∀ i, SameFrame (D.square i) (C.square i)
  same_rays : D.beta = C.beta
  same_tangents : D.tangent = C.tangent
  preserves_all_axes : ∀ i (axis : SignedAxis), axis.Feasible (C.square i) (C.square (next i)) →
    axis.Feasible (D.square i) (D.square (next i))

def coreDistanceSq (K : UnitSquare) : ℝ :=
  (max (alpha K (0, 0) - 1 / 2) 0) ^ 2 +
  (max (beta K (0, 0) - 1 / 2) 0) ^ 2

def OnRadialBoundary (q : ℝ) (K : UnitSquare) : Prop :=
  phi (alpha K (0, 0)) (beta K (0, 0)) = q ∨
  coreDistanceSq K = coreRadius ^ 2

/-- A boundary reduction of `C`: the centres are moved with their frames and witnesses kept
(`raw`), and then each square is given the quarter turn of a canonical frame and its witness is
transported (`result`). The witnesses keep their normals (`axis_transport`), so no axis is
relabelled without its sign. -/
structure BoundaryReduction {q : ℝ} (C : NeighborCycle q) where
  raw : NeighborCycle q
  raw_frames : ∀ i, SameFrame (raw.square i) (C.square i)
  raw_selected : raw.selected = C.selected
  result : BoundaryCycle q
  physical_frames : ∀ i, SamePhysicalFrame (result.square i) (C.square i)
  axis_transport : ∀ i,
    (result.selected i).normal (result.square i) (result.square (next i)) =
    (raw.selected i).normal (raw.square i) (raw.square (next i))

end SquaresInCircles.Eight
