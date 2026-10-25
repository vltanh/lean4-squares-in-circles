module

public import SquaresInCircles.Eight.Owners.LossLedger
public import SquaresInCircles.Eight.Owners.Variation

/-!
# Eight squares: necessary seven-cycles and their owner domains

A signed cycle records the coordinates and frames of the seven squares. The structures here
record containment, core avoidance and spread (`Necessary`), the physical gaps (`Ordered`), a
weak separating-axis owner on each edge among the normal owners (`Witnesses`, `normalOwners`),
and the signs of the anchors and of the zero owners (`NormalAnchors`, `ZeroSignImplications`).

The reductions that move only the intermediates G and T start from a `BoundaryInput`, whose
anchors H, A, B, D lie on the circle. The reductions that move anchors work with a `HardInput`,
which does not require a moved anchor to stay on its circle; strict circle losses are recorded
separately (`AnchorNonincrease`, `StrictAnchorLoss`). Reflection maps each structure to the
reflected cycle (`Necessary.reflected`, `BoundaryInput.reflected`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open Candidate

namespace SignedCycle

def localAngle (C : SignedCycle) (i : Vertex) : ℝ :=
  Real.arctan ((C.point i).y/(C.point i).a)

def physicalGap (C : SignedCycle) (i : Vertex) : ℝ :=
  (Candidate.word i : ℝ)*Real.pi/2+delta C.theta i+
    C.localAngle i-C.localAngle (next i)

def actualSquare (C : SignedCycle) (i : Vertex) : UnitSquare :=
  (C.point i).square (C.theta i+(Candidate.offsets i : ℝ)*Real.pi/2)

def Spread (C : SignedCycle) : Prop :=
  ∀ i j, |C.theta i-C.theta j| ≤ frameCap

def StrictSpread (C : SignedCycle) : Prop :=
  ∀ i j, |C.theta i-C.theta j| < frameCap

/-- A necessary cycle at radius `q`: every point sorted, in the circle and off the core, with
frames of spread at most `frameCap`. -/
structure Necessary (q : ℝ) (C : SignedCycle) : Prop where
  sorted : ∀ i, (C.point i).Sorted
  contained : ∀ i, (C.point i).Contained q
  core : ∀ i, (C.point i).AvoidsCore
  spread : C.Spread

/-- An ordered cycle: every physical gap between consecutive squares lies in `(0, π)`; the gaps add
up to `2π`. -/
structure Ordered (C : SignedCycle) : Prop where
  gap_pos : ∀ i, 0<C.physicalGap i
  gap_lt_pi : ∀ i, C.physicalGap i<Real.pi

def normalOwners : Vertex → Finset (Fin 4) :=
  ![{0,2},{0,1},{0,2},{2,3},{0,2},{2,3},{0,1}]

/-- A weak owner on each edge, among the normal owners of the edge; ties are allowed. -/
structure Witnesses (C : SignedCycle) where
  owner : Vertex → Fin 4
  feasible : ∀ i, C.Feasible i (owner i)
  allowed : ∀ i, owner i∈normalOwners i

structure NormalAnchors (C : SignedCycle) : Prop where
  H_nonneg : 0≤(C.point H).y
  A_nonneg : 0≤(C.point A).y
  B_nonpos : (C.point B).y≤0
  D_nonpos : (C.point D).y≤0

/-- The sign implications of the zero owners: owner `2` on HG makes `G.y < 0`, owner `0` on TD makes
`0 < T.y`. -/
structure ZeroSignImplications (C : SignedCycle) (w : Witnesses C) : Prop where
  HG_canceling : w.owner H=2 → (C.point G).y<0
  TD_canceling : w.owner T=0 → 0<(C.point T).y

/-- A boundary input at radius `q`: a necessary ordered cycle with strict spread and variations
below `frameCap`, its points on the boundary, the anchors H, A, B, D on the circle with their
normal signs, and weak witnesses with their zero-sign implications. The sign of E is left free, so
that the exclusion of positive primaries applies after reflection. -/
structure BoundaryInput (q : ℝ) where
  cycle : SignedCycle
  necessary : cycle.Necessary q
  ordered : cycle.Ordered
  strict_spread : cycle.StrictSpread
  positive_variation : positiveVariation cycle.theta<frameCap
  negative_variation : negativeVariation cycle.theta<frameCap
  radial : ∀ i, (cycle.point i).Boundary q
  anchors_outer : ∀ i∈({H,A,B,D} : Finset Vertex), (cycle.point i).Outer q
  anchors_normal : cycle.NormalAnchors
  witnesses : cycle.Witnesses
  zero_signs : cycle.ZeroSignImplications witnesses

/-- A boundary input with `E.y ≤ 0`. The sign of E is a separate field, since the reflected argument
for positive primaries does not keep it. -/
structure NormalizedBoundaryInput (q : ℝ) extends BoundaryInput q where
  E_nonpos : (cycle.point E).y≤0

/-- A hard input at radius `q`: a necessary cycle with normal anchor signs and `E.y ≤ 0`, weak
witnesses with the hard owners `0` on GA and `2` on BT and the zero-sign implications, and the
radial alternative of E. Its anchors need not lie on the circle, and the signs and frame order of
G and T are free. -/
structure HardInput (q : ℝ) where
  cycle : SignedCycle
  necessary : cycle.Necessary q
  anchors_normal : cycle.NormalAnchors
  E_nonpos : (cycle.point E).y≤0
  witnesses : cycle.Witnesses
  GA_hard : cycle.Feasible G 0
  BT_hard : cycle.Feasible B 2
  zero_signs : cycle.ZeroSignImplications witnesses
  E_radial : (cycle.point E).a≤7/12 ∨
    max |(cycle.point H).y| |(cycle.point D).y|≤(cycle.point E).a

/-- The two hard axes are available: owner `0` on GA and owner `2` on BT. -/
def HardOwners (C : SignedCycle) : Prop := C.Feasible G 0 ∧ C.Feasible B 2

theorem localAngle_mem {C : SignedCycle} (hs : ∀ i, (C.point i).Sorted)
    (i : Vertex) : -Real.pi/4 ≤ C.localAngle i ∧ C.localAngle i≤Real.pi/4 := by
  have ha := (hs i).1
  have hy := (hs i).2
  have hlo : -1 ≤ (C.point i).y/(C.point i).a := by
    apply (le_div_iff₀ ha).2
    linarith [(abs_le.mp hy).1]
  have hhi : (C.point i).y/(C.point i).a≤1 := by
    apply (div_le_iff₀ ha).2
    linarith [(abs_le.mp hy).2]
  unfold localAngle
  constructor
  · simpa [Real.arctan_neg,Real.arctan_one,neg_div] using Real.arctan_mono hlo
  · simpa [Real.arctan_one] using Real.arctan_mono hhi

/-- A normalized boundary input with the two hard owners is a hard input; the radial kind of E
gives its radial alternative. -/
def NormalizedBoundaryInput.toHard {q : ℝ} (I : NormalizedBoundaryInput q)
    (hGA : I.cycle.Feasible G 0) (hBT : I.cycle.Feasible B 2) : HardInput q where
  cycle := I.cycle
  necessary := I.necessary
  anchors_normal := I.anchors_normal
  E_nonpos := I.E_nonpos
  witnesses := I.witnesses
  GA_hard := hGA
  BT_hard := hBT
  zero_signs := I.zero_signs
  E_radial := SignedPoint.boundary_radial_alternative
    (I.necessary.sorted E) (I.radial E)
    (I.necessary.sorted H) (I.necessary.sorted D)
    (I.necessary.contained H) (I.necessary.contained D)

theorem reflected_gap (C : SignedCycle) (i : Vertex) :
    C.reflected.physicalGap i=C.physicalGap (reflectedIndex (next i)) := by
  have hr (j : Vertex) : C.reflected.localAngle j= -C.localAngle (reflectedIndex j) := by
    simp [reflected,localAngle,SignedPoint.reflect,neg_div,Real.arctan_neg]
  rw [physicalGap,physicalGap,reflected_delta,reflected_word]
  rw [hr,hr,reflectedIndex_next]
  ring

theorem reflected_spread {C : SignedCycle} (h : C.Spread) : C.reflected.Spread := by
  intro i j
  have hh := h (reflectedIndex j) (reflectedIndex i)
  simpa [reflected,show C.theta B-C.theta (reflectedIndex i)-
    (C.theta B-C.theta (reflectedIndex j))=
    C.theta (reflectedIndex j)-C.theta (reflectedIndex i) by ring] using hh

theorem reflected_normal {C : SignedCycle} (h : C.NormalAnchors) :
    C.reflected.NormalAnchors := by
  have h1 := h.H_nonneg
  have h2 := h.A_nonneg
  have h3 := h.B_nonpos
  have h4 := h.D_nonpos
  simp only [H,A,B,D] at h1 h2 h3 h4
  constructor <;> simp [reflected,reflectedIndex,SignedPoint.reflect,H,A,B,D] <;>
    linarith

theorem reflected_normalOwners (i : Vertex) (j : Fin 4) :
    reflectedOwner j∈normalOwners i ↔ j∈normalOwners (reflectedIndex (next i)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The witnesses of the reflected cycle: each witness is reflected, its owner and sign
transformed by the projection identity. -/
def Witnesses.reflected {C : SignedCycle} (w : C.Witnesses) : C.reflected.Witnesses where
  owner i := reflectedOwner (w.owner (reflectedIndex (next i)))
  feasible i := (reflected_feasible C i _).2 (w.feasible _)
  allowed i := (reflected_normalOwners i _).2 (w.allowed _)

theorem Necessary.reflected {q : ℝ} {C : SignedCycle} (h : C.Necessary q) :
    C.reflected.Necessary q := by
  exact {
    sorted := fun i => (SignedPoint.reflect_sorted _).2 (h.sorted (reflectedIndex i))
    contained := fun i => (SignedPoint.reflect_contained _ q).2 (h.contained (reflectedIndex i))
    core := fun i => (SignedPoint.reflect_avoidsCore _).2 (h.core (reflectedIndex i))
    spread := reflected_spread h.spread }

theorem Ordered.reflected {C : SignedCycle} (h : C.Ordered) : C.reflected.Ordered := {
  gap_pos i := by rw [reflected_gap]; exact h.gap_pos _
  gap_lt_pi i := by rw [reflected_gap]; exact h.gap_lt_pi _ }

def BoundaryInput.reflected {q : ℝ} (I : BoundaryInput q) : BoundaryInput q where
  cycle := I.cycle.reflected
  necessary := I.necessary.reflected
  ordered := I.ordered.reflected
  strict_spread i j := by
    have h := I.strict_spread (reflectedIndex j) (reflectedIndex i)
    simpa [SignedCycle.reflected,show I.cycle.theta B-I.cycle.theta (reflectedIndex i)-
      (I.cycle.theta B-I.cycle.theta (reflectedIndex j))=
      I.cycle.theta (reflectedIndex j)-I.cycle.theta (reflectedIndex i) by ring] using h
  positive_variation := by
    rw [reflected_positiveVariation]
    exact I.positive_variation
  negative_variation := by
    rw [reflected_negativeVariation]
    exact I.negative_variation
  radial i := by simpa [SignedCycle.reflected] using I.radial (reflectedIndex i)
  anchors_outer i hi := by
    have hj : reflectedIndex i∈({H,A,B,D} : Finset Vertex) := by
      fin_cases i <;> simp [H,A,B,D,reflectedIndex] at hi ⊢
    exact (SignedPoint.reflect_outer _ q).2 (I.anchors_outer _ hj)
  anchors_normal := reflected_normal I.anchors_normal
  witnesses := I.witnesses.reflected
  zero_signs := by
    constructor
    · intro h
      have h' : reflectedOwner (I.witnesses.owner T)=2 := h
      have hT : I.witnesses.owner T=0 := by
        have hh := congrArg reflectedOwner h'
        rwa [reflectedOwner_involutive] at hh
      have hy := I.zero_signs.TD_canceling hT
      show -(I.cycle.point T).y<0
      linarith
    · intro h
      have h' : reflectedOwner (I.witnesses.owner H)=0 := h
      have hG : I.witnesses.owner H=2 := by
        have hh := congrArg reflectedOwner h'
        rwa [reflectedOwner_involutive] at hh
      have hy := I.zero_signs.HG_canceling hG
      show 0 < -(I.cycle.point G).y
      linarith

/-- Replacing the point of one vertex does not change the feasibility of an axis on an edge not
incident to it. -/
theorem replacePoint_other_feasible {C : SignedCycle} {v i : Vertex}
    {p : SignedPoint} {t : ℝ} {j : Fin 4}
    (hi : i≠v) (hn : next i≠v) :
    (replacePoint C v p t).Feasible i j ↔ C.Feasible i j := by
  simp [Feasible,slack,edge,replacePoint,delta,hi,hn,Function.update_of_ne]

end SignedCycle
end SquaresInCircles.Eight