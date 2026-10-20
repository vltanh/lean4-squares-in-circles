module

public import SquaresInCircles.Eight.TableFree.Variation

/-!
# Necessary geometric seven-cycles and the precise owner-entry domains

Uncompiled source draft. These structures record only actual coordinates,
containment, core avoidance, physical gaps, frames, and selected SAT owners.
They contain no capture conclusion, stationary conclusion, endpoint-existence
premise, mismatch bound, or hidden table acceptance predicate.

Intermediate-only boundary reductions use `BoundaryInput`. The later
anchor-changing reductions use `HardInput`, which deliberately does not
require a changed anchor to remain on its old outer circle. Strict circle
losses live in `LossLedger`, separately from radial labels.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree
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

/-- The four physical forward axes, encoded in the canonical chart. -/
structure Necessary (q : ℝ) (C : SignedCycle) : Prop where
  sorted : ∀ i, (C.point i).Sorted
  contained : ∀ i, (C.point i).Contained q
  core : ∀ i, (C.point i).AvoidsCore
  spread : C.Spread

/-- Winding is encoded by actual positive gaps, whose sum is identically 2π. -/
structure Ordered (C : SignedCycle) : Prop where
  gap_pos : ∀ i, 0<C.physicalGap i
  gap_lt_pi : ∀ i, C.physicalGap i<Real.pi

def normalOwners : Vertex → Finset (Fin 4) :=
  ![{0,2},{0,1},{0,2},{2,3},{0,2},{2,3},{0,1}]

/-- One original weak owner per edge. No strictness is built into a tie. -/
structure Witnesses (C : SignedCycle) where
  owner : Vertex → Fin 4
  feasible : ∀ i, C.Feasible i (owner i)
  allowed : ∀ i, owner i∈normalOwners i

/-- This stronger all-witness statement is needed at the boundary source
when the originally selected physical normals are recovered. -/
def AllNormalOwners (C : SignedCycle) : Prop :=
  ∀ i j, C.Feasible i j → j∈normalOwners i

structure NormalAnchors (C : SignedCycle) : Prop where
  H_nonneg : 0≤(C.point H).y
  A_nonneg : 0≤(C.point A).y
  B_nonpos : (C.point B).y≤0
  D_nonpos : (C.point D).y≤0

/-- The actual zero-owner implications, before any G/T sign correction. -/
structure ZeroSignImplications (C : SignedCycle) (w : Witnesses C) : Prop where
  HG_canceling : w.owner H=2 → (C.point G).y<0
  TD_canceling : w.owner T=0 → 0<(C.point T).y

/-- The sharp entry source. E's sign is intentionally absent: positive-primary
exclusion has to remain valid after physical reflection. -/
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

/-- E sign normalization is a separate field, so it cannot silently survive
or be assumed after the full reflected positive-primary argument. -/
structure NormalizedBoundaryInput (q : ℝ) extends BoundaryInput q where
  E_nonpos : (cycle.point E).y≤0

/-- The necessary hard class permits anchor circle loss and arbitrary G/T
signs and frame orders. This is not a boundary-state structure. -/
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

/-- No frame or angle information is inferred from this name: it is the
actual availability of the two hard physical axes. -/
def HardOwners (C : SignedCycle) : Prop := C.Feasible G 0 ∧ C.Feasible B 2

theorem physicalGap_sum (C : SignedCycle) :
    (∑ i, C.physicalGap i)=2*Real.pi := by
  simp [physicalGap,Fin.sum_univ_succ,Candidate.word,delta,next]
  ring

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
  · simpa using Real.arctan_le_arctan hlo
  · simpa using Real.arctan_le_arctan hhi

/-- The four-anchor outer hypothesis is used only before a transport changes
an anchor. E's source radial kind gives the later hard theorem's alternative. -/
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
  constructor <;> simp [reflected,reflectedIndex,SignedPoint.reflect,H,A,B,D] <;>
    linarith [h.H_nonneg,h.A_nonneg,h.B_nonpos,h.D_nonpos]

theorem reflected_normalOwners (i : Vertex) (j : Fin 4) :
    reflectedOwner j∈normalOwners i ↔ j∈normalOwners (reflectedIndex (next i)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- Reflection retains a witness, with its owner and sign transformed by the
exact projection identity. It does not select a convenient new axis. -/
def Witnesses.reflected {C : SignedCycle} (w : C.Witnesses) : C.reflected.Witnesses where
  owner i := reflectedOwner (w.owner (reflectedIndex (next i)))
  feasible i := (reflected_feasible C i _).2 (w.feasible _)
  allowed i := (reflected_normalOwners i _).2 (w.allowed _)

theorem Necessary.reflected {q : ℝ} {C : SignedCycle} (h : C.Necessary q) :
    C.reflected.Necessary q where
  sorted i := by simpa [reflected] using h.sorted (reflectedIndex i)
  contained i := by simpa [reflected] using h.contained (reflectedIndex i)
  core i := by simpa [reflected] using h.core (reflectedIndex i)
  spread := reflected_spread h.spread

theorem Ordered.reflected {C : SignedCycle} (h : C.Ordered) : C.reflected.Ordered where
  gap_pos i := by rw [reflected_gap]; exact h.gap_pos _
  gap_lt_pi i := by rw [reflected_gap]; exact h.gap_lt_pi _

def BoundaryInput.reflected {q : ℝ} (I : BoundaryInput q) : BoundaryInput q where
  cycle := I.cycle.reflected
  necessary := I.necessary.reflected
  ordered := I.ordered.reflected
  strict_spread i j := by
    have h := I.strict_spread (reflectedIndex j) (reflectedIndex i)
    simpa [SignedCycle.reflected,show I.cycle.theta B-I.cycle.theta (reflectedIndex i)-
      (I.cycle.theta B-I.cycle.theta (reflectedIndex j))=
      I.cycle.theta (reflectedIndex j)-I.cycle.theta (reflectedIndex i) by ring] using h
  positive_variation := by simpa [positiveVariation_reflected] using I.positive_variation
  negative_variation := by simpa [negativeVariation_reflected] using I.negative_variation
  radial i := by simpa [SignedCycle.reflected] using I.radial (reflectedIndex i)
  anchors_outer i hi := by
    have hj : reflectedIndex i∈({H,A,B,D} : Finset Vertex) := by
      fin_cases i <;> norm_num [H,A,B,D,reflectedIndex] at hi ⊢
    simpa [SignedCycle.reflected] using I.anchors_outer _ hj
  anchors_normal := reflected_normal I.anchors_normal
  witnesses := I.witnesses.reflected
  zero_signs := by
    constructor
    · intro h
      have hT : I.witnesses.owner T=0 := by
        simpa [Witnesses.reflected,reflectedIndex,next,H,T,reflectedOwner] using h
      have hy := I.zero_signs.TD_canceling hT
      simpa [SignedCycle.reflected,reflectedIndex,H,G,T,SignedPoint.reflect] using neg_neg_of_pos hy
    · intro h
      have hG : I.witnesses.owner H=2 := by
        have := h
        fin_cases hj : I.witnesses.owner H <;>
          simp [Witnesses.reflected,reflectedIndex,next,H,T,reflectedOwner,hj] at this ⊢
      have hy := I.zero_signs.HG_canceling hG
      simpa [SignedCycle.reflected,reflectedIndex,G,T,SignedPoint.reflect] using neg_pos.mpr hy

/-- Changing only one intermediate cannot affect any nonincident separator. -/
theorem replacePoint_other_feasible {C : SignedCycle} {v i : Vertex}
    {p : SignedPoint} {t : ℝ} {j : Fin 4}
    (hi : i≠v) (hn : next i≠v) :
    (C.replacePoint v p t).Feasible i j ↔ C.Feasible i j := by
  simp [Feasible,slack,edge,replacePoint,delta,hi,hn,Function.update_of_ne]

end SignedCycle
end SquaresInCircles.Eight.TableFree