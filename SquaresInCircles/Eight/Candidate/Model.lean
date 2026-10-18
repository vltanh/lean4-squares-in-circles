module

public import SquaresInCircles.Eight.SeparatingAxis
public import SquaresInCircles.Common.Trigonometry
public import SquaresInCircles.Common.Analysis

/-!
# Candidate-word coordinates

The fixed cyclic roles are H,G,A,B,T,D,E. The five charged differences
exclude G→A and E→H. This source is an uncompiled F7/F8 draft.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate

def H : Vertex := 0
def G : Vertex := 1
def A : Vertex := 2
def B : Vertex := 3
def T : Vertex := 4
def D : Vertex := 5
def E : Vertex := 6

def word : Vertex → ℤ := ![0, 1, 0, 1, 0, 1, 1]
def offsets : Vertex → ℤ := ![-1, -1, 0, 0, 1, 1, 2]
def charged : Finset Vertex := {0, 2, 3, 4, 5}
def zeroEdges : Finset Vertex := {0, 2, 4}
def otherQuarterEdges : Finset Vertex := {3, 5}
def mixedEdges : Finset Vertex := {1, 6}

def delta (θ : Vertex → ℝ) (i : Vertex) : ℝ := θ (next i) - θ i
def phi (θ : Vertex → ℝ) (i : Vertex) : ℝ := (word i : ℝ) * Real.pi / 2 + delta θ i
def mismatch (θ : Vertex → ℝ) : ℝ := ∑ i ∈ charged, |delta θ i|
def tilt (θ : Vertex → ℝ) : ℝ := θ G

def h (x : ℝ) : ℝ := (|Real.sin x| + |Real.cos x| - 1) / 2
def hSmooth (x : ℝ) : ℝ := (Real.sin x + Real.cos x - 1) / 2
def hSum (θ : Vertex → ℝ) : ℝ := ∑ i ∈ charged, h (|delta θ i|)

theorem h_nonneg (x : ℝ) : 0 ≤ h x := by
  have hh := one_le_abs_cos_add_abs_sin x
  unfold h
  linarith

@[simp] theorem h_zero : h 0 = 0 := by norm_num [h]
@[simp] theorem h_neg (x : ℝ) : h (-x) = h x := by simp [h]
@[simp] theorem h_abs (x : ℝ) : h |x| = h x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, h_neg]

theorem h_half_pi_add (x : ℝ) : h (Real.pi / 2 + x) = h x := by
  simp [h, Real.sin_add, Real.cos_add, add_comm]

theorem h_phi (θ : Vertex → ℝ) (i : Vertex) : h (phi θ i) = h (|delta θ i|) := by
  fin_cases i <;>
    simp [phi, word, h_half_pi_add, h_abs]

theorem sum_delta (θ : Vertex → ℝ) : (∑ i, delta θ i) = 0 := by
  simp [Fin.sum_univ_succ, delta, next]
  ring

theorem sum_phi (θ : Vertex → ℝ) : (∑ i, phi θ i) = 2 * Real.pi := by
  simp [Fin.sum_univ_succ, phi, word, delta, next]
  ring

theorem sum_marker_difference (L : Vertex → ℝ) : (∑ i, (L i - L (next i))) = 0 := by
  simp [Fin.sum_univ_succ, next]
  ring

theorem mismatch_nonneg (θ : Vertex → ℝ) : 0 ≤ mismatch θ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem delta_le_mismatch (θ : Vertex → ℝ) {i : Vertex} (hi : i ∈ charged) :
    |delta θ i| ≤ mismatch θ :=
  Finset.single_le_sum (fun j _ => abs_nonneg (delta θ j)) hi

/-- Real frame lifts after the geometric quarter-word theorem and an actual
rotation normalizing A. No tangent, mismatch, owner, or tilt conclusion is
included here. -/
structure Frame {q : ℝ} (C : BoundaryCycle q) where
  theta : Vertex → ℝ
  theta_A : theta A = 0
  canonical_eq : ∀ i, C.canonicalAngle i = theta i + (offsets i : ℝ) * Real.pi / 2
  spread : ∀ i j, |theta i - theta j| < 7 / 10
  gap_lower : ∀ i, 19 / 25 < angleGap C.beta i
  gap_upper : ∀ i, angleGap C.beta i < 3 * Real.pi / 4
  forward_complete : ∀ i axis,
    axis.Feasible (C.square i) (C.square (next i)) → ∃ j : Fin 4, axis = forwardAxis j

theorem Frame.delta_small {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Vertex) :
    |delta F.theta i| < 7 / 10 := F.spread _ _

theorem Frame.tilt_small {q : ℝ} {C : BoundaryCycle q} (F : Frame C) :
    |tilt F.theta| < 7 / 10 := by
  simpa [tilt, F.theta_A] using F.spread G A

theorem Frame.physical_angle {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Vertex) :
    phi F.theta i = angleGap C.beta i + C.alpha (next i) - C.alpha i := by
  have hs := F.canonical_eq i
  have ht := F.canonical_eq (next i)
  dsimp [BoundaryCycle.canonicalAngle] at hs ht
  fin_cases i <;>
    simp [phi, delta, word, offsets, next, angleGap] at hs ht ⊢ <;> linarith

def margin {q : ℝ} (C : BoundaryCycle q) (θ : Vertex → ℝ) (i : Vertex) (j : Fin 4) : ℝ :=
  forwardMargin j (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
    (C.sigma i) (C.sigma (next i)) (phi θ i)

/-- Tangent cuts in their exact dependency order. -/
def EHalf {q : ℝ} (C : BoundaryCycle q) : Prop := C.tangent E ≤ 0

def GCut {q : ℝ} (C : BoundaryCycle q) : Prop :=
  -4 / 5 < C.tangent G ∧ C.tangent G < -1 / 20

def TCut {q : ℝ} (C : BoundaryCycle q) : Prop :=
  1 / 20 < C.tangent T ∧ C.tangent T < 4 / 5

def HDCut {q : ℝ} (C : BoundaryCycle q) : Prop :=
  1 / 2 < C.tangent H ∧ C.tangent D < -1 / 2

def Signs {q : ℝ} (C : BoundaryCycle q) : Prop :=
  0 < C.tangent H ∧ C.tangent G < 0 ∧ 0 < C.tangent A ∧
    C.tangent B < 0 ∧ 0 < C.tangent T ∧ C.tangent D < 0

def zeroOwners : Finset (Fin 4) := {0, 2}
def quarterOwners : Finset (Fin 4) := {2, 3}
def terminalOwners : Vertex → Finset (Fin 4) :=
  ![{0, 2}, {0}, {0, 2}, {2, 3}, {0, 2}, {2, 3}, {1}]

def OwnerRestriction {q : ℝ} (C : BoundaryCycle q) (J : Vertex → Finset (Fin 4)) : Prop :=
  ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) → j ∈ J i

def ZeroOwners {q : ℝ} (C : BoundaryCycle q) : Prop :=
  ∀ i ∈ zeroEdges, ∀ j,
    (forwardAxis j).Feasible (C.square i) (C.square (next i)) → j ∈ zeroOwners

def QuarterOwners {q : ℝ} (C : BoundaryCycle q) : Prop :=
  ∀ i ∈ otherQuarterEdges, ∀ j,
    (forwardAxis j).Feasible (C.square i) (C.square (next i)) → j ∈ quarterOwners

def charge (β : ℝ) (i : Vertex) : ℝ := if i ∈ charged then β else 0

/-- The continuous conclusion of a complete charged table. The label is chosen
once per vertex. All initially feasible forward axes receive the same bound. -/
structure ChargedBound {q : ℝ} (C : BoundaryCycle q) (F : Frame C)
    (β : ℝ) (γ : Vertex → ℝ) where
  label : Vertex → ℝ
  pair_bound : ∀ i j,
    (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
    γ i < phi F.theta i - charge β i * h (phi F.theta i) + label i - label (next i)

theorem ChargedBound.cyclic {q : ℝ} {C : BoundaryCycle q} {F : Frame C}
    {β : ℝ} {γ : Vertex → ℝ} (P : ChargedBound C F β γ) :
    (∑ i, γ i) + β * hSum F.theta < 2 * Real.pi := by
  have hedge (i : Vertex) := by
    obtain ⟨j, hj⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact P.pair_bound i j (hj ▸ C.feasible i)
  have hh := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset Vertex))
    Finset.univ_nonempty (fun i _ => hedge i)
  have hid :
      (∑ i, (phi F.theta i - charge β i * h (phi F.theta i) +
        P.label i - P.label (next i))) =
      2 * Real.pi - β * hSum F.theta := by
    simp [Fin.sum_univ_succ, charge, charged, hSum, h_phi,
      phi, delta, word, next]
    ring
  rw [hid] at hh
  linarith

end SquaresInCircles.Eight.Candidate
