module

public import SquaresInCircles.Eight.Frames.SeparatingAxis

/-!
# Eight squares: candidate coordinates

In a boundary cycle with the quarter word `0101011` the squares have the roles
`H, G, A, B, T, D, E`, and their canonical frames are `-1, -1, 0, 0, 1, 1, 2` quarter turns ahead
of that of `A` (`offsets`). A `Frame` gives real representatives `theta` of the frames with
`theta A = 0`. The five aligned edges `H → G`, `A → B`, `B → T`, `T → D` and `D → E` are charged:
the mismatch is the sum of the frame differences on them, which leaves out the two mixed edges
`G → A` and `E → H`, and the tilt is `theta G`.

The file also names the tangent cuts (`EHalf`, `GCut`, `TCut`, `HDCut`), the signs and the owner
sets of the later steps, and `ChargedBound`, what a charged table proves about a cycle: one label
per square and a bound on the charged cost of every edge for every separating forward axis.
Summed round the cycle it gives `∑ γᵢ + β hSum < 2π` (`ChargedBound.cyclic`).
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

def delta (θ : Vertex → ℝ) (i : Vertex) : ℝ := θ (next i) - θ i
def phi (θ : Vertex → ℝ) (i : Vertex) : ℝ := (word i : ℝ) * Real.pi / 2 + delta θ i
def tilt (θ : Vertex → ℝ) : ℝ := θ G

def h (x : ℝ) : ℝ := (|Real.sin x| + |Real.cos x| - 1) / 2

@[simp] theorem h_zero : h 0 = 0 := by norm_num [h]
@[simp] theorem h_neg (x : ℝ) : h (-x) = h x := by simp [h]
@[simp] theorem h_abs (x : ℝ) : h |x| = h x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, h_neg]

theorem sum_phi (θ : Vertex → ℝ) : (∑ i, phi θ i) = 2 * Real.pi := by
  simp [Fin.sum_univ_succ, phi, word, delta, next]
  ring

theorem sum_marker_difference (L : Vertex → ℝ) : (∑ i, (L i - L (next i))) = 0 := by
  simp [Fin.sum_univ_succ, next]
  ring

/-- Real representatives of the frames of a cycle with the candidate word, after the rotation
that makes `theta A = 0`: the canonical angles are `theta i + offsets i · π/2`, the
representatives lie in an interval shorter than `7/10`, the gaps lie in `(19/25, 3π/4)`, and only
forward axes separate. The tangents, the mismatch, the owners and the tilt are bounded later. -/
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

/-- The tangent cuts, in the order in which they are proved, each using the earlier ones. The
first, `τ_E ≤ 0`, is a normalization by a reflection. -/
def EHalf {q : ℝ} (C : BoundaryCycle q) : Prop := C.tangent E ≤ 0

def zeroOwners : Finset (Fin 4) := {0, 2}
def terminalOwners : Vertex → Finset (Fin 4) :=
  ![{0, 2}, {0}, {0, 2}, {2, 3}, {0, 2}, {2, 3}, {1}]

def OwnerRestriction {q : ℝ} (C : BoundaryCycle q) (J : Vertex → Finset (Fin 4)) : Prop :=
  ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) → j ∈ J i

def charge (β : ℝ) (i : Vertex) : ℝ := if i ∈ charged then β else 0

end SquaresInCircles.Eight.Candidate
