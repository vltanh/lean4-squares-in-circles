module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic
public import SquaresInCircles.Common.Analysis
public import SquaresInCircles.Eight.Frames.SeparatingAxis

/-!
# Eight squares: state bounds, and owners and signs at small mismatch

In a boundary cycle at a level at most `Q0` every square has `447/800 < a < 283/200` and
`0 ≤ b < 9/10` (`canonical_bounds`), on either radial curve. For a cycle with a candidate frame
the projections of a pair on the four forward axes, less the threshold, are the margins
`forwardMargin` at the angle `phi` (`Frame.margin_identity`). Two consequences follow, in this
order. If the mismatch is at most `2/5`, only the forward axes `0` and `2` can separate the pairs
of the three edges with digit `0` (`zero_owners_of_mismatch`). If it is at most `1/10`, the source
of each such edge has a positive and the target a negative tangent, which fixes the signs of `H`,
`G`, `A`, `B`, `T` and `D` (`signs_of_mismatch`).
-/

section
/-!
## Candidate coordinates

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
end
end
end

section
/-!
## Candidate frames along a radius expansion

If `D` is an expansion of the boundary cycle `C` to a larger level, a candidate frame of `D` is a
candidate frame of `C` with the same angles (`Frame.pullback`, `Frame.pullback_theta`): the two
cycles have the same frames, centre directions and tangents, and every signed axis that separates
two consecutive squares of `C` separates them in `D`, where it is a forward axis.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

def Frame.pullback {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : Frame D) (hR : RadiusExpansion C D) : Frame C where
  theta := F.theta
  theta_A := F.theta_A
  canonical_eq i := by
    have he : C.canonicalAngle i=D.canonicalAngle i := by
      simp [BoundaryCycle.canonicalAngle,BoundaryCycle.alpha,← hR.same_rays,← hR.same_tangents]
    rw [he]
    exact F.canonical_eq i
  spread := F.spread
  gap_lower i := by simpa only [hR.same_rays] using F.gap_lower i
  gap_upper i := by simpa only [hR.same_rays] using F.gap_upper i
  forward_complete i axis hi := F.forward_complete i axis (hR.preserves_all_axes i axis hi)

@[simp] theorem Frame.pullback_theta {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : Frame D) (hR : RadiusExpansion C D) : (F.pullback hR).theta=F.theta := rfl

end SquaresInCircles.Eight.Candidate
end
end
end

section
/-!
## Quarter edges between core squares of opposite signs

On a quarter edge `φ = π/2 + d` from a core square with transverse sign `+1` to one with sign
`-1`, the gap `π/2 + d + arctan (b / a) + arctan (B / A)` is below `7/4`, a bound of every gap of
a cycle (`cycle_gap_lt_seven_quarters`). Since `arctan x ≥ (3/4) x` on `[0, 1]`, a core
transverse coordinate is at most `7/9` of its angle, so `b + B ≤ (7/9)(1/5 - d)`, and then no
forward axis separates the pair, on the whole frame range `|d| ≤ 7/10`
(`core_quarter_opposite_margin`, `quarter_core_opposite_excluded`). The pair tables leave these
pairs out: the word tables through `WordGeometry.original_not_core_excluded`, the affine tables
through `ExcludedArcs` (`Arithmetic/AffineCoverage.lean`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Candidate.Geometric

/-- `arctan x ≥ (3/4) x` on `[0, 1]`: `arctan` is concave there, so it lies above its chord, of
slope `π/4 > 3/4`. -/
theorem arctan_chord {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : (3/4:ℝ)*x ≤ Real.arctan x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) 1) Real.arctan :=
    concave_of_deriv2 (fun y _ => Real.hasDerivAt_arctan y)
      (fun y _ => (hasDerivAt_const y (1:ℝ)).div ((hasDerivAt_pow 2 y).const_add 1)
        (by positivity))
      (fun y hy => div_nonpos_of_nonpos_of_nonneg (by norm_num; linarith [hy.1]) (by positivity))
  have h := hc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show 0 ≤ 1-x by linarith [hx.2]) hx.1 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.arctan_zero, Real.arctan_one] at h
  nlinarith [Real.pi_gt_three]

/-- A core transverse coordinate is at most `7/9` of its angle: `b ≤ (7/9) arctan (b / a)` when
`0 ≤ b ≤ a ≤ 7/12`. -/
theorem core_transverse_le_angle {a b : ℝ} (ha : 0 < a) (hau : a ≤ 7/12) (hb : 0 ≤ b)
    (hab : b ≤ a) : b ≤ (7/9:ℝ)*Real.arctan (b/a) := by
  have h := arctan_chord ⟨div_nonneg hb ha.le, (div_le_one ha).mpr hab⟩
  have he : (b/a)*a=b := div_mul_cancel₀ b (ne_of_gt ha)
  nlinarith [mul_le_mul_of_nonneg_right hau (div_nonneg hb ha.le)]

end SquaresInCircles.Eight.Candidate.Geometric
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

theorem canonical_alpha {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    SquaresInCircles.alpha (C.square i) (0, 0) = C.a i := by
  have hx : frameX (C.square i) (C.square i).center = C.a i := by
    rw [C.center_eq, frameX_rotate]
  have hid : localX (C.square i) (0, 0) = -frameX (C.square i) (C.square i).center := by
    dsimp [localX, frameX]; ring
  simp [SquaresInCircles.alpha, hid, hx, abs_of_pos (C.a_pos i)]

theorem canonical_beta {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    SquaresInCircles.beta (C.square i) (0, 0) = C.b i := by
  have hy : frameY (C.square i) (C.square i).center = -C.sigma i * C.b i := by
    rw [C.center_eq, frameY_rotate]
  have hid : localY (C.square i) (0, 0) = -frameY (C.square i) (C.square i).center := by
    dsimp [localY, frameY]; ring
  rcases C.sigma_sign i with hs | hs <;>
    simp [SquaresInCircles.beta, hid, hy, hs, abs_of_nonneg (C.b_nonneg i)]

theorem canonical_containment {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    SquaresInCircles.phi (C.a i) (C.b i) ≤ q := by
  simpa only [SqContained, canonical_alpha, canonical_beta] using C.contained i

theorem canonical_core_distance {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    (1 / 12 : ℝ) ^ 2 ≤
      (max (C.a i - 1 / 2) 0) ^ 2 + (max (C.b i - 1 / 2) 0) ^ 2 := by
  obtain ⟨p, hp, he⟩ := exists_clipped_point (C.square i) (0, 0)
  have hc := C.core i p hp
  simp only [canonical_alpha, canonical_beta, sub_zero, sub] at he
  simpa [coreRadius, he] using hc

theorem canonical_bounds {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0) (i : Vertex) :
    447 / 800 < C.a i ∧ C.a i < 283 / 200 ∧ 0 ≤ C.b i ∧ C.b i < 9 / 10 := by
  have ha := C.a_pos i
  have hb := C.b_nonneg i
  have hab := C.b_le_a i
  have hp := (canonical_containment C i).trans hq
  have hcore := canonical_core_distance C i
  have haHalf : 1 / 2 < C.a i := by
    by_contra! h
    have h₁ : max (C.a i - 1 / 2) 0 = 0 := max_eq_right (by linarith)
    have h₂ : max (C.b i - 1 / 2) 0 = 0 := max_eq_right (by linarith)
    norm_num [h₁, h₂] at hcore
  have hmax : max (C.a i - 1 / 2) 0 = C.a i - 1 / 2 :=
    max_eq_left (by linarith)
  have hbmax0 : 0 ≤ max (C.b i - 1 / 2) 0 := le_max_right _ _
  have hbmax : max (C.b i - 1 / 2) 0 ≤ C.a i - 1 / 2 :=
    max_le (by linarith) (by linarith)
  rw [hmax] at hcore
  have hbmaxSq : (max (C.b i - 1 / 2) 0) ^ 2 ≤ (C.a i - 1 / 2) ^ 2 :=
    pow_le_pow_left₀ hbmax0 hbmax 2
  have hal : 447 / 800 < C.a i := by
    by_contra! h
    have hsq : (C.a i - 1 / 2) ^ 2 ≤ (47 / 800 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    norm_num at hsq hcore
    linarith
  have hau : C.a i < 283 / 200 := by
    dsimp [SquaresInCircles.phi, Q0] at hp
    nlinarith only [sq_nonneg (C.b i), hb, hp, ha]
  have hbu : C.b i < 9 / 10 := by
    have hsq : (C.b i + 1 / 2) ^ 2 ≤ (C.a i + 1 / 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    dsimp [SquaresInCircles.phi, Q0] at hp
    nlinarith only [hab, hp, hsq, ha, haHalf, hb]
  exact ⟨hal, hau, hb, hbu⟩

theorem signed_b_abs {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    |C.sigma i * C.b i| = C.b i := by
  rcases C.sigma_sign i with hs | hs <;>
    simp [hs, abs_of_nonneg (C.b_nonneg i)]

theorem Frame.relative_phase {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Vertex) :
    C.canonicalAngle (next i) - C.canonicalAngle i =
      phi F.theta i - if i = 6 then 2 * Real.pi else 0 := by
  rw [F.canonical_eq (next i), F.canonical_eq i]
  fin_cases i <;> simp [phi, delta, word, offsets, next] <;> ring

theorem Frame.relative_trig {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Vertex) :
    relativeC (C.square i) (C.square (next i)) = Real.cos (phi F.theta i) ∧
    relativeS (C.square i) (C.square (next i)) = Real.sin (phi F.theta i) := by
  have hci : (C.square i).cosine = Real.cos (C.canonicalAngle i) := C.frame_cos i
  have hsi : (C.square i).sine = Real.sin (C.canonicalAngle i) := C.frame_sin i
  have hcj : (C.square (next i)).cosine = Real.cos (C.canonicalAngle (next i)) := C.frame_cos _
  have hsj : (C.square (next i)).sine = Real.sin (C.canonicalAngle (next i)) := C.frame_sin _
  have hC : relativeC (C.square i) (C.square (next i)) =
      Real.cos (C.canonicalAngle (next i) - C.canonicalAngle i) := by
    simp [relativeC, hci, hsi, hcj, hsj, Real.cos_sub]; ring
  have hS : relativeS (C.square i) (C.square (next i)) =
      Real.sin (C.canonicalAngle (next i) - C.canonicalAngle i) := by
    simp [relativeS, hci, hsi, hcj, hsj, Real.sin_sub]; ring
  rw [F.relative_phase] at hC hS
  by_cases hi : i = 6
  · simpa [hi, Real.cos_sub, Real.sin_sub] using And.intro hC hS
  · simpa [hi] using And.intro hC hS

theorem Frame.margin_identity {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (i : Vertex) (j : Fin 4) :
    (forwardAxis j).projection (C.square i) (C.square (next i)) -
      SAT.threshold (C.square i) (C.square (next i)) = margin C F.theta i j := by
  exact canonical_margin_identity j _ _ _ _ _ _ _ _ _
    (C.center_eq i) (C.center_eq (next i)) (F.relative_trig i).1 (F.relative_trig i).2

theorem Frame.margin_nonneg_iff {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (i : Vertex) (j : Fin 4) :
    (forwardAxis j).Feasible (C.square i) (C.square (next i)) ↔ 0 ≤ margin C F.theta i j := by
  rw [← F.margin_identity]
  exact (sub_nonneg).symm

end SquaresInCircles.Eight.Candidate
end
end
end
