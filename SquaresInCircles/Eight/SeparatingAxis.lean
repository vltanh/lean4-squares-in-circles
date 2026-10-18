module

public import SquaresInCircles.Eight.Model
public import SquaresInCircles.Common.Contacts

/-!
# All eight signed separating axes and the four forward margins

F0 source draft. The four owner labels and the sign are independent.
Existence comes from the repository SAT theorem; the converse is proved
using the strict support of an open square. Equalities are allowed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight

def AxisOwner.projection (a : AxisOwner) (K L : UnitSquare) : ℝ :=
  match a with
  | .sourceX => frameX K (sub L.center K.center)
  | .sourceY => frameY K (sub L.center K.center)
  | .targetX => frameX L (sub L.center K.center)
  | .targetY => frameY L (sub L.center K.center)

theorem SignedAxis.projection_eq (a : SignedAxis) (K L : UnitSquare) :
    a.projection K L = a.sign.value * a.owner.projection K L := by
  cases a with
  | mk owner sign =>
    cases owner <;> cases sign <;>
      simp [SignedAxis.projection, SignedAxis.normal, AxisOwner.normal,
        AxisOwner.projection, AxisSign.value, e, f, dot, scale, frameX, frameY] <;> ring

theorem signed_projection_exists (owner : AxisOwner) (K L : UnitSquare)
    (h : SAT.threshold K L ≤ |owner.projection K L|) :
    ∃ a : SignedAxis, a.owner = owner ∧ a.Feasible K L := by
  by_cases hp : 0 ≤ owner.projection K L
  · exact ⟨⟨owner, .positive⟩, rfl, by
      simpa [SignedAxis.Feasible, SignedAxis.projection_eq, AxisSign.value,
        abs_of_nonneg hp] using h⟩
  · exact ⟨⟨owner, .negative⟩, rfl, by
      simpa [SignedAxis.Feasible, SignedAxis.projection_eq, AxisSign.value,
        abs_of_neg (lt_of_not_ge hp)] using h⟩

theorem signed_axis_of_disjoint (K L : UnitSquare)
    (h : ∀ p, ¬ (openSquare K p ∧ openSquare L p)) :
    ∃ a : SignedAxis, a.Feasible K L := by
  rcases SAT.separating_axes K L h with h | h | h | h
  · obtain ⟨a, _, ha⟩ := signed_projection_exists .sourceX K L h
    exact ⟨a, ha⟩
  · obtain ⟨a, _, ha⟩ := signed_projection_exists .sourceY K L h
    exact ⟨a, ha⟩
  · obtain ⟨a, _, ha⟩ := signed_projection_exists .targetX K L h
    exact ⟨a, ha⟩
  · obtain ⟨a, _, ha⟩ := signed_projection_exists .targetY K L h
    exact ⟨a, ha⟩

theorem threshold_comm (K L : UnitSquare) : SAT.threshold K L = SAT.threshold L K := by
  have hc : relativeC K L = relativeC L K := by dsimp [relativeC]; ring
  have hs : relativeS K L = -relativeS L K := by dsimp [relativeS]; ring
  simp [SAT.threshold, hc, hs]

theorem threshold_ge_one (K L : UnitSquare) : 1 ≤ SAT.threshold K L := by
  have hu := relative_unit K L
  have hc := abs_nonneg (relativeC K L)
  have hs := abs_nonneg (relativeS K L)
  have hm := mul_nonneg hc hs
  dsimp [SAT.threshold]
  nlinarith [sq_abs (relativeC K L), sq_abs (relativeS K L)]

theorem width_e_self (K : UnitSquare) : width K (e K) = 1 / 2 := by
  have hx : frameX K (e K) = 1 := by simpa [frameX, e, pow_two] using K.unit
  have hy : frameY K (e K) = 0 := by dsimp [frameY, e]; ring
  norm_num [width, hx, hy]

theorem width_f_self (K : UnitSquare) : width K (f K) = 1 / 2 := by
  have hx : frameX K (f K) = 0 := by dsimp [frameX, f]; ring
  have hy : frameY K (f K) = 1 := by
    dsimp [frameY, f]
    nlinarith [K.unit]
  norm_num [width, hx, hy]

theorem width_e_other (K L : UnitSquare) :
    width L (e K) = (|relativeC K L| + |relativeS K L|) / 2 := by
  have hx : frameX L (e K) = relativeC K L := by dsimp [frameX, e, relativeC]; ring
  have hy : frameY L (e K) = -relativeS K L := by dsimp [frameY, e, relativeS]; ring
  simp [width, hx, hy]

theorem width_f_other (K L : UnitSquare) :
    width L (f K) = (|relativeC K L| + |relativeS K L|) / 2 := by
  have hx : frameX L (f K) = relativeS K L := by dsimp [frameX, f, relativeS]; ring
  have hy : frameY L (f K) = relativeC K L := by dsimp [frameY, f, relativeC]; ring
  simp [width, hx, hy, add_comm]

theorem owner_width_sum (a : AxisOwner) (K L : UnitSquare) :
    width K (a.normal K L) + width L (a.normal K L) = SAT.threshold K L := by
  cases a
  · rw [AxisOwner.normal, width_e_self, width_e_other]; unfold SAT.threshold; ring
  · rw [AxisOwner.normal, width_f_self, width_f_other]; unfold SAT.threshold; ring
  · rw [AxisOwner.normal, width_e_other, width_e_self, threshold_comm]
    unfold SAT.threshold; ring
  · rw [AxisOwner.normal, width_f_other, width_f_self, threshold_comm]
    unfold SAT.threshold; ring

theorem signed_width_sum (a : SignedAxis) (K L : UnitSquare) :
    width K (a.normal K L) + width L (a.normal K L) = SAT.threshold K L := by
  cases a with
  | mk owner sign =>
    cases sign
    · simpa [SignedAxis.normal, AxisSign.value, scale] using owner_width_sum owner K L
    · simpa only [SignedAxis.normal, AxisSign.value, width_neg] using owner_width_sum owner K L

theorem signed_normal_unit (a : SignedAxis) (K L : UnitSquare) :
    normSq (a.normal K L) = 1 := by
  cases a with
  | mk owner sign =>
    cases owner <;> cases sign <;>
      simp [SignedAxis.normal, AxisOwner.normal, AxisSign.value, scale, e, f, normSq] <;>
      nlinarith [K.unit, L.unit]

theorem signed_normal_nonzero (a : SignedAxis) (K L : UnitSquare) :
    a.normal K L ≠ (0, 0) := by
  intro h
  have hh := signed_normal_unit a K L
  rw [h] at hh
  norm_num [normSq] at hh

theorem open_point_strict_support (K : UnitSquare) {n p : Point}
    (hn : n ≠ (0, 0)) (hp : openSquare K p) :
    |dot n (sub p K.center)| < width K n := by
  have hnorm := frame_norm K n
  have hab : 0 < |frameX K n| + |frameY K n| := by
    have hpos := normSq_pos_of_ne hn
    have hx := abs_nonneg (frameX K n)
    have hy := abs_nonneg (frameY K n)
    nlinarith [sq_abs (frameX K n), sq_abs (frameY K n)]
  have hid : dot n (sub p K.center) =
      frameX K n * localX K p + frameY K n * localY K p := by
    simpa [frameX, frameY, localX, localY, sub] using (frame_dot K n (sub p K.center)).symm
  have hw := weighted_strict (abs_nonneg (frameX K n)) (abs_nonneg (frameY K n))
    hab hp.1 hp.2
  rw [hid]
  calc
    |frameX K n * localX K p + frameY K n * localY K p|
        ≤ |frameX K n| * |localX K p| + |frameY K n| * |localY K p| := by
          simpa [abs_mul] using abs_add_le (frameX K n * localX K p)
            (frameY K n * localY K p)
    _ < width K n := by simpa [width, div_eq_mul_inv, mul_comm] using hw

theorem SignedAxis.disjoint {a : SignedAxis} {K L : UnitSquare}
    (h : a.Feasible K L) : ∀ p, ¬ (openSquare K p ∧ openSquare L p) := by
  intro p hp
  have hK := open_point_strict_support K (signed_normal_nonzero a K L) hp.1
  have hL := open_point_strict_support L (signed_normal_nonzero a K L) hp.2
  have hid : dot (a.normal K L) (sub L.center K.center) =
      dot (a.normal K L) (sub p K.center) - dot (a.normal K L) (sub p L.center) := by
    dsimp [dot, sub]; ring
  have hproj : a.projection K L < width K (a.normal K L) + width L (a.normal K L) := by
    dsimp [SignedAxis.projection]
    rw [hid]
    linarith [le_abs_self (dot (a.normal K L) (sub p K.center)),
      neg_le_abs (dot (a.normal K L) (sub p L.center))]
  rw [signed_width_sum] at hproj
  exact (not_lt_of_ge h) hproj

theorem disjoint_iff_signed_axis (K L : UnitSquare) :
    (∀ p, ¬ (openSquare K p ∧ openSquare L p)) ↔ ∃ a : SignedAxis, a.Feasible K L :=
  ⟨signed_axis_of_disjoint K L, fun ⟨a, ha⟩ => ha.disjoint⟩

def AxisOwner.swap : AxisOwner → AxisOwner
  | .sourceX => .targetX | .sourceY => .targetY
  | .targetX => .sourceX | .targetY => .sourceY

def SignedAxis.reverse (a : SignedAxis) : SignedAxis := ⟨a.owner.swap, a.sign.flip⟩

theorem reverse_projection (a : SignedAxis) (K L : UnitSquare) :
    a.reverse.projection L K = a.projection K L := by
  cases a with
  | mk owner sign =>
    cases owner <;> cases sign <;>
      simp [SignedAxis.reverse, SignedAxis.projection, SignedAxis.normal,
        AxisOwner.swap, AxisOwner.normal, AxisSign.flip, AxisSign.value, scale,
        e, f, dot, sub] <;> ring

theorem reverse_feasible_iff (a : SignedAxis) (K L : UnitSquare) :
    a.reverse.Feasible L K ↔ a.Feasible K L := by
  simp only [SignedAxis.Feasible, reverse_projection, threshold_comm L K]

/-- Original forward-axis numbering in hand equation (7.2), zero based. -/
def forwardAxis (j : Fin 4) : SignedAxis :=
  ![⟨.sourceY, .positive⟩, ⟨.targetX, .positive⟩,
    ⟨.targetY, .positive⟩, ⟨.sourceX, .negative⟩] j

def pairWidth (φ : ℝ) : ℝ := (1 + |Real.sin φ| + |Real.cos φ|) / 2

def forwardMargin (j : Fin 4) (a b A B σ τ φ : ℝ) : ℝ :=
  ![σ * b + A * Real.sin φ - τ * B * Real.cos φ - pairWidth φ,
    A - a * Real.cos φ + σ * b * Real.sin φ - pairWidth φ,
    a * Real.sin φ + σ * b * Real.cos φ - τ * B - pairWidth φ,
    a - A * Real.cos φ - τ * B * Real.sin φ - pairWidth φ] j

def localSource (a b σ : ℝ) : UnitSquare := axisSquare (a, -σ * b)

def localTarget (A B τ φ : ℝ) : UnitSquare where
  center := (A * Real.cos φ + τ * B * Real.sin φ,
    A * Real.sin φ - τ * B * Real.cos φ)
  cosine := Real.cos φ
  sine := Real.sin φ
  unit := by nlinarith [Real.sin_sq_add_cos_sq φ]

theorem local_threshold (a b A B σ τ φ : ℝ) :
    SAT.threshold (localSource a b σ) (localTarget A B τ φ) = pairWidth φ := by
  simp [SAT.threshold, localSource, localTarget, axisSquare,
    relativeC, relativeS, pairWidth, add_comm]

theorem forward_margin_identity (j : Fin 4) (a b A B σ τ φ : ℝ) :
    (forwardAxis j).projection (localSource a b σ) (localTarget A B τ φ) -
      SAT.threshold (localSource a b σ) (localTarget A B τ φ) =
        forwardMargin j a b A B σ τ φ := by
  rw [local_threshold]
  fin_cases j <;>
    simp [forwardAxis, forwardMargin, SignedAxis.projection, SignedAxis.normal,
      AxisOwner.normal, AxisSign.value, localSource, localTarget, axisSquare,
      e, f, dot, scale, sub] <;>
    nlinarith [Real.sin_sq_add_cos_sq φ]

theorem forward_feasible_iff_margin (j : Fin 4) (a b A B σ τ φ : ℝ) :
    (forwardAxis j).Feasible (localSource a b σ) (localTarget A B τ φ) ↔
      0 ≤ forwardMargin j a b A B σ τ φ := by
  rw [← forward_margin_identity]
  exact (sub_nonneg).symm

theorem frameX_sub (K : UnitSquare) (p r : Point) :
    frameX K (sub p r) = frameX K p - frameX K r := by
  dsimp [frameX, sub]; ring

theorem frameY_sub (K : UnitSquare) (p r : Point) :
    frameY K (sub p r) = frameY K p - frameY K r := by
  dsimp [frameY, sub]; ring

theorem frameX_rotate (K : UnitSquare) (p : Point) : frameX K (rotate K p) = p.1 := by
  dsimp [frameX, rotate]
  linear_combination p.1 * K.unit

theorem frameY_rotate (K : UnitSquare) (p : Point) : frameY K (rotate K p) = p.2 := by
  dsimp [frameY, rotate]
  linear_combination p.2 * K.unit

/-- The canonical-pair formulas hold in any global frame. -/
theorem canonical_margin_identity (j : Fin 4) (K L : UnitSquare) (a b A B σ τ φ : ℝ)
    (hK : K.center = rotate K (a, -σ * b))
    (hL : L.center = rotate L (A, -τ * B))
    (hc : relativeC K L = Real.cos φ) (hs : relativeS K L = Real.sin φ) :
    (forwardAxis j).projection K L - SAT.threshold K L =
      forwardMargin j a b A B σ τ φ := by
  have hKx : frameX K K.center = a := by rw [hK, frameX_rotate]
  have hKy : frameY K K.center = -σ * b := by rw [hK, frameY_rotate]
  have hLx : frameX L L.center = A := by rw [hL, frameX_rotate]
  have hLy : frameY L L.center = -τ * B := by rw [hL, frameY_rotate]
  have hc' : relativeC L K = Real.cos φ := by
    calc relativeC L K = relativeC K L := by dsimp [relativeC]; ring
      _ = Real.cos φ := hc
  have hs' : relativeS L K = -Real.sin φ := by
    calc relativeS L K = -relativeS K L := by dsimp [relativeS]; ring
      _ = -Real.sin φ := by rw [hs]
  obtain ⟨hKLx, hKLy⟩ := relative_normal K L K.center
  obtain ⟨hLKx, hLKy⟩ := relative_normal L K L.center
  rw [hKx, hKy, hc, hs] at hKLx hKLy
  rw [hLx, hLy, hc', hs'] at hLKx hLKy
  have hw : SAT.threshold K L = pairWidth φ := by
    simp [SAT.threshold, hc, hs, pairWidth, add_comm]
  fin_cases j <;>
    simp [forwardAxis, forwardMargin, SignedAxis.projection_eq,
      AxisOwner.projection, AxisSign.value, frameX_sub, frameY_sub,
      hKx, hKy, hLx, hLy, hKLx, hKLy, hLKx, hLKy, hw] <;> ring

end SquaresInCircles.Eight
