module

public import SquaresInCircles.Eight.Arithmetic.Taylor
public import SquaresInCircles.Eight.Arithmetic.Bernstein
public import SquaresInCircles.Common.Basic
public import SquaresInCircles.Eight.SeparatingAxis

/-!
# Eight squares: margins, charged costs and supports on arcs

On an edge of a boundary cycle, from a source square with state `(a, b)` and sign `σ` to a target
square with state `(A, B)` and sign `τ`, with the angle `φ` between their frames, each of the four
forward axes (`ForwardAxis`) separates the two squares exactly where its margin `forwardMargin`
is nonnegative; `forwardMargin_actual` identifies the margins with those of `SeparatingAxis.lean`.
With an affine label `L(a, b) = c + p a + q b` on each square (`AffineLabel`), the charged cost of
the edge is `φ + L_s(a, b) - L_t(A, B) - β h(φ)` with the frame charge
`h(φ) = (|sin φ| + |cos φ| - 1) / 2` (`chargedCost`, `frameCharge`).

Subtracting a multiple `λ` of a margin from the charged cost leaves a constant plus a linear
function of the source state plus a linear function of the target state, with coefficients that
depend on the axis, `λ`, the signs and `φ` (`lagrangian_identity`). Exchanging the source and the
target and negating both signs exchanges the axes one and three and the axes two and four without
changing the margin (`margin_reverse`), and negating and exchanging the labels keeps the charged
cost (`charge_reverse`).

The rest of the module bounds a linear function `X a + Y b` below on an arc. On the circle with
centre `(v, v)` and radius `ρ` it is at least `v (X + Y) - ρ √(X² + Y²)` (`full_circle_lower`).
On the right half, `a = v + √(ρ² - (b - v)²)` (`circleX`), and an arc is an interval of `b`: for
`X ≥ 0` the function is concave in `b`, so the smaller endpoint value is a lower bound
(`circle_endpoints_lower`); its derivative in `b` is `Y - X r`, with the increasing ratio
`r = (b - v) / (a - v)` (`circleRatio`), so when this slope has one sign at both ends the value at
the lower or at the upper end is a lower bound (`circle_lower_endpoint`,
`circle_upper_endpoint`). On a segment the smaller endpoint value is a lower bound
(`side_endpoint_lower`). `TargetSupport.lean` applies these bounds to the arcs of a table.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Arithmetic

/-- The four forward axes of an edge, in the order of `forwardAxis`: `+f` of the source, `+e` of
the target, `+f` of the target and `-e` of the source. -/
inductive ForwardAxis | one | two | three | four
  deriving DecidableEq

/-- The axis after the source and the target are exchanged (`margin_reverse`). -/
def ForwardAxis.reverse : ForwardAxis → ForwardAxis
  | .one => .three | .two => .four | .three => .one | .four => .two

/-- The number of the axis in `forwardAxis`, from zero. -/
def ForwardAxis.index : ForwardAxis → Fin 4
  | .one => 0 | .two => 1 | .three => 2 | .four => 3

/-- An affine label `c + p a + q b` of the states `(a, b)`. -/
structure AffineLabel where
  c : ℚ
  p : ℚ
  q : ℚ

def AffineLabel.eval (L : AffineLabel) (a b : ℝ) : ℝ := L.c+L.p*a+L.q*b
def AffineLabel.neg (L : AffineLabel) : AffineLabel := ⟨-L.c,-L.p,-L.q⟩

/-- The frame charge `h(φ) = (|sin φ| + |cos φ| - 1) / 2`. -/
def frameCharge (φ : ℝ) : ℝ := (|Real.sin φ|+|Real.cos φ|-1)/2
/-- The width `(1 + |sin φ| + |cos φ|) / 2` in the margins (`pairWidth`). -/
def frameWidth (φ : ℝ) : ℝ := (1+|Real.sin φ|+|Real.cos φ|)/2

/-- The margin of a forward axis for a source state `(a, b)` with sign `σ`, a target state
`(A, B)` with sign `τ` and the angle `φ` between the frames. -/
def forwardMargin (axis : ForwardAxis) (σ τ a b A B φ : ℝ) : ℝ :=
  match axis with
  | .one => σ*b+A*Real.sin φ-τ*B*Real.cos φ-frameWidth φ
  | .two => A-a*Real.cos φ+σ*b*Real.sin φ-frameWidth φ
  | .three => a*Real.sin φ+σ*b*Real.cos φ-τ*B-frameWidth φ
  | .four => a-A*Real.cos φ-τ*B*Real.sin φ-frameWidth φ

/-- The margins are those of `SeparatingAxis.lean`, with the axes numbered from zero. -/
theorem forwardMargin_actual (axis : ForwardAxis) (σ τ a b A B φ : ℝ) :
    forwardMargin axis σ τ a b A B φ =
      SquaresInCircles.Eight.forwardMargin axis.index a b A B σ τ φ := by
  cases axis <;> simp [ForwardAxis.index,forwardMargin,
    SquaresInCircles.Eight.forwardMargin,frameWidth,pairWidth]

/-- The charged cost `φ + L_s(a, b) - L_t(A, B) - β h(φ)` of an edge. -/
def chargedCost (Ls Lt : AffineLabel) (β a b A B φ : ℝ) : ℝ :=
  φ+Ls.eval a b-Lt.eval A B-β*frameCharge φ

/-- Exchanging the source and the target and negating both signs keeps the margin of the
reversed axis. -/
theorem margin_reverse (axis : ForwardAxis) (σ τ a b A B φ : ℝ) :
    forwardMargin axis.reverse (-τ) (-σ) A B a b φ =
      forwardMargin axis σ τ a b A B φ := by
  cases axis <;> simp only [ForwardAxis.reverse,forwardMargin] <;> ring

/-- Exchanging the source and the target and negating both labels keeps the charged cost. -/
theorem charge_reverse (Ls Lt : AffineLabel) (β a b A B φ : ℝ) :
    chargedCost Lt.neg Ls.neg β A B a b φ = chargedCost Ls Lt β a b A B φ := by
  simp only [chargedCost,AffineLabel.eval,AffineLabel.neg]
  push_cast
  ring

/-- The coefficient of `a` in the charged cost less `λ` times the margin of an axis
(`lagrangian_identity`); `sourceY`, `targetX` and `targetY` are those of `b`, `A` and `B`. -/
def sourceX (axis : ForwardAxis) (Ls : AffineLabel) (lam φ : ℝ) : ℝ :=
  match axis with
  | .one => Ls.p | .two => Ls.p+lam*Real.cos φ
  | .three => Ls.p-lam*Real.sin φ | .four => Ls.p-lam

def sourceY (axis : ForwardAxis) (Ls : AffineLabel) (lam σ φ : ℝ) : ℝ :=
  match axis with
  | .one => Ls.q-lam*σ | .two => Ls.q-lam*σ*Real.sin φ
  | .three => Ls.q-lam*σ*Real.cos φ | .four => Ls.q

def targetX (axis : ForwardAxis) (Lt : AffineLabel) (lam φ : ℝ) : ℝ :=
  match axis with
  | .one => -Lt.p-lam*Real.sin φ | .two => -Lt.p-lam
  | .three => -Lt.p | .four => -Lt.p+lam*Real.cos φ

def targetY (axis : ForwardAxis) (Lt : AffineLabel) (lam τ φ : ℝ) : ℝ :=
  match axis with
  | .one => -Lt.q+lam*τ*Real.cos φ | .two => -Lt.q
  | .three => -Lt.q+lam*τ | .four => -Lt.q+lam*τ*Real.sin φ

/-- The constant term of the charged cost less `λ` times a margin. -/
def lagrangianBase (Ls Lt : AffineLabel) (lam β φ : ℝ) : ℝ :=
  φ+(Ls.c : ℝ)-Lt.c+lam*frameWidth φ-β*frameCharge φ

/-- The charged cost less `λ` times a margin is a constant plus linear functions of the source
and the target state. -/
theorem lagrangian_identity (axis : ForwardAxis) (Ls Lt : AffineLabel)
    (lam β σ τ a b A B φ : ℝ) :
    chargedCost Ls Lt β a b A B φ-lam*forwardMargin axis σ τ a b A B φ =
      lagrangianBase Ls Lt lam β φ + sourceX axis Ls lam φ*a +
      sourceY axis Ls lam σ φ*b + targetX axis Lt lam φ*A +
      targetY axis Lt lam τ φ*B := by
  cases axis <;>
    simp only [chargedCost,forwardMargin,lagrangianBase,sourceX,sourceY,
      targetX,targetY,AffineLabel.eval] <;> ring

/-- On the circle `(a - v)² + (b - v)² = ρ²`, `X a + Y b ≥ v (X + Y) - ρ √(X² + Y²)`, by
Cauchy–Schwarz. -/
theorem full_circle_lower {v ρ a b X Y : ℝ} (hρ : 0 ≤ ρ)
    (hcircle : (a-v)^2+(b-v)^2=ρ^2) :
    v*(X+Y)-ρ*Real.sqrt (X^2+Y^2) ≤ X*a+Y*b := by
  have hn := Real.sqrt_nonneg (X^2+Y^2)
  have hs := Real.sq_sqrt (show 0 ≤ X^2+Y^2 by positivity)
  have hid : (X*(a-v)+Y*(b-v))^2+(X*(b-v)-Y*(a-v))^2 =
      (X^2+Y^2)*((a-v)^2+(b-v)^2) := by ring
  rw [hcircle] at hid
  have hprod := mul_nonneg hρ hn
  have hl : -ρ*Real.sqrt (X^2+Y^2) ≤ X*(a-v)+Y*(b-v) := by
    nlinarith [sq_nonneg (X*(b-v)-Y*(a-v))]
  nlinarith only [hl]

/-- A lower bound of `X a + Y b` at the two ends of a segment `b ∈ [l, u]` holds on the whole
segment. -/
theorem side_endpoint_lower {a b l u X Y m : ℝ} (hb : l ≤ b ∧ b ≤ u)
    (hl : m ≤ X*a+Y*l) (hu : m ≤ X*a+Y*u) : m ≤ X*a+Y*b := by
  by_cases hY : 0 ≤ Y
  · have h := mul_le_mul_of_nonneg_left hb.1 hY
    linarith
  · have h := mul_le_mul_of_nonpos_left hb.2 (le_of_not_ge hY)
    linarith

/-- The right half of the circle with centre `(v, v)` and radius `ρ`:
`a = v + √(ρ² - (b - v)²)` as a function of `b`. -/
def circleX (v ρ b : ℝ) : ℝ := v+Real.sqrt (ρ^2-(b-v)^2)
/-- The ratio `(b - v) / (a - v)` on the right half of the circle, the negative of the derivative
of `circleX` (`circleX_deriv`). -/
def circleRatio (v ρ b : ℝ) : ℝ := (b-v)/Real.sqrt (ρ^2-(b-v)^2)

theorem circleX_deriv {v ρ b : ℝ} (hb : 0 < ρ^2-(b-v)^2) :
    HasDerivAt (circleX v ρ) (-circleRatio v ρ b) b := by
  have harg : HasDerivAt (fun y : ℝ => ρ^2-(y-v)^2) (-2*(b-v)) b := by
    convert ((((hasDerivAt_id' b).sub_const v).fun_pow 2).const_sub (ρ^2)) using 1
    norm_num
  have hs := harg.sqrt (ne_of_gt hb)
  convert hs.const_add v using 1
  · rfl
  · dsimp [circleRatio]
    ring

theorem circleRatio_deriv {v ρ b : ℝ} (hb : 0 < ρ^2-(b-v)^2) :
    HasDerivAt (circleRatio v ρ) (ρ^2/(Real.sqrt (ρ^2-(b-v)^2))^3) b := by
  have hr : 0 < Real.sqrt (ρ^2-(b-v)^2) := Real.sqrt_pos.mpr hb
  have hs := (circleX_deriv hb).sub_const v
  have hroot : HasDerivAt (fun y => Real.sqrt (ρ^2-(y-v)^2))
      (-circleRatio v ρ b) b := by simpa [circleX] using hs
  have hd := ((hasDerivAt_id b).sub_const v).div hroot (ne_of_gt hr)
  convert hd using 1
  · rfl
  · dsimp [circleRatio]
    field_simp [ne_of_gt hr]
    nlinarith [Real.sq_sqrt hb.le]

/-- The ratio increases along an arc of the right half. -/
theorem circleRatio_mono {v ρ l u : ℝ}
    (hpos : ∀ b ∈ Icc l u, 0 < ρ^2-(b-v)^2) :
    MonotoneOn (circleRatio v ρ) (Icc l u) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun b hb => (circleRatio_deriv (hpos b hb)).continuousAt.continuousWithinAt)
    (fun b hb => circleRatio_deriv (hpos b ⟨hb.1.le,hb.2.le⟩))
  intro b hb
  exact div_nonneg (sq_nonneg ρ) (by positivity)

theorem circle_functional_deriv {v ρ X Y b : ℝ} (hb : 0 < ρ^2-(b-v)^2) :
    HasDerivAt (fun z => X*circleX v ρ z+Y*z) (Y-X*circleRatio v ρ b) b := by
  convert ((circleX_deriv hb).const_mul X).fun_add ((hasDerivAt_id' b).const_mul Y) using 1
  ring

/-- For `X ≥ 0`, `X a + Y b` is concave in `b` along an arc of the right half. -/
theorem circle_functional_concave {v ρ X Y l u : ℝ} (hX : 0 ≤ X)
    (hpos : ∀ b ∈ Icc l u, 0 < ρ^2-(b-v)^2) :
    ConcaveOn ℝ (Icc l u) (fun b => X*circleX v ρ b+Y*b) := by
  apply concave_of_deriv2
    (fun b hb => circle_functional_deriv (X := X) (Y := Y) (hpos b hb))
    (fun b hb => ((circleRatio_deriv (hpos b hb)).const_mul X).const_sub Y)
  intro b hb
  have hn : 0 ≤ X*(ρ^2/(Real.sqrt (ρ^2-(b-v)^2))^3) :=
    mul_nonneg hX (div_nonneg (sq_nonneg ρ) (pow_nonneg (Real.sqrt_nonneg _) 3))
  linarith

/-- For `X ≥ 0`, a lower bound of `X a + Y b` at the two ends of an arc of the right half holds
on the whole arc. -/
theorem circle_endpoints_lower {v ρ X Y l u b m : ℝ} (hX : 0 ≤ X)
    (hpos : ∀ z ∈ Icc l u, 0 < ρ^2-(z-v)^2) (hb : b ∈ Icc l u)
    (hl : m ≤ X*circleX v ρ l+Y*l) (hu : m ≤ X*circleX v ρ u+Y*u) :
    m ≤ X*circleX v ρ b+Y*b := by
  have hc := circle_functional_concave (Y := Y) hX hpos
  exact (le_min hl hu).trans
    (hc.min_le_of_mem_Icc ⟨le_rfl,hb.1.trans hb.2⟩ ⟨hb.1.trans hb.2,le_rfl⟩ hb)

/-- `Y - X r ≥ 0` at the two ends of an interval of `r` gives it on the whole interval, for
either sign of `X`. -/
theorem affine_of_endpoint_bounds {X Y r rl ru : ℝ} (hr : rl ≤ r ∧ r ≤ ru)
    (hl : 0 ≤ Y-X*rl) (hu : 0 ≤ Y-X*ru) : 0 ≤ Y-X*r := by
  by_cases hX : 0 ≤ X
  · have h := mul_le_mul_of_nonneg_left hr.2 hX
    linarith
  · have h := mul_le_mul_of_nonpos_left hr.1 (le_of_not_ge hX)
    linarith

/-- If the slope `Y - X r` is nonnegative at both ends of an arc of the right half, `X a + Y b`
is least at the lower end. -/
theorem circle_lower_endpoint {v ρ X Y l u b : ℝ}
    (hpos : ∀ z ∈ Icc l u, 0 < ρ^2-(z-v)^2) (hb : b ∈ Icc l u)
    (hl : 0 ≤ Y-X*circleRatio v ρ l) (hu : 0 ≤ Y-X*circleRatio v ρ u) :
    X*circleX v ρ l+Y*l ≤ X*circleX v ρ b+Y*b := by
  have hlu := hb.1.trans hb.2
  have hr := circleRatio_mono hpos
  have hf : MonotoneOn (fun z => X*circleX v ρ z+Y*z) (Icc l u) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun z hz => (circle_functional_deriv (X := X) (Y := Y) (hpos z hz)).continuousAt.continuousWithinAt)
      (fun z hz => circle_functional_deriv (X := X) (Y := Y) (hpos z ⟨hz.1.le,hz.2.le⟩))
    intro z hz
    exact affine_of_endpoint_bounds
      ⟨hr ⟨le_rfl,hlu⟩ ⟨hz.1.le,hz.2.le⟩ hz.1.le,
       hr ⟨hz.1.le,hz.2.le⟩ ⟨hlu,le_rfl⟩ hz.2.le⟩ hl hu
  exact hf ⟨le_rfl,hlu⟩ hb hb.1

/-- If the slope `Y - X r` is nonpositive at both ends of an arc of the right half, `X a + Y b`
is least at the upper end. -/
theorem circle_upper_endpoint {v ρ X Y l u b : ℝ}
    (hpos : ∀ z ∈ Icc l u, 0 < ρ^2-(z-v)^2) (hb : b ∈ Icc l u)
    (hl : Y-X*circleRatio v ρ l ≤ 0) (hu : Y-X*circleRatio v ρ u ≤ 0) :
    X*circleX v ρ u+Y*u ≤ X*circleX v ρ b+Y*b := by
  have h := circle_lower_endpoint (X := -X) (Y := -Y) hpos hb
    (by linarith) (by linarith)
  have hlu := hb.1.trans hb.2
  have hr := circleRatio_mono hpos
  have hf : AntitoneOn (fun z => X*circleX v ρ z+Y*z) (Icc l u) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun z hz => (circle_functional_deriv (X := X) (Y := Y) (hpos z hz)).continuousAt.continuousWithinAt)
      (fun z hz => circle_functional_deriv (X := X) (Y := Y) (hpos z ⟨hz.1.le,hz.2.le⟩))
    intro z hz
    have hh := affine_of_endpoint_bounds (X := -X) (Y := -Y)
      ⟨hr ⟨le_rfl,hlu⟩ ⟨hz.1.le,hz.2.le⟩ hz.1.le,
       hr ⟨hz.1.le,hz.2.le⟩ ⟨hlu,le_rfl⟩ hz.2.le⟩
      (by linarith : 0 ≤ -Y-(-X)*circleRatio v ρ l)
      (by linarith : 0 ≤ -Y-(-X)*circleRatio v ρ u)
    linarith
  exact hf hb ⟨hlu,le_rfl⟩ hb.2

end SquaresInCircles.Eight.Arithmetic
