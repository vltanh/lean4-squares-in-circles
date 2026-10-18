module

public import SquaresInCircles.Eight.Arithmetic.Taylor
public import SquaresInCircles.Eight.Arithmetic.Bernstein
public import SquaresInCircles.Common.Basic
public import SquaresInCircles.Eight.SeparatingAxis

/-!
# Semantic affine-arc pair kernel

The four margins are hand equations (7.2)/(7), in their original numbering.
Original axes are retained in the theorem arguments.  Reflection/reversal
changes the labels as well as signs, so charged costs remain attached to the
original ordered edge.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Arithmetic

inductive ForwardAxis | one | two | three | four
  deriving DecidableEq, Repr

instance : Fintype ForwardAxis where
  elems := {.one, .two, .three, .four}
  complete x := by cases x <;> decide

def ForwardAxis.reverse : ForwardAxis → ForwardAxis
  | .one => .three | .two => .four | .three => .one | .four => .two

def ForwardAxis.index : ForwardAxis → Fin 4
  | .one => 0 | .two => 1 | .three => 2 | .four => 3

structure AffineLabel where
  c : ℚ
  p : ℚ
  q : ℚ
  deriving DecidableEq, Repr

def AffineLabel.eval (L : AffineLabel) (a b : ℝ) : ℝ := L.c+L.p*a+L.q*b
def AffineLabel.neg (L : AffineLabel) : AffineLabel := ⟨-L.c,-L.p,-L.q⟩

def frameCharge (φ : ℝ) : ℝ := (|Real.sin φ|+|Real.cos φ|-1)/2
def frameWidth (φ : ℝ) : ℝ := (1+|Real.sin φ|+|Real.cos φ|)/2

def forwardMargin (axis : ForwardAxis) (σ τ a b A B φ : ℝ) : ℝ :=
  match axis with
  | .one => σ*b+A*Real.sin φ-τ*B*Real.cos φ-frameWidth φ
  | .two => A-a*Real.cos φ+σ*b*Real.sin φ-frameWidth φ
  | .three => a*Real.sin φ+σ*b*Real.cos φ-τ*B-frameWidth φ
  | .four => a-A*Real.cos φ-τ*B*Real.sin φ-frameWidth φ

theorem forwardMargin_actual (axis : ForwardAxis) (σ τ a b A B φ : ℝ) :
    forwardMargin axis σ τ a b A B φ =
      SquaresInCircles.Eight.forwardMargin axis.index a b A B σ τ φ := by
  cases axis <;> simp [ForwardAxis.index,forwardMargin,
    SquaresInCircles.Eight.forwardMargin,frameWidth,pairWidth]

theorem actual_axis_iff_margin (axis : ForwardAxis) (σ τ a b A B φ : ℝ) :
    (forwardAxis axis.index).Feasible (localSource a b σ) (localTarget A B τ φ) ↔
      0 ≤ forwardMargin axis σ τ a b A B φ := by
  rw [forwardMargin_actual]
  exact forward_feasible_iff_margin axis.index a b A B σ τ φ

def chargedCost (Ls Lt : AffineLabel) (β a b A B φ : ℝ) : ℝ :=
  φ+Ls.eval a b-Lt.eval A B-β*frameCharge φ

theorem margin_reverse (axis : ForwardAxis) (σ τ a b A B φ : ℝ) :
    forwardMargin axis.reverse (-τ) (-σ) A B a b φ =
      forwardMargin axis σ τ a b A B φ := by
  cases axis <;> simp only [ForwardAxis.reverse,forwardMargin] <;> ring

theorem charge_reverse (Ls Lt : AffineLabel) (β a b A B φ : ℝ) :
    chargedCost Lt.neg Ls.neg β A B a b φ = chargedCost Ls Lt β a b A B φ := by
  simp only [chargedCost,AffineLabel.eval,AffineLabel.neg]
  push_cast
  ring

/-- Coefficients of the four original-axis Lagrangians. -/
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

def lagrangianBase (Ls Lt : AffineLabel) (lam β φ : ℝ) : ℝ :=
  φ+(Ls.c : ℝ)-Lt.c+lam*frameWidth φ-β*frameCharge φ

theorem lagrangian_identity (axis : ForwardAxis) (Ls Lt : AffineLabel)
    (lam β σ τ a b A B φ : ℝ) :
    chargedCost Ls Lt β a b A B φ-lam*forwardMargin axis σ τ a b A B φ =
      lagrangianBase Ls Lt lam β φ + sourceX axis Ls lam φ*a +
      sourceY axis Ls lam σ φ*b + targetX axis Lt lam φ*A +
      targetY axis Lt lam τ φ*B := by
  cases axis <;>
    simp only [chargedCost,forwardMargin,lagrangianBase,sourceX,sourceY,
      targetX,targetY,AffineLabel.eval] <;> push_cast <;> ring

theorem charged_pair_gt_of_support {axis : ForwardAxis} {Ls Lt : AffineLabel}
    {lam β σ τ a b A B φ sourceLower targetLower γ : ℝ}
    (hlam : 0 ≤ lam) (haxis : 0 ≤ forwardMargin axis σ τ a b A B φ)
    (hs : sourceLower ≤ sourceX axis Ls lam φ*a+sourceY axis Ls lam σ φ*b)
    (ht : targetLower ≤ targetX axis Lt lam φ*A+targetY axis Lt lam τ φ*B)
    (hcost : γ < lagrangianBase Ls Lt lam β φ+sourceLower+targetLower) :
    γ < chargedCost Ls Lt β a b A B φ := by
  have hid := lagrangian_identity axis Ls Lt lam β σ τ a b A B φ
  have hn := mul_nonneg hlam haxis
  linarith

/-- Full-circle support is valid without locating the minimizing point in an
arc.  The explicit circle equation is the semantic premise. -/
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

theorem full_circle_majorant_lower {v ρ a b X Y h : ℝ}
    (hρ : 0 ≤ ρ) (hh : 0 < h) (hcircle : (a-v)^2+(b-v)^2=ρ^2) :
    v*(X+Y)-ρ*radicalMajorant h (X^2+Y^2) ≤ X*a+Y*b := by
  have ht := mul_le_mul_of_nonneg_left
    (sqrt_le_radicalMajorant hh (by positivity : 0 ≤ X^2+Y^2)) hρ
  have hc := full_circle_lower hρ hcircle (X := X) (Y := Y)
  linarith

/-- A straight-side functional is affine in its free coordinate. -/
theorem side_endpoint_lower {a b l u X Y m : ℝ} (hb : l ≤ b ∧ b ≤ u)
    (hl : m ≤ X*a+Y*l) (hu : m ≤ X*a+Y*u) : m ≤ X*a+Y*b := by
  by_cases hY : 0 ≤ Y
  · have h := mul_le_mul_of_nonneg_left hb.1 hY
    linarith
  · have h := mul_le_mul_of_nonpos_left hb.2 (le_of_not_ge hY)
    linarith

def circleX (v ρ b : ℝ) : ℝ := v+Real.sqrt (ρ^2-(b-v)^2)
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

theorem circle_endpoints_lower {v ρ X Y l u b m : ℝ} (hX : 0 ≤ X)
    (hpos : ∀ z ∈ Icc l u, 0 < ρ^2-(z-v)^2) (hb : b ∈ Icc l u)
    (hl : m ≤ X*circleX v ρ l+Y*l) (hu : m ≤ X*circleX v ρ u+Y*u) :
    m ≤ X*circleX v ρ b+Y*b := by
  have hc := circle_functional_concave (Y := Y) hX hpos
  exact (le_min hl hu).trans
    (hc.min_le_of_mem_Icc ⟨le_rfl,hb.1.trans hb.2⟩ ⟨hb.1.trans hb.2,le_rfl⟩ hb)

/-- Affineness in the monotone ratio validates both endpoint derivative tests,
including X = 0 and either sign of X. -/
theorem affine_of_endpoint_bounds {X Y r rl ru : ℝ} (hr : rl ≤ r ∧ r ≤ ru)
    (hl : 0 ≤ Y-X*rl) (hu : 0 ≤ Y-X*ru) : 0 ≤ Y-X*r := by
  by_cases hX : 0 ≤ X
  · have h := mul_le_mul_of_nonneg_left hr.2 hX
    linarith
  · have h := mul_le_mul_of_nonpos_left hr.1 (le_of_not_ge hX)
    linarith

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
