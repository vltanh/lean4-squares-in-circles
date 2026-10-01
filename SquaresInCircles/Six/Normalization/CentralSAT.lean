import SquaresInCircles.Six.Normalization.CenterRadius
import SquaresInCircles.Six.SquareSupport
import SquaresInCircles.Seven.SeparatingAxes

/-!
# Separating axes of the central square

Let an exterior square have frame angle `t` and centre `(a, b)` in its frame,
with `a ≥ 1/2`, and let the central square be axis-parallel with centre
`(cx, cy)` in `[0, 1/2]²`. If their interiors are disjoint, one of seven
margins is nonnegative (`central_separators_complete`): along the own axis of
the square, pointing away from the central square; along its secondary axis,
in either direction; or along one of the four sides of the central square. The
own axis pointing the other way is impossible, since `a ≥ 1/2` and the central
square contains the origin. The threshold is `1/2 + angularWidth t`. A
nonnegative margin along a side puts the whole closed square beyond that side.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- The seven axes along which an exterior square can be separated from the
central square: its own axis, its secondary axis in either direction, and the
four sides of the central square. -/
inductive CentralAxis where
  | own | secPlus | secMinus | east | west | north | south
  deriving DecidableEq, Repr

/-- `(|cos t| + |sin t|)/2`, the half-width along a coordinate axis of a unit
square at angle `t`. -/
def angularWidth (t : ℝ) : ℝ := (|Real.cos t|+|Real.sin t|)/2

def centerX (t a b : ℝ) : ℝ := a*Real.cos t-b*Real.sin t
def centerY (t a b : ℝ) : ℝ := a*Real.sin t+b*Real.cos t

def centralNormal (t cx cy : ℝ) : ℝ := cx*Real.cos t+cy*Real.sin t
def centralTransverse (t cx cy : ℝ) : ℝ := -cx*Real.sin t+cy*Real.cos t

/-- The separating inequality of the exterior square and the central square
along the axis `k`, as a margin: it is nonnegative when they are separated
along `k`. -/
def centralMargin (k : CentralAxis) (t a b cx cy : ℝ) : ℝ :=
  match k with
  | .own => a-1/2-centralNormal t cx cy-angularWidth t
  | .secPlus => b-1/2-centralTransverse t cx cy-angularWidth t
  | .secMinus => centralTransverse t cx cy-1/2-angularWidth t-b
  | .east => centerX t a b-angularWidth t-cx-1/2
  | .west => cx-1/2-centerX t a b-angularWidth t
  | .north => centerY t a b-angularWidth t-cy-1/2
  | .south => cy-1/2-centerY t a b-angularWidth t

lemma centralNormal_le_width {t cx cy : ℝ}
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx : cx ≤ 1/2) (hy : cy ≤ 1/2) :
    centralNormal t cx cy ≤ angularWidth t := by
  have hc := mul_le_mul_of_nonneg_left (le_abs_self (Real.cos t)) hx0
  have hs := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin t)) hy0
  have hcx := mul_le_mul_of_nonneg_right hx (abs_nonneg (Real.cos t))
  have hcy := mul_le_mul_of_nonneg_right hy (abs_nonneg (Real.sin t))
  dsimp [centralNormal,angularWidth]
  linarith

lemma central_threshold (t a b cx cy : ℝ) :
    Seven.SAT.threshold (axisSquare (cx,cy)) (orientedSquare t a b) = 1/2+angularWidth t := by
  simp only [Seven.SAT.threshold,relativeC,relativeS,axisSquare,orientedSquare,
    one_mul,zero_mul,zero_add,add_zero,neg_zero]
  dsimp [angularWidth]
  ring

lemma primary_difference (t a b cx cy : ℝ) :
    frameX (orientedSquare t a b)
      (sub (orientedSquare t a b).center (cx,cy)) = a-centralNormal t cx cy := by
  dsimp [frameX,orientedSquare,sub,centralNormal]
  linear_combination a*(Real.sin_sq_add_cos_sq t)

lemma secondary_difference (t a b cx cy : ℝ) :
    frameY (orientedSquare t a b)
      (sub (orientedSquare t a b).center (cx,cy)) = b-centralTransverse t cx cy := by
  dsimp [frameY,orientedSquare,sub,centralTransverse]
  linear_combination b*(Real.sin_sq_add_cos_sq t)

/-- An exterior square with interior disjoint from the central square has a
nonnegative margin along one of the seven axes. -/
theorem central_separators_complete {t a b cx cy : ℝ}
    (ha : 1/2 ≤ a) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ 1/2) (hy : cy ≤ 1/2)
    (hd : ∀ p, ¬ (openSquare (axisSquare (cx,cy)) p ∧
      openSquare (orientedSquare t a b) p)) :
    ∃ k : CentralAxis, 0 ≤ centralMargin k t a b cx cy := by
  have hs := Seven.SAT.separating_axes (axisSquare (cx,cy)) (orientedSquare t a b) hd
  rw [central_threshold,primary_difference,secondary_difference] at hs
  have hX : frameX (axisSquare (cx,cy))
      (sub (orientedSquare t a b).center (axisSquare (cx,cy)).center) = centerX t a b-cx := by
    simp [frameX,axisSquare,orientedSquare,sub,centerX]
  have hY : frameY (axisSquare (cx,cy))
      (sub (orientedSquare t a b).center (axisSquare (cx,cy)).center) = centerY t a b-cy := by
    simp [frameY,axisSquare,orientedSquare,sub,centerY]
  rw [hX,hY] at hs
  have hN : centralNormal t (axisSquare (cx,cy)).center.1 (axisSquare (cx,cy)).center.2 =
      centralNormal t cx cy := rfl
  have hT : centralTransverse t (axisSquare (cx,cy)).center.1 (axisSquare (cx,cy)).center.2 =
      centralTransverse t cx cy := rfl
  rw [hN,hT] at hs
  rcases hs with hs | hs | hs | hs
  · by_cases h0 : 0 ≤ centerX t a b-cx
    · rw [abs_of_nonneg h0] at hs
      exact ⟨.east,by dsimp [centralMargin]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge h0)] at hs
      exact ⟨.west,by dsimp [centralMargin]; linarith⟩
  · by_cases h0 : 0 ≤ centerY t a b-cy
    · rw [abs_of_nonneg h0] at hs
      exact ⟨.north,by dsimp [centralMargin]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge h0)] at hs
      exact ⟨.south,by dsimp [centralMargin]; linarith⟩
  · by_cases h0 : 0 ≤ a-centralNormal t cx cy
    · rw [abs_of_nonneg h0] at hs
      exact ⟨.own,by dsimp [centralMargin]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge h0)] at hs
      have hc := centralNormal_le_width (t := t) hx0 hy0 hx hy
      linarith
  · by_cases h0 : 0 ≤ b-centralTransverse t cx cy
    · rw [abs_of_nonneg h0] at hs
      exact ⟨.secPlus,by dsimp [centralMargin]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge h0)] at hs
      exact ⟨.secMinus,by dsimp [centralMargin]; linarith⟩

lemma oriented_x_width (t a b : ℝ) : width (orientedSquare t a b) (1,0) = angularWidth t := by
  simp [width,frameX,frameY,orientedSquare,angularWidth,abs_neg]

lemma oriented_y_width (t a b : ℝ) : width (orientedSquare t a b) (0,1) = angularWidth t := by
  simp [width,frameX,frameY,orientedSquare,angularWidth,add_comm]

lemma closed_center_coordinate_bounds {t a b : ℝ} {p : Point}
    (hp : closedSquare (orientedSquare t a b) p) :
    (centerX t a b-angularWidth t ≤ p.1 ∧ p.1 ≤ centerX t a b+angularWidth t) ∧
    (centerY t a b-angularWidth t ≤ p.2 ∧ p.2 ≤ centerY t a b+angularWidth t) := by
  have hx := Six.closed_projection_bounds (orientedSquare t a b) (1,0) hp
  have hy := Six.closed_projection_bounds (orientedSquare t a b) (0,1) hp
  rw [oriented_x_width] at hx
  rw [oriented_y_width] at hy
  simpa [dot,orientedSquare,centerX,centerY] using And.intro hx hy

lemma east_margin_cap {t a b cx cy : ℝ} (he : 0 ≤ centralMargin .east t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → cx+1/2 ≤ p.1 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).1.1
  dsimp [centralMargin] at he
  linarith

lemma west_margin_cap {t a b cx cy : ℝ} (hw : 0 ≤ centralMargin .west t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → p.1 ≤ cx-1/2 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).1.2
  dsimp [centralMargin] at hw
  linarith

lemma north_margin_cap {t a b cx cy : ℝ} (hn : 0 ≤ centralMargin .north t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → cy+1/2 ≤ p.2 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).2.1
  dsimp [centralMargin] at hn
  linarith

lemma south_margin_cap {t a b cx cy : ℝ} (hs : 0 ≤ centralMargin .south t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → p.2 ≤ cy-1/2 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).2.2
  dsimp [centralMargin] at hs
  linarith

end SquaresInCircles.Six.Normalization
