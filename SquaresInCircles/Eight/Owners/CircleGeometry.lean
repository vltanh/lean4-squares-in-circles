module

public import SquaresInCircles.Eight.Frames.Signed.Coordinates

/-!
# Eight squares: circles, the core and uniform geometric reserves

The radius levels `qLow`, `qTrial`, `qCap`, the frame bound `frameCap`, and bounds on signed points
that follow from a circle equation or from an inequality on a whole interval: the diagonal and
axis coordinates of a point on the circle (`outer_bounds`, `uniform_circle_reserves`), the flat
side `a = 7/12` of the core (`flat_core_iff`, `flat`), the point `outerAt q y` of the circle, and
the radial alternative of a boundary E (`boundary_radial_alternative`). Radii are squared radii
throughout; constructed points use the radius `q` itself, and `qCap` enters only the estimates.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight

abbrev qLow : ℝ := 19577/5000
abbrev qTrial : ℝ := 1957767069/500000000
abbrev qCap : ℝ := 9789/2500
abbrev frameCap : ℝ := 7/10

def diagonalCoordinate (q : ℝ) : ℝ := Real.sqrt (q/2)-1/2
def axisCoordinate (q : ℝ) : ℝ := Real.sqrt (q-1/4)-1/2

theorem uniform_radius_order :
    (5/2 : ℝ)<qLow ∧ qLow<qTrial ∧ qTrial<qCap ∧ qCap<4 := by
  norm_num [qLow,qTrial,qCap]

namespace SignedPoint

theorem circle_nonneg (p : SignedPoint) : 0 ≤ p.circle := by
  unfold circle
  positivity

theorem primary_gt_half {p : SignedPoint} (hs : p.Sorted) (hc : p.AvoidsCore) :
    1/2 < p.a := by
  by_contra! h
  have ha : max (p.a-1/2) 0=0 := max_eq_right (by linarith)
  have hb : max (|p.y|-1/2) 0=0 := max_eq_right (by linarith [hs.2])
  norm_num [AvoidsCore,coreDistance,ha,hb] at hc

theorem coordinate_bounds {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (hc : p.AvoidsCore) (hd : p.Contained q) (hq : q ≤ qCap) :
    447/800 < p.a ∧ p.a < 283/200 ∧ |p.y| < 9/10 := by
  have ha := primary_gt_half hs hc
  have hb := abs_nonneg p.y
  have hm0 : 0 ≤ max (|p.y|-1/2) 0 := le_max_right _ _
  have hm : max (|p.y|-1/2) 0 ≤ p.a-1/2 :=
    max_le (by linarith [hs.2]) (by linarith)
  have hm2 := pow_le_pow_left₀ hm0 hm 2
  have hcore := hc
  rw [AvoidsCore,coreDistance,max_eq_left (by linarith : 0 ≤ p.a-1/2)] at hcore
  have hbound : (p.a+1/2)^2+(|p.y|+1/2)^2 ≤ qCap := hd.trans hq
  refine ⟨?_,?_,?_⟩
  · by_contra! hbad
    have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ p.a-1/2)
      (show p.a-1/2 ≤ 47/800 by linarith) 2
    norm_num at hsq hcore
    nlinarith
  · dsimp [qCap] at hbound
    nlinarith [sq_nonneg |p.y|]
  · have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ |p.y|+1/2)
      (show |p.y|+1/2 ≤ p.a+1/2 by linarith [hs.2]) 2
    dsimp [qCap] at hbound
    nlinarith

/-- A sorted point on the circle of squared radius `q` lies between the diagonal and the axis
coordinates of that circle. -/
theorem outer_bounds {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (ho : p.Outer q) :
    diagonalCoordinate q ≤ p.a ∧ |p.y| ≤ diagonalCoordinate q ∧
      p.a ≤ axisCoordinate q := by
  have hb := abs_nonneg p.y
  have hq : 0 ≤ q := ho ▸ p.circle_nonneg
  have hq4 : 0 ≤ q-1/4 := by
    dsimp [Outer,circle] at ho
    nlinarith [sq_nonneg p.a,hs.1]
  have hs2 := Real.sq_sqrt (show 0 ≤ q/2 by positivity)
  have hs4 := Real.sq_sqrt hq4
  have hn2 := Real.sqrt_nonneg (q/2)
  have hn4 := Real.sqrt_nonneg (q-1/4)
  have hmono := pow_le_pow_left₀ (by linarith : 0 ≤ |p.y|+1/2)
    (show |p.y|+1/2 ≤ p.a+1/2 by linarith [hs.2]) 2
  dsimp [Outer,circle] at ho
  unfold diagonalCoordinate axisCoordinate
  constructor
  · nlinarith [hs.1]
  constructor
  · nlinarith
  · nlinarith [sq_nonneg |p.y|,hs.1]

theorem contained_minor_le_diagonal {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (hc : p.Contained q) : |p.y| ≤ diagonalCoordinate q := by
  have hb := abs_nonneg p.y
  have hq : 0 ≤ q := p.circle_nonneg.trans hc
  have hs2 := Real.sq_sqrt (show 0 ≤ q/2 by positivity)
  have hn2 := Real.sqrt_nonneg (q/2)
  have hmono := pow_le_pow_left₀ (by linarith : 0 ≤ |p.y|+1/2)
    (show |p.y|+1/2 ≤ p.a+1/2 by linarith [hs.2]) 2
  dsimp [Contained,circle] at hc
  unfold diagonalCoordinate
  nlinarith

theorem core_primary_le {p : SignedPoint} (hs : p.Sorted) (hc : p.Core) :
    p.a ≤ 7/12 := by
  have ha : 1/2 < p.a := primary_gt_half hs hc.ge
  have h := hc
  rw [Core,coreDistance,max_eq_left (by linarith : 0 ≤ p.a-1/2)] at h
  nlinarith [sq_nonneg (max (|p.y|-1/2) 0)]

theorem flat_core_iff {p : SignedPoint} (hs : p.Sorted) (hy : |p.y| ≤ 1/2) :
    p.Core ↔ p.a=7/12 := by
  constructor
  · intro hc
    have ha := primary_gt_half hs hc.ge
    have h := hc
    rw [Core,coreDistance,max_eq_left (by linarith : 0 ≤ p.a-1/2),
      max_eq_right (by linarith : |p.y|-1/2 ≤ 0)] at h
    nlinarith
  · intro ha
    norm_num [Core,coreDistance,ha,max_eq_right (by linarith : |p.y|-1/2 ≤ 0)]

theorem core_of_not_outer {q : ℝ} {p : SignedPoint}
    (hb : p.Boundary q) (hn : ¬p.Outer q) : p.Core := hb.resolve_left hn

/-- A sorted boundary point E with sorted contained H and D either has `E.a ≤ 7/12` or dominates
them radially, `max |H.y| |D.y| ≤ E.a`. -/
theorem boundary_radial_alternative {q : ℝ} {E H D : SignedPoint}
    (hE : E.Sorted) (hb : E.Boundary q) (hH : H.Sorted) (hD : D.Sorted)
    (hcH : H.Contained q) (hcD : D.Contained q) :
    E.a ≤ 7/12 ∨ max |H.y| |D.y| ≤ E.a := by
  rcases hb with ho | hc
  · right
    exact (max_le (contained_minor_le_diagonal hH hcH)
      (contained_minor_le_diagonal hD hcD)).trans (outer_bounds hE ho).1
  · exact Or.inl (core_primary_le hE hc)

/-- The point of the flat side of the core with transverse coordinate `y`, used by the moves of a
negative primary. -/
def flat (y : ℝ) : SignedPoint := ⟨7/12,y⟩

theorem flat_sorted {y : ℝ} (hy : |y| ≤ 1/2) : (flat y).Sorted := by
  exact ⟨by norm_num [flat],by dsimp [flat]; linarith⟩

theorem flat_on_core {y : ℝ} (hy : |y| ≤ 1/2) : (flat y).Core :=
  (flat_core_iff (flat_sorted hy) hy).mpr rfl

theorem flat_contained {q y : ℝ} (hq : qLow ≤ q) (hy : |y| ≤ 1/2) :
    (flat y).Contained q := by
  have hb := abs_nonneg y
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ |y|+1/2)
    (show |y|+1/2 ≤ 1 by linarith) 2
  dsimp [Contained,circle,flat,qLow] at *
  nlinarith

/-- The point of the circle of squared radius `q` with transverse coordinate `y`. -/
def outerAt (q y : ℝ) : SignedPoint :=
  ⟨Real.sqrt (q-(|y|+1/2)^2)-1/2,y⟩

theorem outerAt_spec {q y : ℝ} (hq : qLow ≤ q)
    (hy : |y| ≤ diagonalCoordinate q) :
    (outerAt q y).Sorted ∧ (outerAt q y).Outer q ∧
      (outerAt q y).AvoidsCore := by
  have hq0 : 0 ≤ q := by dsimp [qLow] at hq; linarith
  have hroot := Real.sq_sqrt (show 0 ≤ q/2 by positivity)
  have hroot0 := Real.sqrt_nonneg (q/2)
  have habs := abs_nonneg y
  have hy' : |y|+1/2 ≤ Real.sqrt (q/2) := by
    simpa [diagonalCoordinate,le_sub_iff_add_le] using hy
  have hy2 := pow_le_pow_left₀ (by linarith : 0 ≤ |y|+1/2) hy' 2
  have hrad : 0 ≤ q-(|y|+1/2)^2 := by nlinarith
  have hradSq := Real.sq_sqrt hrad
  have hrad0 := Real.sqrt_nonneg (q-(|y|+1/2)^2)
  have hlarge : (7/12 : ℝ)<Real.sqrt (q-(|y|+1/2)^2)-1/2 := by
    dsimp [qLow] at hq
    nlinarith
  have hsort : |y| ≤ Real.sqrt (q-(|y|+1/2)^2)-1/2 := by
    nlinarith
  refine ⟨⟨by simpa [outerAt] using (show 0 <
    Real.sqrt (q-(|y|+1/2)^2)-1/2 by linarith),hsort⟩,?_,?_⟩
  · dsimp [Outer,circle,outerAt]
    nlinarith
  · dsimp [AvoidsCore,coreDistance,outerAt]
    rw [max_eq_left (by linarith :
      0 ≤ Real.sqrt (q-(|y|+1/2)^2)-1/2-1/2)]
    nlinarith [sq_nonneg (max (|y|-1/2) 0)]

end SignedPoint

theorem uniform_circle_reserves {q : ℝ} (hl : qLow ≤ q) (hu : q ≤ qCap) :
    899/1000 < diagonalCoordinate q ∧ diagonalCoordinate q < 9/10 ∧
      19/10 < Real.sqrt (q-1/4) ∧ Real.sqrt (q-1/4) < 383/200 := by
  have hn := Real.sqrt_nonneg (q/2)
  have hn' := Real.sqrt_nonneg (q-1/4)
  have hs := Real.sq_sqrt (show 0 ≤ q/2 by dsimp [qLow] at hl; linarith)
  have hs' := Real.sq_sqrt (show 0 ≤ q-1/4 by dsimp [qLow] at hl; linarith)
  dsimp [qLow,qCap,diagonalCoordinate] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- A rotation preserves the squared norm of a corner. -/
theorem circle_rotation_identity (x y d : ℝ) :
    (x*Real.cos d-y*Real.sin d)^2+
      (x*Real.sin d+y*Real.cos d)^2=x^2+y^2 := by
  linear_combination (x^2+y^2)*Real.sin_sq_add_cos_sq d

/-- A strict loss `new < old` against a contained `old ≤ q` excludes `new = q`. -/
theorem circle_loss_impossible {q old new : ℝ}
    (hold : old ≤ q) (hloss : new < old) (heq : new=q) : False := by
  linarith

end SquaresInCircles.Eight