module

public import SquaresInCircles.Eight.TableFree.SignedCoordinates

/-!
# Actual-circle and true-core geometry for table-free transports

Uncompiled draft. Radius bounds are internal estimates; every constructed
outer point uses its actual q-circle, never a renamed fixed-ceiling state.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree

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

/-- The endpoints are the actual q-circle endpoints, not fixed-Q labels. -/
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

/-- E's dichotomy follows from actual radial kinds and sorted containment. -/
theorem boundary_radial_alternative {q : ℝ} {E H D : SignedPoint}
    (hE : E.Sorted) (hb : E.Boundary q) (hH : H.Sorted) (hD : D.Sorted)
    (hcH : H.Contained q) (hcD : D.Contained q) :
    E.a ≤ 7/12 ∨ max |H.y| |D.y| ≤ E.a := by
  rcases hb with ho | hc
  · right
    exact (max_le (contained_minor_le_diagonal hH hcH)
      (contained_minor_le_diagonal hD hcD)).trans (outer_bounds hE ho).1
  · exact Or.inl (core_primary_le hE hc)

/-- Increasing only the primary coordinate preserves exact core avoidance. -/
theorem core_mono_primary {p r : SignedPoint} (ha : p.a ≤ r.a) (hy : r.y=p.y) :
    p.coreDistance ≤ r.coreDistance := by
  have hm := max_le_max (sub_le_sub_right ha (1/2)) le_rfl
  have hs := pow_le_pow_left₀ (le_max_right (p.a-1/2) 0) hm 2
  simp only [coreDistance,hy]
  linarith

def flat (y : ℝ) : SignedPoint := ⟨7/12,y⟩

theorem flat_sorted {y : ℝ} (hy : |y| ≤ 1/2) : (flat y).Sorted := by
  exact ⟨by norm_num [flat],by dsimp [flat]; linarith⟩

theorem flat_on_core {y : ℝ} (hy : |y| ≤ 1/2) : (flat y).Core :=
  (flat_core_iff (flat_sorted hy) hy).2 rfl

theorem flat_contained {q y : ℝ} (hq : qLow ≤ q) (hy : |y| ≤ 1/2) :
    (flat y).Contained q := by
  have h0 := abs_nonneg y
  unfold Contained circle flat
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ |y|+1/2)
    (show |y|+1/2 ≤ 1 by linarith) 2
  dsimp [qLow] at hq
  nlinarith

def outerAt (q y : ℝ) : SignedPoint :=
  ⟨Real.sqrt (q-(|y|+1/2)^2)-1/2,y⟩

theorem outerAt_spec {q y : ℝ} (hq : qLow ≤ q)
    (hy : |y| ≤ diagonalCoordinate q) :
    (outerAt q y).Sorted ∧ (outerAt q y).Outer q ∧
      (outerAt q y).AvoidsCore := by
  have hq0 : 0 ≤ q := by dsimp [qLow] at hq; linarith
  have hq2 := Real.sq_sqrt (show 0 ≤ q/2 by positivity)
  have hn2 := Real.sqrt_nonneg (q/2)
  have hy0 := abs_nonneg y
  have hb : |y|+1/2 ≤ Real.sqrt (q/2) := by
    dsimp [diagonalCoordinate] at hy
    linarith
  have hb2 := pow_le_pow_left₀ (by positivity : 0 ≤ |y|+1/2) hb 2
  have hrad : 0 ≤ q-(|y|+1/2)^2 := by nlinarith
  have hroot := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (q-(|y|+1/2)^2)
  have ha : |y|+1/2 ≤ Real.sqrt (q-(|y|+1/2)^2) := by nlinarith
  have hlarge : 7/12 ≤ Real.sqrt (q-(|y|+1/2)^2)-1/2 := by
    dsimp [qLow] at hq
    nlinarith
  refine ⟨⟨by dsimp [outerAt]; linarith,by dsimp [outerAt]; linarith⟩,?_,?_⟩
  · dsimp [outerAt,Outer,circle]
    nlinarith
  · dsimp [outerAt,AvoidsCore,coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ Real.sqrt (q-(|y|+1/2)^2)-1/2-1/2)]
    nlinarith [sq_nonneg (max (|y|-1/2) 0)]

end SignedPoint

theorem uniform_circle_reserves {q : ℝ} (hl : qLow ≤ q) (hu : q ≤ qCap) :
    899/1000 < diagonalCoordinate q ∧ diagonalCoordinate q < 9/10 ∧
      19/10 < Real.sqrt (q-1/4) ∧ Real.sqrt (q-1/4) < 383/200 := by
  have hq2 := Real.sq_sqrt (show 0 ≤ q/2 by dsimp [qLow] at hl; linarith)
  have hq4 := Real.sq_sqrt (show 0 ≤ q-1/4 by dsimp [qLow] at hl; linarith)
  have hn2 := Real.sqrt_nonneg (q/2)
  have hn4 := Real.sqrt_nonneg (q-1/4)
  dsimp [qLow] at hl
  dsimp [qCap] at hu
  dsimp [diagonalCoordinate]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem small_frame_cos {d : ℝ} (hd : |d| ≤ frameCap) : 3/4 < Real.cos d := by
  have h := small_angle hd
  dsimp [frameCap] at h
  norm_num at h
  linarith

theorem small_frame_width {d : ℝ} (hd : |d| ≤ frameCap) :
    edgeWidth d=(1+Real.cos d+|Real.sin d|)/2 := by
  have hc := small_frame_cos hd
  simp [edgeWidth,pairWidth,abs_of_pos (by linarith : 0<Real.cos d),add_comm]

theorem circle_rotation_identity (x y d : ℝ) :
    (x*Real.cos d-y*Real.sin d)^2+(x*Real.sin d+y*Real.cos d)^2=x^2+y^2 := by
  linear_combination (x^2+y^2)*Real.sin_sq_add_cos_sq d

theorem circle_loss_impossible {q old new : ℝ}
    (hold : old ≤ q) (hloss : new < old) (hnew : new=q) : False := by
  linarith

end SquaresInCircles.Eight.TableFree
