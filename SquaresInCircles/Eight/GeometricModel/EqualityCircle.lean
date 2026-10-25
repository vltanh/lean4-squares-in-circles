module

public import SquaresInCircles.Eight.GeometricModel.EqualityEquivalence
public import SquaresInCircles.Eight.ExactFamily.BoxRigidity

/-!
# The unique least enclosing circle, from four anchor vertices

Uncompiled source draft.  The A/B chord crosses the positive horizontal axis;
the D/E chord crosses the negative horizontal axis.  Their two crossing points
give an explicit positive convex combination of four radius vertices equal to
zero.  The resulting second-moment identity includes every possible circle
center and does not use the unrestricted packing lower-bound theorem.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily ExactFamily.Coordinates

def fourAnchorIndex : Fin 4 → Fin 8 := ![3,4,6,7]
def fourAnchorPoint (i : Fin 4) : Point := FiveCorner.selected.point i.castSucc

/-- Positive abscissa where the A/B chord crosses the horizontal axis. -/
def rightCrossing : ℝ :=
  ((sharpData.y+2)*sharpData.x₁-sharpData.y*sharpData.x₂)/2

/-- Negative abscissa where the D/E chord crosses the horizontal axis. -/
def leftCrossing : ℝ :=
  ((2-sharpData.y₃)*sharpData.x₃+sharpData.y₃*sharpData.x₄)/2

theorem crossing_signs : 0<rightCrossing ∧ leftCrossing<0 := by
  have hd := sharpData_stationary
  have hy : -1<sharpData.y ∧ sharpData.y< -(1/2) := ⟨hd.y_lower,hd.y_upper⟩
  have hy₃ : 0<sharpData.y₃ ∧ sharpData.y₃<2 := by
    refine ⟨hd.y₃_pos,?_⟩
    have h := hd.y₄_upper
    dsimp [Coordinates.y₄] at h
    linarith
  have hx₃ : sharpData.x₃<0 := by
    have hq := hd.q_upper
    have hB := hd.second_circle
    dsimp [Coordinates.x₃]
    nlinarith [sq_nonneg (sharpData.y+2)]
  have hR₁ := mul_pos (show 0<sharpData.y+2 by linarith) hd.x₁_pos
  have hR₂ := mul_neg_of_neg_of_pos (show sharpData.y<0 by linarith) hd.x₂_pos
  have hL₁ := mul_neg_of_pos_of_neg (show 0<2-sharpData.y₃ by linarith) hx₃
  have hL₂ := mul_neg_of_pos_of_neg hy₃.1 hd.x₄_neg
  constructor <;> dsimp [rightCrossing,leftCrossing] <;> linarith

/-- Convex weights on A,B,D,E.  The first two combine to the positive
crossing, the latter two to the negative crossing. -/
def fourAnchorWeight : Fin 4 → ℝ :=
  ![(-leftCrossing)*(sharpData.y+2)/(2*(rightCrossing-leftCrossing)),
    (-leftCrossing)*(-sharpData.y)/(2*(rightCrossing-leftCrossing)),
    rightCrossing*(2-sharpData.y₃)/(2*(rightCrossing-leftCrossing)),
    rightCrossing*sharpData.y₃/(2*(rightCrossing-leftCrossing))]

theorem fourAnchorWeight_pos (i : Fin 4) : 0<fourAnchorWeight i := by
  have hright : 0<rightCrossing := crossing_signs.1
  have hleft : 0< -leftCrossing := neg_pos.mpr crossing_signs.2
  have hd := sharpData_stationary
  have hden : 0<2*(rightCrossing-leftCrossing) := by linarith
  have hy : 0<sharpData.y+2 := by linarith [hd.y_lower]
  have hny : 0< -sharpData.y := by linarith [hd.y_upper]
  have hy₃pos : 0<sharpData.y₃ := hd.y₃_pos
  have hy₃ : 0<2-sharpData.y₃ := by
    have h := hd.y₄_upper
    dsimp [Coordinates.y₄] at h
    linarith
  fin_cases i <;> dsimp [fourAnchorWeight] <;> positivity

theorem fourAnchorWeight_sum : (∑ i : Fin 4,fourAnchorWeight i)=1 := by
  have hd : rightCrossing-leftCrossing≠0 := by linarith [crossing_signs.1,crossing_signs.2]
  norm_num [Fin.sum_univ_succ,fourAnchorWeight]
  field_simp [hd]
  ring

theorem fourAnchor_barycenter :
    (∑ i : Fin 4,fourAnchorWeight i*(fourAnchorPoint i).1)=0 ∧
      (∑ i : Fin 4,fourAnchorWeight i*(fourAnchorPoint i).2)=0 := by
  have hd : rightCrossing-leftCrossing≠0 := by linarith [crossing_signs.1,crossing_signs.2]
  constructor
  · norm_num [Fin.sum_univ_succ,fourAnchorWeight,fourAnchorPoint,
      FiveCorner.selected_point,Coordinates.anchorPoints]
    field_simp [hd]
    dsimp [rightCrossing,leftCrossing]
    ring
  · norm_num [Fin.sum_univ_succ,fourAnchorWeight,fourAnchorPoint,
      FiveCorner.selected_point,Coordinates.anchorPoints,Coordinates.y₄]
    field_simp [hd]
    ring

theorem fourAnchor_circle (i : Fin 4) :
    normSq (fourAnchorPoint i)=Eight.radius^2 := by
  rw [fourAnchorPoint,FiveCorner.selected_point,FiveCorner.radius_sq_eq_stationary]
  exact Coordinates.anchor_circle sharpData_stationary.toIsChain
    sharpData_stationary.zero_defect i.castSucc

theorem fourAnchor_closed (p : Parameters) (i : Fin 4) :
    closedSquare (p.model FiveCorner.selected (fourAnchorIndex i)) (fourAnchorPoint i) := by
  fin_cases i
  · change closedSquare (FiveCorner.selected.exteriorSquare p.top p.tilted 2) _
    norm_num [fourAnchorPoint,FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,
      FiveCorner.exteriorAngle,FiveCorner.anchorCenter,turnedSquare,closedSquare,localX,localY]
  · change closedSquare (FiveCorner.selected.exteriorSquare p.top p.tilted 3) _
    norm_num [fourAnchorPoint,FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,
      FiveCorner.exteriorAngle,FiveCorner.anchorCenter,turnedSquare,closedSquare,localX,localY]
  · change closedSquare (FiveCorner.selected.exteriorSquare p.top p.tilted 5) _
    norm_num [fourAnchorPoint,FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,
      FiveCorner.exteriorAngle,FiveCorner.anchorCenter,turnedSquare,closedSquare,localX,localY]
  · change closedSquare (FiveCorner.selected.exteriorSquare p.top p.tilted 6) _
    norm_num [fourAnchorPoint,FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,
      FiveCorner.exteriorAngle,FiveCorner.anchorCenter,turnedSquare,closedSquare,localX,localY]

theorem fourAnchor_second_moment (o : Point) :
    (∑ i : Fin 4,fourAnchorWeight i*normSq (sub (fourAnchorPoint i) o))=
      Eight.radius^2+normSq o := by
  have hb := fourAnchor_barycenter
  have hid :
      (∑ i : Fin 4,fourAnchorWeight i*normSq (sub (fourAnchorPoint i) o))=
      (∑ i : Fin 4,fourAnchorWeight i*normSq (fourAnchorPoint i))-
        2*o.1*(∑ i : Fin 4,fourAnchorWeight i*(fourAnchorPoint i).1)-
        2*o.2*(∑ i : Fin 4,fourAnchorWeight i*(fourAnchorPoint i).2)+
        normSq o*(∑ i : Fin 4,fourAnchorWeight i) := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [normSq,sub]
    ring
  rw [hid,hb.1,hb.2,fourAnchorWeight_sum]
  simp only [fourAnchor_circle,mul_zero,sub_zero,mul_one]
  rw [← Finset.sum_mul,fourAnchorWeight_sum]
  ring

end SquaresInCircles.Eight.GeometricModel

namespace SquaresInCircles.Eight.Parameters
open GeometricModel ExactFamily ExactFamily.Coordinates

/-- Quantitative uniqueness: moving the proposed disk center by `o` costs
at least `normSq o` in squared radius, already on four fixed vertices. -/
theorem enclosing_radius_sq_bound (p : Parameters) (o : Point) (r : ℝ)
    (h : ∀ i x,closedSquare (p.model FiveCorner.selected i) x →
      normSq (sub x o)≤r) : Eight.radius^2+normSq o≤r := by
  have hsum :
      (∑ i : Fin 4,fourAnchorWeight i*normSq (sub (fourAnchorPoint i) o))≤
        ∑ i : Fin 4,fourAnchorWeight i*r := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (h (fourAnchorIndex i) _ (fourAnchor_closed p i)) (fourAnchorWeight_pos i).le
  rw [fourAnchor_second_moment,← Finset.sum_mul,fourAnchorWeight_sum,one_mul] at hsum
  exact hsum

theorem enclosing_center_unique (p : Parameters) (o : Point)
    (h : ∀ i x,closedSquare (p.model FiveCorner.selected i) x →
      normSq (sub x o)≤Eight.radius^2) : o=(0,0) := by
  have hh := enclosing_radius_sq_bound p o _ h
  have hx := sq_nonneg o.1
  have hy := sq_nonneg o.2
  apply Prod.ext <;> dsimp <;> dsimp [normSq] at hh <;> nlinarith

def enclosingRadii (p : Parameters) : Set ℝ :=
  {R | 0≤R ∧ ∃ o : Point, ∀ i x,
    closedSquare (p.model FiveCorner.selected i) x → inDisk o R x}

theorem least_enclosing_radius {p : Parameters} (hp : p.Admissible FiveCorner.selected) :
    IsLeast p.enclosingRadii Eight.radius := by
  have hpacking := model_packing hp
  refine ⟨⟨hpacking.1,(0,0),hpacking.2.1⟩,?_⟩
  rintro R ⟨hR,o,ho⟩
  have hh := enclosing_radius_sq_bound p o (R^2) ho
  have ho0 := normSq_nonneg o
  nlinarith [hpacking.1]

theorem unique_least_circle {p : Parameters} (hp : p.Admissible FiveCorner.selected) :
    IsLeast p.enclosingRadii Eight.radius ∧
      ∀ o : Point, (∀ i x,closedSquare (p.model FiveCorner.selected i) x →
        inDisk o Eight.radius x) → o=(0,0) :=
  ⟨least_enclosing_radius hp,fun o ho => enclosing_center_unique p o ho⟩

theorem model_reaches (p : Parameters) :
    ∃ i x,closedSquare (p.model FiveCorner.selected i) x ∧
      Eight.radius^2≤normSq x :=
  ⟨fourAnchorIndex 0,fourAnchorPoint 0,fourAnchor_closed p 0,(fourAnchor_circle 0).ge⟩

end SquaresInCircles.Eight.Parameters

