import SquaresInCircles.Common.Constructions

/-!
# Seven squares: construction

A column of three unit squares between two columns of two, at the optimal radius
`√13 / 2`. The outer corners of the side columns lie on the circle, but the
middle column is shorter than the room it has, so it can slide: every `Column`
gives an optimal packing, and `Seven.centers` is the one with the column
centred.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- The optimal radius for seven unit squares: the distance from the disk centre
to the outer corners of the side columns. -/
def radius : ℝ := Real.sqrt 13 / 2

lemma radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

lemma radius_sq : radius ^ 2 = 13 / 4 := by
  unfold radius
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- How far a centre of the middle column can be from the disk centre. -/
def columnLimit : ℝ := Real.sqrt 3 - 1 / 2

lemma one_le_columnLimit : (1 : ℝ) ≤ columnLimit := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  dsimp [columnLimit]
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

lemma columnLimit_sq : (columnLimit + 1 / 2) ^ 2 = 3 := by
  simp only [columnLimit, sub_add_cancel]
  exact Real.sq_sqrt (by norm_num)

/-- The heights of the three middle centres: at least 1 apart, and within
`columnLimit` of the disk centre. -/
structure Column where
  bottom : ℝ
  middle : ℝ
  top : ℝ
  lower : -columnLimit ≤ bottom
  gap_lower : bottom + 1 ≤ middle
  gap_upper : middle + 1 ≤ top
  upper : top ≤ columnLimit

namespace Column
lemma bottom_le_middle (c : Column) : c.bottom ≤ c.middle := by linarith [c.gap_lower]
lemma middle_le_top (c : Column) : c.middle ≤ c.top := by linarith [c.gap_upper]
lemma bottom_mem (c : Column) : -columnLimit ≤ c.bottom ∧ c.bottom ≤ columnLimit :=
  ⟨c.lower, (c.bottom_le_middle.trans c.middle_le_top).trans c.upper⟩
lemma middle_mem (c : Column) : -columnLimit ≤ c.middle ∧ c.middle ≤ columnLimit :=
  ⟨c.lower.trans c.bottom_le_middle, c.middle_le_top.trans c.upper⟩
lemma top_mem (c : Column) : -columnLimit ≤ c.top ∧ c.top ≤ columnLimit :=
  ⟨(c.lower.trans c.bottom_le_middle).trans c.middle_le_top, c.upper⟩
end Column

/-- The four side centres, then the three centres of the middle column. -/
def slidingCenters (c : Column) : Fin 7 → Point :=
  ![(1, -1/2), (1, 1/2), (-1, -1/2), (-1, 1/2),
    (0, c.bottom), (0, c.middle), (0, c.top)]

def slidingModel (c : Column) : Fin 7 → UnitSquare :=
  fun i => axisSquare (slidingCenters c i)

/-- Every position of the middle column gives an optimal packing. -/
theorem sliding_packing (c : Column) : Packing (slidingModel c) (0,0) radius := by
  have hbm := c.gap_lower
  have hmt := c.gap_upper
  have hbt : c.bottom+1 ≤ c.top := by linarith
  have hmid {y : ℝ} (hy : -columnLimit ≤ y ∧ y ≤ columnLimit) :
      (|(0:ℝ)|+1/2)^2+(|y|+1/2)^2 ≤ radius^2 := by
    have h := pow_le_pow_left₀ (by positivity)
      (show |y|+1/2 ≤ columnLimit+1/2 by linarith [abs_le.mpr hy]) 2
    rw [columnLimit_sq] at h
    rw [radius_sq]
    norm_num at h ⊢
    linarith
  apply axis_packing radius_nonneg
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [slidingCenters,AxisSeparated,hbm,hmt,hbt] at *
  · intro i
    fin_cases i
    iterate 4 norm_num [slidingCenters,radius_sq]
    exacts [hmid c.bottom_mem,hmid c.middle_mem,hmid c.top_mem]

/-- The middle column centred at the disk centre. -/
def centeredColumn : Column where
  bottom := -1
  middle := 0
  top := 1
  lower := by linarith [one_le_columnLimit]
  gap_lower := by norm_num
  gap_upper := by norm_num
  upper := one_le_columnLimit

/-- The optimal packing with its middle column centred, in the frame of its
disk centre. -/
def centers : Fin 7 → Point :=
  ![(1,-1/2),(1,1/2),(-1,-1/2),(-1,1/2),(0,-1),(0,0),(0,1)]

/-- That packing, centred at the origin. -/
def model : Fin 7 → UnitSquare := fun i => axisSquare (centers i)

theorem model_packing : Packing model (0,0) radius := sliding_packing centeredColumn

end SquaresInCircles.Seven
