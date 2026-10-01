import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# The constants of the normalization

The normalization works in disks of squared radius at most
`Q0 = 142559/50000`, just above the square of the optimal radius. With
`R0 = √Q0`, `ρ0 = √(Q0 - 1/4) - 1/2` is the largest radial offset of a square in
such a disk, `c0 = ρ0 - 1` bounds the coordinates of the centre of C,
`coreRadius = 3/2 - ρ0` is the radius of a disk about the origin inside C, and
`aMin = 2 - ρ0` and `U0` bound the chart of an exterior square that avoids that
disk. Each constant gets rational bounds.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- The rational ceiling on the squared radius, just above `qStar`. -/
def Q0 : ℝ := 142559 / 50000

def R0 : ℝ := Real.sqrt Q0

def rho0 : ℝ := Real.sqrt (Q0 - 1 / 4) - 1 / 2

def c0 : ℝ := rho0 - 1

/-- The radius of a disk about the origin inside C, for the centre of C in
`[0, c0]²`. -/
def coreRadius : ℝ := 3 / 2 - rho0

def aMin : ℝ := 2 - rho0

def U0 : ℝ := Real.sqrt (Q0 - (5 / 2 - rho0) ^ 2) - 1 / 2

lemma Q0_pos : 0 < Q0 := by norm_num [Q0]

lemma Q0_lt_thirteen_fourths : Q0 < 13 / 4 := by norm_num [Q0]

lemma R0_nonneg : 0 ≤ R0 := Real.sqrt_nonneg _

lemma R0_sq : R0 ^ 2 = Q0 := Real.sq_sqrt Q0_pos.le

/-- The corners `(ρ0 + 1/2, ±1/2)` lie on the circle of radius `R0`. -/
lemma rho0_identity : (rho0 + 1 / 2) ^ 2 + 1 / 4 = Q0 := by
  have hs := Real.sq_sqrt (show 0 ≤ Q0 - 1 / 4 by norm_num [Q0])
  dsimp [rho0]
  nlinarith

lemma rho0_sq : rho0 ^ 2 + rho0 + 1 / 2 = Q0 := by
  nlinarith [rho0_identity]

lemma rho0_lower : (111 : ℝ) / 100 < rho0 := by
  have hs : Real.sqrt ((161 / 100 : ℝ) ^ 2) < Real.sqrt (Q0 - 1 / 4) :=
    Real.sqrt_lt_sqrt (by positivity) (by norm_num [Q0])
  rw [Real.sqrt_sq (by norm_num)] at hs
  dsimp [rho0]
  linarith

lemma rho0_upper : rho0 < (1113 : ℝ) / 1000 := by
  have hs : Real.sqrt (Q0 - 1 / 4) < Real.sqrt ((1613 / 1000 : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt (by norm_num [Q0]) (by norm_num [Q0])
  rw [Real.sqrt_sq (by norm_num)] at hs
  dsimp [rho0]
  linarith

lemma rho0_gt_one : 1 < rho0 := by linarith [rho0_lower]

lemma rho0_lt_223_200 : rho0 < (223 : ℝ) / 200 := by
  linarith [rho0_upper]

lemma c0_pos : 0 < c0 := by dsimp [c0]; linarith [rho0_gt_one]

lemma c0_lt_23_200 : c0 < (23 : ℝ) / 200 := by
  dsimp [c0]
  linarith [rho0_lt_223_200]

lemma coreRadius_pos : 0 < coreRadius := by
  dsimp [coreRadius]
  linarith [rho0_upper]

lemma coreRadius_gt_77_200 : (77 : ℝ) / 200 < coreRadius := by
  dsimp [coreRadius]
  linarith [rho0_lt_223_200]

lemma c0_add_coreRadius : c0 + coreRadius = 1 / 2 := by
  dsimp [c0, coreRadius]
  ring

lemma aMin_eq_coreRadius_add_half : aMin = coreRadius + 1 / 2 := by
  dsimp [aMin, coreRadius]
  ring

lemma aMin_gt_177_200 : (177 : ℝ) / 200 < aMin := by
  dsimp [aMin]
  linarith [rho0_lt_223_200]

lemma U0_radicand : Q0 - (5 / 2 - rho0) ^ 2 = 6 * rho0 - 23 / 4 := by
  nlinarith [rho0_sq]

lemma U0_radicand_pos : 0 < Q0 - (5 / 2 - rho0) ^ 2 := by
  rw [U0_radicand]
  linarith [rho0_gt_one]

lemma U0_lt_117_250 : U0 < (117 : ℝ) / 250 := by
  have hs : Real.sqrt (Q0 - (5 / 2 - rho0) ^ 2) <
      Real.sqrt ((121 / 125 : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt U0_radicand_pos.le
      (by rw [U0_radicand]; nlinarith [rho0_upper])
  rw [Real.sqrt_sq (by norm_num)] at hs
  dsimp [U0]
  linarith

lemma U0_lt_half : U0 < 1 / 2 := by linarith [U0_lt_117_250]

end SquaresInCircles.Six.Normalization
