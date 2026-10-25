module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Arithmetic.CorePairGeometry
public import SquaresInCircles.Eight.Arithmetic.Taylor
public import SquaresInCircles.Eight.Boundary.Candidate.GeometricCoreQuarter

/-!
# Eight squares: the exact endpoint bound for every core angle

The side is controlled by one fixed tangent to arctangent. On the corner,
subtracting the diagonal angle reduces the estimate to a small positive
arctangent. The core circle gives a linear lower bound on its argument.
Thus neither a radical second derivative nor an interval cover is needed.

The final theorem strengthens the physical core/core gap to `27/20`,
using the original center separation and one cosine Taylor comparison.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.CoreAngleEndpoint

open CorePairGeometry

/-- The diagonal end of the closed core corner. -/
def diagonal : ℝ := 1/2+Real.sqrt 2/24

theorem diagonal_bounds :
    55892556/100000000<diagonal ∧ diagonal<55892557/100000000 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have h0 := Real.sqrt_nonneg (2:ℝ)
  dsimp [diagonal]
  constructor <;> by_contra! h <;> nlinarith

theorem diagonal_sq : (diagonal-1/2)^2=(1/288:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  dsimp [diagonal]
  nlinarith

/-- Canonical order places the transverse coordinate before the diagonal
and the primary coordinate after it. Both endpoints are included. -/
theorem corner_diagonal {a b : ℝ} (hb : 1/2≤b) (hab : b≤a)
    (hc : (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2) :
    b≤diagonal ∧ diagonal≤a := by
  have hd0 : 0<diagonal-1/2 := by linarith [diagonal_bounds.1]
  have he0 : 0≤a-1/2 := by linarith
  have hf0 : 0≤b-1/2 := by linarith
  have hsq := pow_le_pow_left₀ hf0 (show b-1/2≤a-1/2 by linarith) 2
  constructor
  · by_contra! hbad
    have hp := mul_pos (show 0<b-diagonal by linarith)
      (show 0<(b-1/2)+(diagonal-1/2) by linarith)
    nlinarith [diagonal_sq]
  · by_contra! hbad
    have hp := mul_pos (show 0<diagonal-a by linarith)
      (show 0<(diagonal-1/2)+(a-1/2) by linarith)
    nlinarith [diagonal_sq]

theorem state_bounds {a b : ℝ} (hc : CoreState a b) :
    1/2<a ∧ a≤7/12 ∧ 0≤b ∧ b≤a ∧ b≤diagonal := by
  rcases hc with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
  · refine ⟨by norm_num,le_rfl,hb,by linarith,?_⟩
    linarith [diagonal_bounds.1]
  · have ha := corner_geometry hb hab hcircle
    exact ⟨by linarith [ha.1],ha.2.1,by linarith,hab,
      (corner_diagonal hb hab hcircle).1⟩

/-- The core circle supplies a chord slope that is stronger than the
angular slope needed below. -/
theorem corner_chord {a b : ℝ} (hb : 1/2≤b) (hab : b≤a)
    (hc : (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2) :
    (7/5)*(diagonal-b)≤a-b := by
  have hdiag := corner_diagonal hb hab hc
  have ha := corner_geometry hb hab hc
  have hsum : 0<a+b-1 := by linarith [ha.1]
  have hidentity : (a-b)*(a+b-1)=2*(diagonal-b)*(diagonal+b-1) := by
    nlinarith [diagonal_sq]
  have hcoef : (7/5)*(a+b-1)≤2*(diagonal+b-1) := by
    linarith [ha.2.1,diagonal_bounds.1]
  have hm := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hdiag.1)
  apply (mul_le_mul_iff_of_pos_right hsum).mp
  nlinarith

/-- Subtracting from the diagonal angle keeps arctangent in its principal
range. This identity holds on the whole canonical quadrant. -/
theorem arctan_complement {a b : ℝ} (ha : 0<a) (hb : 0≤b) :
    Real.pi/4-Real.arctan (b/a)=Real.arctan ((a-b)/(a+b)) := by
  have hx : 0≤b/a := div_nonneg hb ha.le
  have h := Real.arctan_add (x := (1:ℝ)) (y := -(b/a)) (by linarith : 1*(-(b/a))<1)
  have hsum : a+b≠0 := ne_of_gt (by linarith)
  have hden : (1:ℝ)-1*(-(b/a))≠0 := ne_of_gt (by linarith)
  have he : (1+ -(b/a))/(1-1*(-(b/a)))=(a-b)/(a+b) := by
    rw [div_eq_div_iff hden hsum]
    field_simp
    ring
  rw [he,Real.arctan_one,Real.arctan_neg] at h
  linarith

/-- The corner endpoint inequality follows from a cubic atan lower bound.
The auxiliary argument is at most `1/12` on the entire corner. -/
theorem corner_upper {a b : ℝ} (hb : 1/2≤b) (hab : b≤a)
    (hc : (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2) :
    Real.arctan (b/a)-(8/7)*b≤Real.pi/4-(8/7)*diagonal := by
  have ha := corner_geometry hb hab hc
  have hd := corner_diagonal hb hab hc
  have ha0 : 0<a := by linarith [ha.1]
  have hsum : 0<a+b := by linarith
  let z : ℝ := (a-b)/(a+b)
  have hz0 : 0≤z := div_nonneg (sub_nonneg.mpr hab) hsum.le
  have hz1 : z≤1/12 := (div_le_iff₀ hsum).mpr (by linarith [ha.2.1])
  have hzid : z*(a+b)=a-b := div_mul_cancel₀ _ hsum.ne'
  have hmul := mul_le_mul_of_nonneg_left
    (show a+b≤7/6 by linarith [ha.2.1]) hz0
  have hzlow : (6/5)*(diagonal-b)≤z := by
    nlinarith [corner_chord hb hab hc]
  have hzsq := pow_le_pow_left₀ hz0 hz1 2
  have hzcube := mul_le_mul_of_nonneg_right hzsq hz0
  have hpoly : (99/100)*z≤z-z^3/3 := by nlinarith
  have hatan := arctan_lower_three hz0
  have hgoal : (8/7)*(diagonal-b)≤Real.arctan z := by
    nlinarith [sub_nonneg.mpr hd.1]
  have he := arctan_complement ha0 (show 0≤b by linarith)
  change Real.pi/4-Real.arctan (b/a)=Real.arctan z at he
  linarith

theorem arctan_seven_tenths : Real.arctan (7/10:ℝ)<1527/2500 := by
  have h := Arithmetic.arctan_le_atanUpper (x := (7/10:ℝ)) (by norm_num)
  norm_num [Arithmetic.atanUpper] at h
  linarith

/-- One tangent, at `7/10`, handles the entire side with a strict reserve. -/
theorem side_upper {b : ℝ} (hb : 0≤b ∧ b≤1/2) :
    Real.arctan (b/(7/12:ℝ))-(8/7)*b<Real.pi/4-(8/7)*diagonal := by
  let x : ℝ := 12*b/7
  have hx : 0≤x ∧ x≤6/7 := by dsimp [x]; constructor <;> linarith [hb.1,hb.2]
  have he : b/(7/12:ℝ)=x := by dsimp [x]; ring
  have hb' : b=(7/12)*x := by dsimp [x]; ring
  have ht := arctan_tangent hx.1 (show (0:ℝ)≤7/10 by norm_num)
  norm_num at ht
  have hu : Real.arctan x-(2/3)*x<(29/200:ℝ) := by
    linarith [arctan_seven_tenths,hx.2]
  rw [he,hb']
  have hdu : diagonal<(14/25:ℝ) := by linarith [diagonal_bounds.2]
  nlinarith [Real.pi_gt_d2]

/-- Exact statewise endpoint control shared by both wrong-word labels. -/
theorem angle_endpoint {a b g : ℝ} (hc : CoreState a b)
    (hg : 0≤g ∧ g≤8/7) :
    0≤Real.arctan (b/a)-g*b ∧
      Real.arctan (b/a)-g*b≤Real.pi/4-g*diagonal := by
  obtain ⟨ha,hau,hb,hab,hbd⟩ := state_bounds hc
  have hlo := Candidate.Geometric.core_transverse_le_angle
    (by linarith : 0<a) hau hb hab
  have hgb := mul_le_mul_of_nonneg_right hg.2 hb
  have hmax : Real.arctan (b/a)-(8/7)*b≤Real.pi/4-(8/7)*diagonal := by
    rcases hc with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
    · exact (side_upper ⟨hb,hbu⟩).le
    · exact corner_upper hb hab hcircle
  have hm := mul_nonneg (show 0≤8/7-g by linarith) (sub_nonneg.mpr hbd)
  constructor <;> nlinarith

/-- A core angle is at most twice its transverse coordinate. -/
theorem angle_le_twice {a b : ℝ} (hc : CoreState a b) :
    Real.arctan (b/a)≤2*b := by
  obtain ⟨ha,hau,hb,hab,hbd⟩ := state_bounds hc
  have ha0 : 0<a := by linarith
  have hx := div_nonneg hb ha0.le
  have ht := arctan_tangent hx (show (0:ℝ)≤0 by rfl)
  norm_num at ht
  have hr : b/a≤2*b := (div_le_iff₀ ha0).mpr (by nlinarith)
  linarith

/-- The original physical center separation sharpens the core/core gap
without selecting an axis or changing either boundary point. -/
theorem core_gap {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hi : C.kind i≠.outer) (hj : C.kind (next i)≠.outer) :
    (27/20:ℝ)<angleGap C.beta i := by
  have hr0 := C.radius_pos i
  have hs0 := C.radius_pos (next i)
  have hr : C.radius i<4/5 := by
    nlinarith [C.radius_sq i,core_radius_sq (boundary_core_state C i hi)]
  have hs : C.radius (next i)<4/5 := by
    nlinarith [C.radius_sq (next i),core_radius_sq (boundary_core_state C (next i) hj)]
  have hd := signed_axis_center_distance (C.feasible i)
  rw [polar_pair_distance (C.center_cos i) (C.center_sin i)
    (C.center_cos (next i)) (C.center_sin (next i))] at hd
  have hcos : Real.cos (angleGap C.beta i)=Real.cos (C.beta (next i)-C.beta i) := by
    by_cases hlast : i=6 <;> simp [angleGap,hlast,Real.cos_add_two_pi]
  rw [← hcos] at hd
  change 1≤C.radius i^2+C.radius (next i)^2-
    2*C.radius i*C.radius (next i)*Real.cos (angleGap C.beta i) at hd
  have hmax := chord_upper ⟨hr0.le,hr.le⟩ ⟨hs0.le,hs.le⟩
  have hc : (7/32:ℝ)<Real.cos (27/20:ℝ) := by
    have hh := Arithmetic.cos10_le_cos (x := (27/20:ℝ)) (by norm_num)
    norm_num [Arithmetic.cos10,Arithmetic.cos8] at hh
    linarith
  by_contra! hbad
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi (C.gap_pos i).le
    (by linarith [Real.pi_gt_three] : (27/20:ℝ)≤Real.pi) hbad
  have hp := mul_pos (mul_pos hr0 hs0)
    (sub_pos.mpr (lt_of_lt_of_le hc hm))
  nlinarith

end SquaresInCircles.Eight.CoreAngleEndpoint
