import SquaresInCircles.Seven.Pair.BoundaryProfiles
import SquaresInCircles.Seven.Pair.Contacts

/-!
# Seven squares: the inward axis with opposite signs, minima on the boundary

In the turn `e = label a u + label A v - π/6` the support sum is
`1/2 - a - A sin e + |sin e|/2 + (v + 1/2) cos e`. For a side source and an
axial target at a positive turn it is at least its value with the source at the
top of its label segment and the target at the end of its label segment. A
diagonal source moves to its junction or a capped axial endpoint, and a circular
source with a straight axial target to one of its two junctions. On the
circular pieces the circle lies below its tangent at `v = 0` lowered by
`(5/16) v²`, which turns the support bound into `radialForm`, a quadratic in the
target height `v`. Minus a square centred at `v = z/2` it is affine in `v`; it is
positive at `v = 0` by Taylor bounds, and at `v = 3/10` because it is concave in
`z`, zero at `0` and positive at `5/8`. The diagonal junction uses one positive
value and monotonicity.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
open Boundary

def inwardOpposite (a A v e : ℝ) : ℝ :=
  1/2-a-A*Real.sin e+|Real.sin e|/2+(v+1/2)*Real.cos e

lemma inward_opposite_formula {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) :
    pairSupport a u A v .positive .negative 2 gap =
      inwardOpposite a A v (label a u+label A v-Real.pi/6) := by
  rw [pairSupport_inward .negative h h']
  simp only [TransverseSign.coe,neg_one_mul,sub_neg_eq_add,inwardOpposite]
  ring

lemma inward_opposite_side_identity {a u A v e : ℝ}
    (hT : label a u=side a u) (hA : label A v=axial v)
    (he : e=label a u+label A v-Real.pi/6) :
    inwardOpposite a A v e =
      (4/5)*e+(2/15)*remainder a u-A*Real.sin e+|Real.sin e|/2-
        (v+1/2)*(1-Real.cos e) := by
  rw [hT,hA] at he
  dsimp [inwardOpposite,side,axial,remainder] at *
  linarith

/-- Below `w = 3/10` the circle lies under its tangent at `w = 0`, lowered by
`(5/16) w²`. -/
lemma circle_quadratic_upper {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 3/10) :
    circle v-1/2 ≤ Real.sqrt 3-1-(Real.sqrt 3/6)*v-(5/16)*v^2 := by
  let B := Real.sqrt 3-(Real.sqrt 3/6)*v-(5/16)*v^2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h3 := sqrt_three_bounds
  have hr : 0 ≤ 3-v-v^2 := by nlinarith [hv.1,hv.2]
  have hrad := Real.sq_sqrt hr
  have hroot := Real.sqrt_nonneg (3-v-v^2)
  have hB0 : 0 < B := by
    have hv2 : v^2 ≤ (3/10:ℝ)^2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hv.2 (Real.sqrt_nonneg 3)
    dsimp [B]
    linarith
  have p2 := mul_nonneg (sq_nonneg v) (show 0 ≤ 13/12-(5/8)*Real.sqrt 3 by linarith)
  have p3 := mul_nonneg (Real.sqrt_nonneg 3) (pow_nonneg hv.1 3)
  have hid : B^2-(3-v-v^2) =
      v^2*(13/12-(5/8)*Real.sqrt 3)+(5/48)*(Real.sqrt 3*v^3)+(25/256)*v^4 := by
    dsimp [B]
    linear_combination (1-v/6)^2*hs
  have hle : Real.sqrt (3-v-v^2) ≤ B := by nlinarith [pow_nonneg hv.1 4]
  have he : targetSq-(v+1/2)^2=3-v-v^2 := by dsimp [targetSq]; ring
  dsimp [circle]
  rw [he]
  dsimp [B] at hle
  linarith

/-- The support bound for a side source and an axial target on the circle, at
the turn `z` and the target height `v`: the remainder is replaced by its lower
bound `(9/5)(z - 5v/4)²` and the target by `circle_quadratic_upper`. -/
def radialForm (z v : ℝ) : ℝ :=
  (4/5)*z+(6/25)*(z-5*v/4)^2-(Real.sqrt 3-1-(Real.sqrt 3/6)*v-(5/16)*v^2)*Real.sin z-
    (v+1/2)*(1-Real.cos z)

/-- `radialForm` at the height `3/10`, minus `(3/8 + (5/16) sin z)(3/10 - z/2)²`. -/
private def radialTop (z : ℝ) : ℝ :=
  radialForm z (3/10)-(3/8+(5/16)*Real.sin z)*(3/10-z/2)^2

/-- `radialTop` is concave on `[0, 5/8]`: in its second derivative the constant
`12/25 - 3/16` and the term in `sin z` lose to the term in `cos z`. -/
private lemma radialTop_concave : ConcaveOn ℝ (Icc 0 (5/8)) radialTop := by
  let ρ := Real.sqrt 3-1-(Real.sqrt 3/6)*(3/10)-(5/16)*(3/10)^2
  let d : ℝ → ℝ := fun x => 4/5+(12/25)*(x-3/8)-ρ*Real.cos x-(4/5)*Real.sin x-
    ((5/16)*Real.cos x*(3/10-x/2)^2-(3/8+(5/16)*Real.sin x)*(3/10-x/2))
  let dd : ℝ → ℝ := fun x => 12/25-3/16+Real.sin x*(ρ-5/32+(5/16)*(3/10-x/2)^2)-
    Real.cos x*(4/5-(5/8)*(3/10-x/2))
  have hd (x : ℝ) : HasDerivAt radialTop (d x) x := by
    have h := (show DifferentiableAt ℝ radialTop x by
      unfold radialTop radialForm; fun_prop).hasDerivAt
    convert h using 1
    unfold radialTop radialForm
    simp (disch := fun_prop)
    ring
  have hdd (x : ℝ) : HasDerivAt d (dd x) x := by
    have h := (show DifferentiableAt ℝ d x by fun_prop).hasDerivAt
    convert h using 1
    simp (disch := fun_prop) [d,dd]
    ring
  refine concave_of_deriv2 (fun x _ => hd x) (fun x _ => hdd x) (fun x hx => ?_)
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hB : ρ-5/32+(5/16)*(3/10-x/2)^2 ≤ 1/2 := by
    have hg : (3/10-x/2)^2 ≤ 9/100 := by nlinarith [hx.1,hx.2]
    dsimp only [ρ]
    linarith [sqrt_three_bounds.2]
  have hS := mul_le_mul_of_nonneg_left hB hs0
  have hC := mul_le_mul_of_nonneg_right (Real.one_sub_sq_div_two_le_cos (x := x))
    (show 0 ≤ 4/5-(5/8)*(3/10-x/2) by linarith [hx.1])
  have h2 := mul_le_mul_of_nonneg_left hx.2 hx.1
  have h3 := mul_le_mul_of_nonneg_left h2 hx.1
  dsimp only [dd]
  linarith [Real.sin_le hx.1,hx.1,hx.2]

private lemma radialTop_zero : radialTop 0 = 0 := by
  unfold radialTop radialForm
  simp
  norm_num

private lemma radialTop_right : 0 < radialTop (5/8) := by
  have hs := sin_upper_five (show (0:ℝ) ≤ 5/8 by norm_num)
  have hc := cos_lower_six (show (0:ℝ) ≤ 5/8 by norm_num)
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi (show (0:ℝ) ≤ 5/8 by norm_num)
    (by linarith [Real.pi_gt_three])
  have hr := mul_le_mul_of_nonneg_right sqrt_three_bounds.2.le hs0
  unfold radialTop radialForm
  norm_num at hs hc ⊢
  linarith [Real.sin_le_one (5/8)]

/-- At the heights `v = 0` and `v = 3/10`, `radialForm` exceeds
`(3/8 + (5/16) sin z)(v - z/2)²`. At `v = 0` Taylor bounds leave `z` times a
positive linear function plus `z³` times a positive one; at `v = 3/10` the excess
is concave in `z`, zero at `0` and positive at `5/8`. -/
lemma radialForm_ends {z : ℝ} (hz : 0 < z ∧ z ≤ 5/8) :
    (3/8+(5/16)*Real.sin z)*(z/2)^2 < radialForm z 0 ∧
      (3/8+(5/16)*Real.sin z)*(3/10-z/2)^2 < radialForm z (3/10) := by
  have hz0 := hz.1.le
  have h3 := sqrt_three_bounds
  constructor
  · have hsU := mul_le_mul_of_nonneg_left (sin_upper_five hz0)
      (show 0 ≤ Real.sqrt 3-1 by linarith [h3.1])
    have hsz := mul_le_mul_of_nonneg_left (Real.sin_le hz0) (sq_nonneg z)
    have hc := Real.one_sub_sq_div_two_le_cos (x := z)
    have hlin := mul_pos hz.1
      (show 0 < 9/5-Real.sqrt 3-(1/100+3/32)*z by linarith [hz.2,h3.2])
    have hcub := mul_nonneg (pow_nonneg hz0 3)
      (show 0 ≤ (Real.sqrt 3-1)*(1/6-z^2/120)-5/64 by nlinarith [h3.1])
    dsimp only [radialForm]
    linarith
  · have h := concave_pos_of_zero_left radialTop_concave hz radialTop_zero radialTop_right
    dsimp only [radialTop] at h
    linarith

/-- `radialForm z v` is positive for `0 ≤ v ≤ 3/10`: minus
`(3/8 + (5/16) sin z)(v - z/2)²` it is affine in `v`, and it is positive at both
ends (`radialForm_ends`). -/
theorem radialForm_pos {z v : ℝ} (hz : 0 < z ∧ z ≤ 5/8) (hv : 0 ≤ v ∧ v ≤ 3/10) :
    0 < radialForm z v := by
  obtain ⟨h0,h3⟩ := radialForm_ends hz
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le (by linarith [hz.2,Real.pi_gt_three])
  have hsq := mul_nonneg (show 0 ≤ 3/8+(5/16)*Real.sin z by linarith) (sq_nonneg (v-z/2))
  have hid : radialForm z v = (3/8+(5/16)*Real.sin z)*(v-z/2)^2+
      (1-10*v/3)*(radialForm z 0-(3/8+(5/16)*Real.sin z)*(z/2)^2)+
      (10*v/3)*(radialForm z (3/10)-(3/8+(5/16)*Real.sin z)*(3/10-z/2)^2) := by
    unfold radialForm
    ring
  rw [hid]
  rcases le_total (radialForm z 0-(3/8+(5/16)*Real.sin z)*(z/2)^2)
    (radialForm z (3/10)-(3/8+(5/16)*Real.sin z)*(3/10-z/2)^2) with hle | hle
  · linarith only [hsq,h0,mul_nonneg hv.1 (sub_nonneg.mpr hle)]
  · linarith only [hsq,h3,mul_nonneg (show 0 ≤ 1-10*v/3 by linarith [hv.2]) (sub_nonneg.mpr hle)]

lemma inward_circular_pos {a u A v z : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v)
    (he : z=label a u+label A v-Real.pi/6)
    (hz : 0 < z ∧ z ≤ 5/8) (hv : v ≤ 3/10) :
    0 < inwardOpposite a A v z := by
  have hquad := circle_quadratic_upper ⟨h'.u_nonneg,hv⟩
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,Real.pi_gt_d2])
  have hmul := mul_le_mul_of_nonneg_right
    (show A-1/2 ≤ Real.sqrt 3-1-(Real.sqrt 3/6)*v-(5/16)*v^2 by linarith [a_le_circle h']) hs0
  have hW := side_remainder_quadratic h hT
  have hwarg : label a u-Real.pi/6=z-(5/4)*v := by
    rw [hA] at he
    dsimp [axial] at he
    linarith
  rw [hwarg] at hW
  have hp := radialForm_pos hz ⟨h'.u_nonneg,hv⟩
  rw [inward_opposite_side_identity hT hA he,abs_of_nonneg hs0]
  dsimp only [radialForm] at hp
  linarith

lemma line_to_circle_turn_margin {z : ℝ}
    (hz : 1/5 ≤ z ∧ z ≤ Real.pi/3) :
    (12:ℝ)/13 < (44/45)*Real.sin z+(4/5)*Real.cos z := by
  have h := trig_concave_gt (α := 0) (A := 44/45) (B := 4/5) (m := 12/13) (by norm_num)
    (by norm_num) (by norm_num) (by linarith [Real.pi_pos]) hz
    (by have := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 1/5 by norm_num)
        have := Real.one_sub_sq_div_two_le_cos (x := (1/5:ℝ))
        linarith)
    (by rw [Real.sin_pi_div_three,Real.cos_pi_div_three]; linarith [sqrt_three_bounds.1])
  linarith

namespace Boundary

def otherLabel (z t : ℝ) : ℝ := z+Real.pi/6-t
def otherV (z t : ℝ) : ℝ := (4/5)*otherLabel z t
def oppositeUpper (z t : ℝ) : ℝ :=
  inwardOpposite (sideTopA t) (axialTop (otherV z t)) (otherV z t) z

def diagonalJunction (z : ℝ) : ℝ :=
  inwardOpposite rd (tieA (otherLabel z td)) (otherV z td) z

lemma sideTopA_diagonal {t : ℝ} (ht : td ≤ t) : sideTopA t=diagonal t := by
  by_cases he : t=td
  · subst t
    simp only [sideTopA,ite_eq_left le_rfl]
    rw [side_at_diagonal.1]
    dsimp [diagonal,td]
    ring
  · simp only [sideTopA,ite_eq_right (show ¬t≤td from fun h => he (le_antisymm h ht))]

lemma sideTopA_td : sideTopA td=rd := by
  simp only [sideTopA,ite_eq_left le_rfl]
  exact side_at_diagonal.1

lemma opposite_upper_circular {z t : ℝ}
    (hz : 0 < z) (ht : s0 ≤ t ∧ t ≤ td)
    (hs : 0 ≤ otherLabel z t ∧ otherLabel z t ≤ s0) :
    0 < oppositeUpper z t := by
  have htt : s0 ≤ t ∧ t ≤ Real.pi/4 := ⟨ht.1,ht.2.trans td_bounds.2.le⟩
  have hs' : 0 ≤ otherV z t ∧ otherV z t ≤ Real.pi/5 := by
    dsimp [otherV]
    constructor <;> linarith [hs.1,hs.2,transition_coarse.2.2.2.2.2,Real.pi_gt_d2]
  obtain ⟨ha,hT,hside⟩ := sideTop_state htt
  obtain ⟨hb,hB⟩ := axialTop_state hs'
  have hv : otherV z t ≤ 3/10 := by
    dsimp [otherV]
    have hu := transition_coarse.2.2.2.1
    dsimp [s0] at hs
    linarith
  have hzz : z ≤ diagonalAngle := by
    dsimp [otherLabel] at hs
    dsimp [diagonalAngle]
    linarith [ht.2]
  have hz' : z ≤ 5/8 := by linarith [diagonal_angle_bounds.2]
  apply inward_circular_pos ha hb hT hB
    (show z=label (sideTopA t) (sideTopU t)+label (axialTop (otherV z t)) (otherV z t)-Real.pi/6 by
      rw [hT,hside,hB]
      dsimp [axial,otherV,otherLabel]
      ring) ⟨hz,hz'⟩ hv

lemma opposite_upper_cap {z t : ℝ}
    (hz : 0 < z ∧ z ≤ Real.pi/3) (ht : td ≤ t ∧ t ≤ Real.pi/4)
    (hs : otherLabel z t=Real.pi/4) : 0 < oppositeUpper z t := by
  have hv : otherV z t=Real.pi/5 := by rw [otherV,hs]; ring
  have hu0 : u0 ≤ Real.pi/5 := by linarith [transition_coarse.2.2.2.1,Real.pi_gt_d2]
  have hur : Real.pi/5 ≤ rd := by linarith [rd_bounds.1,pi_lt_22_over_7]
  have hA : axialTop (Real.pi/5) < 3/4 := by
    rw [axialTop_right ⟨hu0,hur⟩]
    dsimp [axialLine]
    linarith [Real.pi_gt_d2]
  have ha : sideTopA t < 31/40 := by
    rw [sideTopA_diagonal ht.1]
    have hd := diagonal_td
    have hh : diagonal t≤diagonal td := by dsimp [diagonal]; linarith [ht.1]
    rw [hd] at hh
    linarith [rd_bounds.2]
  have hC := cos_ge_half ⟨hz.1.le,hz.2⟩
  have hS0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le (by linarith [hz.2,Real.pi_pos])
  have hb := (axialTop_state ⟨by positivity,le_rfl⟩).1
  have hm := mul_nonneg (show 0≤3/4-axialTop (Real.pi/5) by linarith) hS0
  have hc := mul_le_mul_of_nonneg_left hC (show 0≤Real.pi/5+1/2 by positivity)
  dsimp [oppositeUpper,inwardOpposite]
  rw [hv,abs_of_nonneg hS0]
  linarith [Real.sin_le_one z,Real.pi_gt_d2]

lemma diagonal_junction_pos {z : ℝ}
    (hz : 0 < z ∧ z ≤ Real.pi/3)
    (hs : s0 ≤ otherLabel z td ∧ otherLabel z td ≤ Real.pi/4) :
    0 < diagonalJunction z := by
  have hstart : diagonalAngle ≤ z := by
    dsimp [otherLabel] at hs
    dsimp [diagonalAngle]
    linarith [hs.1]
  have hd0 := diagonal_angle_bounds
  -- the junction without its absolute value, which is harmless where `sin ≥ 0`
  let g : ℝ → ℝ := fun y => 1/2-rd-(tieA (otherLabel y td)-1/2)*Real.sin y+
    (otherV y td+1/2)*Real.cos y
  have hg (y : ℝ) (hy : 0 ≤ Real.sin y) : diagonalJunction y = g y := by
    dsimp [diagonalJunction,inwardOpposite,g]
    rw [abs_of_nonneg hy]
    ring
  have hmono : MonotoneOn g (Icc diagonalAngle z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by dsimp [g,tieA,otherLabel,otherV]; fun_prop)
      (by dsimp [g,tieA,otherLabel,otherV]; fun_prop)
    intro x hx
    have hx' := interior_subset hx
    have hsx : s0 ≤ otherLabel x td ∧ otherLabel x td ≤ Real.pi/4 := by
      dsimp [otherLabel,diagonalAngle] at *
      constructor <;> linarith [hs.1,hs.2,hx'.1,hx'.2]
    have hC := cos_ge_half (z := x) ⟨by linarith [hx'.1],by linarith [hx'.2,hz.2]⟩
    have hS := Real.sin_nonneg_of_nonneg_of_le_pi (x := x) (by linarith [hx'.1])
      (by linarith [hx'.2,hz.2,Real.pi_pos])
    have hp := tie_slope_pos hsx (by linarith) hS (by linarith [Real.sin_le_one x])
    have hd : deriv g x = (43/90-(4/5)*otherLabel x td)*Real.sin x+
        (13/10-tieA (otherLabel x td))*Real.cos x := by
      simp (disch := fun_prop) [g,tieA,otherLabel,otherV]
      ring
    rw [hd]
    exact hp.le
  have hsin (y : ℝ) (hy : y ∈ Icc diagonalAngle z) : 0 ≤ Real.sin y :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hy.1]) (by linarith [hy.2,hz.2,Real.pi_pos])
  have he : g diagonalAngle = diagonalValue := by
    have hs' : otherLabel diagonalAngle td=s0 := by dsimp [otherLabel,diagonalAngle]; ring
    have hv : otherV diagonalAngle td=u0 := by rw [otherV,hs']; dsimp [s0]; ring
    dsimp [g]
    rw [hs',tieA_s0,hv]
    dsimp [diagonalValue,u0]
    ring
  rw [hg z (hsin z ⟨hstart,le_rfl⟩)]
  exact (he ▸ diagonal_value_pos).trans_le (hmono ⟨le_rfl,hstart⟩ ⟨hstart,le_rfl⟩ hstart)

lemma opposite_upper_junction {z : ℝ}
    (hz : 0<z ∧ z≤Real.pi/3)
    (hs : 0≤otherLabel z td ∧ otherLabel z td≤Real.pi/4) :
    0<oppositeUpper z td := by
  by_cases hc : otherLabel z td ≤ s0
  · exact opposite_upper_circular hz.1
      ⟨by linarith [transition_coarse.2.2.2.2.2,td_bounds.1],le_rfl⟩ ⟨hs.1,hc⟩
  · have hs' : s0≤otherLabel z td := (lt_of_not_ge hc).le
    have hv : u0≤otherV z td ∧ otherV z td≤rd := by
      dsimp [otherV]
      constructor
      · dsimp [s0] at hs'; linarith
      · linarith [hs.2,pi_lt_22_over_7,rd_bounds.1]
    have htop : axialTop (otherV z td)=tieA (otherLabel z td) := by
      rw [axialTop_right hv]
      dsimp [otherV,axialLine,tieA]
      ring
    dsimp [oppositeUpper]
    rw [sideTopA_td,htop]
    exact diagonal_junction_pos hz ⟨hs',hs.2⟩

lemma diagonal_source_reduction {z t l : ℝ}
    (hz : 0≤z ∧ z≤Real.pi/3)
    (ht : td≤l ∧ l≤t)
    (hs : 0≤otherLabel z t ∧ otherLabel z l≤Real.pi/4) :
    oppositeUpper z l≤oppositeUpper z t := by
  have hvl : 0≤otherV z t ∧ otherV z t≤otherV z l ∧ otherV z l≤Real.pi/5 := by
    dsimp [otherV,otherLabel] at *
    exact ⟨by linarith,by linarith,by linarith⟩
  have hA := axialTop_displacement hvl.1 hvl.2.1 hvl.2.2
  have hS := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [hz.2,Real.pi_pos])
  have hC := Real.cos_nonneg_of_mem_Icc (x := z) ⟨by linarith [hz.1,Real.pi_pos],by linarith [hz.2,Real.pi_pos]⟩
  have hp := mul_le_mul_of_nonneg_right hA hS
  have hd : 0≤t-l := sub_nonneg.mpr ht.2
  have hvd : otherV z l-otherV z t=(4/5)*(t-l) := by dsimp [otherV,otherLabel]; ring
  have hS1 := mul_nonneg hd (show 0≤1-Real.sin z from sub_nonneg.mpr (Real.sin_le_one z))
  have hC1 := mul_nonneg hd (show 0≤1-Real.cos z from sub_nonneg.mpr (Real.cos_le_one z))
  dsimp [oppositeUpper,inwardOpposite]
  rw [sideTopA_diagonal ht.1,sideTopA_diagonal (ht.1.trans ht.2)]
  dsimp [diagonal]
  rw [hvd] at hp
  nlinarith

lemma circular_source_line_reduction {z t r : ℝ}
    (hz : 1/5≤z ∧ z≤Real.pi/3)
    (ht : s0≤t ∧ t≤r) (hr : r≤td)
    (hs : s0≤otherLabel z r ∧ otherLabel z t≤Real.pi/4) :
    oppositeUpper z r≤oppositeUpper z t := by
  have hsdom (x : ℝ) (hx : t≤x ∧ x≤r) :
      u0≤otherV z x ∧ otherV z x≤rd := by
    dsimp [otherV,otherLabel] at *
    constructor
    · dsimp [s0] at hs; linarith
    · linarith [pi_lt_22_over_7,rd_bounds.1]
  have htline : axialTop (otherV z t)=tieA (otherLabel z t) := by
    rw [axialTop_right (hsdom t ⟨le_rfl,ht.2⟩)]
    dsimp [axialLine,otherV,tieA]; ring
  have hrline : axialTop (otherV z r)=tieA (otherLabel z r) := by
    rw [axialTop_right (hsdom r ⟨ht.2,le_rfl⟩)]
    dsimp [axialLine,otherV,tieA]; ring
  have ha := sideA_displacement ht.1 ht.2 hr
  have hm := line_to_circle_turn_margin hz
  have hp := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hm.le)
  dsimp [oppositeUpper,inwardOpposite]
  rw [htline,hrline]
  simp only [sideTopA,ite_eq_left (ht.2.trans hr),ite_eq_left hr]
  dsimp [tieA,otherV,otherLabel]
  linarith

/-- Every positive-turn pair of upper endpoints is excluded, by a finite case
split. -/
theorem opposite_upper_pos {z t : ℝ}
    (hz : 0<z ∧ z≤Real.pi/3)
    (ht : s0≤t ∧ t≤Real.pi/4)
    (hs : 0≤otherLabel z t ∧ otherLabel z t≤Real.pi/4) :
    0<oppositeUpper z t := by
  by_cases hdiag : td≤t
  · let l := max td (z-Real.pi/12)
    have hlt : l≤t := max_le hdiag (by dsimp [otherLabel] at hs; linarith [hs.2])
    have hld : td≤l := le_max_left _ _
    have hsl : otherLabel z l≤Real.pi/4 := by
      have hh : z-Real.pi/12≤l := le_max_right _ _
      dsimp [otherLabel]
      linarith
    have hsl0 : 0≤otherLabel z l := by dsimp [otherLabel] at *; linarith [hs.1]
    have hcomp := diagonal_source_reduction ⟨hz.1.le,hz.2⟩ ⟨hld,hlt⟩ ⟨hs.1,hsl⟩
    have hbase : 0<oppositeUpper z l := by
      by_cases hc : z-Real.pi/12≤td
      · have he : l=td := max_eq_left hc
        rw [he]
        exact opposite_upper_junction hz ⟨by simpa only [he] using hsl0,by simpa only [he] using hsl⟩
      · have he : l=z-Real.pi/12 := max_eq_right (le_of_not_ge hc)
        exact opposite_upper_cap hz ⟨hld,hlt.trans ht.2⟩
          (by rw [he]; dsimp [otherLabel]; ring)
    exact hbase.trans_le hcomp
  · have htc : t≤td := (lt_of_not_ge hdiag).le
    by_cases hcircle : otherLabel z t ≤ s0
    · exact opposite_upper_circular hz.1 ⟨ht.1,htc⟩ ⟨hs.1,hcircle⟩
    · let r := min td (z+Real.pi/6-s0)
      have htr : t≤r := le_min htc (by dsimp [otherLabel] at hcircle; linarith)
      have hrd : r≤td := min_le_left _ _
      have hsr : s0≤otherLabel z r := by
        have hh : r≤z+Real.pi/6-s0 := min_le_right _ _
        dsimp [otherLabel]
        linarith
      have hzlow : 1/5≤z := by
        have hsc := transition_bounds
        have hh : s0<otherLabel z t := lt_of_not_ge hcircle
        dsimp [otherLabel,s0] at hh ht
        linarith [pi_lt_22_over_7]
      have hcomp := circular_source_line_reduction ⟨hzlow,hz.2⟩ ⟨ht.1,htr⟩ hrd ⟨hsr,hs.2⟩
      have hbase : 0<oppositeUpper z r := by
        by_cases hc : td≤z+Real.pi/6-s0
        · have he : r=td := min_eq_left hc
          rw [he]
          exact opposite_upper_junction hz ⟨by rw [he] at hsr; linarith [transition_coarse.2.2.2.2.1],
            by dsimp [otherLabel] at hs ⊢; linarith [hs.2,htc]⟩
        · have he : r=z+Real.pi/6-s0 := min_eq_right (le_of_not_ge hc)
          have hsEq : otherLabel z r=s0 := by rw [he]; dsimp [otherLabel]; ring
          exact opposite_upper_circular hz.1 ⟨ht.1.trans htr,hrd⟩
            ⟨by rw [hsEq]; linarith [transition_coarse.2.2.2.2.1],by rw [hsEq]⟩
      exact hbase.trans_le hcomp

end Boundary

end SquaresInCircles.Seven
