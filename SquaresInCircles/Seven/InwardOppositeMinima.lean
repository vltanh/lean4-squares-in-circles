import SquaresInCircles.Seven.BoundaryProfiles
import SquaresInCircles.Seven.Contacts

/-!
# The inward axis with opposite signs: minima on the boundary

In the turn `e = label a u + label A v - π/6` the support sum is
`1/2 - a - A sin e + |sin e|/2 + (v + 1/2) cos e`. For a side source and an
axial target at a positive turn it is at least its value with the source at the
top of its label segment and the target at the end of its label segment. A
diagonal source moves to its junction or a capped axial endpoint, and a circular
source with a straight axial target to one of its two junctions. The circular
pieces use a two-circle certificate: the radical envelope is bounded by an
explicit quadratic, which turns the support bound into `radialE`, positive by a
Bernstein certificate; the diagonal junction uses one fixed positive value and
monotonicity.
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

/-- Minus the discriminant of `radialE z` as a quadratic in `v`, divided by `z`
(`radial_discriminant_identity`). -/
def radialPolynomial (z : ℝ) : ℝ :=
  201/2000 - (201353/7098000)*z - (3091/21840)*z^2
  - (1571239/14196000)*z^3 - (23103/7280000)*z^4
  + (977419/182520000)*z^5 - (13/6300)*z^6
  - (364297/196560000)*z^7 + z^8/90720 + z^9/8640 - z^11/518400

lemma radialPolynomial_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 5/8) :
    0 < radialPolynomial z :=
  bernstein_pos ![201/2000,61767947/624624000,160355527/1665664000,
    22183121153/239855616000,1341122208527/15350759424000,
    44622066127207/552627339264000,23358801914587/322365947904000,
    4410162763554631/70736299425792000,1523041486356419/30315556896768000,
    4524018740302909/125753421201408000,406318644428659/20958903533568000,
    125352005285647/418089296461824000]
    (fun i => by fin_cases i <;> norm_num) (by norm_num)
    (fun x => by simp only [radialPolynomial,bernstein,Fin.sum_univ_succ,Fin.sum_univ_zero]
                 norm_num [Nat.choose]; ring) hz

def radialB (z : ℝ) : ℝ :=
  67*z/1000-z^2/4+73*z^3/600+z^4/48-733*z^5/120000-z^6/1440

def radialL (z : ℝ) : ℝ :=
  (15/52)*(z-z^3/6)-(z^2/2-z^4/24+z^6/720)

def radialK (z : ℝ) : ℝ := (15/52+1/42)*(z-z^3/6)

def radialE (z v : ℝ) : ℝ :=
  radialB z+v*radialL z+v^2*radialK z+(6/25)*(z-5*v/4)^2

lemma radial_discriminant_identity (z : ℝ) :
    4*(radialK z+3/8)*(radialB z+(6/25)*z^2)
      -(radialL z-(3/5)*z)^2 = z*radialPolynomial z := by
  unfold radialB radialL radialK radialPolynomial
  ring

/-- `radialE z` is positive for every `v`, by completing the square in `v`. -/
theorem radialE_pos {z : ℝ} (hz : 0 < z ∧ z ≤ 5/8) (v : ℝ) :
    0 < radialE z v := by
  have hK : 0 < radialK z := by
    have hm := mul_nonneg hz.1.le (show 0 ≤ 1-z^2 by nlinarith)
    unfold radialK
    exact mul_pos (by norm_num) (by linarith)
  have hid : 4*(radialK z+3/8)*radialE z v =
      (2*(radialK z+3/8)*v+(radialL z-(3/5)*z))^2+z*radialPolynomial z := by
    rw [← radial_discriminant_identity]
    unfold radialE
    ring
  have hp := mul_pos hz.1 (radialPolynomial_pos ⟨hz.1.le,hz.2⟩)
  have hsq := sq_nonneg (2*(radialK z+3/8)*v+(radialL z-(3/5)*z))
  exact pos_of_mul_pos_right (show 0 < 4*(radialK z+3/8)*radialE z v by linarith)
    (by positivity)

lemma circle_quadratic_upper {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 3/10) :
    circle v-1/2 ≤ Real.sqrt 3-1-(15/52)*v-(15/52+1/42)*v^2 := by
  let a : ℝ := 15/52
  let b : ℝ := 15/52+1/42
  let B := Real.sqrt 3-a*v-b*v^2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hr : 0 ≤ 3-v-v^2 := by nlinarith [hv.1,hv.2]
  have hrad := Real.sq_sqrt hr
  have hroot := Real.sqrt_nonneg (3-v-v^2)
  have hB0 : 0 < B := by
    have hv2 : v^2 ≤ (3/10:ℝ)^2 := by nlinarith
    dsimp [B,a,b]
    linarith [sqrt_three_bounds.1]
  have hcoeff1 : 0 ≤ 1-2*Real.sqrt 3*a := by
    dsimp [a]
    linarith [sqrt_three_bounds.2]
  have hcoeff2 : 0 < 1-2*Real.sqrt 3*b+a^2 := by
    dsimp [a,b]
    linarith [sqrt_three_bounds.2]
  have p1 := mul_nonneg hv.1 hcoeff1
  have p2 := mul_nonneg (sq_nonneg v) hcoeff2.le
  have p3 : 0 ≤ 2*a*b*v^3 := mul_nonneg (by dsimp [a,b]; norm_num) (pow_nonneg hv.1 3)
  have p4 : 0 ≤ b^2*v^4 := by positivity
  have hid : B^2-(3-v-v^2)=v*(1-2*Real.sqrt 3*a)+
      v^2*(1-2*Real.sqrt 3*b+a^2)+2*a*b*v^3+b^2*v^4 := by
    dsimp [B]
    linarith
  have hle : Real.sqrt (3-v-v^2) ≤ B := by nlinarith
  have he : targetSq-(v+1/2)^2=3-v-v^2 := by dsimp [targetSq]; ring
  dsimp [circle]
  rw [he]
  dsimp [B,a,b] at hle
  linarith

lemma radial_trig_lower {z v r : ℝ}
    (hz : 0 ≤ z ∧ z ≤ 5/8) (hv : 0 ≤ v)
    (hr : 73/100 ≤ r ∧ r ≤ 733/1000) :
    radialB z+v*radialL z+v^2*radialK z ≤
      (4/5)*z-(r-(15/52)*v-(15/52+1/42)*v^2)*Real.sin z-
        (v+1/2)*(1-Real.cos z) := by
  have hsinL := Real.sin_ge_sub_cube hz.1
  have hsinU := sin_upper_five hz.1
  have hcosL := cos_lower_six hz.1
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hbase := mul_le_mul_of_nonneg_left hsinU hr0
  have h1 := mul_nonneg hz.1 (show 0 ≤ 733/1000-r by linarith [hr.2])
  have h3 := mul_nonneg (pow_nonneg hz.1 3) (show 0 ≤ r-73/100 by linarith [hr.1])
  have h5 := mul_nonneg (pow_nonneg hz.1 5) (show 0 ≤ 733/1000-r by linarith [hr.2])
  have hvSin := mul_le_mul_of_nonneg_left hsinL
    (show 0 ≤ (15/52)*v by positivity)
  have hv2Sin := mul_le_mul_of_nonneg_left hsinL
    (show 0 ≤ (15/52+1/42)*v^2 by positivity)
  have hcos := mul_le_mul_of_nonneg_left hcosL
    (show 0 ≤ v+1/2 by linarith)
  dsimp [radialB,radialL,radialK]
  linarith

lemma inward_circular_pos {a u A v z : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v)
    (he : z=label a u+label A v-Real.pi/6)
    (hz : 0 < z ∧ z ≤ 5/8) (hv : v ≤ 3/10) :
    0 < inwardOpposite a A v z := by
  have hupper := (a_le_circle h').trans (show circle v ≤ circle v by rfl)
  have hquad := circle_quadratic_upper ⟨h'.u_nonneg,hv⟩
  have hAupper : A-1/2 ≤ Real.sqrt 3-1-(15/52)*v-(15/52+1/42)*v^2 := by
    linarith
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,Real.pi_gt_d2])
  have hmul := mul_le_mul_of_nonneg_right hAupper hs0
  have hW := side_remainder_quadratic h hT
  have hwarg : label a u-Real.pi/6=z-(5/4)*v := by
    rw [hA] at he
    dsimp [axial] at he
    linarith
  rw [hwarg] at hW
  have htrig := radial_trig_lower ⟨hz.1.le,hz.2⟩ h'.u_nonneg
    (r := Real.sqrt 3-1) ⟨by linarith [sqrt_three_bounds.1],by linarith [sqrt_three_bounds.2]⟩
  have hp := radialE_pos hz v
  rw [inward_opposite_side_identity hT hA he]
  rw [abs_of_nonneg hs0]
  dsimp [radialE] at hp
  linarith

lemma line_to_circle_turn_margin {z : ℝ}
    (hz : 19/100 ≤ z ∧ z ≤ Real.pi/3) :
    (12:ℝ)/13 < (44/45)*Real.sin z+(4/5)*Real.cos z := by
  have h := trig_concave_gt (α := 0) (A := 44/45) (B := 4/5) (m := 12/13) (by norm_num)
    (by norm_num) (by norm_num) (by linarith [Real.pi_pos]) hz
    (by have := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 19/100 by norm_num)
        have := Real.one_sub_sq_div_two_le_cos (x := (19/100:ℝ))
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
    (hz : 19/100≤z ∧ z≤Real.pi/3)
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
      have hzlow : 19/100≤z := by
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
