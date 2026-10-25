module

public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroNegativeContact

/-!
# Eight squares: four negative-core contact costs on their complete geometric interval

The exact rotated coordinates make all four contact costs strictly
concave: both terms of their second derivative have the required sign.
The possible diagonal competitor increases. Strict rational comparisons
at the geometric interval's two endpoints complete the scalar proof.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.NegativeContact

open CommonQuarter CorePairGeometry

abbrev Row := Fin 4
def c : Row → ℝ := ![-11418/100000,7943/100000,-25648/100000,-94615/100000]
def p : Row → ℝ := ![9133/100000,19335/100000,0,-51554/100000]
def q : Row → ℝ := ![88074/100000,76744/100000,94766/100000,119909/100000]
def g : Row → ℝ := ![62095/100000,62750/100000,62095/100000,58829/100000]
def H (r : Row) (x : ℝ) : ℝ := x+c r-p r*(U x-1/2)+q r*(V x-1/2)
def Hd (r : Row) (x : ℝ) : ℝ := 1-speed x*(p r*V x+q r*U x)
def Hdd (r : Row) (x : ℝ) : ℝ :=
  -speedD x*(p r*V x+q r*U x)+(speed x)^2*(p r*U x-q r*V x)
def G (r : Row) (x : ℝ) : ℝ := x+c r+(q r-p r)*outerDiagonal-g r*cut x
def Gd (r : Row) (x : ℝ) : ℝ := 1-g r*(outerDiagonal-1/2)*n x

lemma coefficient_bounds (r : Row) : 0<g r ∧ g r<1 ∧ 0<q r := by
  fin_cases r <;> norm_num [g,q]

lemma H_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt (H r) (Hd r x) x := by
  have hh : HasDerivAt (fun y => y+c r-p r*(U y-1/2)+q r*(V y-1/2))
      (1-p r*(V x*speed x)+q r*(-U x*speed x)) x :=
    (((hasDerivAt_id' x).add_const (c r)).sub
      (((U_hasDerivAt hx).sub_const (1/2)).const_mul (p r))).add
        (((V_hasDerivAt hx).sub_const (1/2)).const_mul (q r))
  exact hh.congr_deriv (by dsimp [Hd]; ring)

lemma Hd_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt (Hd r) (Hdd r x) x := by
  have hh : HasDerivAt (fun y => 1-speed y*(p r*V y+q r*U y))
      (-(speedD x*(p r*V x+q r*U x)+speed x*(p r*(-U x*speed x)+q r*(V x*speed x)))) x :=
    ((speed_hasDerivAt hx).mul
      (((V_hasDerivAt hx).const_mul (p r)).add
        ((U_hasDerivAt hx).const_mul (q r)))).const_sub 1
  exact hh.congr_deriv (by dsimp [Hdd]; ring)

lemma contact_coefficients (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) :
    0<p r*V x+q r*U x ∧ p r*U x-q r*V x<0 := by
  have hc := coordinates hx
  fin_cases r <;> norm_num [p,q] <;>
    constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

lemma Hdd_neg (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) : Hdd r x<0 := by
  have hh := contact_coefficients r hx
  have hp := mul_pos (speedD_pos hx) hh.1
  have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (speed x)) hh.2.le
  dsimp [Hdd]
  linarith

lemma H_concave (r : Row) : ConcaveOn ℝ (Icc start (7/10)) (H r) :=
  concave_of_deriv2 (fun _ hx => H_hasDerivAt r hx)
    (fun _ hx => Hd_hasDerivAt r hx) (fun _ hx => (Hdd_neg r hx).le)

lemma H_endpoints (r : Row) : (449/500:ℝ)<H r start ∧ (449/500:ℝ)<H r (7/10) := by
  have he := endpoint_coordinates
  have hend : (7/10:ℝ)∈Icc start (7/10) := by norm_num [start]
  have hc := coordinates hend
  have hst : start=30243/100000 := rfl
  constructor
  · fin_cases r <;> norm_num [H,c,p,q] <;>
      linarith only [he.1,he.2.1,he.2.2.1,he.2.2.2.1,hst]
  · fin_cases r <;> norm_num [H,c,p,q] <;>
      linarith only [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem H_lower (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) : (449/500:ℝ)<H r x :=
  concave_gt_of_endpoints (H_concave r) hx (H_endpoints r).1 (H_endpoints r).2

lemma G_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (G r) (Gd r x) x := by
  have hh : HasDerivAt (fun y => y+c r+(q r-p r)*outerDiagonal-
      g r*((outerDiagonal-1/2)*m y-1/2))
      (1-g r*((outerDiagonal-1/2)*n x)) x :=
    (((hasDerivAt_id' x).add_const (c r)).add_const ((q r-p r)*outerDiagonal)).sub
      ((((m_hasDerivAt x).const_mul (outerDiagonal-1/2)).sub_const (1/2)).const_mul (g r))
  exact hh.congr_deriv (by dsimp [Gd]; ring)

lemma Gd_pos (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) : 0<Gd r x := by
  have hx' : x∈Icc 0 (7/10) := ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩
  have tr := positive_trig hx'
  have hn : n x≤1 := by dsimp [n]; linarith [tr.2.1,tr.2.2.1]
  have hcoef : 0≤g r*(outerDiagonal-1/2) :=
    mul_nonneg (coefficient_bounds r).1.le (by linarith [fine_diagonal_bounds.1])
  have hp := mul_le_mul_of_nonneg_left hn hcoef
  have hd := mul_lt_mul_of_pos_left (show outerDiagonal-1/2<(2/5:ℝ) by
    linarith [outer_endpoint_bounds.2.2.2]) (coefficient_bounds r).1
  dsimp [Gd]
  nlinarith [(coefficient_bounds r).2.1]

lemma G_initial (r : Row) : (449/500:ℝ)<G r start := by
  have hd := fine_diagonal_bounds
  have hp := mul_neg_of_pos_of_neg (coefficient_bounds r).1 cut_start_neg
  dsimp [G]
  fin_cases r <;> norm_num [start,c,p,q,g] at hp ⊢ <;> linarith [hd.1,hd.2]

theorem G_lower (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) : (449/500:ℝ)<G r x := by
  have hm : MonotoneOn (G r) (Icc start (7/10)) :=
    monoOn_of_hasDeriv_nonneg (fun z _ => (G_hasDerivAt r z).continuousAt.continuousWithinAt)
      (fun z _ => G_hasDerivAt r z) (fun z hz => (Gd_pos r (Ioo_subset_Icc_self hz)).le)
  exact (G_initial r).trans_le (hm (by norm_num [start]) hx hx.1)

end SquaresInCircles.Eight.ShortMixedZero.NegativeContact
