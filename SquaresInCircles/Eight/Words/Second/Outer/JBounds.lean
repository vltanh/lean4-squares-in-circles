module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeAlignedShape

/-!
# Eight squares: whole-arc labels for the remaining second-word zero-quarter pairs

The original J label has decreasing curvature
and positive slope on its entire outer arc.  Its rational references
come from the same circle equation.  The stronger lower L slope follows
from a single strong tangent, independently of any angular subdivision.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma J_third_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : JLabel.d3 b<0 := by
  have he := JLabel.third_numerator (outer_domain hb)
  have hu := pow_pos (U_positive (outer_domain hb)) 5
  have hw := (UW_bounds hb).2.2
  have hneg : JLabel.d3 b*(U b)^5<0 := by
    rw [he]
    norm_num [JLabel,Q0]
    linarith [hw.2]
  by_contra hn
  linarith [mul_nonneg (le_of_not_gt hn) hu.le]

lemma J_second_antitone : AntitoneOn JLabel.d2 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (JLabel.d2_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => JLabel.d2_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (J_third_negative (Ioo_subset_Icc_self hb)).le)

lemma J_zero_second : JLabel.d2 0< -(329/1000:ℝ) := by
  have hh := JLabel.second_chart_reference (outer_domain outer_zero_mem)
    (l := (191457567100389/100000000000000:ℝ))
    (u := (191457567100390/100000000000000:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-(329/1000):ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [JLabel,W,Q0]) (by norm_num [JLabel,W,Q0])
  exact hh.2

lemma J_second_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    JLabel.d2 b< -(329/1000:ℝ) :=
  (J_second_antitone outer_zero_mem hb hb.1).trans_lt J_zero_second

lemma J_first_antitone : AntitoneOn JLabel.d1 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (JLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => JLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [J_second_upper (Ioo_subset_Icc_self hb)])

lemma J_zero_first : JLabel.d1 0<(541/500:ℝ) := by
  have hh := JLabel.first_chart_reference (outer_domain outer_zero_mem)
    (l := (191457567100389/100000000000000:ℝ))
    (u := (191457567100390/100000000000000:ℝ))
    (dlo := (1:ℝ)) (dhi := (541/500:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [JLabel,W,Q0]) (by norm_num [JLabel,W,Q0])
  exact hh.2

lemma J_first_diagonal : JLabel.d1 outerDiagonal=
    4161/5000-(1483/6250)*outerDiagonal := by
  dsimp [RoleLabel.d1,JLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal,ratio_diagonal]
  ring

lemma J_first_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (309/500:ℝ)<JLabel.d1 b ∧ JLabel.d1 b<541/500 := by
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hlo := J_first_antitone hb hd hb.2
  rw [J_first_diagonal] at hlo
  exact ⟨by linarith [outer_endpoint_bounds.2.2.2],
    (J_first_antitone outer_zero_mem hb hb.1).trans_lt J_zero_first⟩

lemma J_monotone : MonotoneOn J (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (JLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => JLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [(J_first_bounds (Ioo_subset_Icc_self hb)).1])

lemma J_zero : J 0= -(13/50000)*outerAxial := by
  norm_num [J,RoleLabel.outer,RoleLabel.eval,JLabel,ShortOuterOne.SameContact.arc_zero]

lemma J_diagonal : J outerDiagonal=
    (10396/12500)*outerDiagonal+(5763/100000)*outerDiagonal^2 := by
  dsimp [J,RoleLabel.outer,RoleLabel.eval,JLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  ring

lemma J_concave : ConcaveOn ℝ (Icc 0 outerDiagonal) J :=
  concave_of_deriv2
    (fun b hb => JLabel.outer_hasDerivAt (outer_domain hb))
    (fun b hb => JLabel.d1_hasDerivAt (outer_domain hb))
    (fun b hb => by linarith [J_second_upper hb])

lemma L_first_lower_strong {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (1249/2000:ℝ)<LLabel.d1 b := by
  have ht := curvature_tangent (f := LLabel.d1) (d := LLabel.d2)
    (dd := LLabel.d3) (κ := (317/100:ℝ)) hb L_half_mem
    (fun t ht => LLabel.d1_hasDerivAt (outer_domain ht))
    (fun t ht => LLabel.d2_hasDerivAt (outer_domain ht))
    (fun t ht => (OppositeThree.Aligned.L_third_lower ht).le)
  have hs : (LLabel.d2 (1/2))^2<(4/125:ℝ)^2 := by
    nlinarith [L_half_second.1,L_half_second.2]
  have hp := sq_nonneg ((317/200:ℝ)*(b-1/2)+LLabel.d2 (1/2)/2)
  nlinarith [OppositeThree.Aligned.L_half_first_sharp]

end SquaresInCircles.Eight.SecondWord
