import research.seven.lean.CoarseBoundary
import SquaresInCircles.Seven.ForwardNegativeTarget

/-!
E3. The old theorem is never applied. Production is imported only to share
sideTarget and its geometric definitions. The split is by support-force signs,
not by the old 1/6 angle cutoff.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human
open Boundary

def sideForce (z : ℝ) : ℝ :=
  (12/25)*(Real.cos z-3/5)+Real.sin z-4/15

def sideDefect (A v z : ℝ) : ℝ :=
  Real.cos z-2/15-(4/5)*z+
    (3/5-Real.cos z)*(A+1/2)+(Real.sin z-4/15)*(v+1/2)

lemma transition_admissible_geometric : Admissible a0 u0 := by
  have hb := transition_coarse_geometric
  refine ⟨by linarith,by linarith,by linarith,?_⟩
  have hh := transition_circle_exact
  simpa only [phi,a0,u0,targetSq,sub_add_cancel] using hh.le

lemma sideForce_hasDeriv (z : ℝ) : HasDerivAt sideForce
    (Real.cos z-(12/25)*Real.sin z) z := by
  have hd : DifferentiableAt ℝ sideForce z := by unfold sideForce; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [sideForce] <;> ring

lemma sideForce_mono : MonotoneOn sideForce (Icc 0 1) := by
  apply Seven.monoOn_of_hasDeriv_nonneg
    (d := fun z => Real.cos z-(12/25)*Real.sin z)
  · unfold sideForce; fun_prop
  · intro z _; exact sideForce_hasDeriv z
  · intro z hz
    have hc := Real.one_sub_sq_div_two_le_cos (x := z)
    have hz2 : z^2 ≤ (1 : ℝ) := by nlinarith [hz.1,hz.2]
    linarith [Real.sin_le_one z]

lemma sideForce_at_twelfth : 0 < sideForce (1/12) := by
  have hs := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ 1/12 by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/12 : ℝ))
  dsimp [sideForce]
  linarith

lemma negative_force_small {z : ℝ} (hz : 0 < z ∧ z < 1)
    (hK : sideForce z < 0) : z < (1 : ℝ)/12 := by
  by_contra hn
  have hle : (1 : ℝ)/12 ≤ z := le_of_not_gt hn
  have hh := sideForce_mono
    (show (1/12 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    ⟨hz.1.le,hz.2.le⟩ hle
  linarith [sideForce_at_twelfth]

lemma nonnegative_force_lower {z : ℝ} (hz : 0 ≤ z)
    (hK : 0 ≤ sideForce z) : (28 : ℝ)/375 ≤ z := by
  have hs := Real.sin_le hz
  have hc := Real.cos_le_one z
  dsimp [sideForce] at hK
  linarith

lemma side_transition_defect {z : ℝ} (hz : 0 < z ∧ z < 1)
    (hK : 0 ≤ sideForce z) : (13/22500 : ℝ)*z ≤ sideDefect a0 u0 z := by
  have hb := transition_coarse_geometric
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,pi_lower])
  have hc0 : 0 ≤ 1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
  have hW := transition_admissible_geometric.remainder_nonneg
  have ha := mul_nonneg (show 0 ≤ a0-1/2-3/5 by linarith) hc0
  have hu := mul_nonneg (show 0 ≤ u0+1/2-79/100 by linarith) hs0
  have hid : sideDefect a0 u0 z =
      (2/15)*remainder a0 u0+(a0-1/2)*(1-Real.cos z)+
      (u0+1/2)*Real.sin z-(4/5)*z := by
    dsimp [sideDefect,remainder]
    ring
  have hbase : (3/5)*(1-Real.cos z)+(79/100)*Real.sin z-(4/5)*z ≤
      sideDefect a0 u0 z := by rw [hid]; nlinarith
  have hsin := Real.sin_ge_sub_cube hz.1.le
  have hcos := Seven.cos_upper_four hz.1.le
  have h3 : z^3 ≤ z^2 := by
    have hp := mul_nonneg (sq_nonneg z) (show 0 ≤ 1-z by linarith [hz.2])
    nlinarith
  have h4 : z^4 ≤ z^2 := by
    have hz2 : z^2 ≤ (1 : ℝ) := by nlinarith [hz.1,hz.2]
    have hp := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz2)
    nlinarith
  have hquad : z*(-1/100+(17/120)*z) ≤ sideDefect a0 u0 z := by
    nlinarith [pow_nonneg hz.1.le 3]
  have hzlo := nonnegative_force_lower hz.1.le hK
  have hprod := mul_nonneg hz.1.le (show 0 ≤ z-28/375 by linarith)
  nlinarith

lemma side_tangent_regime {A v z : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (hz : 0 < z ∧ z < 1)
    (hc : (3 : ℝ)/5 ≤ Real.cos z) (hK : 0 ≤ sideForce z) :
    0 < sideDefect A v z := by
  have hb := side_state_transition h hT
  have ht := side_transition_trade h hT
  have h1 := mul_nonneg (sub_nonneg.mpr hc)
    (show 0 ≤ a0-A-(12/25)*(v-u0) by linarith)
  have h2 := mul_nonneg hK (sub_nonneg.mpr hb.1)
  have hcompare : sideDefect a0 u0 z ≤ sideDefect A v z := by
    dsimp [sideDefect,sideForce] at *
    nlinarith
  have hm := side_transition_defect hz hK
  have hpos : 0 < (13/22500 : ℝ)*z := by positivity
  linarith

lemma side_positive_coefficients {A v z : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (hz : 0 < z ∧ z < 1)
    (hc : Real.cos z < (3 : ℝ)/5) : 0 < sideDefect A v z := by
  have hb := side_state_transition h hT
  have hu0 := transition_u_bounds
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,pi_lower])
  have hcos : (1 : ℝ)/2 < Real.cos z := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := z),hz.1,hz.2]
  have hsin : (4 : ℝ)/5 < Real.sin z := by
    nlinarith [Real.sin_sq_add_cos_sq z]
  have hp := mul_nonneg (show 0 ≤ 3/5-Real.cos z by linarith)
    (show 0 ≤ A+1/2-1 by linarith [h.half_le])
  have hq := mul_nonneg (show 0 ≤ Real.sin z-4/15 by linarith)
    (show 0 ≤ v+1/2-79/100 by linarith [hb.1,hu0.1])
  dsimp [sideDefect]
  nlinarith

/-- Disk-only closure in the small regime forced by a negative tangent force. -/
lemma side_small_disk {A v z : ℝ} (h : Admissible A v)
    (hz : 0 < z ∧ z ≤ 1/12) : 0 < sideDefect A v z := by
  let c := Real.cos z
  let s := Real.sin z
  let L := c-2/15-(4/5)*z
  let p := 3/5-c
  let q := s-4/15
  have hs0 : 0 ≤ s := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,pi_lower])
  have hunit : c^2+s^2=1 := by
    dsimp [c,s]
    exact Real.cos_sq_add_sin_sq z
  have hs := Real.sin_le hz.1.le
  have hs2 : s^2 ≤ z^2 := pow_le_pow_left₀ hs0 hs 2
  have hc2 : 1-z^2 ≤ c^2 := by nlinarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have hsin := Real.sin_ge_sub_cube hz.1.le
  have hz2 : z^2 ≤ (1/12 : ℝ)^2 := by nlinarith [hz.1,hz.2]
  have hL : 0 ≤ L := by dsimp [L,c]; nlinarith
  have hid : L^2-(13/4)*(p^2+q^2) =
      c^2+(109/30-(8/5)*z)*c+(26/15)*s+
      (2/15+(4/5)*z)^2-2093/450 := by
    dsimp [L,p,q]
    linear_combination (-13/4 : ℝ)*hunit
  have hmul := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ (109/30 : ℝ)-(8/5)*z by linarith [hz.2])
  have hdelta : z*(26/75-(653/300)*z+(23/45)*z^2) ≤
      L^2-(13/4)*(p^2+q^2) := by
    rw [hid]
    dsimp [c,s] at *
    nlinarith
  have hprod := mul_nonneg hz.1.le (show 0 ≤ 1/12-z by linarith [hz.2])
  have hmargin : (119/720 : ℝ)*z ≤ L^2-(13/4)*(p^2+q^2) := by
    nlinarith [pow_nonneg hz.1.le 3]
  have hstrict : (13/4 : ℝ)*(p^2+q^2) < L^2 := by nlinarith [hz.1]
  have hd := disk_dot_lower_strict (state_disk h) hL hstrict
  have he : sideDefect A v z = L+p*(A+1/2)+q*(v+1/2) := by
    dsimp [sideDefect,L,p,q,c,s]
    ring
  rw [he]
  linarith

lemma side_defect_pos {A v z : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (hz : 0 < z ∧ z < 1) :
    0 < sideDefect A v z := by
  by_cases hc : (3 : ℝ)/5 ≤ Real.cos z
  · by_cases hK : 0 ≤ sideForce z
    · exact side_tangent_regime h hT hz hc hK
    · exact side_small_disk h ⟨hz.1,(negative_force_small hz (lt_of_not_ge hK)).le⟩
  · exact side_positive_coefficients h hT hz (lt_of_not_ge hc)

/-- Exact replacement for the production sideTarget_negative_pos statement. -/
theorem sideTarget_negative_pos {A v z : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (hz : 0 < z ∧ z < 1) :
    0 < Seven.sideTarget A v (-z) := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,pi_lower])
  have he : Seven.sideTarget A v (-z)=sideDefect A v z := by
    dsimp [Seven.sideTarget,sideDefect,remainder]
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs]
    ring
  rw [he]
  exact side_defect_pos h hT hz

end SquaresInCircles.Seven.Human
