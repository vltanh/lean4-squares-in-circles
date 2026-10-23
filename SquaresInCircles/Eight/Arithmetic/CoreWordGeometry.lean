module

public import SquaresInCircles.Eight.Arithmetic.CorePairGeometry

/-!
# Common quarter-word costs on the entire core boundary

The common word label has a uniformly bounded angular correction on both
closed core charts. Combining that bound with the center-distance gap
proves every common core/core cost at once, independently of the quarter
increment, signs, and separating axes. No real-box search is used here.

This source remains an uncompiled draft.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.CoreWordGeometry

open CorePairGeometry

def label (a b : ℝ) : ℝ := (73/10)*(7/12-a)+(291/250)*b
def marker (a b : ℝ) : ℝ := Real.arctan (b/a)-label a b

/-- A single arctangent tangent gives the full side bound. -/
theorem side_marker {b : ℝ} (hb : 0 ≤ b ∧ b ≤ 1/2) :
    0 ≤ Real.arctan (b/(7/12:ℝ))-(291/250)*b ∧
      Real.arctan (b/(7/12:ℝ))-(291/250)*b<41/250 := by
  let x : ℝ := 12*b/7
  have hx : 0 ≤ x ∧ x ≤ 6/7 := by
    dsimp [x]
    constructor <;> linarith [hb.1,hb.2]
  have he : b/(7/12:ℝ)=x := by dsimp [x]; ring
  have hb' : b=(7/12)*x := by dsimp [x]; ring
  have hl := arctan_lower_three hx.1
  have hu := arctan_tangent hx.1 (show (0:ℝ) ≤ 3/4 by norm_num)
  have hp := arctan_three_quarters
  norm_num at hu
  have hsq : x^2 ≤ (6/7:ℝ)^2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hcube := mul_le_mul_of_nonneg_right hsq hx.1
  rw [he,hb']
  constructor <;> nlinarith [hx.1,hx.2]

/-- The corner-circle loss controls the possible increase of the angle.
The lower estimate uses the same circle chord and one fixed atan bound. -/
theorem corner_marker {a b : ℝ}
    (hb : 1/2 ≤ b) (hab : b ≤ a)
    (hc : (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2) :
    -(7/40:ℝ)<marker a b ∧ marker a b<7/40 := by
  obtain ⟨hal,hau,hlossU,hlossL⟩ := corner_geometry hb hab hc
  have ha : 0<a := by linarith
  have hd : 0 ≤ b-1/2 := by linarith
  have hx : 0 ≤ b/a := div_nonneg (by linarith) ha.le
  have hxL : (6/7:ℝ) ≤ b/a := (le_div_iff₀ ha).mpr (by linarith)
  have ht := arctan_tangent hx (show (0:ℝ) ≤ 6/7 by norm_num)
  norm_num at ht
  have hratio : (49/85:ℝ)*(b/a-6/7) ≤ (9/5)*(b-1/2) := by
    have hmul := mul_nonneg (by linarith : 0 ≤ a-5/9) hd
    have hdiv : (b/a)*a=b := div_mul_cancel₀ b (ne_of_gt ha)
    apply (mul_le_mul_iff_of_pos_right ha).mp
    nlinarith
  have hside := (side_marker (b := (1/2:ℝ)) (by norm_num)).2
  norm_num at hside
  have hquad : (9/5-(291/250:ℝ))*(b-1/2)-(219/5)*(b-1/2)^2<1/400 := by
    have hs := sq_nonneg (84*(b-1/2)-(9/5-(291/250:ℝ)))
    nlinarith [sq_nonneg (b-1/2)]
  have hlabelL := mul_le_mul_of_nonneg_left hlossL
    (show (0:ℝ) ≤ 73/10 by norm_num)
  have hlabelU : label a b<2081/2500 := by
    have hgb := mul_nonneg (show (0:ℝ) ≤ 291/250 by norm_num)
      (sub_nonneg.mpr hab)
    have hka := mul_pos (show (0:ℝ)<73/10-291/250 by norm_num)
      (show 0<a-67/120 by linarith)
    dsimp [label]
    linarith
  have hangleL := lt_of_lt_of_le arctan_six_sevenths (Real.arctan_le_arctan hxL)
  constructor
  · dsimp [marker]
    linarith
  · dsimp [marker,label]
    nlinarith

theorem marker_mem {a b : ℝ} (h : CoreState a b) :
    -(7/40:ℝ)<marker a b ∧ marker a b<7/40 := by
  rcases h with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
  · have hh := side_marker ⟨hb,hbu⟩
    dsimp [marker,label]
    constructor <;> linarith [hh.1,hh.2]
  · exact corner_marker hb hab hcircle

/-- The same signed marker is used on the two incident edges of a vertex. -/
theorem boundary_marker_mem {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hk : C.kind i ≠ .outer) :
    -(7/40:ℝ)<C.alpha i-C.sigma i*label (C.a i) (C.b i) ∧
      C.alpha i-C.sigma i*label (C.a i) (C.b i)<7/40 := by
  have h := marker_mem (boundary_core_state C i hk)
  dsimp [marker] at h
  rcases C.sigma_sign i with hσ | hσ <;>
    simp only [BoundaryCycle.alpha,BoundaryCycle.tangent,hσ,
      neg_one_mul,one_mul,neg_div,Real.arctan_neg] <;>
    constructor <;> linarith [h.1,h.2]

/-- One geometric inequality covers all common core/core word entries. -/
theorem common_core_cost {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hi : C.kind i ≠ .outer) (hj : C.kind (next i) ≠ .outer) :
    (59/60:ℝ)<angleGap C.beta i+
      (C.alpha (next i)-C.sigma (next i)*label (C.a (next i)) (C.b (next i)))-
      (C.alpha i-C.sigma i*label (C.a i) (C.b i)) := by
  have hg := core_gap C i hi hj
  have hmi := boundary_marker_mem C i hi
  have hmj := boundary_marker_mem C (next i) hj
  linarith [hmi.2,hmj.1]

end SquaresInCircles.Eight.CoreWordGeometry
