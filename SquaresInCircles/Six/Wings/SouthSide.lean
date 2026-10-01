import SquaresInCircles.Six.Wings.Chord
import SquaresInCircles.Six.Wings.Chart

/-!
# W on its own axis, S on the south side of C

Let W be separated from C along its own axis, S along the south side of C, W
from D along the secondary axis of W and D from S along the secondary axis of
D. Weights `2037/1000`, `1`, `391/1000`, `1`, `1` on C–W, C–S, C–D, W–D and D–S
give S the force `U = cos s + cos (d - s)`, `V = sin (d - s) - sin s`, that is
`2 cos (d/2)` times `cos (d/2 - s)` and `sin (d/2 - s)`. For `d ≤ 11/14` it lies
in the wide cone, where the support is `ρ̄ U + (3/25) V²`; with
`x = d/2 - s` the terms of S are then `C cos x - P sin² x`, with
`P = (12/25) cos² (d/2)` and `C = -2B cos (d/2) + sin (d/2)`, and a completed
square bounds them below by `C - 1/250`. For `d ≥ 157/200`, `0 ≤ s` and
`d - s ≤ 4/7` the force lies in the axial cone, the support is `ρ̄ U` and the
terms of S are `C cos x ≥ C`. Either way the angle of S drops out, and the far
vertex of W, the chord support of D and the face of the box for C leave a
profile in `v` and `d`, concave in each, which exceeds `1/250` on
`[0, 2/3] × [1/2, 11/14]` and is positive on `[0, 2/3] × [11/14, 34/35]`, by
Taylor polynomials at the corners. The first range holds for a missing south
wing, the second, read in the reflection in the diagonal, for a missing west
wing with W on the west side of C and S on its own axis.
-/

noncomputable section
namespace SquaresInCircles.Six.Wings.SouthSide
open Normalization

/-! ### The force on S -/

/-- The force `(U, V)` on S. -/
def southRadial (s d : ℝ) : ℝ := Real.cos s+Real.cos (d-s)
def southTransverse (s d : ℝ) : ℝ := Real.sin (d-s)-Real.sin s

lemma south_half_angle (s d : ℝ) :
    southRadial s d=2*Real.cos (d/2)*Real.cos (d/2-s) ∧
    southTransverse s d=2*Real.cos (d/2)*Real.sin (d/2-s) := by
  have hc0 := Real.cos_sub (d/2) (d/2-s)
  have hc1 := Real.cos_add (d/2) (d/2-s)
  have hs0 := Real.sin_sub (d/2) (d/2-s)
  have hs1 := Real.sin_add (d/2) (d/2-s)
  rw [show d/2-(d/2-s)=s by ring] at hc0 hs0
  rw [show d/2+(d/2-s)=d-s by ring] at hc1 hs1
  constructor
  · dsimp [southRadial]
    nlinarith only [hc0,hc1]
  · dsimp [southTransverse]
    nlinarith only [hs0,hs1]

private lemma square_sum_bound {s d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) (hs : s ≤ 2/5) (hr : d-s ≤ 11/14) :
    s^2+(d-s)^2 ≤ 137/196 := by
  have hr0 : 0 ≤ d-s := by linarith [hd.1,hs]
  by_cases hs0 : 0 ≤ s
  · have hp := mul_nonneg hs0 hr0
    have hq := mul_nonneg (sub_nonneg.mpr hd.2)
      (show 0 ≤ 11/14+d by linarith [hd.1])
    nlinarith only [hp,hq]
  · have hslo : -(2/7) ≤ s := by linarith [hd.1,hr]
    have hS := mul_nonneg (show 0 ≤ s+2/7 by linarith)
      (show 0 ≤ 2/7-s by linarith)
    have hR := mul_nonneg (show 0 ≤ 11/14-(d-s) by linarith)
      (show 0 ≤ 11/14+(d-s) by linarith)
    nlinarith only [hS,hR]

private lemma half_angle_ratio {x : ℝ} (hx : -(15/28) ≤ x ∧ x ≤ 15/28) :
    |Real.sin x| ≤ (3/5)*Real.cos x := by
  have hsq := mul_nonneg (show 0 ≤ 15/28-x by linarith [hx.2])
    (show 0 ≤ 15/28+x by linarith [hx.1])
  have hc : 1343/1568 ≤ Real.cos x := by
    nlinarith only [hsq,Real.one_sub_sq_div_two_le_cos (x := x)]
  have sine_upper (y : ℝ) (hy : -(15/28) ≤ y ∧ y ≤ 15/28) :
      Real.sin y ≤ 511/1000 := by
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ y by linarith [hy.1,Real.pi_gt_d2])
      (show (15:ℝ)/28 ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hy.2
    have hu := sin_upper_five (x := (15:ℝ)/28) (by norm_num)
    nlinarith only [hm,hu]
  have hu := sine_upper x hx
  have hl := sine_upper (-x) (by constructor <;> linarith [hx.1,hx.2])
  rw [Real.sin_neg] at hl
  have hsin : |Real.sin x| ≤ 511/1000 := abs_le.mpr ⟨by linarith,hu⟩
  linarith

/-- The force on S lies in the cone `U ≥ 33/20`, `|V| ≤ 3U/5`. -/
lemma south_force_cone {s d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) (hs : s ≤ 2/5) (hr : d-s ≤ 11/14) :
    33/20 ≤ southRadial s d ∧ |southTransverse s d| ≤ (3/5)*southRadial s d := by
  have hsq := square_sum_bound hd hs hr
  have hsine := Real.one_sub_sq_div_two_le_cos (x := s)
  have hrine := Real.one_sub_sq_div_two_le_cos (x := d-s)
  have hU : 33/20 ≤ southRadial s d := by
    dsimp [southRadial]
    nlinarith only [hsq,hsine,hrine]
  have hx : -(15/28) ≤ d/2-s ∧ d/2-s ≤ 15/28 := by
    constructor <;> linarith [hd.1,hs,hr]
  have hratio := half_angle_ratio hx
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hpos : 0 ≤ 2*Real.cos (d/2) := by positivity
  have hp := mul_le_mul_of_nonneg_left hratio hpos
  obtain ⟨hUI,hVI⟩ := south_half_angle s d
  refine ⟨hU,?_⟩
  rw [hUI,hVI,abs_mul,abs_of_nonneg hpos]
  nlinarith only [hp]

/-- For `0 ≤ s ≤ 2/5` and `0 ≤ d - s ≤ 4/7` the force on S lies in the cone
`U ≥ 7/4`, `|V| ≤ (31/100) U`. -/
lemma south_force_axial {s d : ℝ} (hs : 0 ≤ s ∧ s ≤ 2/5) (hr : 0 ≤ d-s ∧ d-s ≤ 4/7) :
    7/4 ≤ southRadial s d ∧ |southTransverse s d| ≤ (31/100)*southRadial s d := by
  have hssq := mul_nonneg (sub_nonneg.mpr hs.2) (show 0 ≤ 2/5+s by linarith [hs.1])
  have hrsq := mul_nonneg (sub_nonneg.mpr hr.2) (show 0 ≤ 4/7+(d-s) by linarith [hr.1])
  have hU : 7/4 ≤ southRadial s d := by
    dsimp [southRadial]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := s),
      Real.one_sub_sq_div_two_le_cos (x := d-s)]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2,Real.pi_gt_d2])
  have hs1 : Real.sin s ≤ 2/5 := (Real.sin_le hs.1).trans hs.2
  have hr0 := Real.sin_nonneg_of_nonneg_of_le_pi hr.1 (by linarith [hr.2,Real.pi_gt_d2])
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ d-s by linarith [hr.1,Real.pi_pos])
    (show (4:ℝ)/7 ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hr.2
  have ht := sin_upper_five (x := (4:ℝ)/7) (by norm_num)
  have hr1 : Real.sin (d-s) ≤ 541/1000 := by nlinarith only [hmono,ht]
  have hV : |southTransverse s d| ≤ 541/1000 := by
    dsimp [southTransverse]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  exact ⟨hU,by linarith⟩

/-! ### The angle of S

The terms of S in the weighted sum are `southContribution s d`. With
`x = d/2 - s` they are `positiveExpression d x = C cos x - P sin² x` for
`sin s ≥ 0`, where `P = halfQuadratic d` and `C = halfLinear d`, and
`negativeExpression d x` for `sin s ≤ 0`. -/

def halfQuadratic (d : ℝ) : ℝ := (12/25)*Real.cos (d/2)^2
def halfLinear (d : ℝ) : ℝ := -2*B*Real.cos (d/2)+Real.sin (d/2)

def southContribution (s d : ℝ) : ℝ :=
  -B*southRadial s d+(|Real.sin s|+Real.sin (d-s))/2-
    (3/25)*(southTransverse s d)^2

def positiveExpression (d x : ℝ) : ℝ :=
  halfLinear d*Real.cos x-halfQuadratic d*Real.sin x^2

def negativeExpression (d x : ℝ) : ℝ :=
  -2*B*Real.cos (d/2)*Real.cos x+Real.cos (d/2)*Real.sin x-
    halfQuadratic d*Real.sin x^2

lemma half_trig_bounds {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    23/25 ≤ Real.cos (d/2) ∧ 0 ≤ Real.sin (d/2) ∧ Real.sin (d/2) ≤ 383/1000 := by
  obtain ⟨hs,hs',hc,-⟩ := trig_bracket (l := 1/4) (u := 11/28) (x := d/2) (by norm_num)
    (by linarith [Real.pi_gt_d2]) ⟨by linarith [hd.1],by linarith [hd.2]⟩
  norm_num at hs hs' hc
  exact ⟨by linarith,by linarith,by linarith⟩

lemma half_quadratic_lower {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    2/5 ≤ halfQuadratic d := by
  have hc := (half_trig_bounds hd).1
  have hp := mul_nonneg (show 0 ≤ Real.cos (d/2)-23/25 by linarith)
    (show 0 ≤ Real.cos (d/2)+23/25 by linarith)
  dsimp [halfQuadratic]
  nlinarith only [hp]

/-- `2P + C ≤ 3/40` on the diagonal interval: the reserve of the completed
square. -/
lemma half_coefficient_upper {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    2*halfQuadratic d+halfLinear d ≤ 3/40 := by
  have ht := half_trig_bounds hd
  have hc1 := Real.cos_le_one (d/2)
  have hfactor := mul_nonneg
    (show 0 ≤ 1-Real.cos (d/2) by linarith)
    (show 0 ≤ (25/48)*(1+Real.cos (d/2))-1 by linarith [ht.1])
  have hcos : 1-(25/48)*Real.sin (d/2)^2 ≤ Real.cos (d/2) := by
    nlinarith only [hfactor,Real.sin_sq_add_cos_sq (d/2)]
  have hB := mul_nonneg (show 0 ≤ B-153/250 by norm_num [B])
    (show 0 ≤ Real.cos (d/2) by linarith [ht.1])
  have hpoly : 2*halfQuadratic d+halfLinear d ≤
      -33/125+Real.sin (d/2)-(129/400)*Real.sin (d/2)^2 := by
    dsimp [halfQuadratic,halfLinear]
    nlinarith only [hcos,hB,Real.sin_sq_add_cos_sq (d/2)]
  have hmono := mul_nonneg
    (show 0 ≤ 383/1000-Real.sin (d/2) by linarith [ht.2.2])
    (show 0 ≤ 1-(129/400)*(Real.sin (d/2)+383/1000) by linarith [ht.2.2])
  nlinarith only [hpoly,hmono]

lemma quadratic_reserve (z : ℝ) :
    (2/5)*(z-1)^2+(3/40)*(z-1)+1/250 =
      (2/5)*(z-29/32)^2+31/64000 := by ring

lemma positive_expression_lower {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) (x : ℝ) :
    halfLinear d-1/250 ≤ positiveExpression d x := by
  have hP := half_quadratic_lower hd
  have hE := half_coefficient_upper hd
  have h1 := Real.cos_le_one x
  have hp := mul_nonneg (show 0 ≤ halfQuadratic d-2/5 by linarith)
    (sq_nonneg (Real.cos x-1))
  have he := mul_nonneg
    (show 0 ≤ 3/40-(2*halfQuadratic d+halfLinear d) by linarith)
    (show 0 ≤ 1-Real.cos x by linarith)
  have hres : 0 ≤ (2/5)*(Real.cos x-1)^2+(3/40)*(Real.cos x-1)+1/250 := by
    rw [quadratic_reserve]
    positivity
  have hid : positiveExpression d x-halfLinear d =
      halfQuadratic d*(Real.cos x-1)^2+
      (2*halfQuadratic d+halfLinear d)*(Real.cos x-1) := by
    dsimp [positiveExpression]
    linear_combination -halfQuadratic d*(Real.sin_sq_add_cos_sq x)
  nlinarith only [hp,he,hres,hid]

lemma negative_expression_monotone {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    MonotoneOn (negativeExpression d) (Set.Icc 0 (Real.pi/2)) := by
  have hhalf := half_trig_bounds hd
  have hc0 : 0 ≤ Real.cos (d/2) := by linarith [hhalf.1]
  have hc1 := Real.cos_le_one (d/2)
  have hf (x : ℝ) : HasDerivAt (negativeExpression d)
      (2*B*Real.cos (d/2)*Real.sin x+Real.cos (d/2)*Real.cos x-
        2*halfQuadratic d*Real.sin x*Real.cos x) x := by
    convert ((((Real.hasDerivAt_cos x).const_mul (-2*B*Real.cos (d/2))).add
      ((Real.hasDerivAt_sin x).const_mul (Real.cos (d/2)))).sub
      (((Real.hasDerivAt_sin x).pow 2).const_mul (halfQuadratic d))) using 1 <;>
      (try funext y) <;> dsimp [negativeExpression]
    ring
  apply monoOn_of_hasDeriv_nonneg (fun y _ => (hf y).continuousAt.continuousWithinAt)
    (fun x _ => hf x)
  intro x hx
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le
    (by linarith [hx.2,Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hx.1,Real.pi_pos],hx.2.le⟩
  have hprod : Real.cos (d/2)*Real.cos x ≤ 1 := by
    have h := mul_le_mul hc1 (Real.cos_le_one x) hc (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using h
  have hcoef : 0 ≤ 2*B-(24/25)*Real.cos (d/2)*Real.cos x := by
    norm_num [B] at *
    linarith
  have hp := mul_nonneg hc0 (add_nonneg (mul_nonneg hcoef hs) hc)
  dsimp [halfQuadratic]
  nlinarith only [hp]

lemma contribution_of_nonnegative {s d : ℝ} (hs : 0 ≤ Real.sin s) :
    southContribution s d=positiveExpression d (d/2-s) := by
  obtain ⟨hU,hV⟩ := south_half_angle s d
  have h0 := Real.sin_sub (d/2) (d/2-s)
  have h1 := Real.sin_add (d/2) (d/2-s)
  rw [show d/2-(d/2-s)=s by ring] at h0
  rw [show d/2+(d/2-s)=d-s by ring] at h1
  have hsum : Real.sin s+Real.sin (d-s)=2*Real.sin (d/2)*Real.cos (d/2-s) := by
    nlinarith only [h0,h1]
  dsimp [southContribution]
  rw [abs_of_nonneg hs,hU,hV,hsum]
  dsimp [positiveExpression,halfLinear,halfQuadratic]
  ring

lemma contribution_of_nonpositive {s d : ℝ} (hs : Real.sin s ≤ 0) :
    southContribution s d=negativeExpression d (d/2-s) := by
  obtain ⟨hU,hV⟩ := south_half_angle s d
  have hmid : -Real.sin s+Real.sin (d-s)=southTransverse s d := by
    dsimp [southTransverse]
    ring
  dsimp [southContribution]
  rw [abs_of_nonpos hs,hmid,hU,hV]
  dsimp [negativeExpression,halfQuadratic]
  ring

/-- The terms of S in the weighted sum are at least `C - 1/250`, for either
sign of `s`. -/
theorem south_angle_lower {s d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hs : s ≤ 2/5) (hr : d-s ≤ 11/14) :
    halfLinear d-1/250 ≤ southContribution s d := by
  by_cases hs0 : 0 ≤ s
  · have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hs0
      (by linarith [hs,Real.pi_gt_d2])
    rw [contribution_of_nonnegative hsin]
    exact positive_expression_lower hd _
  · have hslo : -(2/7) ≤ s := by linarith [hd.1,hr]
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ -s by linarith) (show -s ≤ Real.pi by linarith [hslo,Real.pi_gt_d2])
    rw [Real.sin_neg] at hsin
    rw [contribution_of_nonpositive (by linarith : Real.sin s ≤ 0)]
    have ht : d/2 ∈ Set.Icc 0 (Real.pi/2) := by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2]
    have hx : d/2-s ∈ Set.Icc 0 (Real.pi/2) := by
      constructor <;> linarith [hd.1,hs0,hr,Real.pi_gt_d2]
    have hm := negative_expression_monotone hd ht hx (by linarith : d/2 ≤ d/2-s)
    have hid : negativeExpression d (d/2)=positiveExpression d (d/2) := by
      dsimp [negativeExpression,positiveExpression,halfLinear]
      ring
    rw [hid] at hm
    exact (positive_expression_lower hd _).trans hm

/-- For `157/200 ≤ d ≤ 34/35` the terms of S with the support `rho0 U` are at
least `C`. -/
lemma south_angle_lower_high {s d : ℝ} (hd : 157/200 ≤ d ∧ d ≤ 34/35) :
    halfLinear d ≤ -B*southRadial s d+(Real.sin s+Real.sin (d-s))/2 := by
  have hsq := mul_nonneg (show 0 ≤ 1/2-d/2 by linarith [hd.2])
    (show 0 ≤ 1/2+d/2 by linarith [hd.1])
  have hc : 7/8 ≤ Real.cos (d/2) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := d/2)]
  have hC : halfLinear d ≤ 0 := by
    dsimp [halfLinear,B]
    linarith [Real.sin_le_one (d/2)]
  have hp := mul_nonneg (neg_nonneg.mpr hC)
    (show 0 ≤ 1-Real.cos (d/2-s) by linarith [Real.cos_le_one (d/2-s)])
  have hU := (south_half_angle s d).1
  have h0 := Real.sin_sub (d/2) (d/2-s)
  have h1 := Real.sin_add (d/2) (d/2-s)
  rw [show d/2-(d/2-s)=s by ring] at h0
  rw [show d/2+(d/2-s)=d-s by ring] at h1
  have hid : -B*southRadial s d+(Real.sin s+Real.sin (d-s))/2 =
      halfLinear d*Real.cos (d/2-s) := by
    rw [hU]
    dsimp [halfLinear]
    nlinarith only [h0,h1]
  rw [hid]
  nlinarith only [hp]

/-! ### The profile -/

/-- `R̄ (2 + z²/4)` and `R̄ z` for the weight `z = 391/1000` on C–D. -/
def chordL : ℝ := 68834774283/20000000000
def chordM : ℝ := 3301213/5000000

/-- The threshold sum less the supports once the angle of S is eliminated, for
the face `y` of the box. -/
def profile (y v d : ℝ) : ℝ :=
  (137023941021/125000000000-y)+harmonic ((2037/1000)*A) ((2037/1000)*(1/2+y)) v+
    harmonic ((391/1000)*A) ((391/1000)*(1/2-y)) d+chord chordL chordM (d+v)+halfLinear d

lemma chord_second_upper {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 5/3) :
    chordSecond chordL chordM q ≤ -(3/40) := by
  have hL : chordL ≤ chordSin := by norm_num [chordL,chordSin]
  have hM : chordM ≤ chordCos := by norm_num [chordM,chordCos]
  rcases le_total q 1 with hq1 | hq1
  · have h := chord_second_envelope hL hM ⟨hq.1,by linarith⟩
    have hm : (1:ℝ)/2 ≤ min q 1 := le_min hq.1 (by norm_num)
    linarith
  · linarith [chord_second_high hL hM ⟨by linarith,hq.2⟩]

lemma profile_west_concave {y d : ℝ} (hy : 0 ≤ y ∧ y ≤ 1/2) (hd : 1/2 ≤ d ∧ d ≤ 34/35) :
    ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun v => profile y v d) := by
  have e : (fun v => profile y v d) = fun v => ((137023941021/125000000000-y)+
      harmonic ((391/1000)*A) ((391/1000)*(1/2-y)) d+halfLinear d)+
      (harmonic ((2037/1000)*A) ((2037/1000)*(1/2+y)) v+chord chordL chordM (d+v)) := by
    funext v; simp only [profile]; ring
  rw [e]
  refine concave_of_deriv2
    (f' := fun v => harmonic ((2037/1000)*(1/2+y)) (-((2037/1000)*A)) v+
      chordFirst chordL chordM (d+v))
    (f'' := fun v => -harmonic ((2037/1000)*A) ((2037/1000)*(1/2+y)) v+
      chordSecond chordL chordM (d+v))
    (fun v _ => (((harmonic_hasDerivAt _ _ v).add ((chord_hasDerivAt _ _ (d+v)).comp v
      ((hasDerivAt_id' v).const_add d))).const_add _).congr_deriv (by simp))
    (fun v _ => ((harmonic_hasDerivAt _ _ v).add ((chordFirst_hasDerivAt _ _ (d+v)).comp v
      ((hasDerivAt_id' v).const_add d))).congr_deriv (by simp [harmonic]; ring))
    (fun v ⟨h1,h2⟩ => ?_)
  obtain ⟨hc,hs⟩ := cos_sin_nonneg (x := v) ⟨h1,by linarith [Real.pi_gt_d2]⟩
  have hq := chord_second_upper (show 1/2 ≤ d+v ∧ d+v ≤ 5/3 by constructor <;> linarith)
  have hp : 0 ≤ harmonic ((2037/1000)*A) ((2037/1000)*(1/2+y)) v := by
    simp only [harmonic,A]; nlinarith
  linarith

lemma profile_diagonal_concave {y v : ℝ} (hy : 0 ≤ y ∧ y ≤ coreUpper)
    (hv : 0 ≤ v ∧ v ≤ 2/3) : ConcaveOn ℝ (Set.Icc (1/2) (34/35)) (profile y v) := by
  have e : profile y v = fun d => ((137023941021/125000000000-y)+
      harmonic ((2037/1000)*A) ((2037/1000)*(1/2+y)) v)+
      (harmonic ((391/1000)*A) ((391/1000)*(1/2-y)) d+chord chordL chordM (d+v)+
        halfLinear d) := by
    funext d; simp only [profile]; ring
  have hhalf (d : ℝ) : HasDerivAt halfLinear (B*Real.sin (d/2)+(1/2)*Real.cos (d/2)) d :=
    (((((hasDerivAt_id' d).div_const 2).cos).const_mul (-2*B)).add
      (((hasDerivAt_id' d).div_const 2).sin)).congr_deriv (by ring)
  have hhalf' (d : ℝ) : HasDerivAt (fun x => B*Real.sin (x/2)+(1/2)*Real.cos (x/2))
      ((B/2)*Real.cos (d/2)-(1/4)*Real.sin (d/2)) d :=
    (((((hasDerivAt_id' d).div_const 2).sin).const_mul B).add
      ((((hasDerivAt_id' d).div_const 2).cos).const_mul (1/2))).congr_deriv (by ring)
  rw [e]
  refine concave_of_deriv2
    (f' := fun d => harmonic ((391/1000)*(1/2-y)) (-((391/1000)*A)) d+
      chordFirst chordL chordM (d+v)+(B*Real.sin (d/2)+(1/2)*Real.cos (d/2)))
    (f'' := fun d => -harmonic ((391/1000)*A) ((391/1000)*(1/2-y)) d+
      chordSecond chordL chordM (d+v)+((B/2)*Real.cos (d/2)-(1/4)*Real.sin (d/2)))
    (fun d _ => ((((harmonic_hasDerivAt _ _ d).add ((chord_hasDerivAt _ _ (d+v)).comp d
      ((hasDerivAt_id' d).add_const v))).add (hhalf d)).const_add _).congr_deriv (by simp))
    (fun d _ => (((harmonic_hasDerivAt _ _ d).add ((chordFirst_hasDerivAt _ _ (d+v)).comp d
      ((hasDerivAt_id' d).add_const v))).add (hhalf' d)).congr_deriv
      (by simp [harmonic]; ring))
    (fun d ⟨h1,h2⟩ => ?_)
  have hd : 1/2 ≤ d ∧ d ≤ 34/35 := ⟨h1,h2⟩
  have htrig := harmonic_pos_of_endpoints (K := -(4/3)) (A := 1) (B := 1)
    (l := 1/2) (u := 34/35) (x := d) (by norm_num) (by norm_num)
    (by norm_num) (by linarith [Real.pi_gt_d2]) hd
    (by nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/2),
      Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)])
    (by nlinarith only [cos_lower_six (x := (34:ℝ)/35) (by norm_num),
      sin_lower_seven (x := (34:ℝ)/35) (by norm_num)])
  obtain ⟨-,hsd⟩ := cos_sin_nonneg (x := d) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
  have hp := mul_nonneg (show 0 ≤ (1/2-y)-A by dsimp [A,coreUpper] at hy ⊢; linarith) hsd
  have hchord := chord_second_upper (show 1/2 ≤ d+v ∧ d+v ≤ 5/3 by constructor <;> linarith)
  have hhalf2 := (Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/4 by linarith [Real.pi_pos])
    (show d/2 ≤ Real.pi/2 by linarith [Real.pi_gt_d2])
    (show (1:ℝ)/4 ≤ d/2 by linarith)).trans' (Real.sin_ge_sub_cube (x := (1:ℝ)/4) (by norm_num))
  have hc := Real.cos_le_one (d/2)
  simp only [harmonic,A,B] at *
  nlinarith

/-- Taylor polynomials below the profile. -/
def lower (y v d : ℝ) : ℝ :=
  (137023941021/125000000000-y)+(2037/1000)*A*cosLower v+(2037/1000)*(1/2+y)*sinBelow v+
    (391/1000)*A*cosLower d+(391/1000)*(1/2-y)*sinBelow d+
    sinBelow (d+v)-chordL*sinAbove ((d+v)/2)-chordM*cosUpper ((d+v)/2)-
    2*B*cosUpper (d/2)+sinBelow (d/2)

lemma lower_le {y v d : ℝ} (hy : 0 ≤ y ∧ y ≤ 1/2) :
    lower y v d ≤ profile y v d := by
  have cv := cosLower_le v
  have sv := sinBelow_le v
  have cd := cosLower_le d
  have sd := sinBelow_le d
  have sq := sinBelow_le (d+v)
  have ch := le_cosUpper ((d+v)/2)
  have sh := le_sinAbove ((d+v)/2)
  have ct := le_cosUpper (d/2)
  have st := sinBelow_le (d/2)
  have hA : (0:ℝ) ≤ A := by norm_num [A]
  simp only [lower,profile,harmonic,chord,halfLinear]
  nlinarith [mul_le_mul_of_nonneg_left cv (show 0 ≤ (2037/1000)*A by positivity),
    mul_le_mul_of_nonneg_left sv (show 0 ≤ (2037/1000)*(1/2+y) by linarith),
    mul_le_mul_of_nonneg_left cd (show 0 ≤ (391/1000)*A by positivity),
    mul_le_mul_of_nonneg_left sd (show 0 ≤ (391/1000)*(1/2-y) by linarith),
    mul_le_mul_of_nonneg_left sh (show (0:ℝ) ≤ chordL by norm_num [chordL]),
    mul_le_mul_of_nonneg_left ch (show (0:ℝ) ≤ chordM by norm_num [chordM]),
    mul_le_mul_of_nonneg_left ct (show (0:ℝ) ≤ 2*B by norm_num [B])]

/-- At `v ∈ {0, 2/3}` and `d ∈ {1/2, 11/14, 34/35}` the Taylor polynomials exceed
`1/100`, `1/100` and `1/2500`. -/
lemma corners {y w : ℝ} (hy : y = 0 ∨ y = coreUpper) (hw : w = 0 ∨ w = 2/3) :
    1/100 < lower y w (1/2) ∧ 1/100 < lower y w (11/14) ∧ 1/2500 < lower y w (34/35) := by
  rcases hy with rfl | rfl <;> rcases hw with rfl | rfl <;>
    norm_num [lower,A,B,chordL,chordM,coreUpper,cosLower,cosUpper,
      sinBelow,sinAbove,sinLower,sinUpper]

/-- At `d ∈ {1/2, 11/14, 34/35}` the profile exceeds `1/100`, `1/100` and
`1/2500` for every `v`, by concavity in `v`. -/
lemma section_lower {y v : ℝ} (hy : y = 0 ∨ y = coreUpper)
    (hv : 0 ≤ v ∧ v ≤ 2/3) :
    1/100 < profile y v (1/2) ∧ 1/100 < profile y v (11/14) ∧ 1/2500 < profile y v (34/35) := by
  have hy' : 0 ≤ y ∧ y ≤ 1/2 := by
    rcases hy with rfl | rfl <;> norm_num [coreUpper]
  have l0 (d : ℝ) := lower_le hy' (v := 0) (d := d)
  have l1 (d : ℝ) := lower_le hy' (v := 2/3) (d := d)
  have c0 := corners hy (Or.inl rfl)
  have c1 := corners hy (Or.inr rfl)
  have sec (c d : ℝ) (hd : 1/2 ≤ d ∧ d ≤ 34/35) (h0 : c < lower y 0 d)
      (h1 : c < lower y (2/3) d) : c < profile y v d :=
    concave_gt_of_endpoints (f := fun v => profile y v d) (profile_west_concave hy' hd) hv
      (h0.trans_le (l0 d)) (h1.trans_le (l1 d))
  exact ⟨sec _ _ (by norm_num) c0.1 c1.1,sec _ _ (by norm_num) c0.2.1 c1.2.1,
    sec _ _ (by norm_num) c0.2.2 c1.2.2⟩

/-- The profile exceeds `1/250` on `[0, 2/3] × [1/2, 11/14]` and is positive on
`[0, 2/3] × [1/2, 34/35]`. -/
theorem positive {y v d : ℝ} (hy : y = 0 ∨ y = coreUpper)
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 34/35) :
    (d ≤ 11/14 → 1/250 < profile y v d) ∧ 0 < profile y v d := by
  have hy' : 0 ≤ y ∧ y ≤ coreUpper := by
    rcases hy with rfl | rfl <;> norm_num [coreUpper]
  have hc := profile_diagonal_concave hy' hv
  obtain ⟨h1,h2,h3⟩ := section_lower hy hv
  have hlow (hd1 : d ≤ 11/14) : 1/250 < profile y v d :=
    concave_gt_of_endpoints (hc.subset (Set.Icc_subset_Icc le_rfl (by norm_num))
      (convex_Icc (1/2) (11/14))) ⟨hd.1,hd1⟩ (by linarith) (by linarith)
  refine ⟨hlow,?_⟩
  rcases le_total d (11/14) with hd1 | hd1
  · linarith [hlow hd1]
  · exact concave_gt_of_endpoints (hc.subset (Set.Icc_subset_Icc (by norm_num) le_rfl)
      (convex_Icc (11/14) (34/35))) ⟨hd1,hd.2⟩ (by linarith) (by linarith)

/-! ### The stress -/

/-- The force on C. -/
def forceX (v d : ℝ) : ℝ := (2037/1000)*Real.cos v+(391/1000)*Real.cos d
def forceY (v d : ℝ) : ℝ := -(2037/1000)*Real.sin v+1+(391/1000)*Real.sin d

/-- The threshold sum less the supports of W, D and the face `y` of the box, and
the bound `ρ̄ U + k V²` on the work of the force on S. -/
def defect (y v s d k : ℝ) : ℝ :=
  (2037/1000)*(1/2+angularWidth v)+(1/2+angularWidth s)+(391/1000)*(1/2+angularWidth d)+
    (1/2+angularWidth (d+v))+(1/2+angularWidth (d-s))-
    (radiusBound*(56730553/25000000)-(2037/1000+1)/2)-
    (radiusBound*chordMajorant (391/1000) (d+v)-
      (391/1000+Real.sin (d+v)+1-Real.cos (d+v))/2)-
    (rhoBound*southRadial s d+k*southTransverse s d^2)-
    (coreUpper*forceX v d+y*forceY v d)

lemma defect_sub_profile {y v s d k : ℝ} (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : |s| ≤ 2/5)
    (hd : 1/2 ≤ d ∧ d ≤ 34/35) (hr : 0 ≤ d-s ∧ d-s ≤ Real.pi/2) :
    defect y v s d k-profile y v d =
      (angularWidth (d+v)-(Real.cos (d+v)+Real.sin (d+v))/2)+
      (-B*southRadial s d+(|Real.sin s|+Real.sin (d-s))/2-k*southTransverse s d^2-
        halfLinear d) := by
  have hw := angularWidth_eq (x := v) ⟨hv.1,by linarith [Real.pi_gt_d2]⟩
  have hD := angularWidth_eq (x := d) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
  have hR := angularWidth_eq hr
  have hcs := Real.cos_nonneg_of_mem_Icc (x := s)
    ⟨by linarith [(abs_le.mp hs).1,Real.pi_gt_d2],by linarith [(abs_le.mp hs).2,Real.pi_gt_d2]⟩
  have hS : angularWidth s=(Real.cos s+|Real.sin s|)/2 := by
    simp only [angularWidth,abs_of_nonneg hcs]
  simp only [defect,profile,harmonic,chord,chordMajorant,forceX,forceY,southRadial,
    southTransverse,A,B,chordL,chordM,radiusBound,rhoBound,
    coreUpper,hw,hS,hD,hR]
  ring

/-- The separations of a missing south wing with W on its own axis and S on the
south side of C are incompatible on `0 ≤ v ≤ 2/3`, `|s| ≤ 2/5`,
`1/2 ≤ d ≤ 34/35`, `d - s ≤ π/4`, if `0 ≤ s` and `d - s ≤ 4/7` for
`d > 11/14`. -/
theorem impossible {X : Chart} (hW : X.WestOwn) (hS : X.SouthSide) (h : X.MissingSouth)
    (hv : 0 ≤ X.v ∧ X.v ≤ 2/3) (hs : |X.s| ≤ 2/5) (hd : 1/2 ≤ X.d ∧ X.d ≤ 34/35)
    (hr : X.d-X.s ≤ Real.pi/4) (hhigh : 11/14 < X.d → 0 ≤ X.s ∧ X.d-X.s ≤ 4/7) : False := by
  have hWD := h.west
  have hDS := h.south
  have hCD := X.diagonal_own
  simp only [Chart.WestOwn,Chart.SouthSide,Chart.WestWing,Chart.SouthDiagonal] at hW hS hWD hDS
  obtain ⟨hs1,hs2⟩ := abs_le.mp hs
  have hw := vertex_support X.west (U := 2037/1000) (V := -1) (r := 56730553/25000000)
    (by norm_num) (by norm_num)
  have hdiag := chord_support X.diagonal (z := 391/1000) (by norm_num)
    (show 0 ≤ X.d+X.v ∧ X.d+X.v ≤ Real.pi by constructor <;> linarith [Real.pi_gt_d2])
  obtain ⟨hcv,-⟩ := cos_sin_nonneg (x := X.v) ⟨hv.1,by linarith [Real.pi_gt_d2]⟩
  obtain ⟨hcd,-⟩ := cos_sin_nonneg (x := X.d) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
  obtain ⟨y,hy,hc⟩ := center_face (X := forceX X.v X.d) (Y := forceY X.v X.d)
    (by simp only [forceX]; positivity) (X.box.1.2.trans ceiling_bounds.2.2.2)
    ⟨X.box.2.1,X.box.2.2.trans ceiling_bounds.2.2.2⟩
  have hbound (k : ℝ) (hsouth : southRadial X.s X.d*X.aS+southTransverse X.s X.d*X.bS ≤
      rhoBound*southRadial X.s X.d+k*southTransverse X.s X.d^2) :
      defect y X.v X.s X.d k ≤ 0 := by
    norm_num at hw
    simp only [defect,forceX,forceY,southRadial,southTransverse] at hc hsouth ⊢
    linarith
  have hwq := angularWidth_lower (X.d+X.v)
  have hp := positive hy hv hd
  rcases le_or_gt X.d (11/14) with hlow | hlow
  · have hcone := south_force_cone ⟨hd.1,hlow⟩ hs2 (by linarith [Real.pi_lt_d4])
    have hG := south_angle_lower ⟨hd.1,hlow⟩ hs2 (by linarith [Real.pi_lt_d4])
    have hid := defect_sub_profile (y := y) (k := 3/25) hv hs hd
      ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
    simp only [southContribution] at hG
    linarith [hbound (3/25) (wide_support X.south hcone.1 hcone.2),hp.1 hlow]
  · obtain ⟨hs0,hr'⟩ := hhigh hlow
    have hcone := south_force_axial ⟨hs0,hs2⟩ ⟨by linarith,hr'⟩
    have hG := south_angle_lower_high (s := X.s) ⟨by linarith,hd.2⟩
    have hid := defect_sub_profile (y := y) (k := 0) hv hs hd
      ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [Real.pi_gt_d2]))]
      at hid
    have hsouth := cone_support X.south (by linarith [hcone.1]) hcone.2
    linarith [hbound 0 (by linarith),hp.2]

end SquaresInCircles.Six.Wings.SouthSide
