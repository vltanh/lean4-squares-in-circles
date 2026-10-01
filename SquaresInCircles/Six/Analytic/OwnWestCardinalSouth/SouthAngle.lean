import SquaresInCircles.Six.Analytic.OwnWestCardinalSouth.Cone

/-!
# Eliminate the cardinal-S angle analytically

Put t=d/2 and x=t-s. The smooth S support leaves
 G=-B(cos s+cos(d-s))+(|sin s|+sin(d-s))/2
       -(3/25)(sin(d-s)-sin s)^2, B=30641/50000.
For s>=0 this is P cos(x)^2+C cos(x)-P, where
 P=(12/25)cos(t)^2 and C=-2B cos(t)+sin(t).
On the full diagonal interval, P>=2/5 and 2P+C<=3/40. A completed square
therefore gives G>=C-1/250. For s<=0 the corresponding expression is
increasing in x, so its value at s=0 gives the same lower bound.
This removes an entire angular variable without a grid or a minimizer oracle.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestCardinalSouth

def southB : ℝ := 30641/50000

def halfQuadratic (d : ℝ) : ℝ := (12/25)*Real.cos (d/2)^2
def halfLinear (d : ℝ) : ℝ := -2*southB*Real.cos (d/2)+Real.sin (d/2)

def southContribution (s d : ℝ) : ℝ :=
  -southB*southRadial s d+(|Real.sin s|+Real.sin (d-s))/2-
    (3/25)*(southTransverse s d)^2

def positiveExpression (d x : ℝ) : ℝ :=
  halfLinear d*Real.cos x-halfQuadratic d*Real.sin x^2

def negativeExpression (d x : ℝ) : ℝ :=
  -2*southB*Real.cos (d/2)*Real.cos x+Real.cos (d/2)*Real.sin x-
    halfQuadratic d*Real.sin x^2

lemma half_trig_bounds {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    23/25 ≤ Real.cos (d/2) ∧ 0 ≤ Real.sin (d/2) ∧ Real.sin (d/2) ≤ 383/1000 := by
  have hsq := mul_nonneg
    (show 0 ≤ 2/5-d/2 by linarith [hd.2])
    (show 0 ≤ 2/5+d/2 by linarith [hd.1])
  have hc := Real.one_sub_sq_div_two_le_cos (x := d/2)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ d/2 by linarith [hd.1])
    (show d/2 ≤ Real.pi by linarith [hd.2,Real.pi_gt_d2])
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ d/2 by linarith [hd.1,Real.pi_pos])
    (show (11:ℝ)/28 ≤ Real.pi/2 by linarith [Real.pi_gt_d2])
    (show d/2 ≤ 11/28 by linarith [hd.2])
  have hu := Seven.sin_upper_five (x := (11:ℝ)/28) (by norm_num)
  exact ⟨by nlinarith only [hsq,hc],hs,by nlinarith only [hm,hu]⟩

lemma half_quadratic_lower {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    2/5 ≤ halfQuadratic d := by
  have hc := (half_trig_bounds hd).1
  have hp := mul_nonneg (show 0 ≤ Real.cos (d/2)-23/25 by linarith)
    (show 0 ≤ Real.cos (d/2)+23/25 by linarith)
  dsimp [halfQuadratic]
  nlinarith only [hp]

/-- The only coefficient reserve in the south-angle elimination. -/
lemma half_coefficient_upper {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    2*halfQuadratic d+halfLinear d ≤ 3/40 := by
  have ht := half_trig_bounds hd
  have hc1 := Real.cos_le_one (d/2)
  have hfactor := mul_nonneg
    (show 0 ≤ 1-Real.cos (d/2) by linarith)
    (show 0 ≤ (25/48)*(1+Real.cos (d/2))-1 by linarith [ht.1])
  have hcos : 1-(25/48)*Real.sin (d/2)^2 ≤ Real.cos (d/2) := by
    nlinarith only [hfactor,Real.sin_sq_add_cos_sq (d/2)]
  have hB := mul_nonneg (show 0 ≤ southB-153/250 by norm_num [southB])
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
      (2*southB*Real.cos (d/2)*Real.sin x+Real.cos (d/2)*Real.cos x-
        2*halfQuadratic d*Real.sin x*Real.cos x) x := by
    convert ((((Real.hasDerivAt_cos x).const_mul (-2*southB*Real.cos (d/2))).add
      ((Real.hasDerivAt_sin x).const_mul (Real.cos (d/2)))).sub
      (((Real.hasDerivAt_sin x).pow 2).const_mul (halfQuadratic d))) using 1 <;>
      (try funext y) <;> dsimp [negativeExpression] <;> ring
  apply Seven.monoOn_of_hasDeriv_nonneg (fun y _ => (hf y).continuousAt.continuousWithinAt)
    (fun x _ => hf x)
  intro x hx
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le
    (by linarith [hx.2,Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hx.1,Real.pi_pos],hx.2.le⟩
  have hprod : Real.cos (d/2)*Real.cos x ≤ 1 := by
    have h := mul_le_mul hc1 (Real.cos_le_one x) hc (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using h
  have hcoef : 0 ≤ 2*southB-(24/25)*Real.cos (d/2)*Real.cos x := by
    norm_num [southB] at *
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

/-- A single bound handles both signs of the actual cardinal-S angle. -/
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

end SquaresInCircles.Six.Analytic.OwnWestCardinalSouth
