import SquaresInCircles.Six.Analytic.SecondaryCostTangent
import SquaresInCircles.Six.Analytic.LowDiagonalEndpoints

/-!
# The cost of a square under two equal weights

A square with equal weights on its own axis and on the secondary axis of a
square at phase gap `q` has the force `(1 + sin q, cos q)` in its frame. For a
contained square with local centre `(a, b)` and `1/2 ≤ q ≤ π - 1/2`, the cost
`(|cos q| + |sin q|)/2 - (1 + sin q) a - (cos q) b` exceeds
`-91/125 - (13/20) q`. For `q ≤ 1` the far-vertex support applies: with
`√(2 + 2 sin q) = 2 cos (π/4 - q/2)` the bound is concave in `q`, and it holds
at `q = 1/2` and `q = 1`. For `1 ≤ q ≤ π/2` we have `sin q ≥ 5/6`, which puts
the force in the cap case, treated in `SecondaryCostTangent`. Beyond `π/2`
the reflection `q ↦ π - q`, `b ↦ -b` gives the bound at `π - q`, which is
stronger.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def secondaryVertexLine (q : ℝ) : ℝ :=
  91/125+(13/20)*q+1/2+Real.cos q+Real.sin q-
    (1689/1000)*Real.sqrt (2+2*Real.sin q)

private def secondaryVertexSmooth (q : ℝ) : ℝ :=
  91/125+(13/20)*q+1/2+Real.cos q+Real.sin q-
    (1689/500)*Real.cos (Real.pi/4-q/2)

lemma secondary_root_half_angle {q : ℝ} (hq : 1/2≤q ∧ q≤1) :
    Real.sqrt (2+2*Real.sin q)=2*Real.cos (Real.pi/4-q/2) := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show Real.pi/4-q/2∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_gt_d2])
  have hd := Real.cos_two_mul (Real.pi/4-q/2)
  rw [show 2*(Real.pi/4-q/2)=Real.pi/2-q by ring,Real.cos_pi_div_two_sub] at hd
  have he : 2+2*Real.sin q=(2*Real.cos (Real.pi/4-q/2))^2 := by nlinarith
  rw [he,Real.sqrt_sq (by positivity)]

private lemma secondary_vertex_smooth_concave :
    ConcaveOn ℝ (Set.Icc (1/2) 1) secondaryVertexSmooth := by
  let f' : ℝ→ℝ := fun q => 13/20-Real.sin q+Real.cos q-
    (1689/1000)*Real.sin (Real.pi/4-q/2)
  let f'' : ℝ→ℝ := fun q => -Real.cos q-Real.sin q+
    (1689/2000)*Real.cos (Real.pi/4-q/2)
  have hu (q : ℝ) : HasDerivAt (fun x : ℝ => Real.pi/4-x/2) (-1/2) q := by
    convert ((hasDerivAt_id' q).div_const 2).const_sub (Real.pi/4) using 1; ring
  have hf (q : ℝ) : HasDerivAt secondaryVertexSmooth (f' q) q := by
    have h := (((((hasDerivAt_id' q).const_mul (13/20)).const_add (91/125+1/2)).fun_add
      (Real.hasDerivAt_cos q)).fun_add (Real.hasDerivAt_sin q)).fun_sub
      (((Real.hasDerivAt_cos (Real.pi/4-q/2)).comp q (hu q)).const_mul (1689/500))
    convert h using 1
    · funext x; simp only [secondaryVertexSmooth, Function.comp_apply]; ring
    · dsimp [f']; ring
  have hff (q : ℝ) : HasDerivAt f' (f'' q) q := by
    have h := ((((Real.hasDerivAt_sin q).fun_neg).const_add (13/20)).fun_add
      (Real.hasDerivAt_cos q)).fun_sub
      (((Real.hasDerivAt_sin (Real.pi/4-q/2)).comp q (hu q)).const_mul (1689/1000))
    convert h using 1
    · funext x; simp only [f', Function.comp_apply]; ring
    · dsimp [f'']; ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) 1)
    (f' := f') (f'' := f'') (fun q _ => (hf q).continuousAt.continuousWithinAt)
  · intro q _; exact (hf q).hasDerivWithinAt
  · intro q _; exact (hff q).hasDerivWithinAt
  · intro q hq
    have hqc : q∈Set.Icc (1/2) 1 := interior_subset hq
    have hcos := Real.cos_nonneg_of_mem_Icc
      (show q∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [hqc.1,hqc.2,Real.pi_gt_d2])
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi (x := q)
      (by linarith [hqc.1]) (by linarith [hqc.2,Real.pi_gt_d2])
    have hsum := one_le_abs_cos_add_abs_sin q
    rw [abs_of_nonneg hcos,abs_of_nonneg hsin] at hsum
    dsimp [f'']
    linarith [Real.cos_le_one (Real.pi/4-q/2)]

private lemma secondary_vertex_line_half : 0< secondaryVertexLine (1/2) := by
  obtain ⟨hcl,_,hsl,hsu⟩ := low_half_bracket
  have hp : 0≤2+2*Real.sin (1/2) := by linarith
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (2+2*Real.sin (1/2))
  have hroot : Real.sqrt (2+2*Real.sin (1/2))≤8601/5000 := by nlinarith
  dsimp [secondaryVertexLine]
  linarith

private lemma secondary_vertex_line_one : 0< secondaryVertexLine 1 := by
  have hc := Seven.cos_lower_six (x := (1:ℝ)) (by norm_num)
  have hl := Seven.sin_lower_seven (x := (1:ℝ)) (by norm_num)
  have hu := Seven.sin_upper_five (x := (1:ℝ)) (by norm_num)
  norm_num at hc hl hu
  have hp : 0≤2+2*Real.sin 1 := by linarith
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (2+2*Real.sin 1)
  have hroot : Real.sqrt (2+2*Real.sin 1)≤48/25 := by nlinarith
  dsimp [secondaryVertexLine]
  linarith

lemma secondary_vertex_line_positive {q : ℝ} (hq : 1/2≤q ∧ q≤1) :
    0< secondaryVertexLine q := by
  have he (x : ℝ) (hx : 1/2≤x ∧ x≤1) :
      secondaryVertexLine x=secondaryVertexSmooth x := by
    dsimp [secondaryVertexLine,secondaryVertexSmooth]
    rw [secondary_root_half_angle hx]
    ring
  rw [he q hq]
  exact positive_on_concave_interval secondary_vertex_smooth_concave hq
    (by rw [← he (1/2) (by constructor <;> norm_num)]; exact secondary_vertex_line_half)
    (by rw [← he 1 (by constructor <;> norm_num)]; exact secondary_vertex_line_one)

private lemma secondary_cap_slope {q : ℝ} (hq : 1≤q ∧ q≤Real.pi/2) :
    (rho0+1/2)*Real.cos q≤(1+Real.sin q)/2 := by
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤(1:ℝ) by linarith [Real.pi_pos]) hq.2 hq.1
  have hs1 := Real.sin_ge_sub_cube (x := (1:ℝ)) (by norm_num)
  norm_num at hs1
  have hslo : 5/6≤Real.sin q := by linarith
  have hc0 := Real.cos_nonneg_of_mem_Icc
    (show q∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_pos])
  have hsq := mul_nonneg (sub_nonneg.mpr hslo)
    (show 0≤Real.sin q+5/6 by linarith)
  have hchi : Real.cos q≤5/9 := by nlinarith [Real.sin_sq_add_cos_sq q]
  have hm := mul_le_mul (show rho0+1/2≤1613/1000 by linarith [rho0_upper])
    hchi hc0 (by norm_num : (0:ℝ)≤1613/1000)
  nlinarith

lemma secondary_cost_first_quadrant {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1/2≤q ∧ q≤Real.pi/2) :
    -91/125-(13/20)*q<angularWidth q-((1+Real.sin q)*a+Real.cos q*b) := by
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show q∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_pos])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi (x := q)
    (by linarith [hq.1]) (by linarith [hq.2,Real.pi_pos])
  have hc' : ContainedChart a |-b| := by simpa only [abs_neg] using hc
  rw [angularWidth,abs_of_nonneg hcos,abs_of_nonneg hsin]
  by_cases hsmall : q≤1
  · have hp := vertex_linear_upper hc' (U := 1+Real.sin q) (V := Real.cos q)
      (L := Real.sqrt ((1+Real.sin q)^2+Real.cos q^2)) hcos (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt (by positivity)])
    have he : (1+Real.sin q)^2+Real.cos q^2=2+2*Real.sin q := by
      nlinarith [Real.sin_sq_add_cos_sq q]
    rw [he] at hp
    have hpositive := secondary_vertex_line_positive ⟨hq.1,hsmall⟩
    dsimp [secondaryVertexLine] at hpositive
    nlinarith only [hp,hpositive]
  · have hp := cap_linear_upper hc' (U := 1+Real.sin q) (V := Real.cos q)
      (by linarith) hcos (secondary_cap_slope ⟨(lt_of_not_ge hsmall).le,hq.2⟩)
    have hpositive := secondary_cap_line_positive ⟨(lt_of_not_ge hsmall).le,hq.2⟩
    dsimp [secondaryCapLine] at hpositive
    nlinarith only [hp,hpositive]

/-- The affine bound on `[1/2, π - 1/2]`; beyond `π/2` it follows from the
bound at `π - q`. -/
theorem secondary_cost_affine_lower {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1/2≤q ∧ q≤Real.pi-1/2) :
    -91/125-(13/20)*q<angularWidth q-((1+Real.sin q)*a+Real.cos q*b) := by
  by_cases hhalf : q≤Real.pi/2
  · exact secondary_cost_first_quadrant hc ⟨hq.1,hhalf⟩
  · have hc' : ContainedChart a |-b| := by simpa only [abs_neg] using hc
    have hrange : 1/2≤Real.pi-q ∧ Real.pi-q≤Real.pi/2 := by
      constructor <;> linarith [hq.2]
    have hh := secondary_cost_first_quadrant hc' hrange
    simp only [angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at hh ⊢
    nlinarith only [hh,hhalf]

end SquaresInCircles.Six.Analytic
