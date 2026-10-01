import SquaresInCircles.Six.Analytic.HighDiagonalProfile
import SquaresInCircles.Six.Analytic.FrozenTrigStress

/-!
# Coupled central profiles when the OWN S angle overtakes D

The two OWN inequalities cancel cx after multiplication by sin(s), cos(d).
Using cy<=c0 and aS<=rho0 gives a lower bound on aD+aS. The required scalar
reserve is proved on the whole geometric triangle 1/2<=d<=s<=2/3:
  aD+aS > 217/100 + (s-d)/3.
Concavity in d sends the point to d=1/2 or d=s. Each resulting boundary is
concave in s. Only the three original vertices are evaluated by rational
Taylor inequalities; there is no subdivision or numerical certificate.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def coupledOwnReserve (d s : ℝ) : ℝ :=
  (387/1000)*Real.cos (s-d)+Real.sin s*Real.cos d-
    (613/1000)*Real.cos d-(557/1000+(s-d)/3)*Real.sin s

private def coupledA (s : ℝ) : ℝ := (387/1000)*Real.cos s+Real.sin s-613/1000
private def coupledB (s : ℝ) : ℝ := (387/1000)*Real.sin s

private lemma coupled_formula (d s : ℝ) :
    coupledOwnReserve d s=coupledA s*Real.cos d+coupledB s*Real.sin d+
      (Real.sin s/3)*d-(557/1000+s/3)*Real.sin s := by
  dsimp [coupledOwnReserve,coupledA,coupledB]
  rw [Real.cos_sub]
  ring

private lemma coupled_trig {x : ℝ} (hx : 1/2≤x ∧ x≤2/3) :
    7/9≤Real.cos x ∧ 4794/10000≤Real.sin x := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hx2 := mul_nonneg (sub_nonneg.mpr hx.2) (show 0≤2/3+x by linarith [hx.1])
  have hc : 7/9≤Real.cos x := by nlinarith only [hcos,hx2]
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤(1:ℝ)/2 by linarith [Real.pi_pos])
    (show x≤Real.pi/2 by linarith [hx.2,Real.pi_gt_d2]) hx.1
  exact ⟨hc,low_half_bracket.2.2.1.trans hm⟩

private lemma affine_interval_concave (a b l u : ℝ) :
    ConcaveOn ℝ (Set.Icc l u) (fun x : ℝ => a*x+b) := by
  refine ⟨convex_Icc l u,?_⟩
  intro x hx y hy p q hp hq hpq
  simp only [smul_eq_mul]
  have he : p*(a*x+b)+q*(a*y+b)-(a*(p*x+q*y)+b)=b*(p+q-1) := by ring
  rw [hpq] at he
  nlinarith only [he]

private lemma coupled_concave_d {s : ℝ} (hs : 1/2≤ s ∧ s≤2/3) :
    ConcaveOn ℝ (Set.Icc (1/2) s) (fun d => coupledOwnReserve d s) := by
  have ht := coupled_trig hs
  have hA : 0≤coupledA s := by dsimp [coupledA]; linarith [ht.1,ht.2]
  have hB : 0≤coupledB s := by dsimp [coupledB]; linarith [ht.2]
  have htrig := positive_trig_affine_concave (A := coupledA s) (B := coupledB s)
    (l := (1:ℝ)/2) (u := s) (a := 1) (b := 0) hA hB
    (by intro x hx; constructor <;> linarith [hx.1,hx.2,hs.2,Real.pi_gt_d2])
  have hlinear := affine_interval_concave (Real.sin s/3)
    (-(557/1000+s/3)*Real.sin s) (1/2) s
  apply (htrig.add hlinear).congr
  intro d _
  simp only [Pi.add_apply,one_mul,add_zero]
  rw [coupled_formula]
  ring

private def coupledLeft (s : ℝ) : ℝ :=
  ((387/1000)*Real.cos (1/2))*Real.cos s+
    ((387/1000)*Real.sin (1/2)+Real.cos (1/2)-557/1000)*Real.sin s-
    (613/1000)*Real.cos (1/2)-((s-1/2)/3)*Real.sin s

private lemma coupled_left_formula (s : ℝ) : coupledOwnReserve (1/2) s=coupledLeft s := by
  dsimp [coupledOwnReserve,coupledLeft]
  rw [Real.cos_sub]
  ring

private lemma coupled_left_concave : ConcaveOn ℝ (Set.Icc (1/2) (2/3)) coupledLeft := by
  let A := (387/1000)*Real.cos (1/2)
  let B := (387/1000)*Real.sin (1/2)+Real.cos (1/2)-557/1000
  let f' : ℝ→ℝ := fun s => -A*Real.sin s+B*Real.cos s-
    Real.sin s/3-((s-1/2)/3)*Real.cos s
  let f'' : ℝ→ℝ := fun s => -A*Real.cos s-B*Real.sin s-
    (2/3)*Real.cos s+((s-1/2)/3)*Real.sin s
  have hA : 0≤A := by dsimp [A]; linarith [low_half_bracket.1]
  have hB : 0≤B := by dsimp [B]; linarith [low_half_bracket.1,low_half_bracket.2.2.1]
  have hu (s : ℝ) : HasDerivAt (fun x : ℝ => (x-1/2)/3) (1/3) s :=
    ((hasDerivAt_id' s).sub_const (1/2)).div_const 3
  have hf (s : ℝ) : HasDerivAt coupledLeft (f' s) s := by
    have h := ((((Real.hasDerivAt_cos s).const_mul A).fun_add
      ((Real.hasDerivAt_sin s).const_mul B)).sub_const
      ((613/1000)*Real.cos (1/2))).fun_sub ((hu s).fun_mul (Real.hasDerivAt_sin s))
    refine h.congr_deriv ?_
    simp only [f']
    ring
  have hff (s : ℝ) : HasDerivAt f' (f'' s) s := by
    have h := ((((Real.hasDerivAt_sin s).const_mul (-A)).fun_add
      ((Real.hasDerivAt_cos s).const_mul B)).fun_sub
      ((Real.hasDerivAt_sin s).div_const 3)).fun_sub ((hu s).fun_mul (Real.hasDerivAt_cos s))
    refine h.congr_deriv ?_
    simp only [f'']
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) (2/3))
    (f' := f') (f'' := f'') (fun x _ => (hf x).continuousAt.continuousWithinAt)
  · intro s _; exact (hf s).hasDerivWithinAt
  · intro s _; exact (hff s).hasDerivWithinAt
  · intro s hs
    have hsc : s∈Set.Icc (1/2) (2/3) := interior_subset hs
    have ht := coupled_trig hsc
    have hAc := mul_nonneg hA (show 0≤Real.cos s by linarith [ht.1])
    have hBs := mul_nonneg hB (show 0≤Real.sin s by linarith [ht.2])
    have hupper := mul_le_mul (show (s-1/2)/3≤(1:ℝ)/18 by linarith [hsc.2])
      (Real.sin_le_one s) (show 0≤Real.sin s by linarith [ht.2]) (by norm_num : (0:ℝ)≤1/18)
    dsimp [f'']
    nlinarith only [hAc,hBs,hupper,ht.1]

private def coupledDiagonal (s : ℝ) : ℝ :=
  387/1000+Real.sin (2*s)/2-(613/1000)*Real.cos s-(557/1000)*Real.sin s

private lemma coupled_diagonal_formula (s : ℝ) : coupledOwnReserve s s=coupledDiagonal s := by
  simp only [coupledOwnReserve,coupledDiagonal,sub_self,Real.cos_zero,Real.sin_two_mul]
  ring

private lemma coupled_diagonal_concave :
    ConcaveOn ℝ (Set.Icc (1/2) (2/3)) coupledDiagonal := by
  let f' : ℝ→ℝ := fun s => Real.cos (2*s)+(613/1000)*Real.sin s-(557/1000)*Real.cos s
  let f'' : ℝ→ℝ := fun s => -2*Real.sin (2*s)+(613/1000)*Real.cos s+(557/1000)*Real.sin s
  have hu (s : ℝ) : HasDerivAt (fun x : ℝ => 2*x) 2 s := by
    simpa using (hasDerivAt_id s).const_mul 2
  have hf (s : ℝ) : HasDerivAt coupledDiagonal (f' s) s := by
    have h := (((((hu s).sin).div_const 2).const_add (387/1000)).fun_sub
      ((Real.hasDerivAt_cos s).const_mul (613/1000))).fun_sub
      ((Real.hasDerivAt_sin s).const_mul (557/1000))
    refine h.congr_deriv ?_
    simp only [f']
    ring
  have hff (s : ℝ) : HasDerivAt f' (f'' s) s := by
    have h := (((hu s).cos).fun_add ((Real.hasDerivAt_sin s).const_mul (613/1000))).fun_sub
      ((Real.hasDerivAt_cos s).const_mul (557/1000))
    refine h.congr_deriv ?_
    simp only [f'']
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) (2/3))
    (f' := f') (f'' := f'') (fun x _ => (hf x).continuousAt.continuousWithinAt)
  · intro s _; exact (hf s).hasDerivWithinAt
  · intro s _; exact (hff s).hasDerivWithinAt
  · intro s hs
    have hsc : s∈Set.Icc (1/2) (2/3) := interior_subset hs
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2)≤(1:ℝ) by linarith [Real.pi_pos])
      (show 2*s≤Real.pi/2 by linarith [hsc.2,Real.pi_gt_d2])
      (show 1≤2*s by linarith [hsc.1])
    have hp := Real.sin_ge_sub_cube (x := (1:ℝ)) (by norm_num)
    norm_num at hp
    dsimp [f'']
    linarith [Real.cos_le_one s,Real.sin_le_one s]

private lemma coupled_vertices :
    0<coupledOwnReserve (1/2) (1/2) ∧
    0<coupledOwnReserve (1/2) (2/3) ∧
    0<coupledOwnReserve (2/3) (2/3) := by
  obtain ⟨hc5l,hc5u,hs5l,hs5u⟩ := low_half_bracket
  obtain ⟨hc6l,hc6u,hs6l,hs6u⟩ := two_thirds_endpoint_bracket
  have hprod5 := mul_le_mul hs5l hc5l (by norm_num : (0:ℝ)≤8775/10000)
    (show 0≤Real.sin (1/2) by linarith)
  have hprod6 := mul_le_mul hs6l hc6l (by norm_num : (0:ℝ)≤157/200)
    (show 0≤Real.sin (2/3) by linarith)
  have hprod56 := mul_le_mul hs6l hc5l (by norm_num : (0:ℝ)≤8775/10000)
    (show 0≤Real.sin (2/3) by linarith)
  have hcr := Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/6)
  refine ⟨?_,?_,?_⟩
  · norm_num [coupledOwnReserve]
    linarith
  · norm_num [coupledOwnReserve]
    linarith
  · norm_num [coupledOwnReserve]
    linarith

/-- The whole original triangle reduces to its three original vertices. -/
theorem coupled_own_reserve_positive {d s : ℝ}
    (hd : 1/2≤d) (hds : d≤ s) (hs : s≤2/3) : 0<coupledOwnReserve d s := by
  have hleft : 0<coupledOwnReserve (1/2) s := by
    rw [coupled_left_formula]
    exact positive_on_concave_interval coupled_left_concave ⟨hd.trans hds,hs⟩
      (by rw [← coupled_left_formula]; exact coupled_vertices.1)
      (by rw [← coupled_left_formula]; exact coupled_vertices.2.1)
  have hdiag : 0<coupledOwnReserve s s := by
    rw [coupled_diagonal_formula]
    exact positive_on_concave_interval coupled_diagonal_concave ⟨hd.trans hds,hs⟩
      (by rw [← coupled_diagonal_formula]; exact coupled_vertices.1)
      (by rw [← coupled_diagonal_formula]; exact coupled_vertices.2.2)
  have h := positive_on_concave_interval (coupled_concave_d ⟨hd.trans hds,hs⟩)
    ⟨hd,hds⟩ hleft hdiag
  exact h

end SquaresInCircles.Six.Analytic
