import SquaresInCircles.Six.Analytic.FrozenTrigStress
import SquaresInCircles.Seven.Analysis
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Concavity with a compensated negative mixed sine term

The low-D secondary stresses have a negative sin(v+d) coefficient. Central
edge terms dominate its second derivative throughout the original rectangle
0<=v<=2/3, 0<=d<=1/2. The rational conditions cover both secondary sources;
only the four original corners remain. No support switch is differentiated.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

lemma trig_sum_concave_of_nonnegative {C A B G H c l u : ℝ}
    (h : ∀ x∈Set.Icc l u,
      0≤A*Real.cos x+B*Real.sin x+G*Real.cos (x+c)+H*Real.sin (x+c)) :
    ConcaveOn ℝ (Set.Icc l u)
      (fun x => C+A*Real.cos x+B*Real.sin x+G*Real.cos (x+c)+H*Real.sin (x+c)) := by
  let f : ℝ→ℝ := fun x => C+A*Real.cos x+B*Real.sin x+G*Real.cos (x+c)+H*Real.sin (x+c)
  let f' : ℝ→ℝ := fun x => -A*Real.sin x+B*Real.cos x-G*Real.sin (x+c)+H*Real.cos (x+c)
  let f'' : ℝ→ℝ := fun x => -A*Real.cos x-B*Real.sin x-G*Real.cos (x+c)-H*Real.sin (x+c)
  have hd (x : ℝ) : HasDerivAt f (f' x) x := by
    convert ((((Real.hasDerivAt_cos x).const_mul A).const_add C).add
      ((Real.hasDerivAt_sin x).const_mul B)).add
      ((((Real.hasDerivAt_cos (x+c)).comp x ((hasDerivAt_id x).add_const c)).const_mul G).add
        (((Real.hasDerivAt_sin (x+c)).comp x ((hasDerivAt_id x).add_const c)).const_mul H))
      using 1 <;> dsimp [f,f'] <;> ring
  have hdd (x : ℝ) : HasDerivAt f' (f'' x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (-A)).add
      ((Real.hasDerivAt_cos x).const_mul B)).add
      ((((Real.hasDerivAt_sin (x+c)).comp x ((hasDerivAt_id x).add_const c)).const_mul (-G)).add
        (((Real.hasDerivAt_cos (x+c)).comp x ((hasDerivAt_id x).add_const c)).const_mul H))
      using 1 <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
    (f' := f') (f'' := f'') (by dsimp [f]; fun_prop)
  · intro x _; exact (hd x).hasDerivWithinAt
  · intro x _; exact (hdd x).hasDerivWithinAt
  · intro x hx
    have hh := h x (interior_subset hx)
    dsimp [f'']
    linarith

private lemma low_diagonal_trig {v d : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) :
    (0≤Real.cos v ∧ 0≤Real.sin v ∧ Real.sin v≤5/8) ∧
    (7/8≤Real.cos d ∧ 0≤Real.sin d ∧ Real.sin d≤1/2) ∧
    (0≤Real.cos (v+d) ∧ 0≤Real.sin (v+d)) := by
  have hcv := Real.cos_nonneg_of_mem_Icc
    (show v∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hsv := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hsinv := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤v by linarith [hv.1,Real.pi_pos])
    (show (2:ℝ)/3≤Real.pi/2 by linarith [Real.pi_gt_d2]) hv.2
  have hpoly := Seven.sin_upper_five (x := (2:ℝ)/3) (by norm_num)
  have hsquares := mul_nonneg (sub_nonneg.mpr hd.2)
    (show 0≤1/2+d by linarith [hd.1])
  have hcosd := Real.one_sub_sq_div_two_le_cos (x := d)
  have hsind := Real.sin_nonneg_of_nonneg_of_le_pi hd.1
    (by linarith [hd.2,Real.pi_gt_d2])
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show v+d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2])
  have hsd := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤v+d by linarith [hv.1,hd.1])
    (by linarith [hv.2,hd.2,Real.pi_gt_d2])
  exact ⟨⟨hcv,hsv,by norm_num at hpoly; linarith⟩,
    ⟨by nlinarith,hsind,(Real.sin_le hd.1).trans hd.2⟩,⟨hcd,hsd⟩⟩

private lemma compensated_v_curvature {A B G H v d : ℝ}
    (hA : 2849/20000≤A) (hB : 37/200≤B) (hG : 0≤G) (hH : -(613/4000)≤H)
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) :
    0≤A*Real.cos v+B*Real.sin v+G*Real.cos (v+d)+H*Real.sin (v+d) := by
  obtain ⟨⟨hcv,hsv,_⟩,⟨hcd,hsd,hsdu⟩,⟨hcq,hsq⟩⟩ := low_diagonal_trig hv hd
  have h1 := mul_nonneg (sub_nonneg.mpr hA) hcv
  have h2 := mul_nonneg (sub_nonneg.mpr hB) hsv
  have h3 := mul_nonneg hG hcq
  have h4 := mul_nonneg (show 0≤H+613/4000 by linarith) hsq
  have h5 := mul_nonneg hsv (sub_nonneg.mpr (Real.cos_le_one d))
  have h6 := mul_nonneg hcv (sub_nonneg.mpr hsdu)
  have hq : Real.sin (v+d)≤Real.sin v+(1/2)*Real.cos v := by
    rw [Real.sin_add]
    nlinarith only [h5,h6]
  nlinarith only [h1,h2,h3,h4,hq,hcv,hsv]

private lemma compensated_d_curvature {A B G H v d : ℝ}
    (hA : 2387/20000≤A) (hB : 2387/20000≤B) (hG : 0≤G) (hH : -(613/4000)≤H)
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) :
    0≤A*Real.cos d+B*Real.sin d+G*Real.cos (v+d)+H*Real.sin (v+d) := by
  obtain ⟨⟨_,_,hsvu⟩,⟨hcd,hsd,hsdu⟩,⟨hcq,hsq⟩⟩ := low_diagonal_trig hv hd
  have hcd0 : 0≤Real.cos d := by linarith
  have h1 := mul_nonneg (sub_nonneg.mpr hA) hcd0
  have h2 := mul_nonneg (sub_nonneg.mpr hB) hsd
  have h3 := mul_nonneg hG hcq
  have h4 := mul_nonneg (show 0≤H+613/4000 by linarith) hsq
  have h5 := mul_nonneg (sub_nonneg.mpr hsvu) hcd0
  have h6 := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one v)) hsd
  have hq : Real.sin (v+d)≤(5/8)*Real.cos d+Real.sin d := by
    rw [Real.sin_add]
    nlinarith only [h5,h6]
  nlinarith only [h1,h2,h3,h4,hq,hcd,hsdu]

/-- One compensation estimate covers both low-diagonal secondary stresses. -/
theorem compensated_frozen_positive {C Av Bv Ad Bd Aq Bq v d : ℝ}
    (hAv : 2849/20000≤Av) (hBv : 37/200≤Bv)
    (hAd : 2387/20000≤Ad) (hBd : 2387/20000≤Bd)
    (hAq : 0≤Aq) (hBq : -(613/4000)≤Bq)
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (h00 : 0<frozenTrig C Av Bv Ad Bd Aq Bq 0 0)
    (h0D : 0<frozenTrig C Av Bv Ad Bd Aq Bq 0 (1/2))
    (hV0 : 0<frozenTrig C Av Bv Ad Bd Aq Bq (2/3) 0)
    (hVD : 0<frozenTrig C Av Bv Ad Bd Aq Bq (2/3) (1/2)) :
    0<frozenTrig C Av Bv Ad Bd Aq Bq v d := by
  have hfirst (y : ℝ) (hy : y∈Set.Icc 0 (1/2)) :
      ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun x => frozenTrig C Av Bv Ad Bd Aq Bq x y) := by
    have h := trig_sum_concave_of_nonnegative
      (C := C+Ad*Real.cos y+Bd*Real.sin y) (c := y)
      (fun x hx => compensated_v_curvature hAv hBv hAq hBq hx hy)
    apply h.congr
    intro x _
    dsimp [frozenTrig]
    ring
  have hsecond (x : ℝ) (hx : x∈Set.Icc 0 (2/3)) :
      ConcaveOn ℝ (Set.Icc 0 (1/2)) (frozenTrig C Av Bv Ad Bd Aq Bq x) := by
    have h := trig_sum_concave_of_nonnegative
      (C := C+Av*Real.cos x+Bv*Real.sin x) (c := x)
      (fun y hy => by simpa only [add_comm] using
        compensated_d_curvature hAd hBd hAq hBq hx hy)
    apply h.congr
    intro y _
    dsimp [frozenTrig]
    ring
  exact positive_on_separately_concave_rectangle hv hd hfirst
    (hsecond 0 (by constructor <;> norm_num))
    (hsecond (2/3) (by constructor <;> norm_num)) h00 h0D hV0 hVD

end SquaresInCircles.Six.Analytic
