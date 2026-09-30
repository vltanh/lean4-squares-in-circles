module
public import SquaresInCircles.Six.Analytic.MixedCardinalWest.Concavity

@[expose] public section

/-!
# The twelve endpoints forced by coordinate concavity

The west endpoints are {-2/5,0}, the south endpoints are {-2/5,0,2/5},
and the diagonal endpoints are {1/2,pi/4}. The middle south endpoint is forced
by the absolute-value wall s=0; these points are not a subdivision mesh.

All bounds below follow from displayed low-degree Taylor inequalities and
squaring rational radical bounds. The least resulting rational reserve is
8839/250000>0. There is no interval evaluator, searched cover, or external
success premise. Together with Concavity.lean this proves positivity on the
entire cardinal mixed-west box. Compilation remains deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.MixedCardinalWest
open Normalization

private lemma sqrt_upper {x U : ℝ} (hU : 0 ≤ U) (hx : x ≤ U^2) :
    Real.sqrt x ≤ U := by
  by_cases hx0 : 0 ≤ x
  · have hs := Real.sq_sqrt hx0
    have hn := Real.sqrt_nonneg x
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h) (show 0 < Real.sqrt x+U by linarith)
    nlinarith
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx0)]
    exact hU

private lemma c4 : (921:ℝ)/1000 ≤ Real.cos (2/5) := by
  nlinarith only [Seven.cos_lower_six (x := (2:ℝ)/5) (by norm_num)]
private lemma s4l : (389:ℝ)/1000 ≤ Real.sin (2/5) := by
  nlinarith only [Seven.sin_lower_seven (x := (2:ℝ)/5) (by norm_num)]
private lemma s4u : Real.sin ((2:ℝ)/5) ≤ 39/100 := by
  nlinarith only [Seven.sin_upper_five (x := (2:ℝ)/5) (by norm_num)]
private lemma c5 : (877:ℝ)/1000 ≤ Real.cos (1/2) := by
  nlinarith only [Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)]
private lemma s5l : (479:ℝ)/1000 ≤ Real.sin (1/2) := by
  nlinarith only [Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)]
private lemma s5u : Real.sin ((1:ℝ)/2) ≤ 12/25 := by
  nlinarith only [Seven.sin_upper_five (x := (1:ℝ)/2) (by norm_num)]
private lemma c9 : (621:ℝ)/1000 ≤ Real.cos (9/10) := by
  nlinarith only [Seven.cos_lower_six (x := (9:ℝ)/10) (by norm_num)]
private lemma s9l : (783:ℝ)/1000 ≤ Real.sin (9/10) := by
  nlinarith only [Seven.sin_lower_seven (x := (9:ℝ)/10) (by norm_num)]
private lemma c1 : (199:ℝ)/200 ≤ Real.cos (1/10) := by
  nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/10)]
private lemma s1l : (99:ℝ)/1000 ≤ Real.sin (1/10) := by
  nlinarith only [Seven.sin_lower_seven (x := (1:ℝ)/10) (by norm_num)]

private lemma half_root_bounds : (707:ℝ)/1000 ≤ Real.sqrt 2/2 ∧
    Real.sqrt 2/2 ≤ 177/250 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  constructor <;> nlinarith

private lemma quarter_shift_bounds :
    (375417:ℝ)/1000000 ≤ Real.cos (Real.pi/4+2/5) ∧
    (92617:ℝ)/100000 ≤ Real.sin (Real.pi/4+2/5) ∧
    (92617:ℝ)/100000 ≤ Real.cos (Real.pi/4-2/5) ∧
    (375417:ℝ)/1000000 ≤ Real.sin (Real.pi/4-2/5) ∧
    (651147:ℝ)/500000 ≤ Real.cos (Real.pi/4+2/5)+Real.sin (Real.pi/4+2/5) := by
  have hm := mul_le_mul half_root_bounds.1
    (show (531:ℝ)/1000 ≤ Real.cos (2/5)-Real.sin (2/5) by linarith [c4,s4u])
    (by norm_num : (0:ℝ) ≤ 531/1000) (by positivity : 0 ≤ Real.sqrt 2/2)
  have hp := mul_le_mul half_root_bounds.1
    (show (131:ℝ)/100 ≤ Real.cos (2/5)+Real.sin (2/5) by linarith [c4,s4l])
    (by norm_num : (0:ℝ) ≤ 131/100) (by positivity : 0 ≤ Real.sqrt 2/2)
  have hc := mul_le_mul half_root_bounds.1 c4
    (by norm_num : (0:ℝ) ≤ 921/1000) (by positivity : 0 ≤ Real.sqrt 2/2)
  rw [Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,
    Real.cos_pi_div_four,Real.sin_pi_div_four]
  constructor
  · nlinarith only [hm]
  constructor
  · nlinarith only [hp]
  constructor
  · nlinarith only [hp]
  constructor
  · nlinarith only [hm]
  · nlinarith only [hc]

/-- Each comparison here is a single squared rational inequality. -/
private lemma endpoint_root_bounds :
    Real.sqrt (13+12*Real.sin (1/2)) ≤ 1083/250 ∧
    Real.sqrt (13+12*Real.sin (Real.pi/4)) ≤ 4637/1000 ∧
    Real.sqrt (18-18*Real.sin (9/10)) ≤ 1977/1000 ∧
    Real.sqrt (18-18*Real.sin (1/2)) ≤ 3063/1000 ∧
    Real.sqrt (18-18*Real.sin (1/10)) ≤ 1007/250 ∧
    Real.sqrt (18-18*Real.sin (Real.pi/4+2/5)) ≤ 1153/1000 ∧
    Real.sqrt (18-18*Real.sin (Real.pi/4)) ≤ 2297/1000 ∧
    Real.sqrt (18-18*Real.sin (Real.pi/4-2/5)) ≤ 3353/1000 ∧
    Real.sqrt (25-24*Real.sin (-(2/5))) ≤ 2931/500 ∧
    Real.sqrt (25-24*Real.sin (2/5)) ≤ 1979/500 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply sqrt_upper (by norm_num)
    nlinarith only [s5u]
  · apply sqrt_upper (by norm_num)
    rw [Real.sin_pi_div_four]
    nlinarith only [half_root_bounds.2]
  · apply sqrt_upper (by norm_num)
    nlinarith only [s9l]
  · apply sqrt_upper (by norm_num)
    nlinarith only [s5l]
  · apply sqrt_upper (by norm_num)
    nlinarith only [s1l]
  · apply sqrt_upper (by norm_num)
    nlinarith only [quarter_shift_bounds.2.1]
  · apply sqrt_upper (by norm_num)
    rw [Real.sin_pi_div_four]
    nlinarith only [half_root_bounds.1]
  · apply sqrt_upper (by norm_num)
    nlinarith only [quarter_shift_bounds.2.2.2.1]
  · apply sqrt_upper (by norm_num)
    rw [Real.sin_neg]
    nlinarith only [s4u]
  · apply sqrt_upper (by norm_num)
    nlinarith only [s4l]

def westEnd : Fin 2 → ℝ := ![-2/5,0]
def southEnd : Fin 3 → ℝ := ![-2/5,0,2/5]
def diagonalEnd : Fin 2 → ℝ := ![1/2,Real.pi/4]

private def westCosLower : Fin 2 → ℝ := ![921/1000,1]
private def southCosLower : Fin 3 → ℝ := ![921/1000,1,921/1000]
private def southNegativeLower : Fin 3 → ℝ := ![389/1000,0,0]
private def westSumLower : Fin 2 → Fin 2 → ℝ :=
  ![![351/250,651147/500000],![339/250,707/500]]
private def diagonalCosLower : Fin 3 → Fin 2 → ℝ :=
  ![![621/1000,375417/1000000],![877/1000,707/1000],![199/200,92617/100000]]
private def westRootUpper : Fin 2 → ℝ := ![1083/250,4637/1000]
private def diagonalRootUpper : Fin 3 → Fin 2 → ℝ :=
  ![![1977/1000,1153/1000],![3063/1000,2297/1000],![1007/250,3353/1000]]
private def southRootUpper : Fin 3 → ℝ := ![2931/500,5,1979/500]

private lemma endpoint_trig (i : Fin 2) (j : Fin 3) (k : Fin 2) :
    westCosLower i ≤ Real.cos (westEnd i) ∧
    southCosLower j ≤ Real.cos (southEnd j) ∧
    southNegativeLower j ≤ max (-Real.sin (southEnd j)) 0 ∧
    westSumLower i k ≤ Real.cos (diagonalEnd k-westEnd i)+Real.sin (diagonalEnd k-westEnd i) ∧
    diagonalCosLower j k ≤ Real.cos (diagonalEnd k-southEnd j) := by
  have hc4 := c4
  have hs4 := s4l
  have hc5 := c5
  have hs5 := s5l
  have hc9 := c9
  have hs9 := s9l
  have hc1 := c1
  have hquarter := half_root_bounds.1
  obtain ⟨hqcm,hqsp,hqcp,hqsm,hqsum⟩ := quarter_shift_bounds
  refine ⟨?_,?_,?_,?_,?_⟩
  · fin_cases i <;> norm_num [westCosLower,westEnd] <;> linarith
  · fin_cases j <;> norm_num [southCosLower,southEnd] <;> linarith
  · fin_cases j
    · simpa [southNegativeLower,southEnd] using hs4.trans (le_max_left (Real.sin (2/5)) 0)
    · simp [southNegativeLower,southEnd]
    · simpa [southNegativeLower,southEnd] using le_max_right (-Real.sin ((2:ℝ)/5)) 0
  · fin_cases i <;> fin_cases k <;>
      norm_num [westSumLower,diagonalEnd,westEnd] at * <;> linarith
  · fin_cases j <;> fin_cases k <;>
      norm_num [diagonalCosLower,diagonalEnd,southEnd] at * <;> linarith

private lemma endpoint_roots (j : Fin 3) (k : Fin 2) :
    Real.sqrt (13+12*Real.sin (diagonalEnd k)) ≤ westRootUpper k ∧
    Real.sqrt (18-18*Real.sin (diagonalEnd k-southEnd j)) ≤ diagonalRootUpper j k ∧
    Real.sqrt (25-24*Real.sin (southEnd j)) ≤ southRootUpper j := by
  obtain ⟨hw0,hw1,hd0,hd1,hd2,hd3,hd4,hd5,hs0,hs2⟩ := endpoint_root_bounds
  refine ⟨?_,?_,?_⟩
  · fin_cases k <;> norm_num [diagonalEnd,westRootUpper] at * <;> linarith
  · fin_cases j <;> fin_cases k <;>
      norm_num [diagonalEnd,southEnd,diagonalRootUpper] at * <;> linarith
  · fin_cases j <;> norm_num [southEnd,southRootUpper] at * <;> linarith

private def rationalReserve (i : Fin 2) (j : Fin 3) (k : Fin 2) : ℝ :=
  9-6*(113/1000)+2*westCosLower i+4*southCosLower j+4*southNegativeLower j+
    3*westSumLower i k+3*diagonalCosLower j k-
    (1689/1000)*(westRootUpper k+diagonalRootUpper j k+southRootUpper j)

/-- Only twelve endpoint fractions, forced by the two intervals and s=0.
The weakest displayed lower bound is 8839/250000, not a sampled minimum. -/
private lemma rationalReserve_positive (i : Fin 2) (j : Fin 3) (k : Fin 2) :
    (8839:ℝ)/250000 ≤ rationalReserve i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [rationalReserve,westCosLower,southCosLower,southNegativeLower,
      westSumLower,diagonalCosLower,westRootUpper,diagonalRootUpper,southRootUpper]

lemma endpoint_positive (i : Fin 2) (j : Fin 3) (k : Fin 2) :
    0 < gap (westEnd i) (southEnd j) (diagonalEnd k) := by
  obtain ⟨hw,hs,hn,hq,hx⟩ := endpoint_trig i j k
  obtain ⟨hrW,hrD,hrS⟩ := endpoint_roots j k
  have hroots : Real.sqrt (13+12*Real.sin (diagonalEnd k))+
      Real.sqrt (18-18*Real.sin (diagonalEnd k-southEnd j))+
      Real.sqrt (25-24*Real.sin (southEnd j)) ≤
      westRootUpper k+diagonalRootUpper j k+southRootUpper j := by linarith
  have hprod := mul_le_mul R0_lt_1689_1000.le hroots
    (show 0 ≤ Real.sqrt (13+12*Real.sin (diagonalEnd k))+
      Real.sqrt (18-18*Real.sin (diagonalEnd k-southEnd j))+
      Real.sqrt (25-24*Real.sin (southEnd j)) by positivity)
    (by norm_num : (0:ℝ) ≤ 1689/1000)
  have hc : c0 ≤ 113/1000 := by dsimp [c0]; linarith [rho0_upper]
  have hres := rationalReserve_positive i j k
  dsimp [gap,southTerm,diagonalTerm,westTerm,rationalReserve] at *
  nlinarith

/-- The full compact domain is covered by coordinate concavity, not by
checking boxes. The sole split s<=0 or s>=0 is its absolute-value wall. -/
theorem positive {w s d : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 0)
    (hs : -(2/5) ≤ s ∧ s ≤ 2/5)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) : 0 < gap w s d := by
  have hdi (k : Fin 2) : 1/2 ≤ diagonalEnd k ∧ diagonalEnd k ≤ Real.pi/4 := by
    fin_cases k <;> norm_num [diagonalEnd] <;> linarith [Real.pi_gt_d2]
  have hwend (i : Fin 2) (j : Fin 3) : 0 < gap (westEnd i) (southEnd j) d := by
    have hw' : -(2/5) ≤ westEnd i ∧ westEnd i ≤ 0 := by
      fin_cases i <;> norm_num [westEnd]
    have hs' : -(2/5) ≤ southEnd j ∧ southEnd j ≤ 2/5 := by
      fin_cases j <;> norm_num [southEnd]
    exact positive_on_concave_interval (gap_diagonal_concave hw' hs') hd
      (endpoint_positive i j 0) (endpoint_positive i j 1)
  have hsend (j : Fin 3) : 0 < gap w (southEnd j) d :=
    positive_on_concave_interval (gap_west_concave hd) hw (hwend 0 j) (hwend 1 j)
  by_cases hs0 : s ≤ 0
  · exact positive_on_concave_interval
      (gap_south_concave hd le_rfl (by norm_num) southTerm_negative_concave)
      ⟨hs.1,hs0⟩ (hsend 0) (hsend 1)
  · exact positive_on_concave_interval
      (gap_south_concave hd (by norm_num) le_rfl southTerm_positive_concave)
      ⟨le_of_not_ge hs0,hs.2⟩ (hsend 1) (hsend 2)

end SquaresInCircles.Six.Analytic.MixedCardinalWest
