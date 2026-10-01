import SquaresInCircles.Six.Analytic.HighChordCurvature

/-!
# The transverse term of the reflected case

The term `J(r) = -B cos r + sin r/2 - sin² r/12` of the reflected stress,
written with `cos 2r` so that its derivatives are sinusoids. The third
derivative is nonpositive on `[0, 2/3]`, so `J''` decreases there, and a Taylor
bound at `3/10` gives `J'' ≤ 31/100` on `[3/10, 2/3]`, the range of the argument
`d - s`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.ReflectedOwnWings

def A : ℝ := 19359/50000
def B : ℝ := 30641/50000

def transverse (r : ℝ) : ℝ :=
  -B*Real.cos r+(1/2)*Real.sin r-1/24+(1/24)*Real.cos (2*r)
def transverseFirst (r : ℝ) : ℝ :=
  B*Real.sin r+(1/2)*Real.cos r-(1/12)*Real.sin (2*r)
def transverseSecond (r : ℝ) : ℝ :=
  B*Real.cos r-(1/2)*Real.sin r-(1/6)*Real.cos (2*r)
def transverseThird (r : ℝ) : ℝ :=
  -B*Real.sin r-(1/2)*Real.cos r+(1/3)*Real.sin (2*r)

lemma transverse_identity (r : ℝ) :
    transverse r=-B*Real.cos r+(1/2)*Real.sin r-Real.sin r^2/12 := by
  have h := Real.cos_two_mul r
  dsimp [transverse]
  nlinarith only [h,Real.sin_sq_add_cos_sq r]

lemma transverse_hasDeriv (r : ℝ) : HasDerivAt transverse (transverseFirst r) r := by
  convert ((((Real.hasDerivAt_cos r).const_mul (-B)).add
    ((Real.hasDerivAt_sin r).const_mul (1/2))).sub_const (1/24)).add
    ((((hasDerivAt_id r).const_mul 2).cos).const_mul (1/24)) using 1
  · funext y; simp only [transverse,Pi.add_apply,id_eq]
  · dsimp [transverseFirst]; ring

lemma transverse_first_hasDeriv (r : ℝ) : HasDerivAt transverseFirst (transverseSecond r) r := by
  convert (((Real.hasDerivAt_sin r).const_mul B).add
    ((Real.hasDerivAt_cos r).const_mul (1/2))).sub
    ((((hasDerivAt_id r).const_mul 2).sin).const_mul (1/12)) using 1
  · funext y; simp only [transverseFirst,Pi.add_apply,Pi.sub_apply,id_eq]
  · dsimp [transverseSecond]; ring

lemma transverse_second_hasDeriv (r : ℝ) : HasDerivAt transverseSecond (transverseThird r) r := by
  convert (((Real.hasDerivAt_cos r).const_mul B).sub
    ((Real.hasDerivAt_sin r).const_mul (1/2))).sub
    ((((hasDerivAt_id r).const_mul 2).cos).const_mul (1/6)) using 1
  · funext y; simp only [transverseSecond,Pi.sub_apply,id_eq]
  · dsimp [transverseThird]; ring

lemma transverse_third_nonpositive {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 2/3) :
    transverseThird r ≤ 0 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hr.1
    (by linarith [hr.2,Real.pi_gt_d2])
  have hsu : Real.sin r ≤ 2/3 := (Real.sin_le hr.1).trans hr.2
  have hsq := mul_nonneg (sub_nonneg.mpr hr.2)
    (show 0 ≤ 2/3+r by linarith [hr.1])
  have hc : 7/9 ≤ Real.cos r := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := r)]
  have hp := mul_nonneg hs (show 0 ≤ 1-Real.cos r by linarith [Real.cos_le_one r])
  dsimp [transverseThird,B]
  rw [Real.sin_two_mul]
  nlinarith only [hp,hsu,hc]

lemma transverse_second_upper {r : ℝ} (hr : 3/10 ≤ r ∧ r ≤ 2/3) :
    transverseSecond r ≤ 31/100 := by
  have hm : MonotoneOn (fun x => -transverseSecond x) (Set.Icc 0 (2/3)) := by
    have hd (x : ℝ) : HasDerivAt (fun x => -transverseSecond x) (-transverseThird x) x :=
      (transverse_second_hasDeriv x).neg
    apply Seven.monoOn_of_hasDeriv_nonneg (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => hd x)
    intro x hx
    exact neg_nonneg.mpr (transverse_third_nonpositive ⟨hx.1.le,hx.2.le⟩)
  have h := hm (by norm_num : (3:ℝ)/10 ∈ Set.Icc 0 (2/3))
    (show r ∈ Set.Icc 0 (2/3) by constructor <;> linarith [hr.1,hr.2]) hr.1
  have he : transverseSecond (3/10) ≤ 31/100 := by
    have hc := Seven.cos_upper_four (x := (3:ℝ)/10) (by norm_num)
    have hs := Seven.sin_lower_seven (x := (3:ℝ)/10) (by norm_num)
    have hd := Seven.cos_lower_six (x := (3:ℝ)/5) (by norm_num)
    dsimp [transverseSecond,B]
    norm_num
    nlinarith only [hc,hs,hd]
  linarith

end SquaresInCircles.Six.Analytic.ReflectedOwnWings
