import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Chord

/-!
# The transverse term and the wing harmonic

The angle `r = d - s` between D and S enters the west-dominant profile
through `J(r) = -B cos r + (1/2) sin r - sin² r/12` with `B = 30641/50000`: up
to a constant, the threshold of D–S less the smooth axial bound on the support
of S. Its third derivative is at most `-2/5` on `[0, 4/5]`, by a cubic in
`sin r` with nonnegative Bernstein coefficients, so
`J''(r) ≤ B - 1/6 - (2/5) r` there. The harmonic `A cos s + B sin s`, with
`A = 19359/50000`, is concave on `[0, 12/25]` and above the line
`A + (49/100) s` at both ends, hence on the whole interval; and
`cos d + sin d ≥ 4/3` on `[1/2, 11/14]`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthWestDominant

def wingCos : ℝ := 19359/50000
def wingSin : ℝ := 30641/50000

def transverse (r : ℝ) : ℝ :=
  -wingSin*Real.cos r+(1/2)*Real.sin r-1/24+(1/24)*Real.cos (2*r)
def transverseFirst (r : ℝ) : ℝ :=
  wingSin*Real.sin r+(1/2)*Real.cos r-(1/12)*Real.sin (2*r)
def transverseSecond (r : ℝ) : ℝ :=
  wingSin*Real.cos r-(1/2)*Real.sin r-(1/6)*Real.cos (2*r)
def transverseThird (r : ℝ) : ℝ :=
  -wingSin*Real.sin r-(1/2)*Real.cos r+(1/3)*Real.sin (2*r)

lemma transverse_eq (r : ℝ) :
    transverse r = -wingSin*Real.cos r+(1/2)*Real.sin r-Real.sin r^2/12 := by
  have h := Real.cos_two_mul r
  dsimp [transverse]
  nlinarith only [h,Real.sin_sq_add_cos_sq r]

lemma transverse_hasDeriv (r : ℝ) : HasDerivAt transverse (transverseFirst r) r := by
  exact (((((Real.hasDerivAt_cos r).const_mul (-wingSin)).fun_add
    ((Real.hasDerivAt_sin r).const_mul (1/2))).sub_const (1/24)).fun_add
    ((((hasDerivAt_id' r).const_mul 2).cos).const_mul (1/24))).congr_deriv
    (by simp only [transverseFirst]; ring)

lemma transverse_first_hasDeriv (r : ℝ) :
    HasDerivAt transverseFirst (transverseSecond r) r := by
  exact ((((Real.hasDerivAt_sin r).const_mul wingSin).fun_add
    ((Real.hasDerivAt_cos r).const_mul (1/2))).fun_sub
    ((((hasDerivAt_id' r).const_mul 2).sin).const_mul (1/12))).congr_deriv
    (by simp only [transverseSecond]; ring)

lemma transverse_second_hasDeriv (r : ℝ) :
    HasDerivAt transverseSecond (transverseThird r) r := by
  exact ((((Real.hasDerivAt_cos r).const_mul wingSin).fun_sub
    ((Real.hasDerivAt_sin r).const_mul (1/2))).fun_sub
    ((((hasDerivAt_id' r).const_mul 2).cos).const_mul (1/6))).congr_deriv
    (by simp only [transverseThird]; ring)

private lemma cubic_identity (x : ℝ) :
    1/10-(17/300)*x-(3/10)*x^2+(2/5)*x^3 =
      (1/10)*(1-4*x/3)^3+(103/400)*(4*x/3)*(1-4*x/3)^2+
      (37/800)*(4*x/3)^2*(1-4*x/3)+(23/400)*(4*x/3)^3 := by
  ring

lemma transverse_third_upper {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 4/5) :
    transverseThird r ≤ -(2/5) := by
  have hrr := mul_nonneg (sub_nonneg.mpr hr.2)
    (show 0 ≤ 4/5+r by linarith [hr.1])
  have hc : 17/25 ≤ Real.cos r := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := r)]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hr.1
    (by linarith [hr.2,Real.pi_gt_d2])
  have hcc := mul_nonneg (show 0 ≤ Real.cos r-17/25 by linarith)
    (show 0 ≤ Real.cos r+17/25 by linarith)
  have hsu : Real.sin r ≤ 3/4 := by
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h) (show 0 < Real.sin r+3/4 by linarith)
    nlinarith only [hcc,hp,Real.sin_sq_add_cos_sq r]
  have hfactor := mul_nonneg
    (show 0 ≤ 1-Real.cos r by linarith [Real.cos_le_one r])
    (show 0 ≤ (3/5)*(1+Real.cos r)-1 by linarith)
  have hcos : 1-(3/5)*Real.sin r^2 ≤ Real.cos r := by
    nlinarith only [hfactor,Real.sin_sq_add_cos_sq r]
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ Real.cos r-(1-(3/5)*Real.sin r^2) by linarith)
    (show (2/3)*Real.sin r-1/2 ≤ 0 by linarith)
  have hB := mul_nonneg (show 0 ≤ wingSin-61/100 by norm_num [wingSin]) hs
  have hid := Real.sin_two_mul r
  have hupper : transverseThird r ≤
      -1/2+(17/300)*Real.sin r+(3/10)*Real.sin r^2-(2/5)*Real.sin r^3 := by
    dsimp [transverseThird]
    nlinarith only [hp,hB,hid]
  have hreserve : 0 ≤ 1/10-(17/300)*Real.sin r-(3/10)*Real.sin r^2+
      (2/5)*Real.sin r^3 := by
    rw [cubic_identity]
    have h0 : 0 ≤ 4*Real.sin r/3 := by positivity
    have h1 : 0 ≤ 1-4*Real.sin r/3 := by linarith
    positivity
  linarith

lemma transverse_second_upper {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 4/5) :
    transverseSecond r ≤ wingSin-1/6-(2/5)*r := by
  have hd (x : ℝ) : HasDerivAt (fun x => -(transverseSecond x+(2/5)*x))
      (-(transverseThird x+2/5)) x :=
    (((transverse_second_hasDeriv x).fun_add
      ((hasDerivAt_id' x).const_mul (2/5))).fun_neg).congr_deriv (by ring)
  have hm : MonotoneOn (fun x => -(transverseSecond x+(2/5)*x)) (Set.Icc 0 (4/5)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    intro x hx
    have h := transverse_third_upper ⟨hx.1.le,hx.2.le⟩
    linarith
  have h0 : transverseSecond 0 = wingSin-1/6 := by norm_num [transverseSecond]
  have h := hm (by norm_num : (0:ℝ) ∈ Set.Icc 0 (4/5)) hr hr.1
  dsimp only at h
  linarith

lemma wing_affine_lower {s : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25) :
    wingCos+(49/100)*s ≤ wingCos*Real.cos s+wingSin*Real.sin s := by
  let f : ℝ → ℝ := fun x => wingCos*Real.cos x+wingSin*Real.sin x-wingCos-(49/100)*x
  let f' : ℝ → ℝ := fun x => -wingCos*Real.sin x+wingSin*Real.cos x-49/100
  let f'' : ℝ → ℝ := fun x => -wingCos*Real.cos x-wingSin*Real.sin x
  have hf (x : ℝ) : HasDerivAt f (f' x) x := by
    exact (((((Real.hasDerivAt_cos x).const_mul wingCos).fun_add
      ((Real.hasDerivAt_sin x).const_mul wingSin)).sub_const wingCos).fun_sub
      ((hasDerivAt_id' x).const_mul (49/100))).congr_deriv (by simp only [f']; ring)
  have hff (x : ℝ) : HasDerivAt f' (f'' x) x := by
    exact ((((Real.hasDerivAt_sin x).const_mul (-wingCos)).fun_add
      ((Real.hasDerivAt_cos x).const_mul wingSin)).sub_const (49/100)).congr_deriv
      (by simp only [f'']; ring)
  have hc : ConcaveOn ℝ (Set.Icc 0 (12/25)) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (12/25))
      (f' := f') (f'' := f'') (by dsimp [f]; fun_prop)
    · intro x _; exact (hf x).hasDerivWithinAt
    · intro x _; exact (hff x).hasDerivWithinAt
    · intro x hx
      have h := interior_subset hx
      have hcos := Real.cos_nonneg_of_mem_Icc
        (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
          constructor <;> linarith [h.1,h.2,Real.pi_gt_d2])
      have hsin := Real.sin_nonneg_of_nonneg_of_le_pi h.1
        (by linarith [h.2,Real.pi_gt_d2])
      dsimp [f'',wingCos,wingSin]
      linarith
  have hleft : 0 ≤ f 0 := by norm_num [f]
  have hright : 0 ≤ f (12/25) := by
    have hcos := Seven.cos_lower_six (x := (12:ℝ)/25) (by norm_num)
    have hsin := Seven.sin_lower_seven (x := (12:ℝ)/25) (by norm_num)
    dsimp [f,wingCos,wingSin]
    nlinarith only [hcos,hsin]
  have hm := hc.min_le_of_mem_Icc (by norm_num : (0:ℝ) ∈ Set.Icc 0 (12/25))
    (by norm_num : (12:ℝ)/25 ∈ Set.Icc 0 (12/25)) hs
  have h := (le_min hleft hright).trans hm
  dsimp [f] at h
  linarith

lemma diagonal_trig_lower {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    4/3 ≤ Real.cos d+Real.sin d := by
  have h := trig_lower_of_endpoints (A := 1) (B := 1) (C := 4/3)
    (l := 1/2) (u := 4/5) (t := d) (by norm_num) (by norm_num)
    (by norm_num) (by linarith [Real.pi_gt_d2])
    (show 1/2 ≤ d ∧ d ≤ 4/5 by constructor <;> linarith [hd.1,hd.2])
    (by nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/2),
      Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)])
    (by nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (4:ℝ)/5),
      Real.sin_ge_sub_cube (x := (4:ℝ)/5) (by norm_num)])
  simpa only [one_mul] using h.le

end SquaresInCircles.Six.Analytic.OwnSouthWestDominant
