import SquaresInCircles.Six.Analytic.TransverseProfileBounds

/-!
# The two scalar bounds in the small-diagonal W-secondary argument

The constrained-circle branch is controlled by an upper derivative bound and
one explicit sextic chord identity. The unconstrained branch lies beyond
q=9/10 and uses trigonometric concavity on [9/10,7/6]. These two cases are
exactly the two circle-support branches; no box subdivision is performed.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def smallDiagonalA (d : ℝ) : ℝ := (77/200)*(Real.cos d+Real.sin d)
def smallDiagonalB (d : ℝ) : ℝ := 3/100+(9/20)*d
def smallDiagonalProjection (d q : ℝ) : ℝ :=
  smallDiagonalA d*Real.sin q-smallDiagonalB d*Real.cos q

lemma smallDiagonal_coefficients {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    (0≤ smallDiagonalA d ∧ smallDiagonalA d≤3/5) ∧
      (0≤ smallDiagonalB d ∧ smallDiagonalB d≤4/15) := by
  have hc0 : 0≤Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_gt_d2]⟩
  have hs0 : 0≤Real.sin d := Real.sin_nonneg_of_nonneg_of_le_pi hd.1
    (by linarith [hd.2,Real.pi_gt_d2])
  have hw : Real.cos d+Real.sin d≤3/2 := by
    nlinarith [Real.sin_sq_add_cos_sq d,sq_nonneg (Real.cos d-Real.sin d)]
  dsimp [smallDiagonalA,smallDiagonalB]
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith [hd.1],by linarith [hd.2]⟩⟩

lemma smallDiagonal_derivative_le {d : ℝ} (hd : 0≤d ∧ d≤1/2) (q : ℝ) :
    smallDiagonalA d*Real.cos q+smallDiagonalB d*Real.sin q≤2/3 := by
  obtain ⟨⟨ha0,ha1⟩,⟨hb0,hb1⟩⟩ := smallDiagonal_coefficients hd
  have hAsq := mul_nonneg (sub_nonneg.mpr ha1) (show 0≤3/5+smallDiagonalA d by linarith)
  have hBsq := mul_nonneg (sub_nonneg.mpr hb1) (show 0≤4/15+smallDiagonalB d by linarith)
  have hid : (smallDiagonalA d*Real.cos q+smallDiagonalB d*Real.sin q)^2+
      (smallDiagonalA d*Real.sin q-smallDiagonalB d*Real.cos q)^2 =
      (smallDiagonalA d)^2+(smallDiagonalB d)^2 := by
    linear_combination ((smallDiagonalA d)^2+(smallDiagonalB d)^2)*(Real.sin_sq_add_cos_sq q)
  by_contra! h
  have hp := mul_pos (show 0< smallDiagonalA d*Real.cos q+smallDiagonalB d*Real.sin q-2/3 by linarith)
    (show 0< smallDiagonalA d*Real.cos q+smallDiagonalB d*Real.sin q+2/3 by linarith)
  nlinarith [sq_nonneg (smallDiagonalA d*Real.sin q-smallDiagonalB d*Real.cos q)]

/-- Increasing the phase gap by v costs at most 2v/3. -/
lemma smallDiagonalProjection_increment {d v : ℝ}
    (hd : 0≤d ∧ d≤1/2) (hv : 0≤v) :
    smallDiagonalProjection d (d+v)≤ smallDiagonalProjection d d+(2/3)*v := by
  let f : ℝ → ℝ := fun q => smallDiagonalProjection d q-(2/3)*q
  have hder (q : ℝ) : HasDerivAt f
      (smallDiagonalA d*Real.cos q+smallDiagonalB d*Real.sin q-2/3) q := by
    exact (((Real.hasDerivAt_sin q).const_mul (smallDiagonalA d)).fun_sub
      ((Real.hasDerivAt_cos q).const_mul (smallDiagonalB d))).fun_sub
      ((hasDerivAt_id' q).const_mul (2/3)) |>.congr_deriv (by ring)
  have hanti := Seven.antiOn_of_hasDeriv_nonpos
    (l := d) (u := d+v) (f := f)
    (d := fun q => smallDiagonalA d*Real.cos q+smallDiagonalB d*Real.sin q-2/3)
    (fun q _ => (hder q).continuousAt.continuousWithinAt)
    (fun q _ => hder q)
    (fun q _ => by linarith [smallDiagonal_derivative_le hd q])
  have hh := hanti (show d∈Set.Icc d (d+v) by constructor <;> linarith)
    (show d+v∈Set.Icc d (d+v) by constructor <;> linarith) (by linarith)
  dsimp [f] at hh
  linarith

/-- Decreasing the gap within the first quadrant can only lower the bound. -/
lemma smallDiagonalProjection_mono {d q : ℝ}
    (hd : 0≤d ∧ d≤1/2) (hq : 0≤q ∧ q≤d) :
    smallDiagonalProjection d q≤ smallDiagonalProjection d d := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤q by linarith [hq.1,Real.pi_pos])
    (show d≤Real.pi/2 by linarith [hd.2,Real.pi_gt_d2]) hq.2
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hq.1
    (show d≤Real.pi by linarith [hd.2,Real.pi_gt_d2]) hq.2
  have hb := smallDiagonal_coefficients hd
  have hA := mul_le_mul_of_nonneg_left hs hb.1.1
  have hB := mul_le_mul_of_nonneg_left hc hb.2.1
  dsimp [smallDiagonalProjection]
  linarith

private def secondaryPolynomial (d : ℝ) : ℝ :=
  (77/4500)*d^6+(77/1500)*d^5-(77/600)*d^4-(19/600)*d^3+
    (2/5)*d^2-(13/200)*d-3/50

private def secondaryChordFactor (d : ℝ) : ℝ :=
  (1232*d^4+4312*d^3-7084*d^2-5822*d+25889)/72000

/-- The sextic is below a strictly negative chord on the full interval. -/
private lemma secondaryPolynomial_negative {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    secondaryPolynomial d<0 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hd.2) (show 0≤1/2+d by linarith [hd.1])
  have hfactor : 0≤ secondaryChordFactor d := by
    dsimp [secondaryChordFactor]
    nlinarith [pow_nonneg hd.1 3,pow_nonneg hd.1 4,hd.2]
  have hp := mul_nonneg (mul_nonneg hd.1 (show 0≤1/2-d by linarith [hd.2])) hfactor
  have hid : secondaryPolynomial d =
      (1-2*d)*(-3/50)+(2*d)*(-751/288000)-d*(1/2-d)*secondaryChordFactor d := by
    dsimp [secondaryPolynomial,secondaryChordFactor]
    ring
  have hchord : (1-2*d)*(-3/50)+(2*d)*(-751/288000)≤-751/288000 := by
    linarith [hd.2]
  nlinarith only [hid,hp,hchord]

lemma smallDiagonalProjection_at_diagonal {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    smallDiagonalProjection d d<3/100 := by
  have hdouble := Seven.sin_upper_five (show 0≤2*d by linarith [hd.1])
  rw [Real.sin_two_mul] at hdouble
  have hcosSq := Seven.cos_sq_lower_six hd.1
  have hunit := Real.sin_sq_add_cos_sq d
  have hcos := Real.one_sub_sq_div_two_le_cos (x := d)
  have hB : 0≤3/100+(9/20)*d := by linarith [hd.1]
  have hcosMul := mul_le_mul_of_nonneg_left hcos hB
  have hupper : smallDiagonalProjection d d-3/100≤ secondaryPolynomial d := by
    dsimp [smallDiagonalProjection,smallDiagonalA,smallDiagonalB,secondaryPolynomial]
    nlinarith only [hdouble,hcosSq,hunit,hcosMul]
  linarith [secondaryPolynomial_negative hd]

/-- Both signs of w are handled by monotonicity or the same derivative bound. -/
theorem smallDiagonalProjection_bound {w d : ℝ}
    (hd : 0≤d ∧ d≤1/2) (hwd : w≤d) :
    smallDiagonalProjection d (d-w)<3/100+(2/3)*max (-w) 0 := by
  by_cases hw : 0≤w
  · rw [max_eq_right (by linarith),mul_zero,add_zero]
    exact (smallDiagonalProjection_mono hd ⟨by linarith,by linarith⟩).trans_lt
      (smallDiagonalProjection_at_diagonal hd)
  · rw [max_eq_left (by linarith)]
    have h := smallDiagonalProjection_increment hd (show 0≤-w by linarith)
    have hid : d+(-w)=d-w := by ring
    rw [hid] at h
    linarith [smallDiagonalProjection_at_diagonal hd]

/-- The circular branch starts strictly after 9/10 for these primary bounds. -/
lemma unconstrained_gap_gt_nine_tenths {l q : ℝ}
    (hl : 277/200≤l) (hq : 0≤q ∧ q≤7/6) (hbranch : l<R0*Real.sin q) : 9/10<q := by
  by_contra! hqsmall
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤q by linarith [hq.1,Real.pi_pos])
    (show (9:ℝ)/10≤Real.pi/2 by linarith [Real.pi_gt_d2]) hqsmall
  have ht := Seven.sin_upper_five (x := (9:ℝ)/10) (by norm_num)
  have hbound : Real.sin q≤(9/10:ℝ)-(9/10)^3/6+(9/10)^5/120 := hs.trans ht
  have hprod := mul_le_mul R0_lt_1689_1000.le hbound
    (Real.sin_nonneg_of_nonneg_of_le_pi hq.1 (by linarith [hq.2,Real.pi_gt_d2]))
    (by norm_num : (0:ℝ)≤1689/1000)
  nlinarith only [hprod,hbranch,hl]

/-- The two endpoints are those of the whole unconstrained branch interval. -/
lemma unconstrained_secondary_reserve {q : ℝ} (hq : 9/10≤q ∧ q≤7/6) :
    5977/3000<(2/3)*q+Real.sin q+Real.cos q := by
  rw [show (2/3:ℝ)*q+Real.sin q+Real.cos q=2/3*q+1*Real.sin q+1*Real.cos q by ring]
  apply Seven.trig_concave_gt (α := (2:ℝ)/3) (A := 1) (B := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Real.pi_gt_d2]) hq
  · have hs := Seven.sin_lower_seven (x := (9:ℝ)/10) (by norm_num)
    have hc := Seven.cos_lower_six (x := (9:ℝ)/10) (by norm_num)
    nlinarith only [hs,hc]
  · have hs := Seven.sin_lower_seven (x := (7:ℝ)/6) (by norm_num)
    have hc := Seven.cos_lower_six (x := (7:ℝ)/6) (by norm_num)
    nlinarith only [hs,hc]

end SquaresInCircles.Six.Analytic
