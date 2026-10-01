import SquaresInCircles.Six.Analytic.CardinalSouthTail.Scalar
import SquaresInCircles.Six.Analytic.CandidateWestTail.Support
import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening

/-!
# The large south tail: the supports

The weights `4`, `10`, `3`, `3` on C–W, C–S, W–D and D–S put the force
`(4 cos v, 4 sin v - 3)` on W, a force of length `6 sin(q/2)` on D, where
`q = d + v`, and on S a force with radial component `10 + 3 cos r` and
transverse component `3 sin r`, where `r = d - s`. The supports of W and D
are bounded by their far vertices, using `√(25 - 24 sin v) ≤ 5 - (12/5) sin v`,
and that of S by `rho0` times its radial force, from the far-corner
quadratic. For `s ≥ 12/25` the first component `4 - 10 sin s` of the force on
C is negative, so the centre of C contributes at most `10 c0 cos s`. The
threshold sum less these bounds is the defect, and the profile is a lower
bound for it.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.CardinalSouthTail
open Normalization

lemma radius_bounds : (5:ℝ)/3 ≤ R0 ∧ R0 ≤ 1689/1000 := by
  constructor
  · have h := R0_sq
    norm_num [Q0] at h
    nlinarith [R0_nonneg]
  · exact R0_lt_1689_1000.le

lemma west_root_upper (v : ℝ) :
    Real.sqrt (25-24*Real.sin v) ≤ 5-(12/5)*Real.sin v := by
  have hr : 0 ≤ 25-24*Real.sin v := by linarith [Real.sin_le_one v]
  have hm : 0 ≤ 5-(12/5)*Real.sin v := by linarith [Real.sin_le_one v]
  have hsq := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (25-24*Real.sin v)
  nlinarith [sq_nonneg (Real.sin v)]

def westUpper (v : ℝ) : ℝ :=
  R0*(5-(12/5)*Real.sin v)-(4*Real.cos v+3-4*Real.sin v)/2

def diagonalUpper (q : ℝ) : ℝ :=
  6*R0*Real.sin (q/2)-(3*Real.sin q+3-3*Real.cos q)/2

lemma west_support {a b : ℝ} (hc : ContainedChart a |b|) (v : ℝ) :
    4*Real.cos v*a+(4*Real.sin v-3)*b ≤ westUpper v := by
  have h := CandidateWestTail.local_vertex_support hc (4*Real.cos v) (4*Real.sin v-3)
  have hid : (4*Real.cos v)^2+(4*Real.sin v-3)^2=25-24*Real.sin v := by
    linear_combination 16*(Real.sin_sq_add_cos_sq v)
  rw [hid] at h
  have hr := mul_le_mul_of_nonneg_left (west_root_upper v) R0_nonneg
  have hw : 4*Real.cos v+3-4*Real.sin v ≤
      |4*Real.cos v|+|4*Real.sin v-3| := by
    linarith [le_abs_self (4*Real.cos v),neg_le_abs (4*Real.sin v-3)]
  dsimp [westUpper]
  linarith

lemma diagonal_support {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 0 ≤ q ∧ q ≤ 6/5) :
    3*Real.sin q*a+(3*Real.cos q-3)*b ≤ diagonalUpper q := by
  have h := CandidateWestTail.local_vertex_support hc (3*Real.sin q) (3*Real.cos q-3)
  have hid : (3*Real.sin q)^2+(3*Real.cos q-3)^2=18-18*Real.cos q := by
    linear_combination 9*(Real.sin_sq_add_cos_sq q)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ q/2 by linarith [hq.1])
    (show q/2 ≤ Real.pi by linarith [hq.2,Real.pi_gt_d2])
  have hcos : Real.cos q=1-2*Real.sin (q/2)^2 := by
    have hh := Real.cos_two_mul (q/2)
    rw [show 2*(q/2)=q by ring] at hh
    nlinarith only [hh,Real.sin_sq_add_cos_sq (q/2)]
  have hnorm : Real.sqrt (18-18*Real.cos q)=6*Real.sin (q/2) := by
    rw [show 18-18*Real.cos q=(6*Real.sin (q/2))^2 by nlinarith only [hcos],
      Real.sqrt_sq (by positivity)]
  rw [hid,hnorm] at h
  have hw : 3*Real.sin q+3-3*Real.cos q ≤
      |3*Real.sin q|+|3*Real.cos q-3| := by
    linarith [le_abs_self (3*Real.sin q),neg_le_abs (3*Real.cos q-3)]
  dsimp [diagonalUpper]
  nlinarith only [h,hw]

/-- The support of S: its force has radial component at least `10` and
transverse component at most `3`, so the far-corner quadratic bounds the
support by `rho0` times the radial component. -/
lemma south_support {a b r : ℝ} (hc : ContainedChart a |b|)
    (hr : 0 ≤ Real.cos r) :
    (10+3*Real.cos r)*a+3*Real.sin r*b ≤ rho0*(10+3*Real.cos r) := by
  have hquad := radial_transverse_quadratic hc
  have hrad : a+(31/100)*|b| ≤ rho0 := by nlinarith [sq_nonneg b]
  have hsin : |Real.sin r| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin r,Real.sin_le_one r⟩
  have hb : Real.sin r*b ≤ |b| := by
    calc
      Real.sin r*b ≤ |Real.sin r*b| := le_abs_self _
      _ = |Real.sin r| *|b| := abs_mul _ _
      _ ≤ 1*|b| := mul_le_mul_of_nonneg_right hsin (abs_nonneg b)
      _ = |b| := one_mul _
  have hm := mul_nonneg (show 0 ≤ 10+3*Real.cos r by linarith)
    (show 0 ≤ rho0-a-(31/100)*|b| by linarith)
  have hcoef := mul_nonneg
    (show 0 ≤ (31/100)*(10+3*Real.cos r)-3 by linarith) (abs_nonneg b)
  nlinarith only [hm,hcoef,hb]

lemma south_trig {s : ℝ} (hs : 12/25 ≤ s ∧ s ≤ 2/3) :
    0 ≤ Real.cos s ∧ 2/5 ≤ Real.sin s := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show s ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (12:ℝ)/25 by linarith [Real.pi_pos])
    (show s ≤ Real.pi/2 by linarith [hs.2,Real.pi_gt_d2]) hs.1
  have hl := Real.sin_ge_sub_cube (x := (12:ℝ)/25) (by norm_num)
  exact ⟨hc,by linarith⟩

lemma central_support {s cx cy : ℝ} (hs : 12/25 ≤ s ∧ s ≤ 2/3)
    (hx : 0 ≤ cx) (hy : cy ≤ c0) :
    (4-10*Real.sin s)*cx+10*Real.cos s*cy ≤ 10*c0*Real.cos s := by
  have ht := south_trig hs
  have hX := mul_nonpos_of_nonpos_of_nonneg (show 4-10*Real.sin s ≤ 0 by linarith) hx
  have hY := mul_nonneg (sub_nonneg.mpr hy) ht.1
  nlinarith only [hX,hY]

def totalThreshold (v s d : ℝ) : ℝ :=
  4*(1/2+angularWidth v)+10*(1/2+angularWidth s)+
    3*(1/2+angularWidth (d+v))+3*(1/2+angularWidth (d-s))

def defect (v s d : ℝ) : ℝ :=
  totalThreshold v s d-westUpper v-diagonalUpper (d+v)-
    rho0*(10+3*Real.cos (d-s))-10*c0*Real.cos s

private lemma sine_term_lower {negative : Bool} {v : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative) :
    coefficient negative*Real.sin v ≤
      2*(|Real.sin v|-Real.sin v)+(12/5)*R0*Real.sin v := by
  cases negative
  · simp only [vLower,vUpper,Bool.false_eq_true,ite_false] at hv
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
      (by linarith [hv.2,Real.pi_gt_d2])
    rw [abs_of_nonneg hs]
    have hp := mul_nonneg (show 0 ≤ R0-5/3 by linarith [radius_bounds.1]) hs
    dsimp [coefficient]
    nlinarith only [hp]
  · simp only [vLower,vUpper,ite_true] at hv
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ -v by linarith [hv.2])
      (show -v ≤ Real.pi by linarith [hv.1,Real.pi_gt_d2])
    rw [Real.sin_neg] at hs
    rw [abs_of_nonpos (by linarith : Real.sin v ≤ 0)]
    have hp := mul_nonneg (show 0 ≤ 1689/1000-R0 by linarith [radius_bounds.2]) hs
    dsimp [coefficient]
    nlinarith only [hp]

/-- The profile is a lower bound for the defect on the large-tail domain. -/
lemma profile_le_defect (negative : Bool) {v s d : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative)
    (hs : 12/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    profile negative v s d ≤ defect v s d := by
  have hraw := v_bounds hv
  have hq : 0 ≤ d+v ∧ d+v ≤ 6/5 := by
    constructor <;> linarith [hraw.1,hraw.2,hd.1,hd.2]
  have hcv := Real.cos_nonneg_of_mem_Icc
    (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hraw.1,hraw.2,Real.pi_gt_d2])
  have hcs := (south_trig hs).1
  have hss : 0 ≤ Real.sin s := by linarith [(south_trig hs).2]
  have hcq := Real.cos_nonneg_of_mem_Icc
    (show d+v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_gt_d2])
  have hsq := Real.sin_nonneg_of_nonneg_of_le_pi hq.1
    (by linarith [hq.2,Real.pi_gt_d2])
  have hsh := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ (d+v)/2 by linarith [hq.1])
    (show (d+v)/2 ≤ Real.pi by linarith [hq.2,Real.pi_gt_d2])
  have hcr := Real.cos_nonneg_of_mem_Icc
    (show d-s ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,hd.1,hd.2,Real.pi_gt_d2])
  have hW : angularWidth v=(Real.cos v+|Real.sin v|)/2 := by
    simp only [angularWidth,abs_of_nonneg hcv]
  have hS : angularWidth s=(Real.cos s+Real.sin s)/2 := by
    simp only [angularWidth,abs_of_nonneg hcs,abs_of_nonneg hss]
  have hQ : angularWidth (d+v)=(Real.cos (d+v)+Real.sin (d+v))/2 := by
    simp only [angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq]
  have hR : (Real.cos (d-s)+Real.sin (d-s))/2 ≤ angularWidth (d-s) := by
    dsimp [angularWidth]
    linarith [le_abs_self (Real.cos (d-s)),le_abs_self (Real.sin (d-s))]
  have hC := mul_nonneg (show 0 ≤ 1113/1000-rho0 by linarith [rho0_upper]) hcs
  have hD := mul_nonneg (show 0 ≤ 1113/1000-rho0 by linarith [rho0_upper]) hcr
  have hH := mul_nonneg (show 0 ≤ 1689/1000-R0 by linarith [radius_bounds.2]) hsh
  have hV := sine_term_lower hv
  dsimp [profile,defect,totalThreshold,westUpper,diagonalUpper,c0]
  rw [hW,hS,hQ]
  nlinarith only [hR,hC,hD,hH,hV,rho0_upper,radius_bounds.2]

end SquaresInCircles.Six.Analytic.CardinalSouthTail
