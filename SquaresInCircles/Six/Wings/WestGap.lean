module

public import SquaresInCircles.Six.Separators.Walls
public import SquaresInCircles.Six.Separators.Profiles
public import SquaresInCircles.Six.Supports

/-!
# Six squares: W and D along the secondary axis of D

If W and D are separated along the secondary axis of D, the phase of D exceeds
that of W by more than one radian. Let `v = -w`, `q = d + v` the phase gap and
`x = -b_W`. The far corner of W gives `a_W + (31/100)(x + x²) ≤ ρ0`, the
separation of W from C bounds `x` by an affine function `U(v)`, and
`b_D < 31/100 - (17/100) d`. If `q ≤ 1`, the separation then exceeds the
threshold by less than
`F = A(U) sin q + (U - 1/2) cos q - 19/100 - (17/100)(q - v)`, with
`A(U) = ρ0 - 1/2 - (31/100)(U + U²)`. On `[0, 1]` it increases in `q`, at `q = 1`
it increases in `v` along `U(v)`, and its values at `v = 1/2` (W on its own
axis) and `v = 2/5` (W on the west side of C) are negative.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six
open Normalization

private def westDefect (U v q : ℝ) : ℝ :=
  (rho0-1/2-(31/100)*(U+U^2))*Real.sin q+(U-1/2)*Real.cos q-
    19/100-(17/100)*q+(17/100)*v

private lemma trig_one_bounds {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) :
    389/720 ≤ Real.cos q ∧ 0 ≤ Real.sin q ∧ Real.sin q ≤ 101/120 := by
  obtain ⟨hs,hs',hc,-⟩ := trig_bracket le_rfl (by linarith [Real.pi_gt_d2]) hq
  norm_num at hs hs' hc
  exact ⟨by linarith,by linarith,by linarith⟩

/-- The far-corner bound with the signed coordinate `-b` in place of `|b|`. -/
private lemma signed_radial_quadratic {a b : ℝ} (hc : ContainedChart a |b|) :
    a+(31/100)*(-b+(-b)^2) ≤ rho0 := by
  have h := radial_transverse_quadratic hc
  nlinarith [neg_le_abs b]

private lemma quadratic_projection_mono {x U q : ℝ}
    (hx : x ≤ U) (hU : U ≤ 47/100) (hq : 0 ≤ q ∧ q ≤ 1) :
    (rho0-1/2-(31/100)*(x+x^2))*Real.sin q+(x-1/2)*Real.cos q ≤
      (rho0-1/2-(31/100)*(U+U^2))*Real.sin q+(U-1/2)*Real.cos q := by
  obtain ⟨hc,hs0,hs⟩ := trig_one_bounds hq
  have hcoef : 1+x+U ≤ 97/50 := by linarith
  have hmult := mul_le_mul_of_nonneg_right hcoef hs0
  have hmargin : 0 ≤ Real.cos q-(31/100)*(1+x+U)*Real.sin q := by
    nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hx) hmargin
  nlinarith only [hp]

private lemma westDefect_mono_q {U v : ℝ}
    (hU : 0 ≤ U ∧ U ≤ 47/100) :
    MonotoneOn (westDefect U v) (Set.Icc 0 1) := by
  let A := rho0-1/2-(31/100)*(U+U^2)
  have hUsq := mul_nonneg (sub_nonneg.mpr hU.2)
    (show 0 ≤ (47:ℝ)/100+U by linarith [hU.1])
  have hA : 39/100 ≤ A := by
    dsimp [A]
    nlinarith [rho0_bounds.1]
  have hd (q : ℝ) : HasDerivAt (westDefect U v)
      (A*Real.cos q-(U-1/2)*Real.sin q-17/100) q := by
    convert (((((Real.hasDerivAt_sin q).const_mul A).fun_add
      ((Real.hasDerivAt_cos q).const_mul (U-1/2))).sub_const (19/100)).fun_sub
      ((hasDerivAt_id q).const_mul (17/100))).add_const ((17/100)*v) using 1
    · funext y; dsimp [westDefect,A]
    · dsimp [A]; ring
  apply monoOn_of_hasDeriv_nonneg
    (fun q _ => (hd q).continuousAt.continuousWithinAt) (fun q _ => hd q)
  intro q hq
  obtain ⟨hc,hs0,_⟩ := trig_one_bounds ⟨hq.1.le,hq.2.le⟩
  have hp := mul_nonneg (show 0 ≤ A-39/100 by linarith)
    (show 0 ≤ Real.cos q by linarith)
  have hn := mul_nonneg (show 0 ≤ 1/2-U by linarith [hU.2]) hs0
  nlinarith

/-- At `q = 1` the bound increases in `v` along an affine profile
`U = U₀ - k v`. -/
private lemma westDefect_profile_endpoint {U0 k V v : ℝ}
    (hk : 0 ≤ k) (hv : 0 ≤ v ∧ v ≤ V)
    (hUmin : 0 ≤ U0-k*V)
    (hreserve : 0 ≤ (31/100)*k*(1+2*(U0-k*V))*(5/6)-k*(13/24)+17/100) :
    westDefect (U0-k*v) v 1 ≤ westDefect (U0-k*V) V 1 := by
  have hs := Real.sin_ge_sub_cube (x := (1:ℝ)) (by norm_num)
  have hc := cos_upper_four (x := (1:ℝ)) (by norm_num)
  have hsin : 5/6 ≤ Real.sin (1:ℝ) := by norm_num at hs; exact hs
  have hcos : Real.cos (1:ℝ) ≤ 13/24 := by norm_num at hc; exact hc
  have hs0 : 0 ≤ Real.sin (1:ℝ) := by linarith
  have hUv : U0-k*V ≤ U0-k*v := by nlinarith
  have ha : 0 ≤ (31/100)*k*(1+2*(U0-k*V)) := by positivity
  have hS := mul_le_mul_of_nonneg_left hsin ha
  have hC := mul_le_mul_of_nonneg_left hcos hk
  have hUv' : 0 ≤ (U0-k*v)-(U0-k*V) := sub_nonneg.mpr hUv
  have hgap := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 31/100) hk) hUv') hs0
  have hbracket : 0 ≤ (31/100)*k*(1+(U0-k*v)+(U0-k*V))*Real.sin 1-
      k*Real.cos 1+17/100 := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hv.2) hbracket
  have hid : westDefect (U0-k*V) V 1-westDefect (U0-k*v) v 1 =
      (V-v)*((31/100)*k*(1+(U0-k*v)+(U0-k*V))*Real.sin 1-
        k*Real.cos 1+17/100) := by
    dsimp [westDefect]
    ring
  linarith

/-- The bound at `q = 1` at the ends `v = 1/2` and `v = 2/5` of the two profiles
`U(v)`, from the Taylor values `sin 1 ≤ 101/120` and `cos 1 ≥ 389/720`. -/
private lemma westDefect_endpoint_bounds :
    westDefect (233/500-(73/100)*(1/2)) (1/2) 1 < 0 ∧
      westDefect (47/100-(2/3)*(2/5)) (2/5) 1 < 0 := by
  obtain ⟨hc,-,hs⟩ := trig_one_bounds (q := 1) ⟨by norm_num,le_rfl⟩
  have bound {U : ℝ} (v : ℝ) (hU : 0 ≤ U ∧ U ≤ 1/2) : westDefect U v 1 ≤
      (rho0-1/2-(31/100)*(U+U^2))*(101/120)+(U-1/2)*(389/720)-19/100-17/100+(17/100)*v := by
    have hA := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ rho0-1/2-(31/100)*(U+U^2) by nlinarith [rho0_bounds.1])
    have hC := mul_le_mul_of_nonpos_left hc (show U-1/2 ≤ 0 by linarith)
    dsimp [westDefect]
    linarith
  constructor <;> refine (bound _ (by norm_num)).trans_lt ?_ <;> norm_num <;>
    linarith [rho0_bounds.2]

private lemma westDefect_own_negative {v q : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1) :
    westDefect (233/500-(73/100)*v) v q < 0 := by
  have hU : 0 ≤ 233/500-(73/100)*v ∧ 233/500-(73/100)*v ≤ 47/100 := by
    constructor <;> linarith [hv.1,hv.2]
  have hqmono := westDefect_mono_q (v := v) hU hq (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) hq.2
  have hvmono := westDefect_profile_endpoint
    (U0 := 233/500) (k := 73/100) (V := 1/2) (by norm_num) hv
    (by norm_num) (by norm_num)
  exact hqmono.trans_lt (hvmono.trans_lt westDefect_endpoint_bounds.1)

private lemma westDefect_cardinal_negative {v q : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/5) (hq : 0 ≤ q ∧ q ≤ 1) :
    westDefect (47/100-(2/3)*v) v q < 0 := by
  have hU : 0 ≤ 47/100-(2/3)*v ∧ 47/100-(2/3)*v ≤ 47/100 := by
    constructor <;> linarith [hv.1,hv.2]
  have hqmono := westDefect_mono_q (v := v) hU hq (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) hq.2
  have hvmono := westDefect_profile_endpoint
    (U0 := 47/100) (k := 2/3) (V := 2/5) (by norm_num) hv
    (by norm_num) (by norm_num)
  exact hqmono.trans_lt (hvmono.trans_lt westDefect_endpoint_bounds.2)

private lemma west_secondary_defect_upper {a b z d v U : ℝ}
    (hc : ContainedChart a |b|) (hq : 0 ≤ d+v ∧ d+v ≤ 1)
    (hU : U ≤ 47/100) (hx : -b ≤ U)
    (hz : z < 31/100-(17/100)*d) :
    a*Real.sin (d+v)-b*Real.cos (d+v)+z-(1/2+angularWidth (d+v)) <
      westDefect U v (d+v) := by
  obtain ⟨hcos,hsin,_⟩ := trig_one_bounds hq
  have hrad := signed_radial_quadratic hc
  have hp := mul_nonneg
    (show 0 ≤ rho0-(31/100)*(-b+(-b)^2)-a by linarith) hsin
  have hm := quadratic_projection_mono hx hU hq
  rw [angularWidth,abs_of_nonneg (by linarith : 0 ≤ Real.cos (d+v)),
    abs_of_nonneg hsin]
  dsimp [westDefect]
  nlinarith only [hp,hm,hz]

/-- If W and D are separated along the secondary axis of D, their phases differ
by more than one radian. -/
theorem westDiagonal_gap_gt_one {R : ℝ} (P : NormalizedPacking R)
    (hsep : SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    1 < P.phase 3-P.phase 2 := by
  have hwall := westDiagonal_wall P hsep
  have hwneg : P.deviation 2 < 0 := by linarith [P.diagonal_angle_range.2]
  let v := -P.deviation 2
  let d := P.diagonalAngle
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hWphase : P.phase 2=Real.pi-v := by
    rw [P.phase_from_deviation 2,show cardinalCenter (matchingCardinal 2)=Real.pi from rfl]
    dsimp [v]; ring
  have hDphase : P.phase 3=Real.pi+d := by dsimp [d,NormalizedPacking.diagonalAngle]; ring
  have hgap : P.phase 3-P.phase 2=d+v := by rw [hWphase,hDphase]; ring
  by_contra! hsmall
  have hq : 0 ≤ d+v ∧ d+v ≤ 1 := by
    have hp := P.primary_order.2.2.1
    rw [hgap] at hsmall
    rw [hWphase,hDphase] at hp
    constructor <;> linarith
  have hd : 1/2 < d := normalized_diagonal_gt_half P
  have hz := normalized_diagonal_transverse_affine P
  have hz' : P.transverse 3 < 31/100-(17/100)*d := (le_abs_self _).trans_lt hz
  change SAT.threshold (P.square 2) (P.square 3) ≤
    frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
  rw [P.square_def 2,P.square_def 3,oriented_pair_threshold,pair_frameY_right,hgap] at hsep
  cases hbit : P.ownAxis 2
  · have ha := abs_lt.mp (P.cardinal_angle 2 hbit)
    have hv : 0 ≤ v ∧ v ≤ 2/5 := ⟨hv0,by dsimp [v]; linarith [ha.1]⟩
    have hcard := P.cardinal_separator 2 hbit
    rw [hWphase] at hcard
    have htrans := cardinal_west_negative_transverse (P.contained 2) P.box.1.2 hv hcard
    have hu : 47/100-(2/3)*v ≤ 47/100 := by linarith [hv.1]
    have hf := west_secondary_defect_upper (P.contained 2) hq hu htrans.le hz'
    have hn := westDefect_cardinal_negative hv hq
    nlinarith only [hsep,hf,hn]
  · have hv : 0 ≤ v ∧ v ≤ 1/2 := ⟨hv0,by linarith [hq.2]⟩
    have hown := P.own_separator 2 hbit
    rw [hWphase] at hown
    have htrans := own_west_transverse_small_angle (P.contained 2) P.box.1.2 P.box.2.1 hv hown
    have hu : 233/500-(73/100)*v ≤ 47/100 := by linarith [hv.1]
    have hf := west_secondary_defect_upper (P.contained 2) hq hu
      ((neg_le_abs _).trans htrans.le) hz'
    have hn := westDefect_own_negative hv hq
    nlinarith only [hsep,hf,hn]

end SquaresInCircles.Six
