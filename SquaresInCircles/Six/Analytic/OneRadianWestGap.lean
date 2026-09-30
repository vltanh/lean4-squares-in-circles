module
public import SquaresInCircles.Six.Analytic.SecondaryReduction
public import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening
public import SquaresInCircles.Six.Analytic.HighDiagonalAffineTransverse

@[expose] public section

/-!
# A full one-radian exclusion for a D-sourced west edge

Use x = -bW and q = d+v, where v = -w. The far-corner circle gives
  aW + (31/100) * (x+x^2) <= rho0.
The existing OWN/cardinal profiles bound x by an affine function U(v), and
  bD < 31/100 - (17/100)*d.
Their combination bounds the separator defect by
  F(U,v,q) = (rho0-1/2-(31/100)*(U+U^2))*sin q
              +(U-1/2)*cos q-19/100-(17/100)*q+(17/100)*v.
For 0 <= q <= 1, F increases in q. At q=1 its affine-profile restriction
increases in v, as a single factored difference shows. Only the two forced
endpoints (v,q)=(1/2,1), (2/5,1) are evaluated. Their rational upper bounds
are respectively -43720331/12000000000 and -195751/1080000000.

No interval cover, sampled minimum or candidate-edge hypothesis is used.
This strengthens a phase restriction; it does not exclude the entire mixed
case or supply the remaining OWN-wing tails. Compilation remains deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private def westDefect (U v q : ℝ) : ℝ :=
  (rho0-1/2-(31/100)*(U+U^2))*Real.sin q+(U-1/2)*Real.cos q-
    19/100-(17/100)*q+(17/100)*v

private lemma trig_one_bounds {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) :
    389/720 ≤ Real.cos q ∧ 0 ≤ Real.sin q ∧ Real.sin q ≤ 101/120 := by
  have hc := Seven.cos_lower_six (x := (1:ℝ)) (by norm_num)
  have hs := Seven.sin_upper_five (x := (1:ℝ)) (by norm_num)
  have hcm := Real.cos_le_cos_of_nonneg_of_le_pi hq.1
    (show (1:ℝ) ≤ Real.pi by linarith [Real.pi_gt_d2]) hq.2
  have hsm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ q by linarith [hq.1,Real.pi_pos])
    (show (1:ℝ) ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hq.2
  exact ⟨by nlinarith,
    Real.sin_nonneg_of_nonneg_of_le_pi hq.1 (by linarith [hq.2,Real.pi_gt_d2]),
    by nlinarith⟩

/-- The signed coordinate x=-b need not be nonnegative. -/
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
    nlinarith [rho0_lower]
  have hd (q : ℝ) : HasDerivAt (westDefect U v)
      (A*Real.cos q-(U-1/2)*Real.sin q-17/100) q := by
    convert (((((Real.hasDerivAt_sin q).const_mul A).add
      ((Real.hasDerivAt_cos q).const_mul (U-1/2))).sub_const (19/100)).sub
      ((hasDerivAt_id q).const_mul (17/100))).add_const ((17/100)*v) using 1 <;>
      dsimp [westDefect,A] <;> ring
  apply Seven.monoOn_of_hasDeriv_nonneg (by dsimp [westDefect]; fun_prop)
    (fun q _ => hd q)
  intro q hq
  obtain ⟨hc,hs0,_⟩ := trig_one_bounds ⟨hq.1.le,hq.2.le⟩
  have hp := mul_nonneg (show 0 ≤ A-39/100 by linarith)
    (show 0 ≤ Real.cos q by linarith)
  have hn := mul_nonneg (show 0 ≤ 1/2-U by linarith [hU.2]) hs0
  nlinarith

/-- At q=1, one factorization replaces the whole affine-profile interval. -/
private lemma westDefect_profile_endpoint {U0 k V v : ℝ}
    (hk : 0 ≤ k) (hv : 0 ≤ v ∧ v ≤ V)
    (hUmin : 0 ≤ U0-k*V)
    (hreserve : 0 ≤ (31/100)*k*(1+2*(U0-k*V))*(5/6)-k*(13/24)+17/100) :
    westDefect (U0-k*v) v 1 ≤ westDefect (U0-k*V) V 1 := by
  have hs := Real.sin_ge_sub_cube (x := (1:ℝ)) (by norm_num)
  have hc := Seven.cos_upper_four (x := (1:ℝ)) (by norm_num)
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

private lemma westDefect_endpoint_bounds :
    westDefect (101/1000) (1/2) 1 < 0 ∧
      westDefect (61/300) (2/5) 1 < 0 := by
  obtain ⟨hc,hs0,hs⟩ := trig_one_bounds (q := 1) ⟨by norm_num,le_rfl⟩
  have ownA : 0 ≤ rho0-1/2-(31/100)*((101/1000)+(101/1000)^2) := by
    linarith [rho0_lower]
  have cardA : 0 ≤ rho0-1/2-(31/100)*((61/300)+(61/300)^2) := by
    linarith [rho0_lower]
  have ownS := mul_le_mul_of_nonneg_left hs ownA
  have cardS := mul_le_mul_of_nonneg_left hs cardA
  have ownC := mul_le_mul_of_nonpos_left hc
    (show (101/1000:ℝ)-1/2 ≤ 0 by norm_num)
  have cardC := mul_le_mul_of_nonpos_left hc
    (show (61/300:ℝ)-1/2 ≤ 0 by norm_num)
  constructor <;> dsimp [westDefect] <;> nlinarith [rho0_upper]

private lemma westDefect_own_negative {v q : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1) :
    westDefect (233/500-(73/100)*v) v q < 0 := by
  have hU : 0 ≤ 233/500-(73/100)*v ∧ 233/500-(73/100)*v ≤ 47/100 := by
    constructor <;> linarith [hv.1,hv.2]
  have hqmono := westDefect_mono_q (v := v) hU hq (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) hq.2
  have hvmono := westDefect_profile_endpoint
    (U0 := 233/500) (k := 73/100) (V := 1/2) (by norm_num) hv
    (by norm_num) (by norm_num)
  have he := westDefect_endpoint_bounds.1
  norm_num at hvmono
  exact hqmono.trans_lt (hvmono.trans_lt he)

private lemma westDefect_cardinal_negative {v q : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/5) (hq : 0 ≤ q ∧ q ≤ 1) :
    westDefect (47/100-(2/3)*v) v q < 0 := by
  have hU : 0 ≤ 47/100-(2/3)*v ∧ 47/100-(2/3)*v ≤ 47/100 := by
    constructor <;> linarith [hv.1,hv.2]
  have hqmono := westDefect_mono_q (v := v) hU hq (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) hq.2
  have hvmono := westDefect_profile_endpoint
    (U0 := 47/100) (k := 2/3) (V := 2/5) (by norm_num) hv
    (by norm_num) (by norm_num)
  have he := westDefect_endpoint_bounds.2
  norm_num at hvmono
  exact hqmono.trans_lt (hvmono.trans_lt he)

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

/-- A D-sourced W/D separator needs a phase gap strictly greater than one radian.
This retains both canonical W cases and uses no candidate-edge conclusion. -/
theorem DW_Dsecondary_gap_gt_one {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    1 < P.phase 3-P.phase 2 := by
  have hwall := DW_Dsecondary_west_of_wall P hsep
  have hwneg : P.helperAngle 2 < 0 := by linarith [P.diagonal_angle_range.2]
  let v := -P.helperAngle 2
  let d := P.diagonalAngle
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hWphase : P.phase 2=Real.pi-v := by rw [P.phase_from_deviation 2]; dsimp [v]; ring
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
  change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
  rw [P.square_def 2,P.square_def 3,oriented_pair_threshold,pair_frameY_right,hgap] at hsep
  cases hbit : P.ownBits 2
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

lemma MissingWestWing.phase_wall_one {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.helperAngle 2 < P.diagonalAngle-1 := by
  have hg := DW_Dsecondary_gap_gt_one P h.from_diagonal
  rw [P.phase_from_deviation 2] at hg
  dsimp [NormalizedPacking.diagonalAngle]
  linarith

end SquaresInCircles.Six.Analytic
