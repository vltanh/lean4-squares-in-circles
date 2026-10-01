import SquaresInCircles.Six.Separators.Walls

/-!
# The signs of the own wings

If S is not separated from C along the south side of C, it is separated along
its own axis at the phase `3π/2 + s`, and `s > 0`. At `s = 0` the two margins
would agree; for `s = -v < 0` their difference gives
`b < c_x + tan (v/2) (a - c_y)` for the chart `(a, b)` of S, and D, at the phase
`π + d` with `1/2 ≤ d ≤ π/4`, is separated from S along the secondary axis of D
or of S. Along that of D, a positive combination of this bound and the south
margin eliminates `v`. Along that of S, the bound `|b_D| < 31/100 - 17d/100` and
the far-corner quadratic of D leave an expression that decreases in `d` and is
negative at `d = 1/2`, by Taylor bounds and a completed square. If W and S are
both separated from C along their own axes, the sum of their separating
inequalities, which share the centre of C, bounds `a_W + a_S` below by a
concave profile of their angles, and `a_W, a_S ≤ ρ0` gives `s - w < 24/25`.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

private def transverseLimit (d : ℝ) : ℝ := 31/100-(17/100)*d
private def radialLimit (d : ℝ) : ℝ :=
  rho0-(31/100)*(transverseLimit d+(transverseLimit d)^2)
private def southDefect (d v : ℝ) : ℝ :=
  c0+rho0*halfRatio v-1/2+(radialLimit d-1/2)*Real.cos (d+v)+
    (transverseLimit d-1/2)*Real.sin (d+v)

private lemma limit_bounds {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    0 ≤ transverseLimit d ∧ transverseLimit d ≤ 9/40 ∧ 1/2 ≤ radialLimit d := by
  have hu0 : 0 ≤ transverseLimit d := by dsimp [transverseLimit]; linarith [hd.2,Real.pi_lt_d2]
  have hu : transverseLimit d ≤ 9/40 := by dsimp [transverseLimit]; linarith [hd.1]
  have hsq := mul_nonneg (sub_nonneg.mpr hu)
    (show 0 ≤ (9:ℝ)/40+transverseLimit d by linarith)
  exact ⟨hu0,hu,by dsimp [radialLimit]; nlinarith [rho0_bounds.1]⟩

private lemma angle_sum_trig {d v : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (hv : 0 ≤ v ∧ v ≤ 5/8) :
    0 ≤ Real.cos (d+v) ∧ 23/48 ≤ Real.sin (d+v) := by
  have htheta : 1/2 ≤ d+v ∧ d+v ≤ Real.pi/2 := by
    constructor <;> linarith [hd.1,hd.2,hv.1,hv.2,Real.pi_gt_d2]
  have hc := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [htheta.1,Real.pi_pos],htheta.2⟩
  have hs := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/2 by linarith [Real.pi_pos]) htheta.2 htheta.1
  exact ⟨hc,by nlinarith⟩

private lemma diagonal_projection_upper {a b d v : ℝ}
    (hc : ContainedChart a |b|) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hv : 0 ≤ v ∧ v ≤ 5/8) (hb : |b| ≤ transverseLimit d) :
    a*Real.cos (d+v)-b*Real.sin (d+v) ≤
      radialLimit d*Real.cos (d+v)+transverseLimit d*Real.sin (d+v) := by
  obtain ⟨hcos,hsin⟩ := angle_sum_trig hd hv
  obtain ⟨hu0,hu,_⟩ := limit_bounds hd
  have hx : -b ≤ transverseLimit d := (neg_le_abs b).trans hb
  have hrad := radial_transverse_quadratic hc
  have hrad' : a+(31/100)*(-b+(-b)^2) ≤ rho0 := by nlinarith [neg_le_abs b]
  have hp := mul_nonneg
    (show 0 ≤ rho0-(31/100)*(-b+(-b)^2)-a by linarith) hcos
  have hcoef : 1+(-b)+transverseLimit d ≤ 29/20 := by linarith
  have hm := mul_le_mul_of_nonneg_right hcoef hcos
  have hmargin : 0 ≤ Real.sin (d+v)-(31/100)*(1+(-b)+transverseLimit d)*Real.cos (d+v) := by
    nlinarith [Real.cos_le_one (d+v)]
  have hproj := mul_nonneg (sub_nonneg.mpr hx) hmargin
  dsimp [radialLimit]
  nlinarith only [hp,hproj]

private lemma southDefect_antitone_d {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 5/8) :
    AntitoneOn (fun d => southDefect d v) (Set.Icc (1/2) (Real.pi/4)) := by
  let derivF : ℝ → ℝ := fun d =>
    ((527/10000)*(1+2*transverseLimit d)+transverseLimit d-1/2)*Real.cos (d+v)-
      (radialLimit d-1/2+17/100)*Real.sin (d+v)
  have hU (d : ℝ) : HasDerivAt transverseLimit (-(17/100)) d := by
    have h := ((hasDerivAt_id' d).const_mul (17/100 : ℝ)).const_sub (31/100 : ℝ)
    simp only [mul_one] at h
    exact h
  have hA (d : ℝ) : HasDerivAt radialLimit ((527/10000)*(1+2*transverseLimit d)) d := by
    have h := (((hU d).fun_add ((hU d).fun_pow 2)).const_mul (31/100 : ℝ)).const_sub rho0
    refine h.congr_deriv ?_
    norm_num
    ring
  have hf (d : ℝ) : HasDerivAt (fun x => southDefect x v) (derivF d) d := by
    have ht : HasDerivAt (fun x => x + v) 1 d := (hasDerivAt_id' d).add_const v
    have h1 := ((hA d).sub_const (1/2)).fun_mul ht.cos
    have h2 := ((hU d).sub_const (1/2)).fun_mul ht.sin
    have h := (h1.const_add (c0+rho0*halfRatio v-1/2)).fun_add h2
    refine h.congr_deriv ?_
    simp only [derivF]
    ring
  apply antiOn_of_hasDeriv_nonpos (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun d _ => hf d)
  intro d hd
  obtain ⟨hu0,hu,ha⟩ := limit_bounds ⟨hd.1.le,hd.2.le⟩
  obtain ⟨hcos,hsin⟩ := angle_sum_trig ⟨hd.1.le,hd.2.le⟩ hv
  have hleft := mul_nonpos_of_nonpos_of_nonneg
    (show (527/10000)*(1+2*transverseLimit d)+transverseLimit d-1/2 ≤ 0 by linarith) hcos
  have hright := mul_nonneg (show 0 ≤ radialLimit d-1/2+17/100 by linarith)
    (show 0 ≤ Real.sin (d+v) by linarith)
  dsimp [derivF]
  linarith

private lemma southDefect_left_negative {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 5/8) :
    southDefect (1/2) v < 0 := by
  have hv' : 0 ≤ v ∧ v ≤ 4/5 := ⟨hv.1,by linarith [hv.2]⟩
  have ht0 := halfRatio_nonnegative hv'
  have ht := halfRatio_upper hv'
  have hc0 : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,Real.pi_pos],by linarith [hv.2,Real.pi_gt_d2]⟩
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hcosSum := (angle_sum_trig (d := 1/2) ⟨le_rfl,by linarith [Real.pi_gt_d2]⟩ hv).1
  have hA : radialLimit (1/2)-1/2 ≤ 84409/160000 := by
    dsimp [radialLimit,transverseLimit]
    linarith [rho0_bounds.2]
  have hAs := mul_le_mul_of_nonneg_right hA hcosSum
  have hT := mul_le_mul_of_nonneg_right (show rho0 ≤ 1113/1000 by linarith [rho0_bounds.2]) ht0
  have hTv := mul_le_mul_of_nonneg_left ht (show (0:ℝ) ≤ 1113/1000 by norm_num)
  have hch := cos_upper_four (x := (1:ℝ)/2) (by norm_num)
  have hcl := Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/2)
  have hsl := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
  have hcoefC : (84409/160000)*Real.cos (1/2)-(11/40)*Real.sin (1/2) ≤ 83/250 := by
    nlinarith only [hch,hsl]
  have hcoefS : 493/1000 ≤ (84409/160000)*Real.sin (1/2)+(11/40)*Real.cos (1/2) := by
    nlinarith only [hcl,hsl]
  have hcM := mul_le_mul_of_nonneg_right hcoefC hc0
  have hsM := mul_le_mul_of_nonneg_right hcoefS hs0
  have htrig : (84409/160000)*Real.cos (1/2+v)-(11/40)*Real.sin (1/2+v) ≤
      (83/250)*Real.cos v-(493/1000)*Real.sin v := by
    rw [Real.cos_add,Real.sin_add]
    nlinarith only [hcM,hsM]
  have hupper : southDefect (1/2) v ≤
      -387/1000+(12243/20000)*v+(83/250)*Real.cos v-(493/1000)*Real.sin v := by
    have hc : c0 ≤ 113/1000 := by dsimp [c0]; linarith [rho0_bounds.2]
    dsimp [southDefect,transverseLimit] at *
    nlinarith only [hc,hAs,hT,hTv,htrig]
  have hcv := cos_upper_four hv.1
  have hsv := Real.sin_ge_sub_cube hv.1
  have hv2 : v^2 ≤ 25/64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) (show 0 ≤ (5:ℝ)/8+v by linarith [hv.1])]
  have hv3 := mul_le_mul hv.2 hv2 (sq_nonneg v) (by norm_num : (0:ℝ) ≤ 5/8)
  have hv4 := mul_le_mul hv2 hv2 (sq_nonneg v) (by norm_num : (0:ℝ) ≤ 25/64)
  have hcomplete := sq_nonneg ((83/500)*v-2383/40000)
  nlinarith only [hupper,hcv,hsv,hv3,hv4,hcomplete]

private lemma southDefect_negative {d v : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (hv : 0 ≤ v ∧ v ≤ 5/8) : southDefect d v < 0 := by
  have hm := southDefect_antitone_d hv
    (show (1:ℝ)/2 ∈ Set.Icc (1/2) (Real.pi/4) by constructor <;> linarith [Real.pi_gt_d2])
    hd hd.1
  exact hm.trans_lt (southDefect_left_negative hv)

/-- If S, at the phase `3π/2 - v` with `0 < v ≤ 5/8`, is separated from C along
its own axis but not along the south side of C, then
`b < c_x + tan (v/2) (a - c_y)`: the difference of the two margins is
`(1 - cos v)(a - c_y) - sin v (b - c_x)`. -/
private lemma own_south_transverse_upper {v a b cx cy : ℝ}
    (hv : 0 < v ∧ v ≤ 5/8)
    (hown : 0 ≤ centralMargin .own (3*Real.pi/2-v) a b cx cy)
    (hcard : centralMargin .south (3*Real.pi/2-v) a b cx cy < 0) :
    b < cx+halfRatio v*(a-cy) := by
  have hdiff : centralMargin .own (3*Real.pi/2-v) a b cx cy-
      centralMargin .south (3*Real.pi/2-v) a b cx cy=
      (1-Real.cos v)*(a-cy)-Real.sin v*(b-cx) := by
    simp only [centralMargin,centralNormal,centerY,Real.cos_sub,Real.sin_sub,
      south_cos,south_sin]
    ring
  have hid := (halfRatio_identities ⟨hv.1.le,by linarith [hv.2]⟩).2
  have hs := Real.sin_pos_of_pos_of_lt_pi hv.1 (by linarith [hv.2,Real.pi_gt_three])
  by_contra! hb
  have hn := mul_nonneg hs.le (show 0 ≤ b-cx-halfRatio v*(a-cy) by linarith)
  have hm := congrArg (fun z : ℝ => (a-cy)*z) hid
  nlinarith only [hown,hcard,hdiff,hm,hn]

private lemma south_diagonal_secondary_excluded {v d a b cx cy z : ℝ}
    (hv : 0 < v ∧ v ≤ 5/8) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hcx : cx ≤ c0) (hcy0 : 0 ≤ cy)
    (hown : 0 ≤ centralMargin .own (3*Real.pi/2-v) a b cx cy)
    (hcard : centralMargin .south (3*Real.pi/2-v) a b cx cy < 0)
    (hz : z ≤ transverseLimit d) :
    a*Real.cos (d+v)+b*Real.sin (d+v)+z <
      (1+Real.cos (d+v)+Real.sin (d+v))/2 := by
  have hv' : 0 ≤ v ∧ v ≤ 4/5 := ⟨hv.1.le,by linarith [hv.2]⟩
  have hids := halfRatio_identities hv'
  have ht0 := halfRatio_nonnegative hv'
  have ht := halfRatio_upper hv'
  have hcV : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,Real.pi_pos],by linarith [hv.2,Real.pi_gt_d2]⟩
  have hsV := Real.sin_nonneg_of_nonneg_of_le_pi hv.1.le (by linarith [hv.2,Real.pi_gt_d2])
  have hDtrig := east_quadrant_trig (by linarith [hd.1]) hd.2
  have hsD := hDtrig.2.1
  let alpha := Real.cos d-halfRatio v*Real.sin d
  have ha : 0 ≤ alpha := by
    have hp := mul_le_mul_of_nonneg_right (show halfRatio v ≤ 1/2 by linarith [hv.2]) hsD
    dsimp [alpha]
    linarith [hDtrig.1,hDtrig.2.2]
  have hb := own_south_transverse_upper hv hown hcard
  have hcap : a*Real.cos v+b*Real.sin v ≤
      1/2-cy+(Real.cos v+Real.sin v)/2 := by
    simp only [centralMargin,centerY,angularWidth,Real.cos_sub,Real.sin_sub,
      south_cos,south_sin,zero_mul,neg_one_mul,zero_add,sub_zero,abs_neg,
      abs_of_nonneg hcV,abs_of_nonneg hsV] at hcard
    linarith
  have hp := mul_le_mul_of_nonneg_left hcap ha
  have htB := mul_le_mul_of_nonneg_left
    (show b-halfRatio v*a ≤ cx-halfRatio v*cy by nlinarith only [hb]) hsD
  have hproj : a*Real.cos (d+v)+b*Real.sin (d+v) =
      alpha*(a*Real.cos v+b*Real.sin v)+Real.sin d*(b-halfRatio v*a) := by
    rw [Real.cos_add,Real.sin_add]
    dsimp [alpha]
    linear_combination a*Real.sin d*hids.1+b*Real.sin d*hids.2
  have hboundary : alpha*(1/2-cy+(Real.cos v+Real.sin v)/2)+
      Real.sin d*(cx-halfRatio v*cy)-(Real.cos (d+v)+Real.sin (d+v))/2 =
      (Real.cos d-Real.sin d)/2+cx*Real.sin d-cy*Real.cos d := by
    rw [Real.cos_add,Real.sin_add]
    dsimp [alpha]
    linear_combination -(Real.sin d/2)*hids.1-(Real.sin d/2)*hids.2
  have hcxM := mul_le_mul_of_nonneg_right hcx hsD
  have hcyM := mul_nonneg hcy0 (show 0 ≤ Real.cos d by linarith [hDtrig.1])
  have hcMon := Real.cos_le_cos_of_nonneg_of_le_pi (show (0:ℝ) ≤ 1/2 by norm_num)
    (show d ≤ Real.pi by linarith [hd.2,Real.pi_pos]) hd.1
  have hsMon := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/2 by linarith [Real.pi_pos])
    (show d ≤ Real.pi/2 by linarith [hd.2,Real.pi_pos]) hd.1
  have hcHalf := cos_upper_four (x := (1:ℝ)/2) (by norm_num)
  have hsHalf := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
  have hcore : 387/1000 ≤ 1/2-c0 := by dsimp [c0]; linarith [rho0_bounds.2]
  have hsin := mul_le_mul hcore
    (show 23/48 ≤ Real.sin d by nlinarith) (by norm_num : (0:ℝ) ≤ 23/48)
    (show 0 ≤ 1/2-c0 by linarith)
  have hz' : z ≤ 9/40 := hz.trans (limit_bounds hd).2.1
  nlinarith only [hp,htB,hproj,hboundary,hcxM,hcyM,hcMon,hcHalf,hsin,hz']

/-- If S is not separated from C along the south side of C, its phase exceeds
`3π/2`. -/
theorem own_south_positive {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownAxis 4=true) : 0 < P.deviation 4 := by
  have hcard := (P.toPinPacking.ownAxis_eq_true 4).mp hown
  change centralMargin .south (P.phase 4) (P.radial 4) (P.transverse 4)
    P.center.1 P.center.2 < 0 at hcard
  have hS := P.own_separator 4 hown
  have hSphase := P.phase_from_deviation 4
  have hmc : cardinalCenter (matchingCardinal 4) = 3*Real.pi/2 := rfl
  by_contra! hs
  by_cases hs0 : P.deviation 4=0
  · rw [hSphase,hs0,add_zero,hmc] at hS hcard
    simp only [centralMargin,centralNormal,centerY,angularWidth,south_cos,south_sin,
      mul_zero,mul_neg_one,add_zero,zero_add,abs_zero,abs_neg,abs_one] at hS hcard
    linarith
  have hsneg : P.deviation 4 < 0 := lt_of_le_of_ne hs hs0
  let v := -P.deviation 4
  let d := P.diagonalAngle
  have hv : 0 < v ∧ v ≤ 5/8 := by
    dsimp [v]
    constructor <;> linarith [P.deviation_windows.2.2.2.1]
  have hd : 1/2 ≤ d ∧ d ≤ Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hSP : P.phase 4=3*Real.pi/2-v := by rw [hSphase,hmc]; dsimp [v]; ring
  have hDP : P.phase 3=Real.pi+d := by dsimp [d,NormalizedPacking.diagonalAngle]; ring
  have hq : P.phase 4-P.phase 3=Real.pi/2-(d+v) := by rw [hSP,hDP]; ring
  have htrig := angle_sum_trig hd ⟨hv.1.le,hv.2⟩
  have hs0' : 0 ≤ Real.sin (d+v) := by linarith [htrig.2]
  have hz : |P.transverse 3| ≤ transverseLimit d := (normalized_diagonal_transverse_affine P).le
  have hsown : 0 ≤ centralMargin .own (3*Real.pi/2-v) (P.radial 4) (P.transverse 4)
      P.center.1 P.center.2 := by simpa only [hSP] using hS
  have hscard : centralMargin .south (3*Real.pi/2-v) (P.radial 4) (P.transverse 4)
      P.center.1 P.center.2 < 0 := by simpa only [hSP] using hcard
  rcases south_secondary_choice P with hD | hwing
  · have hbad := south_diagonal_secondary_excluded hv hd P.box.1.2 P.box.2.1 hsown hscard
      ((neg_le_abs _).trans hz)
    change SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at hD
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_left,hq,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,angularWidth,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,
      abs_of_nonneg htrig.1,abs_of_nonneg hs0'] at hD
    nlinarith only [hD,hbad]
  · have hb := own_south_transverse_upper hv hsown hscard
    have ht0 := halfRatio_nonnegative ⟨hv.1.le,by linarith [hv.2]⟩
    have hr := mul_nonneg
      (show 0 ≤ rho0-(P.radial 4-P.center.2) by linarith [(P.contained 4).a_le_rho0,P.box.2.1]) ht0
    have hbu : P.transverse 4 < c0+rho0*halfRatio v := by nlinarith [P.box.1.2]
    have hproj := diagonal_projection_upper (P.contained 3) hd ⟨hv.1.le,hv.2⟩ hz
    have hnegative := southDefect_negative hd ⟨hv.1.le,hv.2⟩
    change SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at hwing
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_right,hq,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,angularWidth,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,
      abs_of_nonneg htrig.1,abs_of_nonneg hs0'] at hwing
    dsimp [southDefect] at hnegative
    nlinarith only [hwing,hbu,hproj,hnegative]

/-! ### Two own wings -/

/-- The sum of the separating inequalities of W and S along their own axes, which
share the centre of C, bounds `a_W + a_S` below. -/
lemma coupled_own_wing_radial_sum {v s aw bw aS bS cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 2/3)
    (hx : cx ≤ c0) (hy : cy ≤ c0)
    (hW : 0 ≤ centralMargin .own (Real.pi-v) aw bw cx cy)
    (hS : 0 ≤ centralMargin .own (3*Real.pi/2+s) aS bS cx cy) :
    1+(387/1000)*(Real.cos v+Real.cos s)+(61/100)*(Real.sin v+Real.sin s) ≤ aw+aS := by
  obtain ⟨hcv,hsv0,hsv⟩ := small_angle_nonneg hv (by norm_num)
  obtain ⟨hcs,hss0,hss⟩ := small_angle_nonneg hs (by norm_num)
  have hcv0 : 0 ≤ Real.cos v := by linarith
  have hcs0 : 0 ≤ Real.cos s := by linarith
  have hX := mul_nonneg (sub_nonneg.mpr hx)
    (show 0 ≤ Real.cos v-Real.sin s by linarith)
  have hY := mul_nonneg (sub_nonneg.mpr hy)
    (show 0 ≤ Real.cos s-Real.sin v by linarith)
  have hL : 387/1000 ≤ 1/2-c0 := by dsimp [c0]; linarith [rho0_bounds.2]
  have hU : 61/100 ≤ 1/2+c0 := by dsimp [c0]; linarith [rho0_bounds.1]
  have hC := mul_nonneg (sub_nonneg.mpr hL)
    (show 0 ≤ Real.cos v+Real.cos s by linarith)
  have hT := mul_nonneg (sub_nonneg.mpr hU) (add_nonneg hsv0 hss0)
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    abs_neg,abs_of_nonneg hcv0,abs_of_nonneg hsv0] at hW
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
    south_cos,south_sin,zero_mul,neg_one_mul,zero_sub,neg_neg,add_zero,abs_neg,
    abs_of_nonneg hcs0,abs_of_nonneg hss0] at hS
  nlinarith only [hW,hS,hX,hY,hC,hT]

/-- On `[22/75, 2/3]` the radial profile of an own wing lies above
`941/1000 + (9/25) x`: it is concave there and above the line at both ends. -/
private lemma own_wing_profile_line {x : ℝ} (hx : 22/75 ≤ x ∧ x ≤ 2/3) :
    941/1000+(9/25)*x < 1/2+(387/1000)*Real.cos x+(61/100)*Real.sin x := by
  have hl := trig_bracket (l := 22/75) (u := 22/75) (x := 22/75) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  have hu := trig_bracket (l := 2/3) (u := 2/3) (x := 2/3) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  norm_num at hl hu
  have h := trig_concave_gt (α := -(9/25)) (A := 61/100) (B := 387/1000)
    (m := 441/1000) (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Real.pi_gt_three]) hx (by linarith) (by linarith)
  linarith

/-- If W and S are both separated from C along their own axes, then
`s - w < 24/25`: otherwise both angles lie in `[22/75, 2/3]`, and the sum of
the two separating inequalities forces `a_W + a_S > 2ρ0`. -/
theorem normalized_own_wing_angle_sum {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownAxis 2=true) (hS : P.ownAxis 4=true) :
    P.deviation 4-P.deviation 2 < 24/25 := by
  let v := -P.deviation 2
  let s := P.deviation 4
  have hv : 0 ≤ v ∧ v ≤ 2/3 := by
    have hneg := own_west_negative P hW
    dsimp [v]
    constructor <;> linarith [P.deviation_windows.2.2.1.1]
  have hsupper : s ≤ 2/3 := P.deviation_windows.2.2.2.2.le
  by_contra! hlarge
  have hsum : 24/25 ≤ v+s := by dsimp [v,s]; linarith
  have hWphase : P.phase 2=Real.pi-v := by
    have hc : cardinalCenter (matchingCardinal 2)=Real.pi := rfl
    rw [P.phase_from_deviation 2,hc]
    dsimp [v]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hrad := coupled_own_wing_radial_sum hv ⟨by linarith,hsupper⟩ P.box.1.2 P.box.2.2
    (by simpa only [hWphase] using P.own_separator 2 hW)
    (by simpa only [hSphase] using P.own_separator 4 hS)
  have hleft := own_wing_profile_line ⟨by linarith,hv.2⟩
  have hright := own_wing_profile_line ⟨by linarith,hsupper⟩
  linarith [(P.contained 2).a_le_rho0,(P.contained 4).a_le_rho0,rho0_bounds.2]

end SquaresInCircles.Six
