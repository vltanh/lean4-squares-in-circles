import SquaresInCircles.Common.Trigonometry
import SquaresInCircles.Six.Separators.Axes

/-!
# Six squares: W on its own axis turns away from D

If W is separated from C along its own axis but not along the west side of C,
its phase is `π + w` with `w < 0`. At `w = 0` the two margins agree; for
`w > 0` their difference gives `b > -c_y - tan (w/2) (a - c_x)` for the chart
`(a, b)` of W and the centre `(c_x, c_y)` of C. D, at the phase `π + d` with
`w ≤ d ≤ π/4` and separated from C along its own axis, has
`|b_D| + (cos d + sin d)/2 < 97/100`, since its far corner lies in the disk, by
a quadratic in `cos d + sin d - 1` with positive coefficients. Taylor bounds
and monotonicity then exclude both separations of W and D along a secondary
axis.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-- A square at the phase `π + d`, `0 ≤ d ≤ π/4`, separated from C along its
primary axis has `|b| + (cos d + sin d)/2 < 97/100`. -/
theorem diagonal_transverse_profile {a b cx cy d : ℝ}
    (hc : ContainedChart a |b|) (hx : cx≤c0) (hy : cy≤c0)
    (hd : 0≤d ∧ d≤Real.pi/4)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    |b|+(Real.cos d+Real.sin d)/2<97/100 := by
  have hcd : 0≤Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_pos]⟩
  have hsd := Real.sin_nonneg_of_nonneg_of_le_pi hd.1 (by linarith [hd.2,Real.pi_pos])
  let v := Real.cos d+Real.sin d
  have hv0 : 1≤v := by
    simpa only [v,abs_of_nonneg hcd,abs_of_nonneg hsd] using one_le_abs_cos_add_abs_sin d
  have hv1 : v≤3/2 := by
    dsimp [v]
    nlinarith [Real.sin_sq_add_cos_sq d,sq_nonneg (Real.cos d-Real.sin d)]
  have hcx := mul_nonneg (show 0≤1/2-cx-77/200 by linarith [c0_bounds.2]) hcd
  have hcy := mul_nonneg (show 0≤1/2-cy-77/200 by linarith [c0_bounds.2]) hsd
  rw [add_comm Real.pi d] at hown
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_add_pi,Real.sin_add_pi,
    abs_neg,abs_of_nonneg hcd,abs_of_nonneg hsd] at hown
  have hA : 1+(77/200)*v≤a+1/2 := by dsimp [v]; nlinarith only [hown,hcx,hcy]
  by_contra! hbad
  have hB : 147/100-v/2≤|b|+1/2 := by dsimp [v]; linarith
  have hA0 : 0≤1+(77/200)*v := by linarith
  have hB0 : 0≤147/100-v/2 := by linarith
  have hAsq := mul_nonneg (sub_nonneg.mpr hA)
    (show 0≤a+1/2+(1+(77/200)*v) by linarith [hc.half_le])
  have hBsq := mul_nonneg (sub_nonneg.mpr hB)
    (show 0≤|b|+1/2+(147/100-v/2) by linarith [abs_nonneg b])
  have hid : (1+(77/200)*v)^2+(147/100-v/2)^2-Q0=
      (15929/40000)*(v-1)^2+(1929/20000)*(v-1)+1589/200000 := by
    norm_num [Q0]
    ring
  have hpositive : Q0<(1+(77/200)*v)^2+(147/100-v/2)^2 := by
    nlinarith [sq_nonneg (v-1)]
  nlinarith [hc.containment]

/-- The inequality against a separation of W and D along the secondary axis of
W. -/
theorem west_secondary_reserve {w d : ℝ}
    (hw : 0≤w) (hwd : w≤d) (hd : d≤Real.pi/4) :
    113/1000+(1113/1000)*(Real.sin (d-w)+halfRatio w)+
        (97/100-(Real.cos d+Real.sin d)/2)*Real.cos (d-w)<
      (1+Real.cos (d-w)+Real.sin (d-w))/2 := by
  let q := d-w
  have hd0 : 0≤d := hw.trans hwd
  have hd1 : d≤4/5 := by linarith [Real.pi_lt_d2]
  have hq0 : 0≤q := by dsimp [q]; linarith
  have hqd : q≤d := by dsimp [q]; linarith
  have hq1 : q≤4/5 := hqd.trans hd1
  have htp := halfRatio_upper ⟨hw,hwd.trans hd1⟩
  have hsum := (small_polynomial_trig ⟨hd0,hd1⟩).2.2.2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := q)
  have hsin := Real.sin_le hq0
  have hq2p := mul_nonneg (sub_nonneg.mpr hq1) (show 0≤4/5+q by linarith)
  have hq2 : q^2≤16/25 := by nlinarith
  let A := (Real.cos d+Real.sin d)/2-47/100
  have hA : 3/100+(6/25)*d≤A := by dsimp [A]; linarith
  have hA0 : 0≤A := by linarith
  have hC := mul_le_mul hA hcos (show 0≤1-q^2/2 by linarith) hA0
  have hS := mul_le_mul_of_nonneg_left hsin (show (0:ℝ)≤613/1000 by norm_num)
  have hT := mul_le_mul_of_nonneg_left htp (show (0:ℝ)≤1113/1000 by norm_num)
  let p := 417/1000-(373/1000)*d-(3/200)*d^2-(3/25)*d^3
  have hd2p := mul_nonneg (sub_nonneg.mpr hd1) (show 0≤4/5+d by linarith)
  have hd2 : d^2≤16/25 := by nlinarith
  have hd3p := mul_le_mul hd1 hd2 (sq_nonneg d) (by norm_num : (0:ℝ)≤4/5)
  have hd3 : d^3≤64/125 := by nlinarith only [hd3p]
  have hp : 1189/25000≤p := by dsimp [p]; linarith
  have hfactor : 0≤(d-q)*(2400*d^2+2400*d*q+300*d+300*q+17)/20000 := by
    apply div_nonneg
    · apply mul_nonneg (sub_nonneg.mpr hqd)
      positivity
    · norm_num
  have hid : 387/1000+(3/100+(6/25)*d)*(1-q^2/2)-(613/1000)*q-
        (1113/1000)*(11/20)*w=
      p+(d-q)*(2400*d^2+2400*d*q+300*d+300*q+17)/20000 := by
    dsimp [p,q]
    ring
  change 113/1000+(1113/1000)*(Real.sin q+halfRatio w)+
      (97/100-(Real.cos d+Real.sin d)/2)*Real.cos q<
      (1+Real.cos q+Real.sin q)/2
  dsimp [A] at hC
  nlinarith only [hC,hS,hT,hp,hfactor,hid]

/-- The inequality against a separation of W and D along the secondary axis of
D. -/
theorem diagonal_secondary_reserve {w d : ℝ}
    (hw : 0≤w) (hwd : w≤d) (hd : d≤Real.pi/4) :
    (97/100-(Real.cos d+Real.sin d)/2)+
        (1113/1000)*(Real.sin (d-w)+halfRatio w*Real.cos (d-w))+
        (113/1000)*Real.cos (d-w)<
      (1+Real.cos (d-w)+Real.sin (d-w))/2 := by
  let q := d-w
  have hd0 : 0≤d := hw.trans hwd
  have hd1 : d≤4/5 := by linarith [Real.pi_lt_d2]
  have hq0 : 0≤q := by dsimp [q]; linarith
  have hqd : q≤d := by dsimp [q]; linarith
  have hq1 : q≤4/5 := hqd.trans hd1
  have hcd := (small_polynomial_trig ⟨hd0,hd1⟩).1
  have hsd := (small_polynomial_trig ⟨hd0,hd1⟩).2.2.1
  have hcos := cosine_difference_lower hq0 hqd hd1
  have hsin := (le_abs_self _).trans
    ((Real.abs_sin_sub_sin_le d q).trans_eq (abs_of_nonneg (sub_nonneg.mpr hqd)))
  have hT := mul_le_mul_of_nonneg_right
    (halfRatio_lower ⟨hw,hwd.trans hd1⟩) (show 0≤Real.cos d by linarith)
  have hTm := mul_le_mul_of_nonneg_left hT (show (0:ℝ)≤1113/1000 by norm_num)
  have hCm := mul_le_mul_of_nonneg_left hcos (show (0:ℝ)≤387/1000 by norm_num)
  have hpow := mul_nonneg hd0 (sub_nonneg.mpr hd1)
  have hcdpoly := Real.one_sub_sq_div_two_le_cos (x := d)
  have hcdlin : 1-(2/5)*d≤Real.cos d := by nlinarith only [hpow,hcdpoly]
  let coef := (89/200)*(387/1000)*d-1/2+(1113/2000)*Real.cos d
  have hcoef : 0≤coef := by dsimp [coef]; linarith
  have hcp := mul_nonneg hw hcoef
  have hextra : 0≤(89/200)*(387/1000)*w*q := by positivity
  have hdiff : d^2-q^2=w*(d+q) := by dsimp [q]; ring
  have hsub : d-q=w := by dsimp [q]; ring
  have hB : 0≤(387/1000)*(Real.cos q-Real.cos d)+
      (1/2)*(Real.sin q-Real.sin d)+(1113/1000)*halfRatio w*Real.cos d := by
    rw [hsub] at hsin
    rw [hdiff] at hCm
    dsimp [coef] at hcp
    nlinarith only [hCm,hsin,hTm,hcp,hextra]
  have hbase : 1069/25000≤(887/1000)*Real.cos d-(113/1000)*Real.sin d-47/100 := by
    linarith
  rw [halfRatio_shift ⟨hw,hwd.trans hd1⟩]
  change (97/100-(Real.cos d+Real.sin d)/2)+
      (1113/1000)*(Real.sin d-halfRatio w*Real.cos d)+(113/1000)*Real.cos q<
      (1+Real.cos q+Real.sin q)/2
  nlinarith only [hB,hbase]

lemma own_west_transverse_lower {w a b cx cy : ℝ}
    (hw : 0<w ∧ w≤4/5)
    (hown : 0≤centralMargin .own (Real.pi+w) a b cx cy)
    (hcard : centralMargin .west (Real.pi+w) a b cx cy<0) :
    -cy-halfRatio w*(a-cx)<b := by
  have hdiff := own_sub_west_margin w a b cx cy
  have hid := (halfRatio_identities ⟨hw.1.le,hw.2⟩).2
  have hmult := congrArg (fun z : ℝ => (a-cx)*z) hid
  have hpos : 0<Real.sin w*(halfRatio w*(a-cx)+b+cy) := by
    nlinarith only [hown,hcard,hdiff,hmult]
  have hs : 0≤Real.sin w := Real.sin_nonneg_of_nonneg_of_le_pi hw.1.le
    (by linarith [hw.2,Real.pi_gt_d2])
  by_contra! hb
  have hn := mul_nonpos_of_nonneg_of_nonpos hs
    (show halfRatio w*(a-cx)+b+cy≤0 by linarith)
  linarith

private lemma west_coarse_transverse {w a b cx cy : ℝ}
    (hw : 0<w ∧ w≤4/5) (ha : a≤rho0) (hx0 : 0≤cx) (hy : cy≤c0)
    (hown : 0≤centralMargin .own (Real.pi+w) a b cx cy)
    (hcard : centralMargin .west (Real.pi+w) a b cx cy<0) :
    -(113/1000)-(1113/1000)*halfRatio w<b := by
  have hb := own_west_transverse_lower hw hown hcard
  have ht := halfRatio_nonnegative ⟨hw.1.le,hw.2⟩
  have hm := mul_le_mul_of_nonneg_left
    (show a-cx≤1113/1000 by linarith [rho0_bounds.2]) ht
  have hcy : cy≤113/1000 := by dsimp [c0] at hy; linarith [rho0_bounds.2]
  linarith

/-- For `0 ≤ w ≤ d ≤ π/4`, if W is separated from C along its primary axis but
not along the west side of C, and D along its primary axis, then W and D are not
separated along a secondary axis. -/
theorem west_nonnegative_impossible {w d aw bw ad bd cx cy : ℝ}
    (hw : 0≤w) (hwd : w≤d) (hd : d≤Real.pi/4)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hcx0 : 0≤cx) (hcx : cx≤c0) (hcy : cy≤c0)
    (hownW : 0≤centralMargin .own (Real.pi+w) aw bw cx cy)
    (hcardW : centralMargin .west (Real.pi+w) aw bw cx cy<0)
    (hownD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hsec : (1+Real.cos (d-w)+Real.sin (d-w))/2≤
        ad*Real.sin (d-w)+bd*Real.cos (d-w)-bw ∨
      (1+Real.cos (d-w)+Real.sin (d-w))/2≤
        bd+aw*Real.sin (d-w)-bw*Real.cos (d-w)) : False := by
  by_cases hw0 : w=0
  · subst w
    have hdiff := own_sub_west_margin 0 aw bw cx cy
    simp only [Real.cos_zero,Real.sin_zero,sub_self,zero_mul,add_zero] at hdiff hownW hcardW
    linarith
  have hwpos : 0<w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hw1 : w≤4/5 := by linarith [Real.pi_lt_d2]
  have hq : 0≤d-w ∧ d-w≤4/5 := by constructor <;> linarith [Real.pi_lt_d2]
  have htr := small_polynomial_trig hq
  have hsq : 0≤Real.sin (d-w) := by nlinarith [htr.2.1,hq.1]
  have hcq : 0≤Real.cos (d-w) := by linarith [htr.1]
  have hbW := west_coarse_transverse ⟨hwpos,hw1⟩ hW.a_le_rho0 hcx0 hcy hownW hcardW
  have hbD := diagonal_transverse_profile hD hcx hcy ⟨hw.trans hwd,hd⟩ hownD
  have hDtrans : bd≤97/100-(Real.cos d+Real.sin d)/2 := by
    linarith [le_abs_self bd]
  have hDproj := mul_le_mul_of_nonneg_right hDtrans hcq
  have hDrad := mul_le_mul_of_nonneg_right
    (show ad≤1113/1000 by linarith [hD.a_le_rho0,rho0_bounds.2]) hsq
  rcases hsec with hsec | hsec
  · have hbound := west_secondary_reserve hw hwd hd
    nlinarith only [hsec,hbound,hDproj,hDrad,hbW]
  · have ht := halfRatio_nonnegative ⟨hw,hw1⟩
    have hcoeff : 0≤Real.sin (d-w)+halfRatio w*Real.cos (d-w) :=
      add_nonneg hsq (mul_nonneg ht hcq)
    have hWrad := mul_le_mul_of_nonneg_right
      (show aw≤1113/1000 by linarith [hW.a_le_rho0,rho0_bounds.2]) hcoeff
    have hb := own_west_transverse_lower ⟨hwpos,hw1⟩ hownW hcardW
    have hbwcos := mul_le_mul_of_nonneg_right hb.le hcq
    have hcentral : cy-halfRatio w*cx≤113/1000 := by
      have hprod := mul_nonneg ht hcx0
      dsimp [c0] at hcy
      linarith [rho0_bounds.2]
    have hccos := mul_le_mul_of_nonneg_right hcentral hcq
    have hbound := diagonal_secondary_reserve hw hwd hd
    nlinarith only [hsec,hbound,hDtrans,hWrad,hbwcos,hccos]

/-- If W is not separated from C along the west side of C, its phase is less
than `π`. -/
theorem own_west_negative {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownAxis 2=true) : P.deviation 2<0 := by
  by_contra! hw
  let w := P.deviation 2
  let d := P.diagonalAngle
  have hWphase : P.phase 2=Real.pi+w := P.phase_from_deviation 2
  have hDphase : P.phase 3=Real.pi+d := by dsimp [d,NormalizedPacking.diagonalAngle]; ring
  have hwd : w≤d := by
    have hh := P.primary_order.2.2.1
    rw [hWphase,hDphase] at hh
    linarith
  have hd : d≤Real.pi/4 := P.diagonal_angle_range.2
  have hq : 0≤d-w ∧ d-w≤Real.pi/2 := by
    constructor <;> linarith [Real.pi_pos]
  have hcq := Real.cos_nonneg_of_mem_Icc
    (show d-w∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_pos])
  have hsq := Real.sin_nonneg_of_nonneg_of_le_pi hq.1
    (by linarith [hq.2,Real.pi_pos])
  have hcW : centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2)
      P.center.1 P.center.2<0 :=
    (P.toPinPacking.ownAxis_eq_true 2).mp hown
  obtain ⟨k,hsep,hcases⟩ := westDiagonal_secondary P
  have hsecondary : (1+Real.cos (d-w)+Real.sin (d-w))/2≤
        P.radial 3*Real.sin (d-w)+P.transverse 3*Real.cos (d-w)-P.transverse 2 ∨
      (1+Real.cos (d-w)+Real.sin (d-w))/2≤
        P.transverse 3+P.radial 2*Real.sin (d-w)-P.transverse 2*Real.cos (d-w) := by
    rcases hcases with rfl | rfl
    · left
      change SAT.threshold (P.square 2) (P.square 3)≤
        frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at hsep
      rw [P.square_def 2,P.square_def 3,hWphase,hDphase,
        oriented_pair_threshold,pair_frameY_left,
        show (Real.pi+d)-(Real.pi+w)=d-w by ring,
        angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hsep
      linarith
    · right
      change SAT.threshold (P.square 2) (P.square 3)≤
        frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
      rw [P.square_def 2,P.square_def 3,hWphase,hDphase,
        oriented_pair_threshold,pair_frameY_right,
        show (Real.pi+d)-(Real.pi+w)=d-w by ring,
        angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hsep
      linarith
  exact west_nonnegative_impossible hw hwd hd (P.contained 2) (P.contained 3)
    P.box.1.1 P.box.1.2 P.box.2.2
    (by simpa only [hWphase] using P.own_separator 2 hown)
    (by simpa only [hWphase] using hcW)
    (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own) hsecondary

end SquaresInCircles.Six
