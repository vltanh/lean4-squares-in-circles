module
public import SquaresInCircles.Six.Analytic.SecondaryReduction
public import SquaresInCircles.Six.Analytic.OwnWingProfileSharpening
public import SquaresInCircles.Six.Analytic.HighDiagonalAffineTransverse

@[expose] public section

/-!
# Canonical OWN S has positive deviation

This is not obtained by reflecting W while preserving D's half-window. For
s=-v<0, the actual south cardinal margin and the OWN/cardinal difference imply
  bS < cx + halfRatio(v) * (aS-cy).
The two forward secondary D/S sources are excluded directly in that frame.

For the D source, a positive combination of those two inequalities cancels
v exactly. For the S source, the high-D transverse profile and far-corner
quadratic give a scalar upper bound which decreases in d. At d=1/2, the
remaining whole-interval inequality follows from Taylor bounds and one
completed square. No grid, stress table or candidate-edge premise is used.

Thus the former conditional OWN-S lower tail is proved with the stronger
conclusion s>0. The upper tail and the mixed positive-S cases remain separate.
Compilation remains deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
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
  exact ⟨hu0,hu,by dsimp [radialLimit]; nlinarith [rho0_lower]⟩

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

private lemma high_D_projection {a b d v : ℝ}
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
    convert (hasDerivAt_const d (31/100)).sub ((hasDerivAt_id d).const_mul (17/100)) using 1 <;>
      dsimp [transverseLimit] <;> ring
  have hA (d : ℝ) : HasDerivAt radialLimit ((527/10000)*(1+2*transverseLimit d)) d := by
    convert (hasDerivAt_const d rho0).sub (((hU d).add ((hU d).pow 2)).const_mul (31/100)) using 1 <;>
      dsimp [radialLimit] <;> ring
  have hf (d : ℝ) : HasDerivAt (fun x => southDefect x v) (derivF d) d := by
    have ht := (hasDerivAt_id d).add_const v
    convert ((((hA d).sub_const (1/2)).mul ht.cos).const_add
      (c0+rho0*halfRatio v-1/2)).add (((hU d).sub_const (1/2)).mul ht.sin) using 1 <;>
      dsimp [southDefect,derivF] <;> ring
  apply Seven.antiOn_of_hasDeriv_nonpos (by dsimp [southDefect,radialLimit,transverseLimit]; fun_prop)
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
    linarith [rho0_upper]
  have hAs := mul_le_mul_of_nonneg_right hA hcosSum
  have hT := mul_le_mul_of_nonneg_right rho0_upper.le ht0
  have hTv := mul_le_mul_of_nonneg_left ht (show (0:ℝ) ≤ 1113/1000 by norm_num)
  have hch := Seven.cos_upper_four (x := (1:ℝ)/2) (by norm_num)
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
    have hc : c0 ≤ 113/1000 := by dsimp [c0]; linarith [rho0_upper]
    dsimp [southDefect,transverseLimit] at *
    nlinarith only [hc,hAs,hT,hTv,htrig]
  have hcv := Seven.cos_upper_four hv.1
  have hsv := Real.sin_ge_sub_cube hv.1
  have hv2 : v^2 ≤ 25/64 := by nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)
    (show 0 ≤ (5:ℝ)/8+v by linarith [hv.1])]
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

private lemma canonical_south_upper {v a b cx cy : ℝ}
    (hv : 0 < v ∧ v ≤ 5/8)
    (hown : 0 ≤ centralMargin .own (3*Real.pi/2-v) a b cx cy)
    (hcard : centralMargin .south (3*Real.pi/2-v) a b cx cy < 0) :
    b < cx+halfRatio v*(a-cy) := by
  have ho : 0 ≤ centralMargin .own (Real.pi+v) a (-b) cy cx := by
    have h := south_own_as_west (-v) a b cx cy
    simp only [sub_neg_eq_add,add_neg_eq_sub] at h
    rw [h]
    exact hown
  have hc : centralMargin .west (Real.pi+v) a (-b) cy cx < 0 := by
    have h := south_cardinal_as_west (-v) a b cx cy
    simp only [sub_neg_eq_add,add_neg_eq_sub] at h
    rw [h]
    exact hcard
  have h := canonical_west_transverse_lower ⟨hv.1,by linarith [hv.2]⟩ ho hc
  linarith

private lemma Dsource_canonical_south {v d a b cx cy z : ℝ}
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
  have hb := canonical_south_upper hv hown hcard
  have hcap : a*Real.cos v+b*Real.sin v ≤
      1/2-cy+(Real.cos v+Real.sin v)/2 := by
    simp only [centralMargin,centerY,angularWidth,Real.cos_sub,Real.sin_sub,
      south_cos,south_sin,zero_mul,one_mul,neg_one_mul,zero_add,add_zero,
      sub_zero,zero_sub,neg_neg,abs_neg,abs_of_nonneg hcV,abs_of_nonneg hsV] at hcard
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
  have hcHalf := Seven.cos_upper_four (x := (1:ℝ)/2) (by norm_num)
  have hsHalf := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
  have hcore : 387/1000 ≤ 1/2-c0 := by dsimp [c0]; linarith [rho0_upper]
  have hsin := mul_le_mul hcore
    (show 23/48 ≤ Real.sin d by nlinarith) (by norm_num : (0:ℝ) ≤ 23/48)
    (show 0 ≤ 1/2-c0 by linarith)
  have hz' : z ≤ 9/40 := hz.trans (limit_bounds hd).2.1
  nlinarith only [hp,htB,hproj,hboundary,hcxM,hcyM,hcMon,hcHalf,hsin,hz']

/-- This closes the OWN-S lower tail with the stronger strict sign. -/
theorem canonical_own_south_positive {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownBits 4=true) : 0 < P.helperAngle 4 := by
  have hcard := (P.toPinPacking.canonicalOwn_eq_true 4).mp hown
  change centralMargin .south (P.phase 4) (P.radial 4) (P.transverse 4)
    P.center.1 P.center.2 < 0 at hcard
  have hS := P.own_separator 4 hown
  have hSphase := P.phase_from_deviation 4
  by_contra! hs
  by_cases hs0 : P.helperAngle 4=0
  · rw [hSphase,hs0,add_zero] at hS hcard
    simp only [centralMargin,centralNormal,centerY,angularWidth,south_cos,south_sin,
      mul_zero,mul_neg_one,zero_mul,neg_one_mul,add_zero,zero_add,sub_zero,
      neg_neg,abs_zero,abs_neg,abs_one] at hS hcard
    linarith
  have hsneg : P.helperAngle 4 < 0 := lt_of_le_of_ne hs hs0
  let v := -P.helperAngle 4
  let d := P.diagonalAngle
  have hv : 0 < v ∧ v ≤ 5/8 := by
    dsimp [v]
    constructor <;> linarith [P.helper_windows.2.2.2.1]
  have hd : 1/2 ≤ d ∧ d ≤ Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hSP : P.phase 4=3*Real.pi/2-v := by rw [hSphase]; dsimp [v]; ring
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
  · have hbad := Dsource_canonical_south hv hd P.box.1.2 P.box.2.1 hsown hscard
      ((neg_le_abs _).trans hz)
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at hD
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_left,hq,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,angularWidth,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,
      abs_of_nonneg htrig.1,abs_of_nonneg hs0'] at hD
    nlinarith only [hD,hbad]
  · have hb := canonical_south_upper hv hsown hscard
    have ht0 := halfRatio_nonnegative ⟨hv.1.le,by linarith [hv.2]⟩
    have hr := mul_nonneg
      (show 0 ≤ rho0-(P.radial 4-P.center.2) by linarith [(P.contained 4).a_le_rho0,P.box.2.1]) ht0
    have hbu : P.transverse 4 < c0+rho0*halfRatio v := by nlinarith [P.box.1.2]
    have hproj := high_D_projection (P.contained 3) hd ⟨hv.1.le,hv.2⟩ hz
    have hnegative := southDefect_negative hd ⟨hv.1.le,hv.2⟩
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at hwing
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_right,hq,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,angularWidth,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,
      abs_of_nonneg htrig.1,abs_of_nonneg hs0'] at hwing
    dsimp [southDefect] at hnegative
    nlinarith only [hwing,hbu,hproj,hnegative]

end SquaresInCircles.Six.Analytic
