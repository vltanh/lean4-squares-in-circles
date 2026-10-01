import SquaresInCircles.Six.Analytic.SouthTailScalar
import SquaresInCircles.Six.Analytic.SecondaryReduction

/-!
# S separated along its own axis has angle above `-2/25`

Let S be separated from the central square along its own axis and not along the
south side of C, at angle `-v` with `2/25 ≤ v ≤ 5/8`. The difference of the two
margins bounds its transverse coordinate: `b < cx + halfRatio v (a - cy)`, with
`halfRatio v = tan (v/2)`. D and S are separated along the secondary axis of D
or of S. Along that of S, the tangent bound of D and the bound on `b` give a
contradiction. Along that of D, so do a supporting line of the far-corner disk
of S, the bound on `b` and the tangent bound of D, in a combination where the
central coordinates cancel. Both contradictions are the scalar reserves of
`SouthTailScalar`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma south_own_cardinal_difference (v a b cx cy : ℝ) :
    centralMargin .own (3*Real.pi/2-v) a b cx cy-
      centralMargin .south (3*Real.pi/2-v) a b cx cy=
      (1-Real.cos v)*(a-cy)+(cx-b)*Real.sin v := by
  simp only [centralMargin,centralNormal,centerY,Real.cos_sub,Real.sin_sub,
    south_cos,south_sin]
  ring

lemma canonical_south_transverse_upper {v a b cx cy : ℝ}
    (hv : 0 < v ∧ v ≤ 4/5)
    (hown : 0 ≤ centralMargin .own (3*Real.pi/2-v) a b cx cy)
    (hcard : centralMargin .south (3*Real.pi/2-v) a b cx cy < 0) :
    b < cx+halfRatio v*(a-cy) := by
  have hd := south_own_cardinal_difference v a b cx cy
  have hid := (halfRatio_identities ⟨hv.1.le,hv.2⟩).2
  have hm := congrArg (fun z : ℝ => (a-cy)*z) hid
  have hp : 0 < Real.sin v*(cx+halfRatio v*(a-cy)-b) := by
    nlinarith only [hd,hown,hcard,hm]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv.1.le
    (by linarith [hv.2,Real.pi_gt_d2])
  by_contra! hb
  have hn := mul_nonpos_of_nonneg_of_nonpos hs
    (show cx+halfRatio v*(a-cy)-b ≤ 0 by linarith)
  linarith

lemma south_oblique_support {a b : ℝ} (hc : ContainedChart a |b|) :
    a+southDualSlope*b ≤ southSupportCeiling := by
  have hsq : (a+1/2+southDualSlope*(|b|+1/2))^2 <
      (southSupportCeiling+(1+southDualSlope)/2)^2 := by
    have hh := hc.containment
    dsimp [southDualSlope,southSupportCeiling]
    norm_num [Q0] at hh
    nlinarith [sq_nonneg ((21/50)*(a+1/2)-(|b|+1/2))]
  by_contra! h
  have hlarge : southSupportCeiling+(1+southDualSlope)/2 <
      a+1/2+southDualSlope*(|b|+1/2) := by
    dsimp [southDualSlope] at *
    linarith [le_abs_self b]
  have hp := mul_pos (sub_pos.mpr hlarge)
    (show 0 < (a+1/2+southDualSlope*(|b|+1/2))+
        (southSupportCeiling+(1+southDualSlope)/2) by
      dsimp [southDualSlope,southSupportCeiling] at *
      linarith)
  nlinarith

lemma diagonal_tail_projection {a b d v : ℝ} (hc : ContainedChart a |b|)
    (hv : 2/25 ≤ v ∧ v ≤ 5/8) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (ha : diagonalBase d ≤ a) :
    a*Real.cos (d+v)-b*Real.sin (d+v) ≤
      (21/20)*Real.cos (d+v)+diagonalBudget d*Real.sin (d+v) := by
  have htr := south_tail_trig hv hd
  have hs : 0 ≤ Real.sin (d+v) := by linarith [htr.1]
  have hratio : 0 ≤ 2*Real.sin (d+v)-Real.cos (d+v) := by
    linarith [htr.1,Real.cos_le_one (d+v)]
  have hb := diagonal_tangent_budget hc hd ha
  have hB := mul_le_mul_of_nonneg_right hb.le hs
  have hA := mul_nonneg (sub_nonneg.mpr ha) hratio
  have hbase := mul_le_mul_of_nonneg_right (diagonal_base_bounds hd).2 htr.2
  have hsign := mul_le_mul_of_nonneg_right (neg_le_abs b) hs
  nlinarith only [hB,hA,hbase,hsign]

/-- With S at angle `-v` separated along its own axis and not along the south
side of C, and D separated along its own axis, D and S are separated along
neither secondary axis. -/
theorem negative_own_south_impossible {v d a b A B cx cy : ℝ}
    (hv : 2/25 ≤ v ∧ v ≤ 5/8) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hS : ContainedChart a |b|) (hD : ContainedChart A |B|)
    (hx : 0 ≤ cx ∧ cx ≤ coreCeiling) (hy : 0 ≤ cy ∧ cy ≤ coreCeiling)
    (hownS : 0 ≤ centralMargin .own (3*Real.pi/2-v) a b cx cy)
    (hcardS : centralMargin .south (3*Real.pi/2-v) a b cx cy < 0)
    (hownD : 0 ≤ centralMargin .own (Real.pi+d) A B cx cy)
    (hsep : (1+Real.cos (d+v)+Real.sin (d+v))/2 ≤
        a*Real.cos (d+v)+b*Real.sin (d+v)-B ∨
      (1+Real.cos (d+v)+Real.sin (d+v))/2 ≤
        b+A*Real.cos (d+v)-B*Real.sin (d+v)) : False := by
  let t := halfRatio v
  let z := d+v
  have hvr : 0 ≤ v ∧ v ≤ 4/5 := ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have ht0 : 0 ≤ t := halfRatio_nonnegative hvr
  have ht1 : t ≤ 11/32 := by linarith [halfRatio_upper hvr,hv.2]
  have htr := south_tail_trig hv hd
  have hs0 : 0 ≤ Real.sin z := by dsimp [z]; linarith [htr.1]
  have hc0 : 0 ≤ Real.cos z := htr.2
  have hb : b < cx+t*(a-cy) := canonical_south_transverse_upper
    ⟨by linarith [hv.1],hvr.2⟩ hownS hcardS
  have hcd : 0 ≤ Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_pos]⟩
  have hsd0 : 0 ≤ Real.sin d := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  have hX := mul_nonneg (sub_nonneg.mpr hx.2) hcd
  have hY := mul_nonneg (sub_nonneg.mpr hy.2) hsd0
  have hprofile := own_diagonal_profile hd hownD
  have haD : diagonalBase d ≤ A := by linarith
  rcases hsep with hsep | hsep
  · let k := Real.sin z-southDualSlope*Real.cos z
    let f := 1+southDualSlope*t
    let g := Real.cos z+t*Real.sin z
    have hk0 : 0 ≤ k := by
      dsimp [k,southDualSlope]
      linarith [htr.1,Real.cos_le_one z]
    have hk1 : k ≤ 1 := by
      dsimp [k,southDualSlope]
      linarith [Real.sin_le_one z]
    have hf0 : 0 ≤ f := by dsimp [f,southDualSlope]; positivity
    have hg0 : 0 ≤ g := by dsimp [g]; positivity
    have hsup := south_oblique_support hS
    have hsupprod := mul_nonneg (sub_nonneg.mpr hsup) hg0
    have hcanprod := mul_nonneg (sub_nonneg.mpr hb.le) hk0
    have hprojection : f*(a*Real.cos z+b*Real.sin z) ≤
        southSupportCeiling*g+(cx-t*cy)*k := by
      dsimp [f,g,k] at *
      nlinarith only [hsupprod,hcanprod]
    have hDshared := diagonal_shared_center_budget hD hx.2 hy.2 hd hownD
    have hDP := mul_le_mul_of_nonneg_right hDshared.le hf0
    have hsign := mul_le_mul_of_nonneg_right (neg_le_abs B) hf0
    have hsd : 9/20 ≤ Real.sin d := by
      have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi/2) ≤ (1:ℝ)/2 by linarith [Real.pi_pos])
        (show d ≤ Real.pi/2 by linarith [hd.2,Real.pi_pos]) hd.1
      have hp := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
      linarith
    have hkterm := mul_le_mul_of_nonneg_left hk1 ht0
    have hplus := mul_nonneg hsd0 (show 0 ≤ southDualSlope*t by dsimp [southDualSlope]; positivity)
    have hycoef : 0 ≤ 2*Real.sin d*f-t*k := by
      dsimp [f]
      nlinarith only [hsd,ht1,hkterm,hplus]
    have hxcoef : 0 ≤ 2*Real.cos d*f+k := by positivity
    have hxp := mul_nonneg (sub_nonneg.mpr hx.2) hxcoef
    have hyp := mul_nonneg (sub_nonneg.mpr hy.2) hycoef
    have hcenter : -B*f+(cx-t*cy)*k ≤
        diagonalBudget d*f+coreCeiling*(1-t)*k := by
      nlinarith only [hDP,hsign,hxp,hyp]
    have hsepP := mul_le_mul_of_nonneg_left hsep hf0
    have hreserve := south_diagonal_tail_reserve hv hd
    change southSupportCeiling*g+coreCeiling*(1-t)*k+diagonalBudget d*f <
      ((1+Real.cos z+Real.sin z)/2)*f at hreserve
    nlinarith only [hprojection,hcenter,hsepP,hreserve]
  · have hproj := diagonal_tail_projection hD hv hd haD
    have hrad : a ≤ 55641/50000 := hS.a_le_rho0.trans rho0_lt_five_digit.le
    have hp := mul_nonneg ht0 (show 0 ≤ 55641/50000-a+cy by linarith [hy.1])
    have hbs : b ≤ coreCeiling+(55641/50000)*t := by nlinarith only [hb,hx.2,hp]
    have hr := south_wing_tail_reserve hv hd
    nlinarith only [hsep,hproj,hbs,hr]

/-- If S is separated from the central square along its own axis and not along
the south side of C, the angle of S exceeds `-2/25`. -/
theorem normalized_own_south_lower_tail {R : ℝ} (P : NormalizedPacking R)
    (hS : P.ownBits 4=true) : -2/25 < P.helperAngle 4 := by
  by_contra! htail
  let v := -P.helperAngle 4
  let d := P.diagonalAngle
  have hv : 2/25 ≤ v ∧ v ≤ 5/8 := by
    dsimp [v]
    constructor <;> linarith [P.helper_windows.2.2.2.1]
  have hd : 1/2 ≤ d ∧ d ≤ Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hDphase : P.phase 3=Real.pi+d := by dsimp [d,NormalizedPacking.diagonalAngle]; ring
  have hSphase : P.phase 4=3*Real.pi/2-v := by
    have hh : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
    rw [hh]; dsimp [v]; ring
  have hcS : centralMargin .south (P.phase 4) (P.radial 4) (P.transverse 4)
      P.center.1 P.center.2 < 0 :=
    (P.toPinPacking.canonicalOwn_eq_true 4).mp hS
  have htr := south_tail_trig hv hd
  have hcos : 0 ≤ Real.cos (d+v) := htr.2
  have hsin : 0 ≤ Real.sin (d+v) := by linarith [htr.1]
  have hq : (3*Real.pi/2-v)-(Real.pi+d)=Real.pi/2-(d+v) := by ring
  have hsep : (1+Real.cos (d+v)+Real.sin (d+v))/2 ≤
        P.radial 4*Real.cos (d+v)+P.transverse 4*Real.sin (d+v)-P.transverse 3 ∨
      (1+Real.cos (d+v)+Real.sin (d+v))/2 ≤
        P.transverse 4+P.radial 3*Real.cos (d+v)-P.transverse 3*Real.sin (d+v) := by
    rcases south_secondary_choice P with h | h
    · left
      change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
        frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at h
      rw [P.square_def 3,P.square_def 4,hDphase,hSphase,
        oriented_pair_threshold,pair_frameY_left,hq,angularWidth,
        Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,
        abs_of_nonneg hcos,abs_of_nonneg hsin] at h
      linarith
    · right
      change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
        frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at h
      rw [P.square_def 3,P.square_def 4,hDphase,hSphase,
        oriented_pair_threshold,pair_frameY_right,hq,angularWidth,
        Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,
        abs_of_nonneg hcos,abs_of_nonneg hsin] at h
      linarith
  exact negative_own_south_impossible hv hd (P.contained 4) (P.contained 3)
    ⟨P.box.1.1,P.box.1.2.trans c0_lt_coreCeiling.le⟩
    ⟨P.box.2.1,P.box.2.2.trans c0_lt_coreCeiling.le⟩
    (by simpa only [hSphase] using P.own_separator 4 hS)
    (by simpa only [hSphase] using hcS)
    (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own) hsep

end SquaresInCircles.Six.Analytic
