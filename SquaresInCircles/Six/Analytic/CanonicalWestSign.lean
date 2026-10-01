import SquaresInCircles.Six.Analytic.CanonicalWestBounds
import SquaresInCircles.Six.Analytic.PrimaryClassification

/-!
# Canonical OWN W has negative deviation

The cardinal-preferred convention supplies strict negativity of the west
cardinal margin. Subtracting it from the nonnegative OWN margin gives a
transverse lower bound involving sin(w)/(1+cos(w)). When w>=0 this contradicts
BOTH surviving W/D secondary separators by the analytic reserves in
CanonicalWestBounds. At w=0 the two central margins agree exactly.

No candidate D-edge choice, tail table or pair-envelope domain is assumed.
The global D half-window is used explicitly; this theorem is not reflected to
S while silently keeping that half-window.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma west_own_cardinal_difference (w a b cx cy : ℝ) :
    centralMargin .own (Real.pi+w) a b cx cy-
      centralMargin .west (Real.pi+w) a b cx cy=
      (1-Real.cos w)*(a-cx)+Real.sin w*(b+cy) := by
  rw [add_comm Real.pi w]
  simp only [centralMargin,centralNormal,centerX,Real.cos_add_pi,Real.sin_add_pi]
  ring

lemma canonical_west_transverse_lower {w a b cx cy : ℝ}
    (hw : 0<w ∧ w≤4/5)
    (hown : 0≤centralMargin .own (Real.pi+w) a b cx cy)
    (hcard : centralMargin .west (Real.pi+w) a b cx cy<0) :
    -cy-halfRatio w*(a-cx)<b := by
  have hdiff := west_own_cardinal_difference w a b cx cy
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

private lemma canonical_west_coarse_transverse {w a b cx cy : ℝ}
    (hw : 0<w ∧ w≤4/5) (ha : a≤rho0) (hx0 : 0≤cx) (hy : cy≤c0)
    (hown : 0≤centralMargin .own (Real.pi+w) a b cx cy)
    (hcard : centralMargin .west (Real.pi+w) a b cx cy<0) :
    -(113/1000)-(1113/1000)*halfRatio w<b := by
  have hb := canonical_west_transverse_lower hw hown hcard
  have ht := halfRatio_nonnegative ⟨hw.1.le,hw.2⟩
  have hm := mul_le_mul_of_nonneg_left
    (show a-cx≤1113/1000 by linarith [rho0_upper]) ht
  have hcy : cy≤113/1000 := by dsimp [c0] at hy; linarith [rho0_upper]
  linarith

/-- A scalar two-square contradiction; the full packing is used only to
supply one of the two actual secondary inequalities. -/
theorem canonical_west_nonnegative_impossible {w d aw bw ad bd cx cy : ℝ}
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
    have hdiff := west_own_cardinal_difference 0 aw bw cx cy
    simp only [Real.cos_zero,Real.sin_zero,sub_self,zero_mul,add_zero] at hdiff hownW hcardW
    linarith
  have hwpos : 0<w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hw1 : w≤4/5 := by linarith [Real.pi_lt_d2]
  have hq : 0≤d-w ∧ d-w≤4/5 := by constructor <;> linarith [Real.pi_lt_d2]
  have htr := small_polynomial_trig hq
  have hsq : 0≤Real.sin (d-w) := by nlinarith [htr.2.1,hq.1]
  have hcq : 0≤Real.cos (d-w) := by linarith [htr.1]
  have hbW := canonical_west_coarse_transverse ⟨hwpos,hw1⟩ hW.a_le_rho0 hcx0 hcy hownW hcardW
  have hbD := diagonal_transverse_profile hD hcx hcy ⟨hw.trans hwd,hd⟩ hownD
  have hDtrans : bd≤97/100-(Real.cos d+Real.sin d)/2 := by
    linarith [le_abs_self bd]
  have hDproj := mul_le_mul_of_nonneg_right hDtrans hcq
  have hDrad := mul_le_mul_of_nonneg_right
    (show ad≤1113/1000 by linarith [hD.a_le_rho0,rho0_upper]) hsq
  rcases hsec with hsec | hsec
  · have hbound := canonical_west_secondary_reserve hw hwd hd
    nlinarith only [hsec,hbound,hDproj,hDrad,hbW]
  · have ht := halfRatio_nonnegative ⟨hw,hw1⟩
    have hcoeff : 0≤Real.sin (d-w)+halfRatio w*Real.cos (d-w) :=
      add_nonneg hsq (mul_nonneg ht hcq)
    have hWrad := mul_le_mul_of_nonneg_right
      (show aw≤1113/1000 by linarith [hW.a_le_rho0,rho0_upper]) hcoeff
    have hb := canonical_west_transverse_lower ⟨hwpos,hw1⟩ hownW hcardW
    have hbwcos := mul_le_mul_of_nonneg_right hb.le hcq
    have hcentral : cy-halfRatio w*cx≤113/1000 := by
      have hprod := mul_nonneg ht hcx0
      dsimp [c0] at hcy
      linarith [rho0_upper]
    have hccos := mul_le_mul_of_nonneg_right hcentral hcq
    have hbound := canonical_diagonal_secondary_reserve hw hwd hd
    nlinarith only [hsec,hbound,hDtrans,hWrad,hbwcos,hccos]

/-- The positive-side OWN-W tail is eliminated without a stress table. In
fact the canonical choice yields the stronger strict sign w<0. -/
theorem canonical_own_west_negative {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownBits 2=true) : P.helperAngle 2<0 := by
  by_contra! hw
  let w := P.helperAngle 2
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
    (P.toPinPacking.canonicalOwn_eq_true 2).mp hown
  obtain ⟨k,hsep,hcases⟩ := DW_secondary_exists P
  have hsecondary : (1+Real.cos (d-w)+Real.sin (d-w))/2≤
        P.radial 3*Real.sin (d-w)+P.transverse 3*Real.cos (d-w)-P.transverse 2 ∨
      (1+Real.cos (d-w)+Real.sin (d-w))/2≤
        P.transverse 3+P.radial 2*Real.sin (d-w)-P.transverse 2*Real.cos (d-w) := by
    rcases hcases with rfl | rfl
    · left
      change Seven.SAT.threshold (P.square 2) (P.square 3)≤
        frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at hsep
      rw [P.square_def 2,P.square_def 3,hWphase,hDphase,
        oriented_pair_threshold,pair_frameY_left,
        show (Real.pi+d)-(Real.pi+w)=d-w by ring,
        angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hsep
      linarith
    · right
      change Seven.SAT.threshold (P.square 2) (P.square 3)≤
        frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
      rw [P.square_def 2,P.square_def 3,hWphase,hDphase,
        oriented_pair_threshold,pair_frameY_right,
        show (Real.pi+d)-(Real.pi+w)=d-w by ring,
        angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hsep
      linarith
  exact canonical_west_nonnegative_impossible hw hwd hd (P.contained 2) (P.contained 3)
    P.box.1.1 P.box.1.2 P.box.2.2
    (by simpa only [hWphase] using P.own_separator 2 hown)
    (by simpa only [hWphase] using hcW)
    (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own) hsecondary

end SquaresInCircles.Six.Analytic
