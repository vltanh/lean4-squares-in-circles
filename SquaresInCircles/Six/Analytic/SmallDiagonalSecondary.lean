import SquaresInCircles.Six.Analytic.SmallDiagonalSecondaryBounds
import SquaresInCircles.Six.Analytic.ConstrainedCircleSupport
import SquaresInCircles.Six.Analytic.PrimaryClassification

/-!
# The small-diagonal W-secondary exclusion

A negative W tilt consumes its transverse reserve at rate 2/3. D's primary
coordinate is constrained by its actual OWN separator. On the constrained
circle branch the same 2/3 slope controls the projection; on the circular
branch the phase gap must exceed 9/10 and a concavity bound excludes it.

Consequently an actual W-secondary edge forces d>1/2. This does NOT assert
that D-secondary is impossible: when d<=1/2 the remaining W/D source is
D-secondary. The subsequent joint W/D/S reduction must exclude that source.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- Pure coordinate version, before choosing a normalized packing. -/
theorem small_diagonal_W_secondary_excluded {w d a b bw : ℝ}
    (hw : -2/3≤w) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d)
    (hprofile : 1+(77/200)*(Real.cos d+Real.sin d)≤a+1/2)
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0)
    (hbudget : -bw<47/100-(2/3)*max (-w) 0) :
    a*Real.sin (d-w)+b*Real.cos (d-w)-bw<1/2+angularWidth (d-w) := by
  let q := d-w
  let l := 1+(77/200)*(Real.cos d+Real.sin d)
  have hq : 0≤q ∧ q≤7/6 := by dsimp [q]; constructor <;> linarith [hd.2]
  have hcos : 0≤Real.cos q := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.1,Real.pi_pos],by linarith [hq.2,Real.pi_gt_d2]⟩
  have hsin : 0≤Real.sin q := Real.sin_nonneg_of_nonneg_of_le_pi hq.1
    (by linarith [hq.2,Real.pi_gt_d2])
  have hdc : 0≤Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_gt_d2]⟩
  have hds : 0≤Real.sin d := Real.sin_nonneg_of_nonneg_of_le_pi hd.1
    (by linarith [hd.2,Real.pi_gt_d2])
  have hwidth : 1≤Real.cos d+Real.sin d := by
    have hh := one_le_abs_cos_add_abs_sin d
    simpa only [abs_of_nonneg hdc,abs_of_nonneg hds] using hh
  have hlower : 277/200≤l := by dsimp [l]; linarith
  have hlpos : 0<l := by linarith
  have ha : l≤a+1/2 := hprofile
  change a*Real.sin q+b*Real.cos q-bw<1/2+angularWidth q
  rw [angularWidth,abs_of_nonneg hcos,abs_of_nonneg hsin]
  by_cases hbranch : R0*Real.sin q≤l
  · let B := Real.sqrt (Q0-l^2)
    have hroot := constrained_root_bounds hlpos ha hbox
    have hBhalf : 1/2≤B := hroot.1
    have hcircle : B^2+l^2=Q0 := hroot.2
    have hsynthetic : ((l-1/2)+1/2)^2+(|B-1/2|+1/2)^2≤Q0 := by
      rw [abs_of_nonneg (by linarith : 0≤B-1/2)]
      nlinarith only [hcircle]
    have hsyntheticProfile : 1+(77/200)*(Real.cos d+Real.sin d)≤(l-1/2)+1/2 := by
      dsimp [l]
      linarith
    have hBt := transverse_lt_from_front_profile hd hsyntheticProfile hsynthetic
    rw [abs_of_nonneg (by linarith : 0≤B-1/2)] at hBt
    have hBc := mul_le_mul_of_nonneg_right
      (show B≤97/100-(9/20)*d by linarith) hcos
    have hsupp := circle_support_above_primary hlpos ha hbox hsin hcos
      (Real.sin_sq_add_cos_sq q) hbranch
    change a*Real.sin q+b*Real.cos q≤(l-1/2)*Real.sin q+(B-1/2)*Real.cos q at hsupp
    have hsmall := smallDiagonalProjection_bound hd hwd
    change smallDiagonalProjection d q<3/100+(2/3)*max (-w) 0 at hsmall
    dsimp [smallDiagonalProjection,smallDiagonalA,smallDiagonalB] at hsmall
    dsimp [l] at hsupp
    nlinarith only [hsupp,hBc,hsmall,hbudget]
  · have hqlo := unconstrained_gap_gt_nine_tenths hlower hq (lt_of_not_ge hbranch)
    have hwneg : w<0 := by dsimp [q] at hqlo; linarith [hd.2]
    rw [max_eq_left (by linarith : 0≤-w)] at hbudget
    have hsupp := circle_support_unconstrained hbox hcos (Real.sin_sq_add_cos_sq q)
    have hreserve := unconstrained_secondary_reserve ⟨hqlo.le,hq.2⟩
    dsimp [q] at hsupp hreserve ⊢
    nlinarith [hbudget,R0_lt_1689_1000,hd.2]

/-- The signed transverse budget is a consequence of the actual W bit,
not a new restriction on the normalized packing. -/
lemma normalized_west_transverse_budget {R : ℝ} (P : NormalizedPacking R) :
    -P.transverse 2<47/100-(2/3)*max (-P.helperAngle 2) 0 := by
  by_cases hw : 0≤P.helperAngle 2
  · rw [max_eq_right (by linarith),mul_zero,sub_zero]
    have hb := (P.contained 2).u_le_U0 (P.avoidsCore 2)
    linarith [neg_le_abs (P.transverse 2),U0_lt_117_250]
  · have hv0 : 0≤-P.helperAngle 2 := by linarith
    rw [max_eq_left hv0]
    have hwphase : P.phase 2=Real.pi-(-P.helperAngle 2) := by
      have hh : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
      rw [hh]
      ring
    cases hbit : P.ownBits 2
    · have hangle := abs_lt.mp (P.cardinal_angle 2 hbit)
      apply cardinal_west_negative_transverse (P.contained 2) P.box.1.2
        ⟨hv0,by linarith [hangle.1]⟩
      have h := P.cardinal_separator 2 hbit
      rw [hwphase] at h
      exact h
    · have hwindow := P.window 2
      norm_num [Certificates.windowLower,Certificates.windowUpper,Certificates.phaseCenter] at hwindow
      have hbound := own_west_negative_transverse (P.contained 2) P.box.1.2 P.box.2.1
        ⟨hv0,by linarith [hwindow.1]⟩
        (by simpa only [hwphase] using P.own_separator 2 hbit)
      exact (neg_le_abs (P.transverse 2)).trans_lt hbound

/-- The W-secondary source alone already supplies the d>1/2 reduction. -/
theorem W_secondary_forces_large_diagonal {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)) :
    1/2<P.diagonalAngle := by
  by_contra! hdsmall
  have hd : 0≤P.diagonalAngle ∧ P.diagonalAngle≤1/2 := ⟨P.diagonal_angle_range.1.le,hdsmall⟩
  have hwphase : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hdphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hwindow := P.window 2
  norm_num [Certificates.windowLower,Certificates.windowUpper,Certificates.phaseCenter] at hwindow
  have hw : -2/3≤P.helperAngle 2 := by
    linarith [hwindow.1]
  have horder : P.helperAngle 2≤P.diagonalAngle := by
    have hh := P.primary_order.2.2.1
    rw [hwphase,hdphase] at hh
    linarith
  have hown := P.own_separator 3 P.diagonal_own
  rw [hdphase] at hown
  have hprofile := own_front_radial_profile P.box.1.2 P.box.2.2 hd hown
  have hbound := small_diagonal_W_secondary_excluded hw hd horder hprofile
    (P.contained 3).containment (normalized_west_transverse_budget P)
  have hcoordinate : dot (normalY (P.square 2))
      (sub (P.square 3).center (P.square 2).center)=
      P.radial 3*Real.sin (P.diagonalAngle-P.helperAngle 2)+
        P.transverse 3*Real.cos (P.diagonalAngle-P.helperAngle 2)-P.transverse 2 := by
    change frameY (P.square 2) (sub (P.square 3).center (P.square 2).center)=_
    rw [P.square_def 2,P.square_def 3,pair_frameY_left,hwphase,hdphase]
    have hdiff : (Real.pi+P.diagonalAngle)-(Real.pi+P.helperAngle 2)=
        P.diagonalAngle-P.helperAngle 2 := by ring
    rw [hdiff]
  rw [hcoordinate,P.square_def 2,P.square_def 3,oriented_pair_threshold,hwphase,hdphase] at hsep
  have hdiff : (Real.pi+P.diagonalAngle)-(Real.pi+P.helperAngle 2)=
      P.diagonalAngle-P.helperAngle 2 := by ring
  rw [hdiff] at hsep
  linarith

/-- A precise partial classification: small d leaves only D-secondary. -/
theorem DW_small_diagonal_selected_source {R : ℝ} (P : NormalizedPacking R)
    (hd : P.diagonalAngle≤1/2) (k : Fin 8)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (Stress.pairNormal k (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center)) : k=6 := by
  rcases DW_selected_secondary P k hsep with hk | hk
  · subst k
    have hlarge := W_secondary_forces_large_diagonal P hsep
    linarith
  · exact hk

end SquaresInCircles.Six.Analytic
