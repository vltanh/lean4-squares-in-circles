import SquaresInCircles.Six.Analytic.FrozenPrimaryExclusion

/-!
# Positive D-primary is impossible when W is OWN

Use the two edges C-W and W-D with weights 10 and 3. Local centers are frozen,
so the residual is a sum of positive-coefficient trigonometric functions of
v=-w and v+d. All four original rectangle corners are bounded by the universal
vertex support. No D-primary pin-sign restriction is needed for this stronger
whole-rectangle statement.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def destinationPrimaryFrozen (v d aw bw ad cx cy : ℝ) : ℝ :=
  frozenTrig (13/2-10*aw-3*ad)
    (10*(1/2-cx)) (10*(1/2+cy)) 0 0
    (3*(1/2+aw)) (3*(1/2+bw)) v d

lemma destination_primary_norm_identity (q : ℝ) :
    (10-3*Real.cos q)^2+(3*Real.sin q)^2=109-60*Real.cos q := by
  nlinarith [Real.sin_sq_add_cos_sq q]

lemma destination_primary_endpoint_lower {v d aw bw ad cx cy L X : ℝ}
    (had : ad≤rho0) (hW : ContainedChart aw |bw|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hv : 0≤Real.sin v) (hq : 0≤Real.sin (v+d)) (hL : 0≤L)
    (hNorm : 109-60*Real.cos (v+d)≤L^2)
    (hX : 0≤X) (hcx : 10*Real.cos v≤X) :
    23/2+5*(Real.cos v+Real.sin v)+3*Real.sin (v+d)-
      3*(1113/1000)-(1689/1000)*L-(113/1000)*X≤
        destinationPrimaryFrozen v d aw bw ad cx cy := by
  have hvertex := vertex_linear_upper hW
    (U := 10-3*Real.cos (v+d)) (V := 3*Real.sin (v+d))
    (by positivity) hL (by rwa [destination_primary_norm_identity])
  have hcentral := coarse_central_work (gx := 10*Real.cos v) (gy := -10*Real.sin v)
    (Y := 0) hc hX (by norm_num) hcx (by linarith)
  have had' : ad≤1113/1000 := had.trans rho0_upper.le
  dsimp [destinationPrimaryFrozen,frozenTrig]
  nlinarith

lemma destination_primary_corners {aw bw ad cx cy : ℝ}
    (had : ad≤rho0) (hW : ContainedChart aw |bw|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<destinationPrimaryFrozen 0 0 aw bw ad cx cy ∧
    0<destinationPrimaryFrozen 0 (Real.pi/4) aw bw ad cx cy ∧
    0<destinationPrimaryFrozen (2/3) 0 aw bw ad cx cy ∧
    0<destinationPrimaryFrozen (2/3) (Real.pi/4) aw bw ad cx cy := by
  obtain ⟨hcl,hcu,hsl,hsu⟩ := two_thirds_endpoint_bracket
  obtain ⟨hhl,hhu,hsc⟩ := quarter_endpoint_bracket
  have hdiff : (166:ℝ)/1000≤Real.cos (2/3)-Real.sin (2/3) := by linarith
  have hsum : (1403:ℝ)/1000≤Real.cos (2/3)+Real.sin (2/3) := by linarith
  have hmc := mul_le_mul hdiff hhl (by norm_num : (0:ℝ)≤707/1000)
    (show 0≤Real.cos (2/3)-Real.sin (2/3) by linarith)
  have hms := mul_le_mul hsum hhl (by norm_num : (0:ℝ)≤707/1000)
    (show 0≤Real.cos (2/3)+Real.sin (2/3) by linarith)
  have hqcos : (166:ℝ)/1000*(707/1000)≤Real.cos (2/3+Real.pi/4) := by
    rw [Real.cos_add,hsc]
    nlinarith only [hmc]
  have hqsin : (1403:ℝ)/1000*(707/1000)≤Real.sin (2/3+Real.pi/4) := by
    rw [Real.sin_add,hsc]
    nlinarith only [hms]
  refine ⟨?_,?_,?_,?_⟩
  · have h := destination_primary_endpoint_lower (v := 0) (d := 0) (L := 7) (X := 10)
      had hW hc (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  · have h := destination_primary_endpoint_lower (v := 0) (d := Real.pi/4)
      (L := 817/100) (X := 10) had hW hc (by norm_num)
      (by rw [zero_add,hsc]; linarith) (by norm_num)
      (by simp only [zero_add]; nlinarith) (by norm_num) (by norm_num)
    simp only [Real.cos_zero,Real.sin_zero,zero_add,hsc] at h
    linarith
  · have h := destination_primary_endpoint_lower (v := (2:ℝ)/3) (d := 0)
      (L := 787/100) (X := 10*(787/1000)) had hW hc (by linarith)
      (by simp only [add_zero]; linarith) (by norm_num)
      (by simp only [add_zero]; nlinarith) (by norm_num) (by linarith)
    simp only [add_zero] at h
    linarith
  · have h := destination_primary_endpoint_lower (v := (2:ℝ)/3) (d := Real.pi/4)
      (L := 101/10) (X := 10*(787/1000)) had hW hc (by linarith)
      (by linarith) (by norm_num) (by nlinarith) (by norm_num) (by linarith)
    linarith

lemma destination_primary_frozen_positive {v d aw bw ad cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤Real.pi/4)
    (had : ad≤rho0) (hW : ContainedChart aw |bw|) (hb : |bw|<1/2)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<destinationPrimaryFrozen v d aw bw ad cx cy := by
  have hcx : 0≤1/2-cx := by linarith [hc.1.2,c0_lt_23_200]
  have hcy : 0≤1/2+cy := by linarith [hc.2.1]
  have haw : 0≤1/2+aw := by linarith [hW.half_le]
  have hbw : 0≤1/2+bw := by linarith [(abs_lt.mp hb).1]
  obtain ⟨h00,h0D,hV0,hVD⟩ := destination_primary_corners had hW hc
  unfold destinationPrimaryFrozen
  exact frozenTrig_positive (by positivity) (by positivity) (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by norm_num) (by positivity)
    (by linarith [Real.pi_gt_d2]) hv hd h00 h0D hV0 hVD

lemma destination_primary_frozen_nonpositive {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤Real.pi/4)
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (normalX (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) :
    destinationPrimaryFrozen v d aw bw ad cx cy≤0 := by
  have hcv : 0≤Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,Real.pi_pos],by linarith [hv.2,Real.pi_gt_d2]⟩
  have hsv := Real.sin_nonneg_of_nonneg_of_le_pi hv.1 (by linarith [hv.2,Real.pi_gt_d2])
  have hcq : 0≤Real.cos (v+d) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,hd.1,Real.pi_pos],by linarith [hv.2,hd.2,Real.pi_gt_d2]⟩
  have hsq := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤v+d by linarith [hv.1,hd.1]) (show v+d≤Real.pi by linarith [hv.2,hd.2,Real.pi_gt_d2])
  have hW : 1/2-aw+(1/2-cx)*Real.cos v+(1/2+cy)*Real.sin v≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,
      Real.sin_pi_sub,abs_neg,abs_of_nonneg hcv,abs_of_nonneg hsv] at hCW
    nlinarith only [hCW]
  change Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
      (orientedSquare (Real.pi+d) ad bd)≤
    frameX (orientedSquare (Real.pi+d) ad bd)
      (sub (orientedSquare (Real.pi+d) ad bd).center
        (orientedSquare (Real.pi-v) aw bw).center) at hWD
  rw [oriented_pair_threshold,pair_frameX_right,
    show (Real.pi+d)-(Real.pi-v)=v+d by ring,
    angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hWD
  have hE : 1/2-ad+(1/2+aw)*Real.cos (v+d)+(1/2+bw)*Real.sin (v+d)≤0 := by
    nlinarith only [hWD]
  dsimp [destinationPrimaryFrozen,frozenTrig]
  nlinarith only [hW,hE]

/-- Complete OWN-W positive-D-primary exclusion, with no stress-table premise. -/
theorem normalized_ownW_destination_primary_excluded {R : ℝ}
    (P : NormalizedPacking R) (hown : P.ownBits 2=true) :
    ¬ Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalX (P.square 3)) (sub (P.square 3).center (P.square 2).center) := by
  intro hsep
  have hwphase : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hdphase : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [NormalizedPacking.diagonalAngle]; ring
  by_cases hw : 0≤P.helperAngle 2
  · have hq : |P.phase 3-P.phase 2|≤Real.pi/3 := by
      rw [abs_of_nonneg (sub_nonneg.mpr P.primary_order.2.2.1.le),hwphase,hdphase]
      linarith [P.diagonal_angle_range.2,Real.pi_pos]
    exact not_le_of_gt (oriented_destination_primary_excluded (P.contained 2) (P.contained 3)
      (P.avoidsCore 2) (P.avoidsCore 3) hq) hsep
  · have hv : 0≤-P.helperAngle 2 ∧ -P.helperAngle 2≤2/3 := by
      constructor <;> linarith [P.helper_windows.2.2.1.1]
    have hd := P.diagonal_angle_range
    have hpositive := destination_primary_frozen_positive hv ⟨hd.1.le,hd.2⟩
      (P.contained 3).a_le_rho0 (P.contained 2)
      ((P.contained 2).u_lt_half (P.avoidsCore 2)) P.box
    have hwphase' : P.phase 2=Real.pi-(-P.helperAngle 2) := by rw [hwphase]; ring
    have hnegative := destination_primary_frozen_nonpositive hv ⟨hd.1.le,hd.2⟩
      (by simpa only [hwphase'] using P.own_separator 2 hown)
      (by simpa only [P.square_def,hwphase',hdphase] using hsep)
    linarith

end SquaresInCircles.Six.Analytic
