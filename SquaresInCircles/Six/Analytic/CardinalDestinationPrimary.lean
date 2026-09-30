import SquaresInCircles.Six.Analytic.FrozenPrimaryEndpoints

/-!
# Cardinal W cannot separate from D on positive D-primary

Use the single stress (1/20,11/20,2/5) on C-D,C-W,W-D. The D force is axial;
the W force has squared length 37/80-(11/25)cos d, independent of W's phase.
Universal radial support therefore reduces the contradiction to one quarter-
circle inequality. A chord lower bound for sine and one increasing quadratic
prove it on the whole domain. No angle subdivision or curvature certificate
is needed, and no W-angle tail is assumed.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Stress

lemma quarter_circle_chord {c s : ℝ} (hc : 7/10≤c ∧ c≤1) (hs : 0≤s)
    (hu : c^2+s^2=1) : (7/3)*(1-c)≤s := by
  have hp := mul_nonneg (show 0≤1-c by linarith) (show 0≤58*c-40 by linarith)
  by_contra! h
  have hprod := mul_pos (sub_pos.mpr h)
    (show 0<(7/3)*(1-c)+s by linarith)
  nlinarith

/-- A visible quadratic identity controls the entire radial endpoint family. -/
lemma cardinal_destination_scalar {c s L : ℝ}
    (hc : 707/1000≤c ∧ c≤1) (hs : 0≤s) (hu : c^2+s^2=1)
    (hL : 0≤L) (hLs : L^2=37/80-(11/25)*c) :
    (1113/1000)*L<103/250+(387/20000)*(c+s) := by
  have hsin := quarter_circle_chord ⟨by linarith [hc.1],hc.2⟩ hs hu
  have hV : 0<45715/100000-(258/10000)*c := by linarith [hc.2]
  have hfactor := mul_nonneg (show 0≤c-707/1000 by linarith [hc.1])
    (show 0≤(16641/25000000)*(c+707/1000)+26073471/50000000 by linarith [hc.1])
  have hid : (45715/100000-(258/10000)*c)^2-
      (1113/1000)^2*(37/80-(11/25)*c)=
      126676485709/25000000000000+
      (c-707/1000)*((16641/25000000)*(c+707/1000)+26073471/50000000) := by ring
  have hsq : 0<(45715/100000-(258/10000)*c)^2-((1113/1000)*L)^2 := by
    rw [mul_pow,hLs]
    linarith only [hid,hfactor]
  have hbound : (1113/1000)*L<45715/100000-(258/10000)*c := by
    by_contra! h
    have hp := mul_nonneg (sub_nonneg.mpr h)
      (show 0≤(1113/1000)*L+(45715/100000-(258/10000)*c) by positivity)
    nlinarith
  linarith

lemma cardinal_destination_reserve {c s L : ℝ}
    (hc : 707/1000≤c ∧ c≤1) (hs : 0≤s) (hu : c^2+s^2=1)
    (hL : 0≤L) (hLs : L^2=37/80-(11/25)*c) :
    rho0*(9/20+L)+c0*(11/20+(c+s)/20)<39/40+(c+s)/40 := by
  have hscalar := cardinal_destination_scalar hc hs hu hL hLs
  have hsum : 0≤c+s := by linarith [hc.1]
  have hR := mul_le_mul_of_nonneg_right rho0_upper.le (show 0≤9/20+L by linarith)
  have hC := mul_le_mul_of_nonneg_right
    (show c0≤113/1000 by dsimp [c0]; linarith [rho0_upper])
    (show 0≤11/20+(c+s)/20 by linarith)
  nlinarith only [hscalar,hR,hC]

lemma angularWidth_ge_half (t : ℝ) : 1/2≤angularWidth t := by
  have h := one_le_abs_cos_add_abs_sin t
  dsimp [angularWidth]
  linarith

/-- The scalar stress is connected directly to the actual normalized packing.
The argument uses cardinal W and OWN D, and no selected edge other than +eD. -/
theorem normalized_cardinalW_destination_primary_excluded {R : ℝ}
    (P : NormalizedPacking R) (hWcard : P.ownBits 2=false) :
    ¬ Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalX (P.square 3)) (sub (P.square 3).center (P.square 2).center) := by
  intro hsep
  let d := P.diagonalAngle
  let c := Real.cos d
  let s := Real.sin d
  let g : Point := (-11/20+(2/5)*c,(2/5)*s)
  let L := vectorLength g
  have hd : 0≤d ∧ d≤Real.pi/4 := ⟨P.diagonal_angle_range.1.le,P.diagonal_angle_range.2⟩
  have hcoslo : 707/1000≤c := by
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hd.1
      (show Real.pi/4≤Real.pi by linarith [Real.pi_pos]) hd.2
    exact quarter_endpoint_bracket.1.trans hmono
  have hcoshi : c≤1 := Real.cos_le_one d
  have hsin : 0≤s := Real.sin_nonneg_of_nonneg_of_le_pi hd.1
    (by linarith [hd.2,Real.pi_pos])
  have hunit : c^2+s^2=1 := by nlinarith [Real.sin_sq_add_cos_sq d]
  have hL : 0≤L := vectorLength_nonneg g
  have hLs : L^2=37/80-(11/25)*c := by
    have h := vectorLength_sq g
    dsimp [g,normSq] at h
    nlinarith
  have hreserve := cardinal_destination_reserve ⟨hcoslo,hcoshi⟩ hsin hunit hL hLs
  have hDphase : P.phase 3=Real.pi+d := by dsimp [d,NormalizedPacking.diagonalAngle]; ring
  have hDaxis : normalX (P.square 3)=(-c,-s) := by
    rw [P.square_def,hDphase]
    simp [normalX,orientedSquare,c,s,Real.cos_pi_add,Real.sin_pi_add]
  have hDcenter : dot (normalX (P.square 3)) (P.square 3).center=P.radial 3 := by
    have h := oriented_frame_centerX (P.phase 3) (P.radial 3) (P.transverse 3)
    simpa [P.square_def,frameX,normalX,dot,sub] using h
  have hDWlower : 1≤dot (normalX (P.square 3))
      (sub (P.square 3).center (P.square 2).center) := by
    have hth : 1≤Seven.SAT.threshold (P.square 2) (P.square 3) := by
      rw [P.square_def 2,P.square_def 3,oriented_pair_threshold]
      linarith [angularWidth_ge_half (P.phase 3-P.phase 2)]
    exact hth.trans hsep
  rw [dot_sub_right,hDcenter,hDaxis] at hDWlower
  have hCW := P.cardinal_separator 2 hWcard
  have hWlower : 1≤P.center.1-(P.square 2).center.1 := by
    change 0≤P.center.1-1/2-centerX (P.phase 2) (P.radial 2) (P.transverse 2)-angularWidth (P.phase 2) at hCW
    have hwidth := angularWidth_ge_half (P.phase 2)
    change 1≤P.center.1-centerX (P.phase 2) (P.radial 2) (P.transverse 2)
    linarith
  have hCD := P.own_separator 3 P.diagonal_own
  have hDlower : 1/2+(c+s)/2≤P.radial 3+P.center.1*c+P.center.2*s := by
    rw [hDphase] at hCD
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,
      Real.sin_pi_add,abs_neg] at hCD
    change 0≤P.radial 3-1/2-(P.center.1*(-c)+P.center.2*(-s))-(|c|+|s|)/2 at hCD
    rw [abs_of_nonneg (by linarith),abs_of_nonneg hsin] at hCD
    nlinarith
  have hWsupport := dot_le_radius (v := g)
    (R := rho0) (by linarith [rho0_gt_one]) (normalized_center_radius P 2)
  have hAd := (P.contained 3).a_le_rho0
  have hx := mul_le_mul_of_nonneg_left P.box.1.2
    (show 0≤11/20+c/20 by linarith)
  have hy := mul_le_mul_of_nonneg_left P.box.2.2
    (show 0≤s/20 by positivity)
  dsimp [dot,g] at hWsupport hDWlower
  change (-11/20+(2/5)*c)*(P.square 2).center.1+(2/5)*s*(P.square 2).center.2≤rho0*L at hWsupport
  nlinarith only [hDWlower,hWlower,hDlower,hWsupport,hAd,hx,hy,hreserve]

end SquaresInCircles.Six.Analytic
