module
public import SquaresInCircles.Six.Analytic.FrozenTrigStress
public import SquaresInCircles.Six.Analytic.SharpFrontProfile
public import SquaresInCircles.Six.Stress.Support

@[expose] public section

/-!
# Analytic tools for frozen-center small-diagonal stresses

Only the four original rectangle corners are used in the applications. The
circle-support bounds are derived from actual containment, with an explicit
slope test whenever the primary cap bound is used. The concavity theorem
allows signed trigonometric coefficients and proves their combined curvature
on the whole domain rather than guessing the signs individually.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma normalization_radius_upper_sharp : R0<33771/20000 := by
  have h : Real.sqrt Q0<Real.sqrt ((33771/20000:ℝ)^2) :=
    Real.sqrt_lt_sqrt Q0_pos.le (by norm_num [Q0])
  rw [Real.sqrt_sq (by norm_num)] at h
  exact h

lemma normalization_center_upper_sharp : c0<5641/50000 := by
  dsimp [c0]
  linarith [normalization_rho_upper_sharp]

/-- A displayed rational root bound gives an upper support for any contained
center. Its force coefficients are nonnegative; the sign of b is unrestricted. -/
lemma circle_vertex_from_root_bound {a b U V L : ℝ}
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0)
    (hV : 0≤V) (hL : 0≤L) (hnorm : U^2+V^2≤L^2) :
    U*a+V*b≤(33771/20000)*L-(U+V)/2 := by
  have hroot := Real.sqrt_le_sqrt hnorm
  rw [Real.sqrt_sq hL] at hroot
  have hprod := mul_le_mul normalization_radius_upper_sharp.le hroot
    (Real.sqrt_nonneg (U^2+V^2)) (by norm_num : (0:ℝ)≤33771/20000)
  have hp : normSq (a+1/2,|b|+1/2)≤R0^2 := by
    simpa only [normSq,R0_sq] using hbox
  have hd := Stress.dot_le_radius (v := (U,V)) R0_nonneg hp
  have hb := mul_le_mul_of_nonneg_left (le_abs_self b) hV
  dsimp [dot,Stress.vectorLength,normSq] at hd
  nlinarith only [hd,hprod,hb]

/-- Primary cap support, selected by its proved slope condition. -/
lemma circle_primary_from_slope {a b U V : ℝ}
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0)
    (hU : 0≤U) (hV : 0≤V) (hslope : 2*(rho0+1/2)*V≤U) :
    U*a+V*b≤(55641/50000)*U := by
  have hcorner := disk_corner_support
    (A := a+1/2) (B := |b|+1/2) (a := rho0+1/2) (b := (1:ℝ)/2)
    (c := U) (s := V) (by linarith [rho0_gt_one])
    (by linarith [abs_nonneg b]) hU (by nlinarith [rho0_identity]) hbox (by linarith)
  have hb := mul_le_mul_of_nonneg_left (le_abs_self b) hV
  have hR := mul_le_mul_of_nonneg_right normalization_rho_upper_sharp.le hU
  nlinarith only [hcorner,hb,hR]

lemma central_projection_bound {cx cy X Y : ℝ}
    (hbox : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) (hX : 0≤X) :
    X*cx+Y*cy≤(5641/50000)*(X+max Y 0) := by
  have hx := Stress.scalar_box_support (v := X) hbox.1
  have hy := Stress.scalar_box_support (v := Y) hbox.2
  rw [max_eq_left hX] at hx
  have hupper := mul_le_mul_of_nonneg_right normalization_center_upper_sharp.le
    (show 0≤X+max Y 0 by linarith [le_max_right Y 0])
  nlinarith only [hx,hy,hupper]

/-- Sine and cosine on the entire rectangle's sum interval. -/
lemma small_secondary_trig {q : ℝ} (hq : 0≤q ∧ q≤7/6) :
    0≤Real.cos q ∧ 0≤Real.sin q ∧ Real.sin q≤15/16 := by
  have hc : 0≤Real.cos q := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.1,Real.pi_pos],by linarith [hq.2,Real.pi_gt_d2]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hq.1 (by linarith [hq.2,Real.pi_gt_d2])
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤q by linarith [hq.1,Real.pi_pos])
    (show (7:ℝ)/6≤Real.pi/2 by linarith [Real.pi_gt_d2]) hq.2
  have hu := Seven.sin_upper_five (x := (7:ℝ)/6) (by norm_num)
  exact ⟨hc,hs,by nlinarith only [hm,hu]⟩

lemma small_profile_trig_lower {A B z : ℝ}
    (hA : 387/1000≤A) (hB : 387/1000≤B) (hz : 0≤z ∧ z≤2/3) :
    387/1000≤A*Real.cos z+B*Real.sin z := by
  have ht := small_secondary_trig ⟨hz.1,by linarith [hz.2]⟩
  have hw := one_le_abs_cos_add_abs_sin z
  rw [abs_of_nonneg ht.1,abs_of_nonneg ht.2.1] at hw
  have hc := mul_le_mul_of_nonneg_right hA ht.1
  have hs := mul_le_mul_of_nonneg_right hB ht.2.1
  nlinarith only [hc,hs,hw]

/-- The signed outer trigonometric term is dominated by the central term.
This is the whole-domain curvature inequality used before support maximization. -/
lemma frozen_secondary_curvature {k A B a b z q : ℝ}
    (hk : 3/2≤k) (hA : 387/1000≤A) (hB : 387/1000≤B)
    (ha0 : 1/2≤a) (ha1 : a≤rho0) (hb : -1/2≤b)
    (hz : 0≤z ∧ z≤2/3) (hq : 0≤q ∧ q≤7/6) :
    0≤k*(A*Real.cos z+B*Real.sin z)+(1/2+b)*Real.cos q+(1/2-a)*Real.sin q := by
  have ht := small_secondary_trig hq
  have hcentral := small_profile_trig_lower hA hB hz
  have hc := mul_le_mul hk hcentral (by norm_num : (0:ℝ)≤387/1000) (by linarith)
  have hpositive := mul_nonneg (show 0≤1/2+b by linarith) ht.1
  have hnegative := mul_le_mul
    (show a-1/2≤613/1000 by linarith [rho0_upper]) ht.2.2 ht.2.1
    (by norm_num : (0:ℝ)≤613/1000)
  nlinarith only [hc,hpositive,hnegative]

/-- Nonnegative trigonometric value is precisely the required curvature sign;
its two coefficients themselves need not be nonnegative. -/
lemma signed_trig_concave {A B C l u : ℝ}
    (h : ∀ x∈Set.Icc l u, 0≤A*Real.cos x+B*Real.sin x) :
    ConcaveOn ℝ (Set.Icc l u) (fun x => C+A*Real.cos x+B*Real.sin x) := by
  have ht := radicalTrig_concave (A := A) (B := B) (p := 1) (q := 0) (R := 0)
    (l := l) (u := u) (by norm_num) (by norm_num)
    (by intro x _; norm_num) (by intro x hx; simpa using mul_nonneg (by norm_num : (0:ℝ)≤4) (h x hx))
  have hc := concave_constant C l u
  simpa [radicalTrig,add_assoc] using hc.add ht

lemma frozenTrig_concave_v_of_curvature {C Av Bv Ad Bd Aq Bq l u d : ℝ}
    (h : ∀ x∈Set.Icc l u,
      0≤Av*Real.cos x+Bv*Real.sin x+Aq*Real.cos (x+d)+Bq*Real.sin (x+d)) :
    ConcaveOn ℝ (Set.Icc l u) (fun v => frozenTrig C Av Bv Ad Bd Aq Bq v d) := by
  let A := Av+Aq*Real.cos d+Bq*Real.sin d
  let B := Bv-Aq*Real.sin d+Bq*Real.cos d
  have he (x : ℝ) : A*Real.cos x+B*Real.sin x =
      Av*Real.cos x+Bv*Real.sin x+Aq*Real.cos (x+d)+Bq*Real.sin (x+d) := by
    dsimp [A,B]
    rw [Real.cos_add,Real.sin_add]
    ring
  have hc := signed_trig_concave (A := A) (B := B)
    (C := C+Ad*Real.cos d+Bd*Real.sin d) (l := l) (u := u)
    (fun x hx => by rw [he]; exact h x hx)
  apply hc.congr
  intro x _
  rw [show C+Ad*Real.cos d+Bd*Real.sin d+A*Real.cos x+B*Real.sin x =
      C+Ad*Real.cos d+Bd*Real.sin d+(A*Real.cos x+B*Real.sin x) by ring,he]
  dsimp [frozenTrig]
  ring

lemma frozenTrig_concave_d_of_curvature {C Av Bv Ad Bd Aq Bq l u v : ℝ}
    (h : ∀ x∈Set.Icc l u,
      0≤Ad*Real.cos x+Bd*Real.sin x+Aq*Real.cos (v+x)+Bq*Real.sin (v+x)) :
    ConcaveOn ℝ (Set.Icc l u) (fun d => frozenTrig C Av Bv Ad Bd Aq Bq v d) := by
  have hc := frozenTrig_concave_v_of_curvature
    (C := C) (Av := Ad) (Bv := Bd) (Ad := Av) (Bd := Bv) (Aq := Aq) (Bq := Bq)
    (l := l) (u := u) (d := v) (by intro x hx; simpa only [add_comm] using h x hx)
  apply hc.congr
  intro x _
  dsimp [frozenTrig]
  rw [add_comm x v]
  ring

end SquaresInCircles.Six.Analytic
