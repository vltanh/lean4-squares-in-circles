import SquaresInCircles.Six.Analytic.CardinalLowDiagonalEndpoints

/-!
# Support comparison for the cardinal-W low-diagonal stress

The sign of every transverse force component is proved on the full ordered
low-D domain. The support bounds are the universal far-vertex inequalities;
no cap approximation is used here. The D-sourced W norm depends on d, not on
w or d-w. Its exact mixed term is retained.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def cardLowWForce (ds : Bool) (w d : ℝ) : Point :=
  if ds then (cardLowBeta ds*Real.cos w+cardLowMu ds*Real.sin (d-w),
    -cardLowBeta ds*Real.sin w-cardLowMu ds*Real.cos (d-w))
  else (cardLowBeta ds*Real.cos w,-cardLowBeta ds*Real.sin w-cardLowMu ds)

def cardLowDForce (ds : Bool) (w d : ℝ) : Point :=
  if ds then (cardLowAlpha ds,cardLowMu ds)
  else (cardLowAlpha ds+cardLowMu ds*Real.sin (d-w),cardLowMu ds*Real.cos (d-w))

def cardLowFrozen (ds : Bool) (w d aw bw ad bd cx cy : ℝ) : ℝ :=
  1/2+(cardLowBeta ds/2)*(Real.cos w+|Real.sin w|)+
    (cardLowAlpha ds/2)*(Real.cos d+Real.sin d)+
    (cardLowMu ds/2)*(Real.cos (d-w)+Real.sin (d-w))-
    dot (cardLowWForce ds w d) (aw,bw)-dot (cardLowDForce ds w d) (ad,bd)-
    ((cardLowBeta ds+cardLowAlpha ds*Real.cos d)*cx+cardLowAlpha ds*Real.sin d*cy)

lemma cardLow_transverse_norm (beta mu w : ℝ) :
    (beta*Real.cos w)^2+(beta*Real.sin w+mu)^2=beta^2+mu^2+2*beta*mu*Real.sin w := by
  linear_combination beta^2*(Real.sin_sq_add_cos_sq w)

lemma cardLow_Ds_norm (beta mu w d : ℝ) :
    (beta*Real.cos w+mu*Real.sin (d-w))^2+
      (beta*Real.sin w+mu*Real.cos (d-w))^2=
      beta^2+mu^2+2*beta*mu*Real.sin d := by
  have hs : Real.sin w*Real.cos (d-w)+Real.cos w*Real.sin (d-w)=Real.sin d := by
    rw [← Real.sin_add]
    congr 1
    ring
  linear_combination beta^2*(Real.sin_sq_add_cos_sq w)+
    mu^2*(Real.sin_sq_add_cos_sq (d-w))+2*beta*mu*hs

lemma cardinal_low_trig {w d : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d) :
    0≤Real.cos w ∧ -(2/5)≤Real.sin w ∧
    (0≤Real.cos d ∧ 0≤Real.sin d) ∧
    (119/200≤Real.cos (d-w) ∧ 0≤Real.sin (d-w)) := by
  have hcw := cardLow_cos_lower hw
  have hsw : -(2/5)≤Real.sin w := by
    by_cases h : 0≤w
    · have hs := Real.sin_nonneg_of_nonneg_of_le_pi h
        (by linarith [hw.2,Real.pi_gt_d2])
      linarith
    · have hs := Real.sin_le (show 0≤-w by linarith)
      rw [Real.sin_neg] at hs
      linarith [hw.1]
  have hdt := cardLow_trig ⟨hd.1,by linarith [hd.2]⟩
  have hq : 0≤d-w ∧ d-w≤9/10 := by constructor <;> linarith [hw.1,hd.2]
  have hqt := cardLow_trig hq
  have hsq := mul_nonneg (sub_nonneg.mpr hq.2)
    (show 0≤9/10+(d-w) by linarith [hq.1])
  have hcq := Real.one_sub_sq_div_two_le_cos (x := d-w)
  exact ⟨by linarith,hsw,⟨hdt.1,hdt.2.1⟩,⟨by nlinarith,hqt.2.1⟩⟩

/-- The purely angle-dependent analytic gap is a valid lower bound on the
actual stress, with the central support correction included once. -/
theorem cardLowGap_le_frozen (ds : Bool) {w d aw bw ad bd cx cy : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    cardLowGap ds w d≤cardLowFrozen ds w d aw bw ad bd cx cy := by
  obtain ⟨hcw,hsw,hdt,hqt⟩ := cardinal_low_trig hw hd hwd
  have hcq : 0≤Real.cos (d-w) := by linarith [hqt.1]
  have hD' : ContainedChart ad |-bd| := by simpa only [abs_neg] using hD
  have hcentral := coarse_central_work hc
    (X := cardLowBeta ds+cardLowAlpha ds*Real.cos d)
    (Y := cardLowAlpha ds*Real.sin d)
    (by cases ds <;> dsimp [cardLowAlpha,cardLowBeta] <;> linarith [hdt.1])
    (by cases ds <;> dsimp [cardLowAlpha] <;> linarith [hdt.2]) le_rfl le_rfl
  have hpos (h : 0≤w) : 0≤Real.sin w :=
    Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [hw.2,Real.pi_gt_d2])
  have hneg (h : ¬0≤w) : Real.sin w≤0 := by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-w by linarith)
      (by linarith [hw.1,Real.pi_gt_d2])
    rw [Real.sin_neg] at hs
    linarith
  cases ds
  · have hWb := vertex_linear_upper hW
      (U := (40/100)*Real.cos w) (V := (40/100)*Real.sin w+25/100)
      (L := Real.sqrt (((40/100)*Real.cos w)^2+((40/100)*Real.sin w+25/100)^2))
      (by linarith) (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt (by positivity)]; exact le_rfl)
    rw [cardLow_transverse_norm] at hWb
    have hDb := vertex_linear_upper hD'
      (U := 35/100+(25/100)*Real.sin (d-w)) (V := (25/100)*Real.cos (d-w))
      (L := Real.sqrt ((35/100+(25/100)*Real.sin (d-w))^2+((25/100)*Real.cos (d-w))^2))
      (by positivity) (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt (by positivity)]; exact le_rfl)
    rw [low_rotating_norm] at hDb
    dsimp [cardLowAlpha,cardLowBeta] at hcentral
    unfold cardLowGap
    split_ifs with h
    · dsimp [cardLowSmooth,cardLowC,cardLowF,cardLowG,cardLowH,cardLowFrozen,
        cardLowWForce,cardLowDForce,cardLowAlpha,cardLowBeta,cardLowMu,sineRoot,dot]
      rw [abs_of_nonneg (hpos h)]
      nlinarith only [hWb,hDb,hcentral]
    · dsimp [cardLowSmooth,cardLowC,cardLowF,cardLowG,cardLowH,cardLowFrozen,
        cardLowWForce,cardLowDForce,cardLowAlpha,cardLowBeta,cardLowMu,sineRoot,dot]
      rw [abs_of_nonpos (hneg h)]
      nlinarith only [hWb,hDb,hcentral]
  · have hWb := vertex_linear_upper hW
      (U := (30/100)*Real.cos w+(27/100)*Real.sin (d-w))
      (V := (30/100)*Real.sin w+(27/100)*Real.cos (d-w))
      (L := Real.sqrt (((30/100)*Real.cos w+(27/100)*Real.sin (d-w))^2+
        ((30/100)*Real.sin w+(27/100)*Real.cos (d-w))^2))
      (by nlinarith [hqt.1]) (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt (by positivity)]; exact le_rfl)
    rw [cardLow_Ds_norm] at hWb
    have hDb := vertex_linear_upper hD' (U := (43:ℝ)/100) (V := (27:ℝ)/100)
      (L := (5078:ℝ)/10000) (by norm_num) (by norm_num) (by norm_num)
    dsimp [cardLowAlpha,cardLowBeta] at hcentral
    unfold cardLowGap
    split_ifs with h
    · dsimp [cardLowSmooth,cardLowC,cardLowF,cardLowG,cardLowH,cardLowFrozen,
        cardLowWForce,cardLowDForce,cardLowAlpha,cardLowBeta,cardLowMu,sineRoot,dot]
      rw [abs_of_nonneg (hpos h)]
      nlinarith only [hWb,hDb,hcentral]
    · dsimp [cardLowSmooth,cardLowC,cardLowF,cardLowG,cardLowH,cardLowFrozen,
        cardLowWForce,cardLowDForce,cardLowAlpha,cardLowBeta,cardLowMu,sineRoot,dot]
      rw [abs_of_nonpos (hneg h)]
      nlinarith only [hWb,hDb,hcentral]

end SquaresInCircles.Six.Analytic
