module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Stationary.Analysis
public import SquaresInCircles.Eight.Stationary.Envelope

/-!
# Eight squares: the stationary configuration

`sharpData` is the chain at the stationary zero `(qStar, sharpPose)` of `Analysis.lean`, with its
coordinates given by the successive square roots (`radicalCoordinates`). Its equations, its
branch signs and its uniqueness are theorems: it solves the stationary system
(`sharpData_stationary`), and every solution of that system equals it (`stationary_unique`), by
the geometric argument of `Envelope.lean` (`FiveCornerGeometry.stationary_chain_unique`). The
decimals below are rational brackets for `qStar` and the coordinates (`qStar_bracket`,
`qStar_limits`, `sharp_coordinates`, `sharp_y`), not definitions of them.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Stationary
open Arithmetic Generated Coordinates

def radicalCoordinates (q y z : ℝ) : Coordinates where
  q := q
  y := y
  z := z
  x₁ := Real.sqrt (q-y^2)
  x₂ := Real.sqrt (q-(y+2)^2)
  y₃ := Real.sqrt (q-(Real.sqrt (q-(y+2)^2)-3)^2)
  x₄ := -Real.sqrt (q-(Real.sqrt (q-(Real.sqrt (q-(y+2)^2)-3)^2)-2)^2)

theorem radical_formula_values (q y z : ℝ) :
    xOneFormula.eval ![q,y,z] = (radicalCoordinates q y z).x₁ ∧
    xTwoFormula.eval ![q,y,z] = (radicalCoordinates q y z).x₂ ∧
    yThreeFormula.eval ![q,y,z] = (radicalCoordinates q y z).y₃ ∧
    xFourFormula.eval ![q,y,z] = (radicalCoordinates q y z).x₄ ∧
    cosineFormula.eval ![q,y,z] = (radicalCoordinates q y z).c ∧
    sineFormula.eval ![q,y,z] = (radicalCoordinates q y z).s ∧
    hOneFormula.eval ![q,y,z] = (radicalCoordinates q y z).h₁ ∧
    hTwoFormula.eval ![q,y,z] = (radicalCoordinates q y z).h₂ := by
  simp [xOne_eval,xTwo_eval,yThree_eval,xFour_eval,cosine_eval,sine_eval,
    hOne_eval,hTwo_eval,scalarxOne,scalarxTwo,scalaryThree,scalarxFour,
    scalarcosine,scalarsine,scalarhOne,scalarhTwo,radicalCoordinates,
    c,s,h₁,h₂,y₄,halfAngleCos,halfAngleSin,div_eq_mul_inv,sub_eq_add_neg]

theorem radical_local_bounds {q y z : ℝ} (he : localBox.Mem ![q,y,z]) :
    17428/10000 ≤ (radicalCoordinates q y z).x₁ ∧
      (radicalCoordinates q y z).x₁ ≤ 17649/10000 ∧
    16414/10000 ≤ (radicalCoordinates q y z).x₂ ∧
      (radicalCoordinates q y z).x₂ ≤ 16691/10000 ∧
    14387/10000 ≤ (radicalCoordinates q y z).y₃ ∧
      (radicalCoordinates q y z).y₃ ≤ 14643/10000 ∧
    -19049/10000 ≤ (radicalCoordinates q y z).x₄ ∧
      (radicalCoordinates q y z).x₄ ≤ -18974/10000 ∧
    -14263/10000 ≤ (radicalCoordinates q y z).h₁ ∧
      (radicalCoordinates q y z).h₁ ≤ -13198/10000 ∧
    -15316/10000 ≤ (radicalCoordinates q y z).h₂ ∧
      (radicalCoordinates q y z).h₂ ≤ -13202/10000 := by
  obtain ⟨hx₁,hx₂,hy₃,hx₄,hc,hs,hh₁,hh₂⟩ := radical_formula_values q y z
  have h₁ := localXOne_bound _ he
  have h₂ := localXTwo_bound _ he
  have h₃ := localYThree_bound _ he
  have h₄ := localXFour_bound _ he
  have h₅ := localHOne_bound _ he
  have h₆ := localHTwo_bound _ he
  rw [show formula10 = xOneFormula from rfl, hx₁] at h₁
  rw [show formula15 = xTwoFormula from rfl, hx₂] at h₂
  rw [show formula21 = yThreeFormula from rfl, hy₃] at h₃
  rw [show formula28 = xFourFormula from rfl, hx₄] at h₄
  rw [show formula42 = hOneFormula from rfl, hh₁] at h₅
  rw [show formula50 = hTwoFormula from rfl, hh₂] at h₆
  exact ⟨by linarith only [h₁.1],by linarith only [h₁.2],by linarith only [h₂.1],
    by linarith only [h₂.2],by linarith only [h₃.1],by linarith only [h₃.2],
    by linarith only [h₄.1],by linarith only [h₄.2],by linarith only [h₅.1],
    by linarith only [h₅.2],by linarith only [h₆.1],by linarith only [h₆.2]⟩

theorem radical_isChain {q y z : ℝ} (he : localBox.Mem ![q,y,z]) :
    (radicalCoordinates q y z).IsChain := by
  obtain ⟨hx₁,_,hx₂,_,hy₃,_,_,hx₄,_⟩ := radical_local_bounds he
  have h₁ : 0 < (radicalCoordinates q y z).x₁ := by linarith only [hx₁]
  have h₂ : 0 < (radicalCoordinates q y z).x₂ := by linarith only [hx₂]
  have h₃ : 0 < (radicalCoordinates q y z).y₃ := by linarith only [hy₃]
  have h₄ : (radicalCoordinates q y z).x₄ < 0 := by linarith only [hx₄]
  have r₁ : 0 ≤ q-y^2 := (Real.sqrt_pos.mp h₁).le
  have r₂ : 0 ≤ q-(y+2)^2 := (Real.sqrt_pos.mp h₂).le
  have r₃ : 0 ≤ q-(Real.sqrt (q-(y+2)^2)-3)^2 := (Real.sqrt_pos.mp h₃).le
  have r₄ : 0 ≤ q-(Real.sqrt (q-(Real.sqrt (q-(y+2)^2)-3)^2)-2)^2 := by
    apply le_of_lt (Real.sqrt_pos.mp ?_)
    dsimp [radicalCoordinates] at h₄
    linarith only [h₄]
  refine ⟨h₁,h₂,h₃,h₄,?_,?_,?_,?_⟩ <;>
    simp [radicalCoordinates,x₃,y₄,Real.sq_sqrt,r₁,r₂,r₃,r₄]

theorem familyValue_radical (q y z : ℝ) :
    familyValue q (y,z) = (radicalCoordinates q y z).defect := by
  simp [familyValue,F_eval,scalarF,radicalCoordinates,defect,h₁,h₂,c,s,y₄,
    halfAngleCos,halfAngleSin,div_eq_mul_inv,sub_eq_add_neg]

theorem familyY_radical {q y z : ℝ}
    (h : (radicalCoordinates q y z).IsChain) :
    familyY q (y,z) = (radicalCoordinates q y z).positionDerivative := by
  have hn₁ := ne_of_gt h.x₁_pos
  have hn₂ := ne_of_gt h.x₂_pos
  have hn₃ := ne_of_gt h.y₃_pos
  have hn₄ := ne_of_lt h.x₄_neg
  have hden := ne_of_gt (halfAngle_den_pos z)
  simp only [familyY,Fy_eval]
  dsimp [scalarFy,positionDerivative,h₁deriv,h₂deriv,y₄deriv,
    h₁,h₂,c,s,x₃,y₄,halfAngleCos,halfAngleSin,radicalCoordinates] at *
  push_cast
  simp only [sub_eq_add_neg]
  ring_nf

theorem familyZ_radical (q y z : ℝ) :
    familyZ q (y,z) = (2/(1+z^2))*(radicalCoordinates q y z).tiltDerivative := by
  simp only [familyZ,Fz_eval]
  dsimp [scalarFz,tiltDerivative,h₁,h₂,c,s,y₄,halfAngleCos,halfAngleSin,
    radicalCoordinates]
  field_simp [ne_of_gt (halfAngle_den_pos z)]
  ring_nf

theorem sharp_endpoint_signs : 0 < minimumValue sharpLower ∧ minimumValue sharpUpper < 0 := by
  have hL := sharpLowF_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFBox,QInterval.Mem,trialY,trialZ])
  have hU := sharpHighF_bound ![sharpUpper,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpUpper,sharpHighFBox,QInterval.Mem,trialY,trialZ])
  have hy := sharpLowFy_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFyBox,QInterval.Mem,trialY,trialZ])
  have hz := sharpLowFz_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFzBox,QInterval.Mem,trialY,trialZ])
  have hlo := minimum_trial_lower (q:=sharpLower) (by norm_num [sharpLower,radiusBox])
  have hup := minimumValue_le sharpUpper trial_mem
  change _ ≤ familyValue sharpLower trial ∧ _ at hL
  change _ ∧ familyValue sharpUpper trial ≤ _ at hU
  change _ ≤ familyY sharpLower trial ∧ familyY sharpLower trial ≤ _ at hy
  change _ ≤ familyZ sharpLower trial ∧ familyZ sharpLower trial ≤ _ at hz
  constructor <;> nlinarith only [hlo, hL, hy, hz, hup, hU]

theorem qStar_bracket : sharpLower < qStar ∧ qStar < sharpUpper := by
  obtain ⟨hL,hU⟩ := sharp_endpoint_signs
  constructor
  · by_contra! h
    have hh := (minimum_radius_difference qStar_mem
      (by norm_num [sharpLower,radiusBox]) h).2
    linarith [minimum_qStar]
  · by_contra! h
    have hh := (minimum_radius_difference
      (by norm_num [sharpUpper,radiusBox]) qStar_mem h).2
    linarith [minimum_qStar]

theorem qStar_limits : 7831/2000 < qStar ∧
    qStar < 1957767069/500000000 ∧ qStar < 9789/2500 := by
  have hh := qStar_bracket
  norm_num [sharpLower,sharpUpper] at hh
  constructor
  · linarith
  constructor <;> linarith

theorem sharpPose_close : |sharpPose.1-trialY| < 1/1000000000000 ∧
    |sharpPose.2-trialZ| < 1/1000000000000 := by
  have hq := qStar_bracket
  have hy := sharpTrialFy_bound ![qStar,trialY,trialZ] (by
    intro i; fin_cases i <;> norm_num [sharpTrialFyBox,QInterval.Mem,trialY,trialZ]
    norm_num [sharpLower,sharpUpper] at hq
    exact ⟨hq.1.le,hq.2.le⟩)
  have hz := sharpTrialFz_bound ![qStar,trialY,trialZ] (by
    intro i; fin_cases i <;> norm_num [sharpTrialFzBox,QInterval.Mem,trialY,trialZ]
    norm_num [sharpLower,sharpUpper] at hq
    exact ⟨hq.1.le,hq.2.le⟩)
  have hc := family_strong_convex qStar_mem trial_mem (minimizingPose_mem qStar)
  have hm := minimumValue_le qStar trial_mem
  change _ ≤ familyY qStar trial ∧ familyY qStar trial ≤ _ at hy
  change _ ≤ familyZ qStar trial ∧ familyZ qStar trial ≤ _ at hz
  have hr : (sharpPose.1-trialY)^2+(sharpPose.2-trialZ)^2 <
      (1/1000000000000:ℝ)^2 := by
    dsimp [sharpPose,minimumValue,trial] at *
    nlinarith only [sq_nonneg ((minimizingPose qStar).1-trialY+8*familyY qStar (trialY,trialZ)),
      sq_nonneg ((minimizingPose qStar).2-trialZ+8*familyZ qStar (trialY,trialZ)), hc, hm, hy, hz]
  exact ⟨abs_lt_of_sq_lt_sq (by linarith only [hr,sq_nonneg (sharpPose.2-trialZ)]) (by norm_num),
    abs_lt_of_sq_lt_sq (by linarith only [hr,sq_nonneg (sharpPose.1-trialY)]) (by norm_num)⟩

theorem sharpBox_mem : sharpBox.Mem ![qStar,sharpPose.1,sharpPose.2] := by
  have hq := qStar_bracket
  obtain ⟨hy,hz⟩ := sharpPose_close
  have hy' := abs_lt.mp hy
  have hz' := abs_lt.mp hz
  intro i; fin_cases i <;>
    norm_num [sharpBox,QInterval.Mem,sharpLower,sharpUpper,trialY,trialZ] at * <;>
    constructor <;> linarith only [hq, hy', hz']

def sharpData : Coordinates := radicalCoordinates qStar sharpPose.1 sharpPose.2

theorem sharpData_stationary : sharpData.IsStationary := by
  have he := local_mem qStar_mem (minimizingPose_mem qStar)
  have hchain : sharpData.IsChain := radical_isChain he
  have hrad := radical_local_bounds he
  have hy := (minimizingPose_mem qStar).1
  have hz := (minimizingPose_mem qStar).2
  norm_num [poseBox] at hy hz
  refine { hchain with
    q_lower := by dsimp [sharpData,radicalCoordinates]; linarith only [qStar_mem.1]
    q_upper := qStar_mem.2
    y_lower := by dsimp [sharpData,sharpPose,radicalCoordinates]; linarith only [hy]
    y_upper := by dsimp [sharpData,sharpPose,radicalCoordinates]; linarith only [hy]
    y₄_lower := ?_
    y₄_upper := ?_
    position_order := ?_
    z_pos := by dsimp [sharpData,sharpPose,radicalCoordinates]; linarith only [hz]
    tilt_range := ?_
    z_lt_one := by dsimp [sharpData,sharpPose,radicalCoordinates]; linarith only [hz]
    zero_defect := ?_
    position_stationary := ?_
    tilt_stationary := ?_ }
  · dsimp [sharpData,sharpPose,y₄]; linarith only [hrad.2.2.2.2.1]
  · dsimp [sharpData,sharpPose,y₄]; linarith only [hrad.2.2.2.2.2.1]
  · dsimp [sharpData,sharpPose,y₄,radicalCoordinates] at *
    linarith only [hrad.2.2.2.2.1, hy]
  · dsimp [sharpData,sharpPose,radicalCoordinates]
    rw [div_lt_iff₀ (by nlinarith only [hz] : 0<1-(minimizingPose qStar).2^2)]
    nlinarith only [hz]
  · exact (familyValue_radical qStar sharpPose.1 sharpPose.2).symm.trans sharpPose_value
  · exact (familyY_radical hchain).symm.trans sharpPose_stationary.1
  · have hzv := sharpPose_stationary.2
    rw [familyZ_radical] at hzv
    exact (mul_eq_zero.mp hzv).resolve_left
      (ne_of_gt (div_pos (by norm_num) (halfAngle_den_pos sharpPose.2)))

theorem stationary_unique {d : Coordinates} (hd : d.IsStationary) : d=sharpData :=
  FiveCornerGeometry.stationary_chain_unique hd sharpData_stationary

theorem exact_stationary_existsUnique : ∃! d : Coordinates, d.IsStationary :=
  ⟨sharpData,sharpData_stationary,fun _ h => stationary_unique h⟩

theorem sharp_coordinates :
    175152/100000 ≤ sharpData.x₁ ∧ sharpData.x₁ ≤ 175159/100000 ∧
    165843/100000 ≤ sharpData.x₂ ∧ sharpData.x₂ ≤ 165852/100000 ∧
    145455/100000 ≤ sharpData.y₃ ∧ sharpData.y₃ ≤ 145464/100000 ∧
    -190214/100000 ≤ sharpData.x₄ ∧ sharpData.x₄ ≤ -190211/100000 ∧
    99231/100000 ≤ sharpData.c ∧ sharpData.c ≤ 99242/100000 ∧
    12327/100000 ≤ sharpData.s ∧ sharpData.s ≤ 12338/100000 ∧
    -136797/100000 ≤ sharpData.h₁ ∧ sharpData.h₁ ≤ -136748/100000 ∧
    -143022/100000 ≤ sharpData.h₂ ∧ sharpData.h₂ ≤ -142976/100000 := by
  have hv := radical_formula_values qStar sharpPose.1 sharpPose.2
  have h₁ := sharpXOne_bound _ sharpBox_mem
  have h₂ := sharpXTwo_bound _ sharpBox_mem
  have h₃ := sharpYThree_bound _ sharpBox_mem
  have h₄ := sharpXFour_bound _ sharpBox_mem
  have h₅ := sharpCosine_bound _ sharpBox_mem
  have h₆ := sharpSine_bound _ sharpBox_mem
  have h₇ := sharpHOne_bound _ sharpBox_mem
  have h₈ := sharpHTwo_bound _ sharpBox_mem
  rcases hv with ⟨hx₁,hx₂,hy₃,hx₄,hc,hs,hh₁,hh₂⟩
  rw [show formula10 = xOneFormula from rfl, hx₁] at h₁
  rw [show formula15 = xTwoFormula from rfl, hx₂] at h₂
  rw [show formula21 = yThreeFormula from rfl, hy₃] at h₃
  rw [show formula28 = xFourFormula from rfl, hx₄] at h₄
  rw [show formula34 = cosineFormula from rfl, hc] at h₅
  rw [show formula36 = sineFormula from rfl, hs] at h₆
  rw [show formula42 = hOneFormula from rfl, hh₁] at h₇
  rw [show formula50 = hTwoFormula from rfl, hh₂] at h₈
  unfold sharpData
  exact ⟨by linarith only [h₁.1],by linarith only [h₁.2],by linarith only [h₂.1],
    by linarith only [h₂.2],by linarith only [h₃.1],by linarith only [h₃.2],
    by linarith only [h₄.1],by linarith only [h₄.2],by linarith only [h₅.1],
    by linarith only [h₅.2],by linarith only [h₆.1],by linarith only [h₆.2],
    by linarith only [h₇.1],by linarith only [h₇.2],by linarith only [h₈.1],
    by linarith only [h₈.2]⟩

theorem sharp_y : -92071/100000 < sharpData.y ∧ sharpData.y < -92059/100000 := by
  have h := abs_lt.mp sharpPose_close.1
  dsimp [sharpData,radicalCoordinates]
  norm_num [trialY] at h
  constructor <;> linarith

end SquaresInCircles.Eight.Stationary
