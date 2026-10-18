module

public import SquaresInCircles.Eight.ExactFamily.Analysis
public import SquaresInCircles.Eight.ExactFamily.Weights
public import SquaresInCircles.Eight.ExactFamily.Generated.StationaryLocalization
public import SquaresInCircles.Eight.ExactFamily.TiltCurvature

/-!
# The exact selected stationary configuration

Uncompiled draft.  `sharpData` is selected from the analytic existence theorem;
its equations, branch signs, and uniqueness are conclusions.  Decimal strings
below are rational brackets, never definitions of the stationary root.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ExactFamily
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
    c,s,h₁,h₂,y₄,halfAngleCos,halfAngleSin,div_eq_mul_inv]

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
  simpa only [← hx₁,← hx₂,← hy₃,← hx₄,← hh₁,← hh₂] using
    And.intro h₁.1 (And.intro h₁.2 (And.intro h₂.1 (And.intro h₂.2
      (And.intro h₃.1 (And.intro h₃.2 (And.intro h₄.1 (And.intro h₄.2
        (And.intro h₅.1 (And.intro h₅.2 h₆)))))))))

theorem radical_isChain {q y z : ℝ} (he : localBox.Mem ![q,y,z]) :
    (radicalCoordinates q y z).IsChain := by
  obtain ⟨hx₁,_,hx₂,_,hy₃,_,_,hx₄,_⟩ := radical_local_bounds he
  have h₁ : 0 < (radicalCoordinates q y z).x₁ := by linarith
  have h₂ : 0 < (radicalCoordinates q y z).x₂ := by linarith
  have h₃ : 0 < (radicalCoordinates q y z).y₃ := by linarith
  have h₄ : (radicalCoordinates q y z).x₄ < 0 := by linarith
  have r₁ : 0 ≤ q-y^2 := (Real.sqrt_pos.mp h₁).le
  have r₂ : 0 ≤ q-(y+2)^2 := (Real.sqrt_pos.mp h₂).le
  have r₃ : 0 ≤ q-(Real.sqrt (q-(y+2)^2)-3)^2 := (Real.sqrt_pos.mp h₃).le
  have r₄ : 0 ≤ q-(Real.sqrt (q-(Real.sqrt (q-(y+2)^2)-3)^2)-2)^2 := by
    apply le_of_lt (Real.sqrt_pos.mp ?_)
    dsimp [radicalCoordinates] at h₄
    linarith
  refine ⟨h₁,h₂,h₃,h₄,?_,?_,?_,?_⟩ <;>
    simp [radicalCoordinates,x₃,y₄,Real.sq_sqrt,r₁,r₂,r₃,r₄] <;> ring

theorem radical_weightDomain {q y z : ℝ} (he : localBox.Mem ![q,y,z]) :
    (radicalCoordinates q y z).WeightDomain := by
  obtain ⟨hx₁,_,hx₂,hx₂u,hy₃,_,_,hx₄,_,hh₁,_,hh₂⟩ := radical_local_bounds he
  have hy := he 1
  have hz := he 2
  norm_num [localBox,QInterval.Mem] at hy hz
  refine ⟨by linarith,by linarith,by linarith,?_,by linarith,
    by simpa [radicalCoordinates] using (by linarith : y<0),
    by simpa [radicalCoordinates] using (by linarith : 0<y+2),
    halfAngleCos_pos (by rw [abs_lt]; constructor <;> linarith),
    halfAngleSin_pos (by linarith),by linarith,by linarith⟩
  dsimp [x₃]; linarith

theorem familyValue_radical (q y z : ℝ) :
    familyValue q (y,z) = (radicalCoordinates q y z).defect := by
  simp [familyValue,F_eval,scalarF,radicalCoordinates,defect,h₁,h₂,c,s,y₄,
    halfAngleCos,halfAngleSin,div_eq_mul_inv]

/-- The existing scalar function is exactly the geometric radical chain,
with position `u=-y`.  This identity does not assume stationarity, a box
membership, or even positivity of the radicals. -/
theorem familyValue_geometric (q u z : ℝ) :
    familyValue q (-u,z)=
      FiveCornerGeometry.defect q (halfAngleCos z) (halfAngleSin z) u := by
  let d := radicalCoordinates q (-u) z
  have hr : FiveCornerGeometry.lowerRight q u=d.x₁ := by
    change Real.sqrt (q-u^2)=Real.sqrt (q-(-u)^2)
    rw [sq_neg]
  have hU : FiveCornerGeometry.topRight q u=d.x₂ := by
    change Real.sqrt (q-(2-u)^2)=Real.sqrt (q-(-u+2)^2)
    congr 1
    ring
  have hY : FiveCornerGeometry.topHeight q u=d.y₃ := by
    change Real.sqrt (q-(3-FiveCornerGeometry.topRight q u)^2)=
      Real.sqrt (q-(d.x₂-3)^2)
    rw [hU]
    congr 1
    ring
  have hv : FiveCornerGeometry.lowerHeight q u=2-d.y₃ := by
    rw [FiveCornerGeometry.lowerHeight,hY]
  have hw : FiveCornerGeometry.lowerLeft q u= -d.x₄ := by
    change Real.sqrt (q-FiveCornerGeometry.lowerHeight q u^2)=
      -(-Real.sqrt (q-(d.y₃-2)^2))
    rw [hv,neg_neg]
    congr 1
    ring
  have hfirst : FiveCornerGeometry.firstComponent q (halfAngleCos z) (halfAngleSin z) u=
      -d.h₁ := by
    rw [FiveCornerGeometry.firstComponent,hr]
    change 2-halfAngleCos z*(d.x₁-1)+halfAngleSin z*u=
      -(halfAngleCos z*d.x₁+halfAngleSin z*(-u)-2-halfAngleCos z)
    ring
  have hsecond : FiveCornerGeometry.secondComponent q (halfAngleCos z) (halfAngleSin z) u=
      -d.h₂ := by
    rw [FiveCornerGeometry.secondComponent,hv,hw]
    change 1+halfAngleCos z*(2-d.y₃)-halfAngleSin z*(-d.x₄-1)=
      -(-halfAngleSin z*d.x₄+halfAngleCos z*(d.y₃-2)-1-halfAngleSin z)
    ring
  rw [familyValue_radical,FiveCornerGeometry.defect,hfirst,hsecond]
  change d.h₁^2+d.h₂^2-d.q=(-d.h₁)^2+(-d.h₂)^2-q
  have hdq : d.q=q := rfl
  rw [hdq]
  ring

/-- The strict-convexity interface for `familyValue` itself now covers the
entire radical position domain, including its endpoints. -/
theorem familyValue_position_strictConvex {q z : ℝ} (hq : q<4)
    (hz : 0 ≤ z) (hzu : z<1) :
    StrictConvexOn ℝ {u : ℝ | FiveCornerGeometry.Domain q u}
      (fun u => familyValue q (-u,z)) := by
  simpa only [familyValue_geometric] using FiveCornerGeometry.strictConvexOn_halfAngle hq hz hzu

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
  field_simp [hn₁,hn₂,hn₃,hn₄,hden]
  ring

theorem familyZ_radical (q y z : ℝ) :
    familyZ q (y,z) = (2/(1+z^2))*(radicalCoordinates q y z).tiltDerivative := by
  simp only [familyZ,Fz_eval]
  dsimp [scalarFz,tiltDerivative,h₁,h₂,c,s,y₄,halfAngleCos,halfAngleSin,
    radicalCoordinates]
  field_simp [ne_of_gt (halfAngle_den_pos z)]
  ring

theorem chain_eq_radical {d : Coordinates} (hd : d.IsChain) :
    d=radicalCoordinates d.q d.y d.z := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hd.radicals
  cases d
  simp_all [radicalCoordinates,Coordinates.x₃,Coordinates.y₄]

theorem stationary_local {d : Coordinates} (hd : d.IsStationary) :
    localBox.Mem ![d.q,d.y,d.z] := by
  have hc := chain_eq_radical hd.toIsChain
  have hzden : 0 < 1-d.z^2 := by nlinarith [hd.z_pos,hd.z_lt_one]
  have hzsmall : d.z < 1/10 := by
    have ht := (div_lt_iff₀ hzden).mp hd.tilt_range
    nlinarith [sq_nonneg d.z]
  apply stationary_localization ![d.q,d.y,d.z]
  · intro i; fin_cases i <;> norm_num [initialBox,QInterval.Mem]
    · exact ⟨by nlinarith [hd.q_lower],hd.q_upper⟩
    · exact ⟨hd.y_lower.le,hd.y_upper.le⟩
    · exact ⟨hd.z_pos.le,hzsmall.le⟩
  · intro i; fin_cases i
    · change familyValue d.q (d.y,d.z)=0
      rw [familyValue_radical,← hc]
      exact hd.zero_defect
    · change familyY d.q (d.y,d.z)=0
      rw [familyY_radical (hc ▸ hd.toIsChain),← hc]
      exact hd.position_stationary
    · change familyZ d.q (d.y,d.z)=0
      rw [familyZ_radical,← hc,hd.tilt_stationary,mul_zero]

theorem sharp_endpoint_signs : 0 < minimumValue sharpLower ∧ minimumValue sharpUpper < 0 := by
  have hL := sharpLowF_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFBox,QInterval.Mem])
  have hU := sharpHighF_bound ![sharpUpper,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpUpper,sharpHighFBox,QInterval.Mem])
  have hy := sharpLowFy_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFyBox,QInterval.Mem])
  have hz := sharpLowFz_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFzBox,QInterval.Mem])
  have hlo := minimum_trial_lower (q:=sharpLower) (by norm_num [sharpLower,radiusBox])
  have hup := minimumValue_le sharpUpper trial_mem
  change _ ≤ familyValue sharpLower trial ∧ _ at hL
  change _ ∧ familyValue sharpUpper trial ≤ _ at hU
  change _ ≤ familyY sharpLower trial ∧ familyY sharpLower trial ≤ _ at hy
  change _ ≤ familyZ sharpLower trial ∧ familyZ sharpLower trial ≤ _ at hz
  constructor <;> nlinarith

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
    intro i; fin_cases i <;> norm_num [sharpTrialFyBox,QInterval.Mem]
    exact ⟨hq.1.le,hq.2.le⟩)
  have hz := sharpTrialFz_bound ![qStar,trialY,trialZ] (by
    intro i; fin_cases i <;> norm_num [sharpTrialFzBox,QInterval.Mem]
    exact ⟨hq.1.le,hq.2.le⟩)
  have hc := family_strong_convex qStar_mem trial_mem (minimizingPose_mem qStar)
  have hm := minimumValue_le qStar trial_mem
  change _ ≤ familyY qStar trial ∧ familyY qStar trial ≤ _ at hy
  change _ ≤ familyZ qStar trial ∧ familyZ qStar trial ≤ _ at hz
  have hr : (sharpPose.1-trialY)^2+(sharpPose.2-trialZ)^2 <
      (1/1000000000000:ℝ)^2 := by
    dsimp [sharpPose,minimumValue,trial] at *
    nlinarith [sq_nonneg ((minimizingPose qStar).1-trialY+8*familyY qStar (trialY,trialZ)),
      sq_nonneg ((minimizingPose qStar).2-trialZ+8*familyZ qStar (trialY,trialZ))]
  constructor <;> rw [abs_lt] <;> constructor <;>
    nlinarith [sq_nonneg (sharpPose.1-trialY),sq_nonneg (sharpPose.2-trialZ)]

theorem sharpBox_mem : sharpBox.Mem ![qStar,sharpPose.1,sharpPose.2] := by
  have hq := qStar_bracket
  obtain ⟨hy,hz⟩ := sharpPose_close
  have hy' := abs_lt.mp hy
  have hz' := abs_lt.mp hz
  intro i; fin_cases i <;>
    norm_num [sharpBox,QInterval.Mem,sharpLower,sharpUpper,trialY,trialZ] at * <;>
    constructor <;> linarith

def sharpData : Coordinates := radicalCoordinates qStar sharpPose.1 sharpPose.2

theorem sharpData_stationary : sharpData.IsStationary := by
  have he := local_mem qStar_mem (minimizingPose_mem qStar)
  have hchain := radical_isChain he
  have hrad := radical_local_bounds he
  have hy := (minimizingPose_mem qStar).1
  have hz := (minimizingPose_mem qStar).2
  norm_num [poseBox] at hy hz
  refine { hchain with
    q_lower := by dsimp [sharpData,radicalCoordinates]; nlinarith [qStar_mem.1]
    q_upper := qStar_mem.2
    y_lower := by dsimp [sharpData,radicalCoordinates]; linarith
    y_upper := by dsimp [sharpData,radicalCoordinates]; linarith
    y₄_lower := ?_
    y₄_upper := ?_
    position_order := ?_
    z_pos := by dsimp [sharpData,radicalCoordinates]; linarith
    tilt_range := ?_
    z_lt_one := by dsimp [sharpData,radicalCoordinates]; linarith
    zero_defect := ?_
    position_stationary := ?_
    tilt_stationary := ?_ }
  · dsimp [sharpData,y₄]; linarith [hrad.2.2.2.2.1]
  · dsimp [sharpData,y₄]; linarith [hrad.2.2.2.2.2.1]
  · dsimp [sharpData,y₄,radicalCoordinates] at *
    linarith [hrad.2.2.2.2.1]
  · dsimp [sharpData,radicalCoordinates]
    rw [div_lt_iff₀ (by nlinarith : 0<1-sharpPose.2^2)]
    nlinarith
  · rw [← familyValue_radical]
    exact sharpPose_value
  · rw [← familyY_radical hchain]
    exact sharpPose_stationary.1
  · have hzv := sharpPose_stationary.2
    rw [familyZ_radical] at hzv
    exact (mul_eq_zero.mp hzv).resolve_left
      (ne_of_gt (div_pos (by norm_num) (halfAngle_den_pos sharpPose.2)))

theorem stationary_unique {d : Coordinates} (hd : d.IsStationary) : d=sharpData := by
  have he := stationary_local hd
  have hq : d.q ∈ radiusBox := he 0
  have hp : (d.y,d.z) ∈ poseBox := ⟨he 1,he 2⟩
  have hc := chain_eq_radical hd.toIsChain
  have hv : familyValue d.q (d.y,d.z)=0 := by
    rw [familyValue_radical,← hc]; exact hd.zero_defect
  have hy : familyY d.q (d.y,d.z)=0 := by
    rw [familyY_radical (hc ▸ hd.toIsChain),← hc]; exact hd.position_stationary
  have hz : familyZ d.q (d.y,d.z)=0 := by
    rw [familyZ_radical,← hc,hd.tilt_stationary,mul_zero]
  have hroot := (Classical.choose_spec stationary_existsUnique).2
    (d.q,(d.y,d.z)) ⟨hq,hp,hv,hy,hz⟩
  have hsharp := (Classical.choose_spec stationary_existsUnique).2
    (qStar,sharpPose) ⟨qStar_mem,minimizingPose_mem _,sharpPose_value,
      sharpPose_stationary.1,sharpPose_stationary.2⟩
  have hx : (d.q,(d.y,d.z))=(qStar,sharpPose) := hroot.trans hsharp.symm
  apply chain_unique_radicals hd.toIsChain sharpData_stationary.toIsChain
  · exact congrArg Prod.fst hx
  · exact congrArg (fun x : ℝ × Pose => x.2.1) hx
  · exact congrArg (fun x : ℝ × Pose => x.2.2) hx

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
  rw [hx₁] at h₁; rw [hx₂] at h₂; rw [hy₃] at h₃; rw [hx₄] at h₄
  rw [hc] at h₅; rw [hs] at h₆; rw [hh₁] at h₇; rw [hh₂] at h₈
  exact ⟨h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2,
    h₅.1,h₅.2,h₆.1,h₆.2,h₇.1,h₇.2,h₈.1,h₈.2⟩

theorem sharp_y : -92071/100000 < sharpData.y ∧ sharpData.y < -92059/100000 := by
  have h := abs_lt.mp sharpPose_close.1
  dsimp [sharpData,radicalCoordinates]
  norm_num [trialY] at h
  constructor <;> linarith

theorem sharp_mu_positive (i : Fin 5) : 0 < sharpData.mu i :=
  sharpData_stationary.weightDomain.mu_pos i

theorem sharp_lambda_positive (i : Fin 7) : 0 < sharpData.lam i :=
  sharpData_stationary.weightDomain.lam_pos i

end SquaresInCircles.Eight.ExactFamily
