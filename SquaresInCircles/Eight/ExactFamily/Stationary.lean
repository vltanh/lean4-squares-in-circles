module

public import SquaresInCircles.Eight.ExactFamily.Analysis
public import SquaresInCircles.Eight.ExactFamily.Weights
public import SquaresInCircles.Eight.ExactFamily.Envelope

/-!
# Eight squares: the stationary configuration

`sharpData` is the chain at the stationary zero `(qStar, sharpPose)` of `Analysis.lean`, with its
coordinates given by the successive square roots (`radicalCoordinates`). Its equations, its
branch signs and its uniqueness are theorems: it solves the stationary system
(`sharpData_stationary`), and every solution of that system equals it (`stationary_unique`), by
the geometric argument of `Envelope.lean` (`FiveCornerGeometry.stationary_chain_unique`). The
decimals below are rational brackets for `qStar` and the coordinates (`qStar_bracket`,
`qStar_limits`, `sharp_coordinates`, `sharp_y`), not definitions of them. The coordinate
bounds follow from the circle equations, the half-angle formulas and products of short
decimal bounds; they use no separate interval certificates.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic Generated Coordinates

/-- The refined pose is used for the numerical radius bracket and coordinate bounds.
The existence proof uses the short decimal `trial` of `Analysis.lean`. -/
def refinementTrial : Pose := (trialY,trialZ)

theorem refinementTrial_mem : refinementTrial ∈ poseBox := by
  norm_num [refinementTrial,poseBox,trialY,trialZ]

theorem radical_formula_values (q y z : ℝ) :
    xOneFormula.eval ![q,y,z] = (radicalCoordinates q y z).x₁ ∧
    xTwoFormula.eval ![q,y,z] = (radicalCoordinates q y z).x₂ ∧
    yThreeFormula.eval ![q,y,z] = (radicalCoordinates q y z).y₃ ∧
    xFourFormula.eval ![q,y,z] = (radicalCoordinates q y z).x₄ ∧
    cosineFormula.eval ![q,y,z] = (radicalCoordinates q y z).c ∧
    sineFormula.eval ![q,y,z] = (radicalCoordinates q y z).s ∧
    hOneFormula.eval ![q,y,z] = (radicalCoordinates q y z).h₁ ∧
    hTwoFormula.eval ![q,y,z] = (radicalCoordinates q y z).h₂ := by
  simp [xOneFormula,xTwoFormula,yThreeFormula,xFourFormula,cosineFormula,sineFormula,
    hOneFormula,hTwoFormula,Formula.eval,radicalCoordinates,
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
  have hq := he 0
  have hy := he 1
  have hz := he 2
  norm_num [localBox,QInterval.Mem] at hq hy hz
  exact radical_coordinate_bounds hq
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩ hz

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

theorem radical_weightDomain {q y z : ℝ} (he : localBox.Mem ![q,y,z]) :
    (radicalCoordinates q y z).WeightDomain := by
  obtain ⟨hx₁,_,hx₂,hx₂u,hy₃,_,_,hx₄,_,hh₁,_,hh₂⟩ := radical_local_bounds he
  have hy := he 1
  have hz := he 2
  norm_num [localBox,QInterval.Mem] at hy hz
  have hyy : (radicalCoordinates q y z).y = y := rfl
  have hzz : (radicalCoordinates q y z).z = z := rfl
  refine ⟨by linarith only [hx₁],by linarith only [hx₂],by linarith only [hy₃],?_,
    by linarith only [hx₄],
    by rw [hyy]; linarith only [hy],
    by rw [hyy]; linarith only [hy],
    halfAngleCos_pos (by rw [hzz,abs_lt]; constructor <;> linarith only [hz]),
    halfAngleSin_pos (by rw [hzz]; linarith only [hz]),by linarith only [hh₁],
    by linarith only [hh₂]⟩
  dsimp [x₃]; linarith only [hx₂u]

theorem familyValue_radical (q y z : ℝ) :
    familyValue q (y,z) = (radicalCoordinates q y z).defect := by
  simp [familyValue,FFormula,Formula.eval,radicalCoordinates,defect,h₁,h₂,c,s,y₄,
    halfAngleCos,halfAngleSin,div_eq_mul_inv,sub_eq_add_neg]

theorem familyY_radical {q y z : ℝ}
    (h : (radicalCoordinates q y z).IsChain) :
    familyY q (y,z) = (radicalCoordinates q y z).positionDerivative := by
  rw [familyY_geometric]
  have hh := FiveCornerGeometry.coordinate_positionHalf h
  change 2*FiveCornerGeometry.positionHalf q (halfAngleCos z) (halfAngleSin z) (-y) = _ at hh
  linarith only [hh]

theorem familyZ_radical (q y z : ℝ) :
    familyZ q (y,z) = (2/(1+z^2))*(radicalCoordinates q y z).tiltDerivative := by
  rw [familyZ_geometric]
  congr 1
  let a := radicalCoordinates q y z
  have hvalues : FiveCornerGeometry.lowerRight q (-y) = a.x₁ ∧
      FiveCornerGeometry.topRight q (-y) = a.x₂ ∧ FiveCornerGeometry.topLeft q (-y) = -a.x₃ ∧
      FiveCornerGeometry.topHeight q (-y) = a.y₃ ∧
      FiveCornerGeometry.lowerHeight q (-y) = -a.y₄ ∧
      FiveCornerGeometry.lowerLeft q (-y) = -a.x₄ := FiveCornerGeometry.radical_coordinate_values q y z
  obtain ⟨hr,_,_,_,hv,hw⟩ := hvalues
  have hy : a.y = y := rfl
  have hz : a.z = z := rfl
  change _ = a.tiltDerivative
  simp only [FiveCornerGeometry.tiltFirst,FiveCornerGeometry.firstComponent,
    FiveCornerGeometry.secondComponent,FiveCornerGeometry.firstTilt,FiveCornerGeometry.secondTilt,
    hr,hv,hw,tiltDerivative,h₁,h₂,c,s,hy,hz]
  ring

theorem sharp_endpoint_signs : 0 < minimumValue sharpLower ∧ minimumValue sharpUpper < 0 := by
  have hL := sharpLowF_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFBox,QInterval.Mem,trialY,trialZ])
  have hU := sharpHighF_bound ![sharpUpper,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpUpper,sharpHighFBox,QInterval.Mem,trialY,trialZ])
  have hy := sharpLowFy_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFyBox,QInterval.Mem,trialY,trialZ])
  have hz := sharpLowFz_bound ![sharpLower,trialY,trialZ]
    (by intro i; fin_cases i <;> norm_num [sharpLower,sharpLowFzBox,QInterval.Mem,trialY,trialZ])
  have hlo := minimum_lower_at (q:=sharpLower) (by norm_num [sharpLower,radiusBox])
    refinementTrial_mem
  have hup := minimumValue_le sharpUpper refinementTrial_mem
  change _ ≤ familyValue sharpLower refinementTrial ∧ _ at hL
  change _ ∧ familyValue sharpUpper refinementTrial ≤ _ at hU
  change _ ≤ familyY sharpLower refinementTrial ∧ familyY sharpLower refinementTrial ≤ _ at hy
  change _ ≤ familyZ sharpLower refinementTrial ∧ familyZ sharpLower refinementTrial ≤ _ at hz
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
  have hc := family_strong_convex qStar_mem refinementTrial_mem (minimizingPose_mem qStar)
  have hm := minimumValue_le qStar refinementTrial_mem
  change _ ≤ familyY qStar refinementTrial ∧ familyY qStar refinementTrial ≤ _ at hy
  change _ ≤ familyZ qStar refinementTrial ∧ familyZ qStar refinementTrial ≤ _ at hz
  have hr : (sharpPose.1-trialY)^2+(sharpPose.2-trialZ)^2 <
      (1/1000000000000:ℝ)^2 := by
    dsimp [sharpPose,minimumValue,refinementTrial] at *
    nlinarith only [sq_nonneg ((minimizingPose qStar).1-trialY+8*familyY qStar (trialY,trialZ)),
      sq_nonneg ((minimizingPose qStar).2-trialZ+8*familyZ qStar (trialY,trialZ)), hc, hm, hy, hz]
  exact ⟨abs_lt_of_sq_lt_sq (by linarith only [hr,sq_nonneg (sharpPose.2-trialZ)]) (by norm_num),
    abs_lt_of_sq_lt_sq (by linarith only [hr,sq_nonneg (sharpPose.1-trialY)]) (by norm_num)⟩

/-- Coarse bounds on the stationary pose, shared by circle and root-motion estimates. -/
theorem sharpPose_bounds :
    (-0.920657 ≤ sharpPose.1 ∧ sharpPose.1 ≤ -0.920656) ∧
    (0.061897 ≤ sharpPose.2 ∧ sharpPose.2 ≤ 0.061898) := by
  have hy := abs_lt.mp sharpPose_close.1
  have hz := abs_lt.mp sharpPose_close.2
  norm_num [trialY] at hy
  norm_num [trialZ] at hz
  exact ⟨⟨by linarith only [hy],by linarith only [hy]⟩,
    ⟨by linarith only [hz],by linarith only [hz]⟩⟩

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

/-- Short bounds for `(q,y,z)` propagate along the four circle equations and the tilted frame. -/
private theorem coordinate_bounds_of_close {d : Coordinates} (hchain : d.IsChain)
    (hq : 3.915534 ≤ d.q ∧ d.q ≤ 3.915535)
    (hy : -0.920657 ≤ d.y ∧ d.y ≤ -0.920656)
    (hz : 0.061897 ≤ d.z ∧ d.z ≤ 0.061898) :
    175152/100000 ≤ d.x₁ ∧ d.x₁ ≤ 175159/100000 ∧
    165843/100000 ≤ d.x₂ ∧ d.x₂ ≤ 165852/100000 ∧
    145455/100000 ≤ d.y₃ ∧ d.y₃ ≤ 145464/100000 ∧
    -190214/100000 ≤ d.x₄ ∧ d.x₄ ≤ -190211/100000 ∧
    99231/100000 ≤ d.c ∧ d.c ≤ 99242/100000 ∧
    12327/100000 ≤ d.s ∧ d.s ≤ 12338/100000 ∧
    -136797/100000 ≤ d.h₁ ∧ d.h₁ ≤ -136748/100000 ∧
    -143022/100000 ≤ d.h₂ ∧ d.h₂ ≤ -142976/100000 := by
  have hx₁ : 1.75154 ≤ d.x₁ ∧ d.x₁ ≤ 1.75156 :=
    circle_coordinate_bounds hchain.first_circle hchain.x₁_pos.le (by norm_num)
      (by nlinarith only [hq.1,hy.1,hy.2]) (by nlinarith only [hq.2,hy.1,hy.2])
  have hx₂ : 1.65847 ≤ d.x₂ ∧ d.x₂ ≤ 1.65849 :=
    circle_coordinate_bounds hchain.second_circle hchain.x₂_pos.le (by norm_num)
      (by nlinarith only [hq.1,hy.1,hy.2]) (by nlinarith only [hq.2,hy.1,hy.2])
  have hy₃ : 1.45458 ≤ d.y₃ ∧ d.y₃ ≤ 1.45462 :=
    circle_coordinate_bounds (q:=d.q) (x:=d.y₃) (y:=d.x₂-3)
      (by simpa only [x₃,add_comm] using hchain.third_circle)
      hchain.y₃_pos.le (by norm_num)
      (by nlinarith only [hq.1,hx₂.1,hx₂.2]) (by nlinarith only [hq.2,hx₂.1,hx₂.2])
  have hx₄ : (-190214/100000) ≤ d.x₄ ∧ d.x₄ ≤ (-190211/100000) := by
    have h : (190211/100000) ≤ -d.x₄ ∧ -d.x₄ ≤ (190214/100000) :=
      circle_coordinate_bounds (by simpa [neg_sq,y₄] using hchain.fourth_circle)
        (neg_nonneg.mpr hchain.x₄_neg.le) (by norm_num)
        (by nlinarith only [hq.1,hy₃.1,hy₃.2]) (by nlinarith only [hq.2,hy₃.1,hy₃.2])
    constructor <;> linarith only [h]
  have hz₂ : (0.061897:ℝ)^2 ≤ d.z^2 ∧ d.z^2 ≤ (0.061898:ℝ)^2 := by
    constructor <;> nlinarith only [hz]
  have hc : (99231/100000) ≤ d.c ∧ d.c ≤ (99242/100000) := by
    dsimp only [c,halfAngleCos]
    constructor
    · rw [le_div_iff₀ (halfAngle_den_pos d.z)]
      nlinarith only [hz₂.2]
    · rw [div_le_iff₀ (halfAngle_den_pos d.z)]
      nlinarith only [hz₂.1]
  have hs : (12327/100000) ≤ d.s ∧ d.s ≤ (12338/100000) := by
    dsimp only [s,halfAngleSin]
    constructor
    · rw [le_div_iff₀ (halfAngle_den_pos d.z)]
      nlinarith only [hz.1,hz₂.2]
    · rw [div_le_iff₀ (halfAngle_den_pos d.z)]
      nlinarith only [hz.2,hz₂.1]
  have hcx := positive_product_bounds hc
    (show 0.75154 ≤ d.x₁-1 ∧ d.x₁-1 ≤ 0.75156 by constructor <;> linarith only [hx₁])
    (by norm_num) (by norm_num)
  have hsy := positive_product_bounds hs
    (show 0.920656 ≤ -d.y ∧ -d.y ≤ 0.920657 by constructor <;> linarith only [hy])
    (by norm_num) (by norm_num)
  have hcy := positive_product_bounds hc
    (show 0.54538 ≤ 2-d.y₃ ∧ 2-d.y₃ ≤ 0.54542 by constructor <;> linarith only [hy₃])
    (by norm_num) (by norm_num)
  have hsx := positive_product_bounds hs
    (show 0.90211 ≤ -d.x₄-1 ∧ -d.x₄-1 ≤ 0.90214 by constructor <;> linarith only [hx₄])
    (by norm_num) (by norm_num)
  have hh₁ : (-136797/100000) ≤ d.h₁ ∧ d.h₁ ≤ (-136748/100000) := by
    dsimp only [h₁]
    constructor <;> linarith only [hcx,hsy]
  have hh₂ : (-143022/100000) ≤ d.h₂ ∧ d.h₂ ≤ (-142976/100000) := by
    dsimp only [h₂,y₄]
    constructor <;> linarith only [hcy,hsx]
  exact ⟨by linarith only [hx₁.1],by linarith only [hx₁.2],
    by linarith only [hx₂.1],by linarith only [hx₂.2],
    by linarith only [hy₃.1],by linarith only [hy₃.2],
    hx₄.1,hx₄.2,hc.1,hc.2,hs.1,hs.2,hh₁.1,hh₁.2,hh₂.1,hh₂.2⟩

theorem sharp_coordinates :
    175152/100000 ≤ sharpData.x₁ ∧ sharpData.x₁ ≤ 175159/100000 ∧
    165843/100000 ≤ sharpData.x₂ ∧ sharpData.x₂ ≤ 165852/100000 ∧
    145455/100000 ≤ sharpData.y₃ ∧ sharpData.y₃ ≤ 145464/100000 ∧
    -190214/100000 ≤ sharpData.x₄ ∧ sharpData.x₄ ≤ -190211/100000 ∧
    99231/100000 ≤ sharpData.c ∧ sharpData.c ≤ 99242/100000 ∧
    12327/100000 ≤ sharpData.s ∧ sharpData.s ≤ 12338/100000 ∧
    -136797/100000 ≤ sharpData.h₁ ∧ sharpData.h₁ ≤ -136748/100000 ∧
    -143022/100000 ≤ sharpData.h₂ ∧ sharpData.h₂ ≤ -142976/100000 := by
  have hq : (3.915534:ℝ) ≤ qStar ∧ qStar ≤ 3.915535 := by
    have h := qStar_bracket
    norm_num [sharpLower,sharpUpper] at h
    constructor <;> linarith only [h]
  have hy : -0.920657 ≤ sharpData.y ∧ sharpData.y ≤ -0.920656 := sharpPose_bounds.1
  have hz : 0.061897 ≤ sharpData.z ∧ sharpData.z ≤ 0.061898 := sharpPose_bounds.2
  change (3.915534 ≤ sharpData.q ∧ sharpData.q ≤ 3.915535) at hq
  have hchain := sharpData_stationary.toIsChain
  exact coordinate_bounds_of_close hchain hq hy hz

theorem sharp_y : -92071/100000 < sharpData.y ∧ sharpData.y < -92059/100000 := by
  change -92071/100000 < sharpPose.1 ∧ sharpPose.1 < -92059/100000
  constructor <;> linarith only [sharpPose_bounds.1.1,sharpPose_bounds.1.2]

end SquaresInCircles.Eight.ExactFamily
