module

public import SquaresInCircles.Eight.ExactFamily.Adaptive

/-!
# Eight squares: bounds along the adaptive chain

The formulas of `Generated/AdaptiveFormula.lean` are read as quantities of the chain: the contact
weights (`adaptive_lambda_interpretation`), the nine owner reserves
(`adaptive_reserve_interpretation`) and `h₂` (`adaptive_hTwo_interpretation`). With the interval
checks of the 256 graph boxes this gives, at every tilt of `tiltBox`, a positive lower bound for
the owner reserves of the adaptive chain (`adaptive_owner_bounds`), an upper bound for its contact
weights (`adaptive_edge_weight_bound`) and bounds for `h₂` (`adaptive_hTwo_bound`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic Generated Coordinates

/-! The formulas are interpreted node by node. Each lemma below identifies one
shared node with the coordinate quantity it computes, so every step is a short
field identity. -/

private theorem AdaptiveBounds.base (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula10.eval ![q,y,z] = (radicalCoordinates q y z).x₁ ∧
    AdaptiveGenerated.adaptiveFormula15.eval ![q,y,z] = (radicalCoordinates q y z).x₂ ∧
    AdaptiveGenerated.adaptiveFormula21.eval ![q,y,z] = (radicalCoordinates q y z).y₃ ∧
    AdaptiveGenerated.adaptiveFormula28.eval ![q,y,z] = (radicalCoordinates q y z).x₄ ∧
    AdaptiveGenerated.adaptiveFormula34.eval ![q,y,z] = (radicalCoordinates q y z).c ∧
    AdaptiveGenerated.adaptiveFormula36.eval ![q,y,z] = (radicalCoordinates q y z).s ∧
    AdaptiveGenerated.adaptiveFormula42.eval ![q,y,z] = (radicalCoordinates q y z).h₁ ∧
    AdaptiveGenerated.adaptiveFormula50.eval ![q,y,z] = (radicalCoordinates q y z).h₂ :=
  radical_formula_values q y z

private theorem AdaptiveBounds.e10 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula10.eval ![q,y,z] = (radicalCoordinates q y z).x₁ :=
  (AdaptiveBounds.base q y z).1

private theorem AdaptiveBounds.e15 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula15.eval ![q,y,z] = (radicalCoordinates q y z).x₂ :=
  (AdaptiveBounds.base q y z).2.1

private theorem AdaptiveBounds.e21 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula21.eval ![q,y,z] = (radicalCoordinates q y z).y₃ :=
  (AdaptiveBounds.base q y z).2.2.1

private theorem AdaptiveBounds.e28 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula28.eval ![q,y,z] = (radicalCoordinates q y z).x₄ :=
  (AdaptiveBounds.base q y z).2.2.2.1

private theorem AdaptiveBounds.e34 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula34.eval ![q,y,z] = (radicalCoordinates q y z).c :=
  (AdaptiveBounds.base q y z).2.2.2.2.1

private theorem AdaptiveBounds.e36 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula36.eval ![q,y,z] = (radicalCoordinates q y z).s :=
  (AdaptiveBounds.base q y z).2.2.2.2.2.1

private theorem AdaptiveBounds.e42 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula42.eval ![q,y,z] = (radicalCoordinates q y z).h₁ :=
  (AdaptiveBounds.base q y z).2.2.2.2.2.2.1

private theorem AdaptiveBounds.e50 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula50.eval ![q,y,z] = (radicalCoordinates q y z).h₂ :=
  (AdaptiveBounds.base q y z).2.2.2.2.2.2.2

private theorem AdaptiveBounds.e11 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula11.eval ![q,y,z] = y+2 := by
  simp only [AdaptiveGenerated.adaptiveFormula11, AdaptiveGenerated.adaptiveFormula1,
    AdaptiveGenerated.adaptiveFormula4, Formula.eval, Matrix.cons_val_one, Matrix.cons_val_zero]
  push_cast
  ring

private theorem AdaptiveBounds.e17 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula17.eval ![q,y,z] = (radicalCoordinates q y z).x₃ := by
  simp only [AdaptiveGenerated.adaptiveFormula17, AdaptiveGenerated.adaptiveFormula16, Formula.eval,
    AdaptiveBounds.e15 q y z, Coordinates.x₃]
  push_cast
  ring

private theorem AdaptiveBounds.e23 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula23.eval ![q,y,z] = (radicalCoordinates q y z).y₄ := by
  simp only [AdaptiveGenerated.adaptiveFormula23, AdaptiveGenerated.adaptiveFormula22, Formula.eval,
    AdaptiveBounds.e21 q y z, Coordinates.y₄]
  push_cast
  ring

private theorem AdaptiveBounds.e27 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula27.eval ![q,y,z] = -(radicalCoordinates q y z).x₄ := by
  have h := AdaptiveBounds.e28 q y z
  simp only [AdaptiveGenerated.adaptiveFormula28, Formula.eval] at h
  linarith

private theorem AdaptiveBounds.e60 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula60.eval ![q,y,z] = (radicalCoordinates q y z).rawMuA := by
  simp only [AdaptiveGenerated.adaptiveFormula60, AdaptiveGenerated.adaptiveFormula59,
    AdaptiveGenerated.adaptiveFormula58, AdaptiveGenerated.adaptiveFormula4, Formula.eval,
    AdaptiveBounds.e10 q y z, AdaptiveBounds.e34 q y z, rawMuA]
  push_cast
  ring

private theorem AdaptiveBounds.e77 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula77.eval ![q,y,z] =
      (2*(-(radicalCoordinates q y z).x₄))⁻¹ := by
  simp only [AdaptiveGenerated.adaptiveFormula77, AdaptiveGenerated.adaptiveFormula76,
    AdaptiveGenerated.adaptiveFormula4, Formula.eval, AdaptiveBounds.e27 q y z]
  push_cast
  rfl

private theorem AdaptiveBounds.e255 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula255.eval ![q,y,z] = (radicalCoordinates q y z).rawAlpha := by
  simp only [AdaptiveGenerated.adaptiveFormula255, AdaptiveGenerated.adaptiveFormula254,
    AdaptiveGenerated.adaptiveFormula253, AdaptiveGenerated.adaptiveFormula251,
    AdaptiveGenerated.adaptiveFormula252, AdaptiveGenerated.adaptiveFormula1, Formula.eval,
    AdaptiveBounds.e10 q y z, AdaptiveBounds.e34 q y z, AdaptiveBounds.e36 q y z, rawAlpha,
    show (radicalCoordinates q y z).y = y from rfl, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

private theorem AdaptiveBounds.e257 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula257.eval ![q,y,z] = (radicalCoordinates q y z).rawMuB := by
  simp only [AdaptiveGenerated.adaptiveFormula257, AdaptiveGenerated.adaptiveFormula256,
    AdaptiveGenerated.adaptiveFormula95, AdaptiveGenerated.adaptiveFormula4, Formula.eval,
    AdaptiveBounds.e255 q y z, AdaptiveBounds.e11 q y z, rawMuB,
    show (radicalCoordinates q y z).y = y from rfl]
  push_cast
  ring

private theorem AdaptiveBounds.e260 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula260.eval ![q,y,z] = (radicalCoordinates q y z).rawBeta := by
  simp only [AdaptiveGenerated.adaptiveFormula260, AdaptiveGenerated.adaptiveFormula258,
    AdaptiveGenerated.adaptiveFormula259, Formula.eval, AdaptiveBounds.e255 q y z,
    AdaptiveBounds.e15 q y z, AdaptiveBounds.e11 q y z, rawBeta,
    show (radicalCoordinates q y z).y = y from rfl]
  ring

private theorem AdaptiveBounds.e264 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula264.eval ![q,y,z] = (radicalCoordinates q y z).rawMuD := by
  simp only [AdaptiveGenerated.adaptiveFormula264, AdaptiveGenerated.adaptiveFormula263,
    AdaptiveGenerated.adaptiveFormula262, AdaptiveGenerated.adaptiveFormula261,
    AdaptiveGenerated.adaptiveFormula4, Formula.eval, AdaptiveBounds.e260 q y z,
    AdaptiveBounds.e17 q y z, rawMuD, mul_neg, inv_neg]
  push_cast
  ring

private theorem AdaptiveBounds.e266 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula266.eval ![q,y,z] = (radicalCoordinates q y z).rawDelta := by
  simp only [AdaptiveGenerated.adaptiveFormula266, AdaptiveGenerated.adaptiveFormula265,
    AdaptiveGenerated.adaptiveFormula4, Formula.eval, AdaptiveBounds.e264 q y z,
    AdaptiveBounds.e21 q y z, rawDelta]
  push_cast
  ring

private theorem AdaptiveBounds.e269 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula269.eval ![q,y,z] = (radicalCoordinates q y z).rawMuH := by
  simp only [AdaptiveGenerated.adaptiveFormula269, AdaptiveGenerated.adaptiveFormula268,
    AdaptiveGenerated.adaptiveFormula267, AdaptiveGenerated.adaptiveFormula4, Formula.eval,
    AdaptiveBounds.e42 q y z, rawMuH, mul_neg, inv_neg]
  push_cast
  ring

private theorem AdaptiveBounds.e272 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula272.eval ![q,y,z] = (radicalCoordinates q y z).rawEpsilon := by
  simp only [AdaptiveGenerated.adaptiveFormula272, AdaptiveGenerated.adaptiveFormula270,
    AdaptiveGenerated.adaptiveFormula271, AdaptiveGenerated.adaptiveFormula267, Formula.eval,
    AdaptiveBounds.e42 q y z, AdaptiveBounds.e50 q y z, rawEpsilon, inv_neg]
  ring

private theorem AdaptiveBounds.e274 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula274.eval ![q,y,z] = (radicalCoordinates q y z).rawMuE := by
  simp only [AdaptiveGenerated.adaptiveFormula274, AdaptiveGenerated.adaptiveFormula273,
    Formula.eval, AdaptiveBounds.e36 q y z, AdaptiveBounds.e272 q y z, AdaptiveBounds.e77 q y z,
    rawMuE, mul_neg, inv_neg]
  ring

private theorem AdaptiveBounds.e278 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula278.eval ![q,y,z] = (radicalCoordinates q y z).weightMass := by
  simp only [AdaptiveGenerated.adaptiveFormula278, AdaptiveGenerated.adaptiveFormula277,
    AdaptiveGenerated.adaptiveFormula276, AdaptiveGenerated.adaptiveFormula275, Formula.eval,
    AdaptiveBounds.e60 q y z, AdaptiveBounds.e257 q y z, AdaptiveBounds.e264 q y z,
    AdaptiveBounds.e274 q y z, AdaptiveBounds.e269 q y z, weightMass, Fin.sum_univ_five, rawMu,
    Matrix.cons_val]

private theorem AdaptiveBounds.e279 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula279.eval ![q,y,z] = (radicalCoordinates q y z).edgeOmega := by
  simp only [AdaptiveGenerated.adaptiveFormula279, Formula.eval, AdaptiveBounds.e278 q y z,
    edgeOmega, lam, rawLambda, Matrix.cons_val]
  ring

private theorem AdaptiveBounds.e280 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula280.eval ![q,y,z] = (radicalCoordinates q y z).edgeAlpha := by
  simp only [AdaptiveGenerated.adaptiveFormula280, Formula.eval, AdaptiveBounds.e279 q y z,
    AdaptiveBounds.e255 q y z, edgeOmega, edgeAlpha, lam, rawLambda, Matrix.cons_val]
  ring

private theorem AdaptiveBounds.e281 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula281.eval ![q,y,z] = (radicalCoordinates q y z).edgeBeta := by
  simp only [AdaptiveGenerated.adaptiveFormula281, Formula.eval, AdaptiveBounds.e279 q y z,
    AdaptiveBounds.e260 q y z, edgeOmega, edgeBeta, lam, rawLambda, Matrix.cons_val]
  ring

private theorem AdaptiveBounds.e282 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula282.eval ![q,y,z] = (radicalCoordinates q y z).edgeDelta := by
  simp only [AdaptiveGenerated.adaptiveFormula282, Formula.eval, AdaptiveBounds.e279 q y z,
    AdaptiveBounds.e266 q y z, edgeOmega, edgeDelta, lam, rawLambda, Matrix.cons_val]
  ring

private theorem AdaptiveBounds.e283 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula283.eval ![q,y,z] =
      (radicalCoordinates q y z).edgeEpsilon := by
  simp only [AdaptiveGenerated.adaptiveFormula283, Formula.eval, AdaptiveBounds.e279 q y z,
    AdaptiveBounds.e272 q y z, edgeOmega, edgeEpsilon, lam, rawLambda, Matrix.cons_val]
  ring

private theorem AdaptiveBounds.e290 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula290.eval ![q,y,z] = (radicalCoordinates q y z).cutY := by
  simp only [AdaptiveGenerated.adaptiveFormula290, AdaptiveGenerated.adaptiveFormula289,
    Formula.eval, AdaptiveBounds.e10 q y z, AdaptiveBounds.e15 q y z, cutY]
  ring

private theorem AdaptiveBounds.e298 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula298.eval ![q,y,z] = (radicalCoordinates q y z).cutJ := by
  simp only [AdaptiveGenerated.adaptiveFormula298, AdaptiveGenerated.adaptiveFormula293,
    AdaptiveGenerated.adaptiveFormula291, AdaptiveGenerated.adaptiveFormula292,
    AdaptiveGenerated.adaptiveFormula297, AdaptiveGenerated.adaptiveFormula296,
    AdaptiveGenerated.adaptiveFormula294, AdaptiveGenerated.adaptiveFormula295,
    AdaptiveGenerated.adaptiveFormula261, Formula.eval, AdaptiveBounds.e283 q y z,
    AdaptiveBounds.e34 q y z, AdaptiveBounds.e281 q y z, AdaptiveBounds.e21 q y z,
    AdaptiveBounds.e27 q y z, AdaptiveBounds.e17 q y z, cutJ, inv_neg]
  ring

private theorem AdaptiveBounds.e300 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula300.eval ![q,y,z] = (radicalCoordinates q y z).cutX := by
  simp only [AdaptiveGenerated.adaptiveFormula300, AdaptiveGenerated.adaptiveFormula299,
    Formula.eval, AdaptiveBounds.e281 q y z, AdaptiveBounds.e11 q y z, AdaptiveBounds.e298 q y z,
    cutX, show (radicalCoordinates q y z).y = y from rfl]

private theorem AdaptiveBounds.e302 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula302.eval ![q,y,z] = (radicalCoordinates q y z).cutK := by
  simp only [AdaptiveGenerated.adaptiveFormula302, AdaptiveGenerated.adaptiveFormula301,
    Formula.eval, AdaptiveBounds.e281 q y z, AdaptiveBounds.e21 q y z, AdaptiveBounds.e298 q y z,
    cutK]

private theorem AdaptiveBounds.e307 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula307.eval ![q,y,z] = (radicalCoordinates q y z).cutL := by
  simp only [AdaptiveGenerated.adaptiveFormula307, AdaptiveGenerated.adaptiveFormula305,
    AdaptiveGenerated.adaptiveFormula303, AdaptiveGenerated.adaptiveFormula304,
    AdaptiveGenerated.adaptiveFormula306, Formula.eval, AdaptiveBounds.e283 q y z,
    AdaptiveBounds.e36 q y z, AdaptiveBounds.e23 q y z, AdaptiveBounds.e27 q y z, cutL, inv_neg]
  ring

private theorem AdaptiveBounds.e313 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula313.eval ![q,y,z] = (radicalCoordinates q y z).h₂tilt := by
  simp only [AdaptiveGenerated.adaptiveFormula313, AdaptiveGenerated.adaptiveFormula310,
    AdaptiveGenerated.adaptiveFormula309, AdaptiveGenerated.adaptiveFormula308,
    AdaptiveGenerated.adaptiveFormula312, AdaptiveGenerated.adaptiveFormula311,
    AdaptiveGenerated.adaptiveFormula3, Formula.eval, AdaptiveBounds.e34 q y z,
    AdaptiveBounds.e28 q y z, AdaptiveBounds.e36 q y z, AdaptiveBounds.e23 q y z, h₂tilt]
  push_cast
  ring

private theorem AdaptiveBounds.e315 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula315.eval ![q,y,z] =
      (radicalCoordinates q y z).edgeEpsilon*
        ((radicalCoordinates q y z).h₁+(radicalCoordinates q y z).h₂tilt) := by
  simp only [AdaptiveGenerated.adaptiveFormula315, AdaptiveGenerated.adaptiveFormula314,
    Formula.eval, AdaptiveBounds.e283 q y z, AdaptiveBounds.e42 q y z, AdaptiveBounds.e313 q y z]

private theorem AdaptiveBounds.e316 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula316.eval ![q,y,z] = (radicalCoordinates q y z).cutN := by
  simp only [AdaptiveGenerated.adaptiveFormula316, Formula.eval, AdaptiveBounds.e315 q y z, cutN]
  ring

private theorem AdaptiveBounds.r1 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula321.eval ![q,y,z] =
      (radicalCoordinates q y z).edgeAlpha*(1-(radicalCoordinates q y z).cutY)
        -(radicalCoordinates q y z).cutX := by
  simp only [AdaptiveGenerated.adaptiveFormula321, AdaptiveGenerated.adaptiveFormula319,
    AdaptiveGenerated.adaptiveFormula318, AdaptiveGenerated.adaptiveFormula317,
    AdaptiveGenerated.adaptiveFormula320, AdaptiveGenerated.adaptiveFormula3, Formula.eval,
    AdaptiveBounds.e280 q y z, AdaptiveBounds.e290 q y z, AdaptiveBounds.e300 q y z]
  push_cast
  ring

private theorem AdaptiveBounds.r3 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula323.eval ![q,y,z] =
      (radicalCoordinates q y z).edgeBeta-(radicalCoordinates q y z).cutK := by
  simp only [AdaptiveGenerated.adaptiveFormula323, AdaptiveGenerated.adaptiveFormula322,
    Formula.eval, AdaptiveBounds.e281 q y z, AdaptiveBounds.e302 q y z]
  ring

private theorem AdaptiveBounds.r4 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula327.eval ![q,y,z] =
      (radicalCoordinates q y z).edgeBeta*(-917/1000-(radicalCoordinates q y z).cutJ) := by
  simp only [AdaptiveGenerated.adaptiveFormula327, AdaptiveGenerated.adaptiveFormula326,
    AdaptiveGenerated.adaptiveFormula324, AdaptiveGenerated.adaptiveFormula325, Formula.eval,
    AdaptiveBounds.e281 q y z, AdaptiveBounds.e298 q y z]
  push_cast
  ring

private theorem AdaptiveBounds.r5 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula330.eval ![q,y,z] =
      (radicalCoordinates q y z).edgeBeta*(1057/1000+(radicalCoordinates q y z).cutJ) := by
  simp only [AdaptiveGenerated.adaptiveFormula330, AdaptiveGenerated.adaptiveFormula329,
    AdaptiveGenerated.adaptiveFormula328, Formula.eval, AdaptiveBounds.e281 q y z,
    AdaptiveBounds.e298 q y z]
  push_cast
  ring

private theorem AdaptiveBounds.r7 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula334.eval ![q,y,z] =
      (radicalCoordinates q y z).cutN-(392/1000)*(radicalCoordinates q y z).edgeOmega := by
  simp only [AdaptiveGenerated.adaptiveFormula334, AdaptiveGenerated.adaptiveFormula333,
    AdaptiveGenerated.adaptiveFormula332, AdaptiveGenerated.adaptiveFormula331, Formula.eval,
    AdaptiveBounds.e316 q y z, AdaptiveBounds.e279 q y z]
  push_cast
  ring

private theorem AdaptiveBounds.r8 (q y z : ℝ) :
    AdaptiveGenerated.adaptiveFormula337.eval ![q,y,z] =
      (485/1000)*(radicalCoordinates q y z).edgeOmega-(radicalCoordinates q y z).cutN := by
  simp only [AdaptiveGenerated.adaptiveFormula337, AdaptiveGenerated.adaptiveFormula336,
    AdaptiveGenerated.adaptiveFormula335, Formula.eval, AdaptiveBounds.e279 q y z,
    AdaptiveBounds.e315 q y z, cutN]
  push_cast
  ring

theorem adaptive_lambda_interpretation (q y z : ℝ) (j : Fin 7) :
    (AdaptiveGenerated.lambdaFormula j).eval ![q,y,z] = (radicalCoordinates q y z).lam j := by
  fin_cases j
  · exact AdaptiveBounds.e280 q y z
  · exact AdaptiveBounds.e281 q y z
  · exact (AdaptiveBounds.e281 q y z).trans (by simp [edgeBeta,lam,rawLambda])
  · exact AdaptiveBounds.e282 q y z
  · exact AdaptiveBounds.e279 q y z
  · exact (AdaptiveBounds.e279 q y z).trans (by simp [edgeOmega,lam,rawLambda])
  · exact AdaptiveBounds.e283 q y z

theorem adaptive_reserve_interpretation (q y z : ℝ) (j : Fin 9) :
    (AdaptiveGenerated.reserveFormula j).eval ![q,y,z] =
      (radicalCoordinates q y z).ownerReserve j := by
  fin_cases j
  · exact AdaptiveBounds.e300 q y z
  · exact AdaptiveBounds.r1 q y z
  · exact AdaptiveBounds.e302 q y z
  · exact AdaptiveBounds.r3 q y z
  · exact AdaptiveBounds.r4 q y z
  · exact AdaptiveBounds.r5 q y z
  · exact AdaptiveBounds.e307 q y z
  · exact AdaptiveBounds.r7 q y z
  · exact AdaptiveBounds.r8 q y z

theorem adaptive_hTwo_interpretation (q y z : ℝ) :
    AdaptiveGenerated.hTwoFormula.eval ![q,y,z] = (radicalCoordinates q y z).h₂ :=
  AdaptiveBounds.e50 q y z

theorem adaptive_owner_bounds {z : ℝ} (hz : z ∈ tiltBox) (j : Fin 9) :
    56793/5000000 ≤ (adaptiveData z hz).ownerReserve j := by
  obtain ⟨i,hi⟩ := adaptive_graph_mem hz
  have hb := AdaptiveGenerated.reserve_bound i j _ hi
  simpa [adaptive_reserve_interpretation,adaptiveData] using hb

theorem adaptive_edge_weight_bound {z : ℝ} (hz : z ∈ tiltBox) (j : Fin 7) :
    (adaptiveData z hz).lam j ≤ 4209/5000 := by
  obtain ⟨i,hi⟩ := adaptive_graph_mem hz
  have hb := AdaptiveGenerated.weight_bound i j _ hi
  simpa [adaptive_lambda_interpretation,adaptiveData] using hb

theorem adaptive_hTwo_bound {z : ℝ} (hz : z ∈ tiltBox) :
    -29/20 ≤ (adaptiveData z hz).h₂ ∧ (adaptiveData z hz).h₂ ≤ -7/5 := by
  obtain ⟨i,hi⟩ := adaptive_graph_mem hz
  have hb := AdaptiveGenerated.hTwo_bound i _ hi
  simpa [adaptive_hTwo_interpretation,adaptiveData,neg_div] using hb

end SquaresInCircles.Eight.ExactFamily
