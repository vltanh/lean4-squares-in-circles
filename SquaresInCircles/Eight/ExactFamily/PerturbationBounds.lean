module

public import SquaresInCircles.Eight.ExactFamily.PerturbationEstimates

/-!
# Eight squares: the remainder coefficients along the adaptive chain

The quadratic and cubic remainder coefficients of the terminal inequality are the formulas
`quadraticFormula` and `cubicFormula` of `Generated/AdaptiveFormula.lean` (`remainder_formulas`),
so the interval checks of the graph boxes bound them by `232/25` and `3/2` at every tilt of
`tiltBox` (`adaptive_remainder_bounds`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExactFamily.Perturbation
open Arithmetic Generated Coordinates

theorem remainder_formulas (q y z : ℝ) (hw : (radicalCoordinates q y z).WeightDomain) :
    AdaptiveGenerated.quadraticFormula.eval ![q,y,z]=
      quadraticCoefficient (radicalCoordinates q y z) (4209/5000) ∧
    AdaptiveGenerated.cubicFormula.eval ![q,y,z]=
      cubicCoefficient (radicalCoordinates q y z) (4209/5000) := by
  obtain ⟨ha,hb,hd,he,hh⟩ := coefficient_identities hw
  have hα : AdaptiveGenerated.adaptiveFormula280.eval ![q,y,z]=
      (radicalCoordinates q y z).edgeAlpha := adaptive_lambda_interpretation q y z 0
  have hβ : AdaptiveGenerated.adaptiveFormula281.eval ![q,y,z]=
      (radicalCoordinates q y z).edgeBeta := adaptive_lambda_interpretation q y z 1
  have hδ : AdaptiveGenerated.adaptiveFormula282.eval ![q,y,z]=
      (radicalCoordinates q y z).edgeDelta := adaptive_lambda_interpretation q y z 3
  have hε : AdaptiveGenerated.adaptiveFormula283.eval ![q,y,z]=
      (radicalCoordinates q y z).edgeEpsilon := adaptive_lambda_interpretation q y z 6
  dsimp only [quadraticCoefficient,cubicCoefficient]
  rw [ha,hb,hd,he,hh]
  constructor
  · simp only [AdaptiveGenerated.quadraticFormula,AdaptiveGenerated.adaptiveFormula0,AdaptiveGenerated.adaptiveFormula1,AdaptiveGenerated.adaptiveFormula2,AdaptiveGenerated.adaptiveFormula3,AdaptiveGenerated.adaptiveFormula4,AdaptiveGenerated.adaptiveFormula6,AdaptiveGenerated.adaptiveFormula7,AdaptiveGenerated.adaptiveFormula9,AdaptiveGenerated.adaptiveFormula10,AdaptiveGenerated.adaptiveFormula11,AdaptiveGenerated.adaptiveFormula12,AdaptiveGenerated.adaptiveFormula13,AdaptiveGenerated.adaptiveFormula14,AdaptiveGenerated.adaptiveFormula15,AdaptiveGenerated.adaptiveFormula16,AdaptiveGenerated.adaptiveFormula17,AdaptiveGenerated.adaptiveFormula18,AdaptiveGenerated.adaptiveFormula19,AdaptiveGenerated.adaptiveFormula20,AdaptiveGenerated.adaptiveFormula21,AdaptiveGenerated.adaptiveFormula22,AdaptiveGenerated.adaptiveFormula23,AdaptiveGenerated.adaptiveFormula24,AdaptiveGenerated.adaptiveFormula25,AdaptiveGenerated.adaptiveFormula26,AdaptiveGenerated.adaptiveFormula27,AdaptiveGenerated.adaptiveFormula29,AdaptiveGenerated.adaptiveFormula30,AdaptiveGenerated.adaptiveFormula31,AdaptiveGenerated.adaptiveFormula32,AdaptiveGenerated.adaptiveFormula33,AdaptiveGenerated.adaptiveFormula34,AdaptiveGenerated.adaptiveFormula35,AdaptiveGenerated.adaptiveFormula36,AdaptiveGenerated.adaptiveFormula303,AdaptiveGenerated.adaptiveFormula338,AdaptiveGenerated.adaptiveFormula339,AdaptiveGenerated.adaptiveFormula340,AdaptiveGenerated.adaptiveFormula343,AdaptiveGenerated.adaptiveFormula344,AdaptiveGenerated.adaptiveFormula345,AdaptiveGenerated.adaptiveFormula348,AdaptiveGenerated.adaptiveFormula349,AdaptiveGenerated.adaptiveFormula350,AdaptiveGenerated.adaptiveFormula351,AdaptiveGenerated.adaptiveFormula352,AdaptiveGenerated.adaptiveFormula353,AdaptiveGenerated.adaptiveFormula354,AdaptiveGenerated.adaptiveFormula356,AdaptiveGenerated.adaptiveFormula357,AdaptiveGenerated.adaptiveFormula358,Formula.eval,hα,hδ,hε]
    simp only [radicalCoordinates,c,s,halfAngleCos,halfAngleSin,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Rat.cast_ofNat,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one]
    push_cast
    ring_nf
  · simp only [AdaptiveGenerated.cubicFormula,AdaptiveGenerated.adaptiveFormula0,AdaptiveGenerated.adaptiveFormula1,AdaptiveGenerated.adaptiveFormula2,AdaptiveGenerated.adaptiveFormula3,AdaptiveGenerated.adaptiveFormula4,AdaptiveGenerated.adaptiveFormula6,AdaptiveGenerated.adaptiveFormula7,AdaptiveGenerated.adaptiveFormula9,AdaptiveGenerated.adaptiveFormula10,AdaptiveGenerated.adaptiveFormula11,AdaptiveGenerated.adaptiveFormula12,AdaptiveGenerated.adaptiveFormula13,AdaptiveGenerated.adaptiveFormula14,AdaptiveGenerated.adaptiveFormula15,AdaptiveGenerated.adaptiveFormula16,AdaptiveGenerated.adaptiveFormula17,AdaptiveGenerated.adaptiveFormula22,AdaptiveGenerated.adaptiveFormula29,AdaptiveGenerated.adaptiveFormula30,AdaptiveGenerated.adaptiveFormula31,AdaptiveGenerated.adaptiveFormula32,AdaptiveGenerated.adaptiveFormula33,AdaptiveGenerated.adaptiveFormula34,AdaptiveGenerated.adaptiveFormula35,AdaptiveGenerated.adaptiveFormula36,AdaptiveGenerated.adaptiveFormula37,AdaptiveGenerated.adaptiveFormula38,AdaptiveGenerated.adaptiveFormula39,AdaptiveGenerated.adaptiveFormula40,AdaptiveGenerated.adaptiveFormula41,AdaptiveGenerated.adaptiveFormula42,AdaptiveGenerated.adaptiveFormula261,AdaptiveGenerated.adaptiveFormula267,AdaptiveGenerated.adaptiveFormula338,AdaptiveGenerated.adaptiveFormula339,AdaptiveGenerated.adaptiveFormula340,AdaptiveGenerated.adaptiveFormula341,AdaptiveGenerated.adaptiveFormula342,AdaptiveGenerated.adaptiveFormula346,AdaptiveGenerated.adaptiveFormula352,AdaptiveGenerated.adaptiveFormula359,AdaptiveGenerated.adaptiveFormula360,AdaptiveGenerated.adaptiveFormula361,AdaptiveGenerated.adaptiveFormula363,AdaptiveGenerated.adaptiveFormula364,AdaptiveGenerated.adaptiveFormula365,AdaptiveGenerated.adaptiveFormula366,AdaptiveGenerated.adaptiveFormula367,AdaptiveGenerated.adaptiveFormula368,AdaptiveGenerated.adaptiveFormula369,Formula.eval,hα,hβ,hδ,hε]
    simp only [radicalCoordinates,c,s,h₁,x₃,halfAngleCos,halfAngleSin,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Rat.cast_ofNat,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one]
    push_cast
    ring_nf

theorem adaptive_remainder_bounds {z : ℝ} (hz : z ∈ tiltBox) :
    quadraticCoefficient (adaptiveData z hz) (4209/5000)≤232/25 ∧
    cubicCoefficient (adaptiveData z hz) (4209/5000)≤3/2 := by
  obtain ⟨i,hi⟩ := adaptive_graph_mem hz
  have hq := AdaptiveGenerated.quadratic_bound i _ hi
  have hc := AdaptiveGenerated.cubic_bound i _ hi
  have he := remainder_formulas qStar (adaptiveY z hz) z (adaptive_weightDomain hz)
  rw [he.1] at hq
  rw [he.2] at hc
  exact ⟨hq,hc⟩

end SquaresInCircles.Eight.ExactFamily.Perturbation
