module

public import SquaresInCircles.Eight.ExactFamily.PerturbationEstimates

/-! Uncompiled exact-rational remainder coefficients on the adaptive graph. -/

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
  dsimp [quadraticCoefficient,cubicCoefficient]
  rw [ha,hb,hd,he,hh]
  constructor <;>
    norm_num [AdaptiveGenerated.quadraticFormula,AdaptiveGenerated.cubicFormula,
      AdaptiveGenerated.adaptiveFormula0, AdaptiveGenerated.adaptiveFormula1, AdaptiveGenerated.adaptiveFormula2, AdaptiveGenerated.adaptiveFormula3, AdaptiveGenerated.adaptiveFormula4, AdaptiveGenerated.adaptiveFormula6, AdaptiveGenerated.adaptiveFormula7, AdaptiveGenerated.adaptiveFormula9, AdaptiveGenerated.adaptiveFormula10, AdaptiveGenerated.adaptiveFormula11, AdaptiveGenerated.adaptiveFormula12, AdaptiveGenerated.adaptiveFormula13, AdaptiveGenerated.adaptiveFormula14, AdaptiveGenerated.adaptiveFormula15, AdaptiveGenerated.adaptiveFormula16, AdaptiveGenerated.adaptiveFormula17, AdaptiveGenerated.adaptiveFormula18, AdaptiveGenerated.adaptiveFormula19, AdaptiveGenerated.adaptiveFormula20, AdaptiveGenerated.adaptiveFormula21, AdaptiveGenerated.adaptiveFormula22, AdaptiveGenerated.adaptiveFormula23, AdaptiveGenerated.adaptiveFormula24, AdaptiveGenerated.adaptiveFormula25, AdaptiveGenerated.adaptiveFormula26, AdaptiveGenerated.adaptiveFormula27, AdaptiveGenerated.adaptiveFormula28, AdaptiveGenerated.adaptiveFormula29, AdaptiveGenerated.adaptiveFormula30, AdaptiveGenerated.adaptiveFormula31, AdaptiveGenerated.adaptiveFormula32, AdaptiveGenerated.adaptiveFormula33, AdaptiveGenerated.adaptiveFormula34, AdaptiveGenerated.adaptiveFormula35, AdaptiveGenerated.adaptiveFormula36, AdaptiveGenerated.adaptiveFormula37, AdaptiveGenerated.adaptiveFormula38, AdaptiveGenerated.adaptiveFormula39, AdaptiveGenerated.adaptiveFormula40, AdaptiveGenerated.adaptiveFormula41, AdaptiveGenerated.adaptiveFormula42, AdaptiveGenerated.adaptiveFormula43, AdaptiveGenerated.adaptiveFormula44, AdaptiveGenerated.adaptiveFormula45, AdaptiveGenerated.adaptiveFormula46, AdaptiveGenerated.adaptiveFormula47, AdaptiveGenerated.adaptiveFormula48, AdaptiveGenerated.adaptiveFormula49, AdaptiveGenerated.adaptiveFormula50, AdaptiveGenerated.adaptiveFormula58, AdaptiveGenerated.adaptiveFormula59, AdaptiveGenerated.adaptiveFormula60, AdaptiveGenerated.adaptiveFormula76, AdaptiveGenerated.adaptiveFormula77, AdaptiveGenerated.adaptiveFormula95, AdaptiveGenerated.adaptiveFormula251, AdaptiveGenerated.adaptiveFormula252, AdaptiveGenerated.adaptiveFormula253, AdaptiveGenerated.adaptiveFormula254, AdaptiveGenerated.adaptiveFormula255, AdaptiveGenerated.adaptiveFormula256, AdaptiveGenerated.adaptiveFormula257, AdaptiveGenerated.adaptiveFormula258, AdaptiveGenerated.adaptiveFormula259, AdaptiveGenerated.adaptiveFormula260, AdaptiveGenerated.adaptiveFormula261, AdaptiveGenerated.adaptiveFormula262, AdaptiveGenerated.adaptiveFormula263, AdaptiveGenerated.adaptiveFormula264, AdaptiveGenerated.adaptiveFormula265, AdaptiveGenerated.adaptiveFormula266, AdaptiveGenerated.adaptiveFormula267, AdaptiveGenerated.adaptiveFormula268, AdaptiveGenerated.adaptiveFormula269, AdaptiveGenerated.adaptiveFormula270, AdaptiveGenerated.adaptiveFormula271, AdaptiveGenerated.adaptiveFormula272, AdaptiveGenerated.adaptiveFormula273, AdaptiveGenerated.adaptiveFormula274, AdaptiveGenerated.adaptiveFormula275, AdaptiveGenerated.adaptiveFormula276, AdaptiveGenerated.adaptiveFormula277, AdaptiveGenerated.adaptiveFormula278, AdaptiveGenerated.adaptiveFormula279, AdaptiveGenerated.adaptiveFormula280, AdaptiveGenerated.adaptiveFormula281, AdaptiveGenerated.adaptiveFormula282, AdaptiveGenerated.adaptiveFormula283, AdaptiveGenerated.adaptiveFormula303, AdaptiveGenerated.adaptiveFormula338, AdaptiveGenerated.adaptiveFormula339, AdaptiveGenerated.adaptiveFormula340, AdaptiveGenerated.adaptiveFormula341, AdaptiveGenerated.adaptiveFormula342, AdaptiveGenerated.adaptiveFormula343, AdaptiveGenerated.adaptiveFormula344, AdaptiveGenerated.adaptiveFormula345, AdaptiveGenerated.adaptiveFormula346, AdaptiveGenerated.adaptiveFormula348, AdaptiveGenerated.adaptiveFormula349, AdaptiveGenerated.adaptiveFormula350, AdaptiveGenerated.adaptiveFormula351, AdaptiveGenerated.adaptiveFormula352, AdaptiveGenerated.adaptiveFormula353, AdaptiveGenerated.adaptiveFormula354, AdaptiveGenerated.adaptiveFormula356, AdaptiveGenerated.adaptiveFormula357, AdaptiveGenerated.adaptiveFormula358, AdaptiveGenerated.adaptiveFormula359, AdaptiveGenerated.adaptiveFormula360, AdaptiveGenerated.adaptiveFormula361, AdaptiveGenerated.adaptiveFormula363, AdaptiveGenerated.adaptiveFormula364, AdaptiveGenerated.adaptiveFormula365, AdaptiveGenerated.adaptiveFormula366, AdaptiveGenerated.adaptiveFormula367, AdaptiveGenerated.adaptiveFormula368, AdaptiveGenerated.adaptiveFormula369,Formula.eval,radicalCoordinates,
      edgeAlpha,edgeBeta,edgeDelta,edgeEpsilon,edgeOmega,
      lam,mu,rawLambda,rawMu,weightMass,rawMuA,rawMuB,rawMuD,rawMuE,rawMuH,
      rawAlpha,rawBeta,rawDelta,rawEpsilon,c,s,h₁,h₂,x₃,y₄,
      halfAngleCos,halfAngleSin,Fin.sum_univ_succ,div_eq_mul_inv,
      inv_neg,mul_inv_rev,neg_mul,mul_neg] <;> ring

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
