module

public import SquaresInCircles.Eight.ExactFamily.PerturbationEstimates

/-!
# Eight squares: the remainder coefficients along the adaptive chain

The force identities express the remainder coefficients in terms of coordinates and contact
weights. Bounding each positive product by its coordinate and weight bounds gives the constants
`terminalQuadratic` and `terminalCubic`; the frame bounds come from the two endpoints of
`tiltBox`. This argument applies uniformly to the whole adaptive chain, without interval
checks of the remainder formulas.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ExactFamily.Perturbation
open Coordinates

private theorem frame_bounds {z : ℝ} (hz : z ∈ tiltBox) :
    halfAngleCos (81/1000) ≤ halfAngleCos z ∧
    halfAngleSin (1/20) ≤ halfAngleSin z ∧
    halfAngleSin z ≤ halfAngleSin (81/1000) := by
  have hz0 : 0 ≤ z := by linarith only [hz.1]
  have hz2 : z^2 ≤ (81/1000:ℝ)^2 := pow_le_pow_left₀ hz0 hz.2 2
  have hlow := mul_nonneg (sub_nonneg.mpr hz.1)
    (show 0 ≤ 1-z*(1/20) by linarith only [hz.2])
  have hupp := mul_nonneg (sub_nonneg.mpr hz.2)
    (show 0 ≤ 1-z*(81/1000) by linarith only [hz.2])
  norm_num [halfAngleCos,halfAngleSin]
  constructor
  · rw [le_div_iff₀ (halfAngle_den_pos z)]
    nlinarith only [hz2]
  constructor
  · rw [le_div_iff₀ (halfAngle_den_pos z)]
    nlinarith only [hlow]
  · rw [div_le_iff₀ (halfAngle_den_pos z)]
    nlinarith only [hupp]

private theorem weighted_upper {a x w X : ℝ} (ha : 0 ≤ a) (haw : a ≤ w)
    (hx : x ≤ X) (hX : 0 ≤ X) : a*x ≤ w*X :=
  (mul_le_mul_of_nonneg_left hx ha).trans (mul_le_mul_of_nonneg_right haw hX)

/-- Coordinate and weight bounds suffice for both remainder estimates. -/
theorem remainder_bounds_of_coordinates {d : Coordinates} (hw : d.WeightDomain)
    (hz : d.z ∈ tiltBox) (hy : d.y ≤ -179/200)
    (hx₁ : d.x₁ ≤ 17649/10000) (hx₂ : 16414/10000 ≤ d.x₂)
    (hx₄ : -19049/10000 ≤ d.x₄) (hh₁ : -14263/10000 ≤ d.h₁)
    (hweight : ∀ j : Fin 7, d.lam j ≤ 4209/5000) :
    quadraticCoefficient d (4209/5000) ≤ terminalQuadratic ∧
    cubicCoefficient d (4209/5000) ≤ terminalCubic := by
  obtain ⟨hc,hs,hs'⟩ := frame_bounds hz
  have hprod {j : Fin 7} {x X : ℝ} (hx : x ≤ X) (hX : 0 ≤ X) :
      d.lam j*x ≤ (4209/5000)*X :=
    weighted_upper (hw.lam_pos j).le (hweight j) hx hX
  obtain ⟨ha,hb,hd,he,hh⟩ := coefficient_identities hw
  have hA : KA d ≤ (4209/5000)*(17649/10000)/halfAngleCos (81/1000) := by
    rw [ha]
    exact div_le_div₀ (by norm_num) (hprod hx₁ (by norm_num))
      (by norm_num [halfAngleCos]) hc
  have hB : KB d ≤ (4209/5000)*(221/200) := by
    rw [hb]
    exact hprod (by linarith only [hy]) (by norm_num)
  have hD : KD d ≤ (4209/5000)*(6793/5000) := by
    rw [hd,neg_mul,← mul_neg]
    exact hprod (by dsimp [x₃]; linarith only [hx₂]) (by norm_num)
  have hE : KE d ≤ (4209/5000)*(19049/10000)/halfAngleSin (1/20) := by
    rw [he,neg_mul,← mul_neg]
    exact div_le_div₀ (by norm_num)
      (hprod (by linarith only [hx₄]) (by norm_num))
      (by norm_num [halfAngleSin]) hs
  have hH : KH d ≤ (4209/5000)*(14263/10000) := by
    rw [hh,neg_mul,← mul_neg]
    exact hprod (by linarith only [hh₁]) (by norm_num)
  have hAs : KA d*d.s ≤
      ((4209/5000)*(17649/10000)/halfAngleCos (81/1000))*halfAngleSin (81/1000) :=
    mul_le_mul hA hs' hw.s_pos.le (by norm_num [halfAngleCos])
  have hεs : d.edgeEpsilon*d.s ≤ (4209/5000)*halfAngleSin (81/1000) :=
    mul_le_mul (hweight 6) hs' hw.s_pos.le (by norm_num)
  constructor
  · dsimp only [quadraticCoefficient,terminalQuadratic]
    linarith only [hAs,hE,hεs]
  · dsimp only [cubicCoefficient,terminalCubic]
    have hε : d.edgeEpsilon ≤ 4209/5000 := hweight 6
    linarith only [hA,hB,hD,hH,hε]

theorem adaptive_remainder_bounds {z : ℝ} (hz : z ∈ tiltBox) :
    quadraticCoefficient (adaptiveData z hz) (4209/5000)≤232/25 ∧
    cubicCoefficient (adaptiveData z hz) (4209/5000)≤3/2 := by
  obtain ⟨_,hx₁,hx₂,_,_,_,hx₄,_,hh₁,_⟩ := radical_local_bounds (adaptive_local_mem hz)
  have h := remainder_bounds_of_coordinates (adaptive_weightDomain hz) hz
    (by simpa only [adaptiveData,radicalCoordinates,neg_div] using (adaptiveY_mem hz).2)
    hx₁ hx₂ hx₄ hh₁ (adaptive_edge_weight_bound hz)
  exact ⟨h.1.trans terminal_constants.2.1.le,h.2.trans terminal_constants.2.2.2.1.le⟩

end SquaresInCircles.Eight.ExactFamily.Perturbation
