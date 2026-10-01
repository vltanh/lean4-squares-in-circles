import SquaresInCircles.Six.Analytic.CandidateWestTail.Support

/-!
# A force on D with a radial part

With weight one on W–D, along the secondary axis of W, and on D–S, along the
secondary axis of D, the force on D is `(sin q, cos q - 1)` in its frame, where
`q` is the angle from W to D; a weight `z ≥ 0` on C–D, along the own axis of D,
adds `(z, 0)`. For `0 ≤ q ≤ π` the length of `(z + sin q, cos q - 1)` is at
most `majorant z q = (2 + z^2/4) sin (q/2) + z cos (q/2)`, whose square exceeds
the squared length by `z^3/2 sin (q/2) cos (q/2) + z^4/16 sin (q/2)^2`. With
this majorant for the length, the far-vertex support bounds the work of the
force.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.RadialChordSupport
open Normalization

def majorant (z q : ℝ) : ℝ :=
  (2+z^2/4)*Real.sin (q/2)+z*Real.cos (q/2)

/-- The square of the majorant minus the squared length of the force. -/
lemma square_identity (z q : ℝ) :
    majorant z q ^ 2-((z+Real.sin q)^2+(Real.cos q-1)^2) =
      (z^3/2)*Real.sin (q/2)*Real.cos (q/2)+
      (z^4/16)*Real.sin (q/2)^2 := by
  have hs : Real.sin q=2*Real.sin (q/2)*Real.cos (q/2) := by
    simpa only [show 2*(q/2)=q by ring] using Real.sin_two_mul (q/2)
  have hc : Real.cos q=2*Real.cos (q/2)^2-1 := by
    simpa only [show 2*(q/2)=q by ring] using Real.cos_two_mul (q/2)
  rw [hs,hc]
  dsimp [majorant]
  linear_combination
    (z^2-4*Real.cos (q/2)^2+4)*(Real.sin_sq_add_cos_sq (q/2))

lemma majorant_nonnegative {z q : ℝ} (hz : 0 ≤ z)
    (hq : 0 ≤ q ∧ q ≤ Real.pi) : 0 ≤ majorant z q := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ q/2 by linarith [hq.1])
    (show q/2 ≤ Real.pi by linarith [hq.2,Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc
    (show q/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_pos])
  dsimp [majorant]
  positivity

/-- The majorant bounds the length of the force for `0 ≤ q ≤ π`. -/
lemma length_le_majorant {z q : ℝ} (hz : 0 ≤ z)
    (hq : 0 ≤ q ∧ q ≤ Real.pi) :
    Real.sqrt ((z+Real.sin q)^2+(Real.cos q-1)^2) ≤ majorant z q := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ q/2 by linarith [hq.1])
    (show q/2 ≤ Real.pi by linarith [hq.2,Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc
    (show q/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_pos])
  have he := square_identity z q
  have herr : 0 ≤ (z^3/2)*Real.sin (q/2)*Real.cos (q/2)+
      (z^4/16)*Real.sin (q/2)^2 := by positivity
  have hroot := Real.sq_sqrt
    (show 0 ≤ (z+Real.sin q)^2+(Real.cos q-1)^2 by positivity)
  have hn := Real.sqrt_nonneg ((z+Real.sin q)^2+(Real.cos q-1)^2)
  have hm := majorant_nonnegative hz hq
  nlinarith only [he,herr,hroot,hn,hm]

/-- The far-vertex support of D, with the majorant in place of the length of
the force. -/
lemma support {a b z q : ℝ} (hC : ContainedChart a |b|)
    (hz : 0 ≤ z) (hq : 0 ≤ q ∧ q ≤ Real.pi) :
    (z+Real.sin q)*a+(Real.cos q-1)*b ≤
      R0*majorant z q-(z+Real.sin q+1-Real.cos q)/2 := by
  have h := CandidateWestTail.local_vertex_support hC (z+Real.sin q) (Real.cos q-1)
  have hnorm := mul_le_mul_of_nonneg_left (length_le_majorant hz hq) R0_nonneg
  have hwidth : z+Real.sin q+1-Real.cos q ≤
      |z+Real.sin q|+|Real.cos q-1| := by
    linarith [le_abs_self (z+Real.sin q),neg_le_abs (Real.cos q-1)]
  linarith

end SquaresInCircles.Six.Analytic.RadialChordSupport
