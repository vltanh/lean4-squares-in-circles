module
public import SquaresInCircles.Six.Analytic.CandidateWestTail.Support

@[expose] public section

/-!
# An analytic support bound for a radial force added to a chord

Equal incident secondary weights give the local resultant
  (sin q, cos q - 1).
Adding a nonnegative CD weight z gives (z + sin q, cos q - 1).
The displayed half-angle majorant has a nonnegative square difference on the
whole interval 0 <= q <= pi. In particular, adding the CD inequality need not
be weakened by the triangle inequality z + 2 sin(q/2), which loses its useful
radial direction.

This is a single symbolic identity and a universal disk-support argument, not
a subdivision or finite certificate. Compilation remains unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.RadialChordSupport
open Normalization

def majorant (z q : ℝ) : ℝ :=
  (2+z^2/4)*Real.sin (q/2)+z*Real.cos (q/2)

/-- The error is visibly nonnegative in the first-quadrant half-angle. -/
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

/-- Whole-domain radical majorization without choosing a support branch. -/
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

/-- The far-vertex support keeps the direction of the added radial force. -/
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
