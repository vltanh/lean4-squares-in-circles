module
public import SquaresInCircles.Six.Analytic.CardinalSouthTail.Support

@[expose] public section

/-!
# The asymmetric chord in the ordered two-OWN south argument

The W/D and D/S weights are 109/100 and 1. Their D resultant has squared
length (9/100)^2+(109/25)*sin(q/2)^2. On the geometrically forced interval
1/2 <= q <= 443/350, a single affine function of sin(q/2) majorizes the root.
Its squared error is a concave quadratic, so its two endpoints suffice.
The chord contribution left in the stress has negative second derivative.
No angular subdivision, finite-cover checker, or numerical premise is used.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthOrdered
open Normalization

def westWeight : ℝ := 91/50
def southWeight : ℝ := 159/100
def pairWeight : ℝ := 109/100

def rootIntercept : ℝ := 111/10000
def rootSlope : ℝ := 20751/10000

def chordCoefficient : ℝ := 175200693/50000000

def chord (q : ℝ) : ℝ :=
  (109/100)*Real.sin q-chordCoefficient*Real.sin (q/2)

def chordDerivative (q : ℝ) : ℝ :=
  (109/100)*Real.cos q-(chordCoefficient/2)*Real.cos (q/2)

def chordSecond (q : ℝ) : ℝ :=
  -(109/100)*Real.sin q+(chordCoefficient/4)*Real.sin (q/2)

lemma half_sine_bounds {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 443/350) :
    95/384 ≤ Real.sin (q/2) ∧ Real.sin (q/2) ≤ 3/5 := by
  have hlo := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/4 by linarith [Real.pi_pos])
    (show q/2 ≤ Real.pi/2 by linarith [hq.2,Real.pi_gt_d2])
    (show (1:ℝ)/4 ≤ q/2 by linarith [hq.1])
  have hhi := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ q/2 by linarith [hq.1,Real.pi_pos])
    (show (443:ℝ)/700 ≤ Real.pi/2 by linarith [Real.pi_gt_d2])
    (show q/2 ≤ (443:ℝ)/700 by linarith [hq.2])
  have hl := Real.sin_ge_sub_cube (x := (1:ℝ)/4) (by norm_num)
  have hu := Seven.sin_upper_five (x := (443:ℝ)/700) (by norm_num)
  constructor <;> nlinarith only [hlo,hhi,hl,hu]

private def rootError (t : ℝ) : ℝ :=
  (rootIntercept+rootSlope*t)^2-(9/100)^2-(109/25)*t^2

/-- One quadratic chord identity controls the entire half-sine interval. -/
private lemma root_error_positive {t : ℝ} (ht : 95/384 ≤ t ∧ t ≤ 3/5) :
    0 < rootError t := by
  let l : ℝ := 95/384
  let u : ℝ := 3/5
  have hl : 0 < rootError l := by norm_num [rootError,rootIntercept,rootSlope,l]
  have hu : 0 < rootError u := by norm_num [rootError,rootIntercept,rootSlope,u]
  have hlu : l < u := by norm_num [l,u]
  have htl : 0 ≤ t-l := by dsimp [l]; linarith [ht.1]
  have htu : 0 ≤ u-t := by dsimp [u]; linarith [ht.2]
  have hcor : 0 ≤ (u-l)*(t-l)*(u-t)*((109:ℝ)/25-rootSlope^2) := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hlu.le) htl) htu
    · norm_num [rootSlope]
  have hid : (u-l)*rootError t =
      (u-t)*rootError l+(t-l)*rootError u+
      (u-l)*(t-l)*(u-t)*((109:ℝ)/25-rootSlope^2) := by
    dsimp [rootError]
    ring
  have hchord : 0 < (u-t)*rootError l+(t-l)*rootError u := by
    rcases lt_or_eq_of_le (show t ≤ u from ht.2) with h | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr h) hl)
        (mul_nonneg htl hu.le)
    · simpa using mul_pos (sub_pos.mpr hlu) hu
  by_contra! h
  have hn := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlu.le) h
  linarith

lemma chord_norm_sq (q : ℝ) :
    ((109/100)*Real.sin q)^2+((109/100)*Real.cos q-1)^2 =
      (9/100)^2+(109/25)*Real.sin (q/2)^2 := by
  have hcos : Real.cos q=1-2*Real.sin (q/2)^2 := by
    have h := Real.cos_two_mul (q/2)
    rw [show 2*(q/2)=q by ring] at h
    nlinarith only [h,Real.sin_sq_add_cos_sq (q/2)]
  calc
    _ = (109/100:ℝ)^2+1-(109/50)*Real.cos q := by
      linear_combination (109/100:ℝ)^2*(Real.sin_sq_add_cos_sq q)
    _ = _ := by rw [hcos]; ring

lemma chord_norm_upper {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 443/350) :
    Real.sqrt (((109/100)*Real.sin q)^2+((109/100)*Real.cos q-1)^2) ≤
      rootIntercept+rootSlope*Real.sin (q/2) := by
  have ht := half_sine_bounds hq
  have herr := root_error_positive ht
  have hnonneg : 0 ≤ rootIntercept+rootSlope*Real.sin (q/2) := by
    dsimp [rootIntercept,rootSlope]
    linarith [ht.1]
  have hs := Real.sq_sqrt
    (show 0 ≤ ((109/100)*Real.sin q)^2+((109/100)*Real.cos q-1)^2 by positivity)
  have hn := Real.sqrt_nonneg
    (((109/100)*Real.sin q)^2+((109/100)*Real.cos q-1)^2)
  rw [chord_norm_sq] at hs
  dsimp [rootError] at herr
  nlinarith only [herr,hs,hn,hnonneg]

lemma chord_hasDeriv (q : ℝ) : HasDerivAt chord (chordDerivative q) q := by
  convert ((Real.hasDerivAt_sin q).const_mul (109/100)).sub
    ((((hasDerivAt_id q).div_const 2).sin).const_mul chordCoefficient) using 1 <;>
    dsimp [chord,chordDerivative] <;> ring

lemma chord_derivative_hasDeriv (q : ℝ) :
    HasDerivAt chordDerivative (chordSecond q) q := by
  convert ((Real.hasDerivAt_cos q).const_mul (109/100)).sub
    ((((hasDerivAt_id q).div_const 2).cos).const_mul (chordCoefficient/2)) using 1 <;>
    dsimp [chordDerivative,chordSecond] <;> ring

lemma chord_second_nonpositive {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 4/3) :
    chordSecond q ≤ 0 := by
  have hsq := mul_nonneg
    (show 0 ≤ 2/3-q/2 by linarith [hq.2])
    (show 0 ≤ 2/3+q/2 by linarith [hq.1])
  have hc : 7/9 ≤ Real.cos (q/2) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := q/2)]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ q/2 by linarith [hq.1])
    (show q/2 ≤ Real.pi by linarith [hq.2,Real.pi_gt_d2])
  have hcoef : -(109/50)*Real.cos (q/2)+chordCoefficient/4 ≤ 0 := by
    dsimp [chordCoefficient]
    linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos hs hcoef
  have hid : Real.sin q=2*Real.sin (q/2)*Real.cos (q/2) := by
    simpa only [show 2*(q/2)=q by ring] using Real.sin_two_mul (q/2)
  dsimp [chordSecond]
  nlinarith only [hp,hid]

lemma chord_concave : ConcaveOn ℝ (Set.Icc (1/2) (4/3)) chord := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) (4/3))
    (f' := chordDerivative) (f'' := chordSecond) (by dsimp [chord]; fun_prop)
  · intro q _; exact (chord_hasDeriv q).hasDerivWithinAt
  · intro q _; exact (chord_derivative_hasDeriv q).hasDerivWithinAt
  · intro q hq
    exact chord_second_nonpositive (interior_subset hq)

lemma chord_derivative_antitone :
    AntitoneOn chordDerivative (Set.Icc (1/2) (4/3)) := by
  have hm : MonotoneOn (fun q => -chordDerivative q) (Set.Icc (1/2) (4/3)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (by dsimp [chordDerivative]; fun_prop)
      (fun q _ => (chord_derivative_hasDeriv q).neg)
    intro q hq
    exact neg_nonneg.mpr (chord_second_nonpositive ⟨hq.1.le,hq.2.le⟩)
  intro q hq r hr hqr
  have h := hm hq hr hqr
  linarith

end SquaresInCircles.Six.Analytic.OwnSouthOrdered
