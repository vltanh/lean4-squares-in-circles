module
public import SquaresInCircles.Six.Analytic.WestCoreBounds.Geometry
public import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Chord

@[expose] public section

/-!
# A single half-angle support for the mixed-west diagonal

The two secondary weights are 1 and 211/200. Writing
 u=cos(r/2)-sin(r/2) gives the exact squared resultant
 (11/200)^2+(211/100)u^2.
On 0<=r<=6/5 we have u>=13/50. One increasing quadratic then proves the
uniform root bound (7263/5000)u+1/250. This is not an angular partition.
The resulting diagonal wave is concave and its derivative is at least 7/10
on the entire interval, by its single right-endpoint Taylor inequality.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestMixed
open Normalization

def nu : ℝ := 211/200
def rootSlope : ℝ := 7263/5000
def rootError : ℝ := 1/250
def halfDifference (r : ℝ) : ℝ := Real.cos (r/2)-Real.sin (r/2)
def waveCoefficient : ℝ := CandidateWestTail.radiusBound*rootSlope

def diagonalWave (r : ℝ) : ℝ :=
  nu*Real.cos r-waveCoefficient*Real.cos (r/2)+waveCoefficient*Real.sin (r/2)
def diagonalFirst (r : ℝ) : ℝ :=
  -nu*Real.sin r+(waveCoefficient/2)*(Real.sin (r/2)+Real.cos (r/2))
def diagonalSecond (r : ℝ) : ℝ :=
  -nu*Real.cos r+(waveCoefficient/4)*(Real.cos (r/2)-Real.sin (r/2))

lemma half_difference_lower {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    13/50 ≤ halfDifference r := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ r/2 by linarith [hr.1])
    (show (3:ℝ)/5 ≤ Real.pi by linarith [Real.pi_gt_d2])
    (show r/2 ≤ 3/5 by linarith [hr.2])
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ r/2 by linarith [hr.1,Real.pi_pos])
    (show (3:ℝ)/5 ≤ Real.pi/2 by linarith [Real.pi_gt_d2])
    (show r/2 ≤ 3/5 by linarith [hr.2])
  have hcl := Seven.cos_lower_six (x := (3:ℝ)/5) (by norm_num)
  have hsu := Seven.sin_upper_five (x := (3:ℝ)/5) (by norm_num)
  dsimp [halfDifference]
  nlinarith only [hc,hs,hcl,hsu]

lemma norm_identity (r : ℝ) :
    (nu*Real.cos r)^2+(1-nu*Real.sin r)^2 =
      (nu-1)^2+2*nu*(halfDifference r)^2 := by
  have hs : Real.sin r=2*Real.sin (r/2)*Real.cos (r/2) := by
    simpa only [show 2*(r/2)=r by ring] using Real.sin_two_mul (r/2)
  dsimp [halfDifference]
  rw [hs]
  linear_combination nu^2*(Real.sin_sq_add_cos_sq r)-2*nu*(Real.sin_sq_add_cos_sq (r/2))

lemma norm_upper {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    Real.sqrt ((nu*Real.cos r)^2+(1-nu*Real.sin r)^2) ≤
      rootSlope*halfDifference r+rootError := by
  have hu := half_difference_lower hr
  have hsq := mul_nonneg (show 0 ≤ halfDifference r-13/50 by linarith)
    (show 0 ≤ halfDifference r+13/50 by linarith)
  have hp : (nu-1)^2+2*nu*(halfDifference r)^2 ≤
      (rootSlope*halfDifference r+rootError)^2 := by
    dsimp [nu,rootSlope,rootError]
    nlinarith only [hu,hsq]
  have hnonneg : 0 ≤ rootSlope*halfDifference r+rootError := by
    dsimp [rootSlope,rootError]
    linarith
  have hs := Real.sq_sqrt
    (show 0 ≤ (nu*Real.cos r)^2+(1-nu*Real.sin r)^2 by positivity)
  have hn := Real.sqrt_nonneg ((nu*Real.cos r)^2+(1-nu*Real.sin r)^2)
  rw [norm_identity] at hs
  nlinarith only [hp,hnonneg,hs,hn]

lemma support {a b r : ℝ} (hc : ContainedChart a |b|) (hr : 0 ≤ r ∧ r ≤ 6/5) :
    nu*Real.cos r*a+(1-nu*Real.sin r)*b ≤
      CandidateWestTail.radiusBound*(rootSlope*halfDifference r+rootError)-
      (nu*Real.cos r+1-nu*Real.sin r)/2 := by
  have h := CandidateWestTail.local_vertex_support hc (nu*Real.cos r) (1-nu*Real.sin r)
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 (norm_upper hr) (Real.sqrt_nonneg _)
    (by norm_num [CandidateWestTail.radiusBound])
  have hw : nu*Real.cos r+1-nu*Real.sin r ≤ |nu*Real.cos r|+|1-nu*Real.sin r| := by
    linarith [le_abs_self (nu*Real.cos r),le_abs_self (1-nu*Real.sin r)]
  linarith

lemma diagonal_hasDeriv (r : ℝ) : HasDerivAt diagonalWave (diagonalFirst r) r := by
  convert ((((Real.hasDerivAt_cos r).const_mul nu).sub
    ((((hasDerivAt_id r).div_const 2).cos).const_mul waveCoefficient)).add
    ((((hasDerivAt_id r).div_const 2).sin).const_mul waveCoefficient)) using 1 <;>
    dsimp [diagonalWave,diagonalFirst] <;> ring

lemma diagonal_first_hasDeriv (r : ℝ) : HasDerivAt diagonalFirst (diagonalSecond r) r := by
  convert (((Real.hasDerivAt_sin r).const_mul (-nu)).add
    (((((hasDerivAt_id r).div_const 2).sin).add
      (((hasDerivAt_id r).div_const 2).cos)).const_mul (waveCoefficient/2))) using 1 <;>
    dsimp [diagonalFirst,diagonalSecond] <;> ring

lemma diagonal_second_nonpositive {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    diagonalSecond r ≤ 0 := by
  have hu := half_difference_lower hr
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ r/2 by linarith [hr.1])
    (show r/2 ≤ Real.pi by linarith [hr.2,Real.pi_gt_d2])
  have hc := Real.cos_nonneg_of_mem_Icc
    (show r/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hr.1,hr.2,Real.pi_gt_d2])
  have hsum : 1 ≤ Real.cos (r/2)+Real.sin (r/2) := by
    have hp := mul_nonneg hs hc
    nlinarith [Real.sin_sq_add_cos_sq (r/2)]
  have hcoef : -nu*(Real.cos (r/2)+Real.sin (r/2))+waveCoefficient/4 ≤ 0 := by
    dsimp [nu,waveCoefficient,rootSlope,CandidateWestTail.radiusBound]
    linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ halfDifference r by linarith) hcoef
  have hid : Real.cos r=halfDifference r*(Real.cos (r/2)+Real.sin (r/2)) := by
    have h := Real.cos_two_mul (r/2)
    rw [show 2*(r/2)=r by ring] at h
    dsimp [halfDifference]
    nlinarith only [h,Real.sin_sq_add_cos_sq (r/2)]
  dsimp [diagonalSecond]
  rw [hid]
  dsimp [halfDifference] at hp
  nlinarith only [hp]

lemma diagonal_concave : ConcaveOn ℝ (Set.Icc 0 (6/5)) diagonalWave := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (6/5))
    (f' := diagonalFirst) (f'' := diagonalSecond) (by dsimp [diagonalWave]; fun_prop)
  · intro r _; exact (diagonal_hasDeriv r).hasDerivWithinAt
  · intro r _; exact (diagonal_first_hasDeriv r).hasDerivWithinAt
  · intro r hr; exact diagonal_second_nonpositive (interior_subset hr)

lemma diagonal_first_lower {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 6/5) :
    7/10 ≤ diagonalFirst r := by
  have hm : MonotoneOn (fun x => -diagonalFirst x) (Set.Icc 0 (6/5)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (by dsimp [diagonalFirst]; fun_prop)
      (fun x _ => (diagonal_first_hasDeriv x).neg)
    intro x hx
    exact neg_nonneg.mpr (diagonal_second_nonpositive ⟨hx.1.le,hx.2.le⟩)
  have h := hm hr (by norm_num : (6:ℝ)/5 ∈ Set.Icc 0 (6/5)) hr.2
  have he : 7/10 ≤ diagonalFirst (6/5) := by
    have hs := Seven.sin_upper_five (x := (6:ℝ)/5) (by norm_num)
    have hc := Seven.cos_lower_six (x := (3:ℝ)/5) (by norm_num)
    have ht := Seven.sin_lower_seven (x := (3:ℝ)/5) (by norm_num)
    dsimp [diagonalFirst,nu,waveCoefficient,rootSlope,CandidateWestTail.radiusBound]
    norm_num
    nlinarith only [hs,hc,ht]
  linarith

end SquaresInCircles.Six.Analytic.WestMixed
