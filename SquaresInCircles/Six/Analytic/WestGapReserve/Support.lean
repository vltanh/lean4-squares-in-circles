import SquaresInCircles.Six.Analytic.WestGapReserve.Scalar

/-!
# A wider gap between W and D: the supports

The separations C–W, C–D and W–D, with weights `27/100`, `57/25` and `1`,
against the vertex supports of W and D and the box of the central square. The
length `√(β² + 1 + 2β sin q)` of the force on W, with `β = 27/100`, is bounded
by its tangent at `31/25`, and both coordinates of the force on the central
square are nonnegative on the rectangle. The weighted thresholds exceed the sum
of the bounds by the profile, which is positive, so the three separations cannot
all hold.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestGapReserve
open Normalization

def beta : ℝ := 27/100
def delta : ℝ := 57/25

def westUpper (q : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*(5221/4960+(27/124)*Real.sin q)-
    (beta+Real.sin q+Real.cos q)/2

def diagonalUpper : ℝ :=
  CandidateWestTail.radiusBound*(2489659/1000000)-(delta+1)/2

def forceX (v d : ℝ) : ℝ := beta*Real.cos v+delta*Real.cos d
def forceY (v d : ℝ) : ℝ := -beta*Real.sin v+delta*Real.sin d

def centerUpper (v d : ℝ) : ℝ :=
  CandidateWestTail.coreUpper*(forceX v d+forceY v d)

def thresholdSum (v d : ℝ) : ℝ :=
  beta*(1/2+angularWidth v)+delta*(1/2+angularWidth d)+(1/2+angularWidth (v+d))

def defect (v d : ℝ) : ℝ :=
  thresholdSum v d-westUpper (v+d)-diagonalUpper-centerUpper v d

lemma west_root (q : ℝ) :
    Real.sqrt (beta^2+1+2*beta*Real.sin q) ≤ 5221/4960+(27/124)*Real.sin q := by
  have hr : 0 ≤ beta^2+1+2*beta*Real.sin q := by
    dsimp [beta]
    linarith [Real.neg_one_le_sin q]
  have hs := Real.sq_sqrt hr
  have hp := sq_nonneg (Real.sqrt (beta^2+1+2*beta*Real.sin q)-31/25)
  dsimp [beta] at *
  nlinarith only [hs,hp]

lemma west_support {a b q : ℝ} (hc : ContainedChart a |b|) :
    (beta+Real.sin q)*a-Real.cos q*b ≤ westUpper q := by
  have h := CandidateWestTail.local_vertex_support hc (beta+Real.sin q) (-Real.cos q)
  have hid : (beta+Real.sin q)^2+(-Real.cos q)^2=beta^2+1+2*beta*Real.sin q := by
    linear_combination Real.sin_sq_add_cos_sq q
  rw [hid] at h
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 (west_root q)
    (Real.sqrt_nonneg _) (by norm_num [CandidateWestTail.radiusBound])
  have hw : beta+Real.sin q+Real.cos q ≤ |beta+Real.sin q|+|-Real.cos q| := by
    linarith [le_abs_self (beta+Real.sin q),neg_le_abs (-Real.cos q)]
  dsimp [westUpper]
  nlinarith only [h,hm,hw]

lemma diagonal_support {a b : ℝ} (hc : ContainedChart a |b|) :
    delta*a+b ≤ diagonalUpper := by
  have h := CandidateWestTail.local_vertex_support hc delta 1
  have hroot : Real.sqrt (delta^2+1) ≤ 2489659/1000000 := by
    have hr := Real.sqrt_le_sqrt
      (show delta^2+1 ≤ ((2489659:ℝ)/1000000)^2 by norm_num [delta])
    simpa only [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2489659/1000000)] using hr
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 hroot (Real.sqrt_nonneg _)
    (by norm_num [CandidateWestTail.radiusBound])
  have hdelta : |delta| = delta := abs_of_pos (by norm_num [delta])
  rw [one_pow,abs_one,one_mul,hdelta] at h
  dsimp only [diagonalUpper]
  linarith

lemma center_support {v d cx cy : ℝ}
    (hq : 1 ≤ v+d ∧ v+d ≤ 53/50) (hd : 3/5 ≤ d ∧ d ≤ 11/14)
    (hx : cx ≤ CandidateWestTail.coreUpper) (hy : cy ≤ CandidateWestTail.coreUpper) :
    forceX v d*cx+forceY v d*cy ≤ centerUpper v d := by
  have hv : 0 ≤ v ∧ v ≤ 23/50 := by
    constructor <;> linarith [hq.1,hq.2,hd.1,hd.2]
  have hcv := Real.cos_nonneg_of_mem_Icc
    (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show d ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hs0 := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
  have hs1 := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/2 by linarith [Real.pi_pos])
    (show d ≤ Real.pi/2 by linarith [hd.2,Real.pi_gt_d2])
    (show (1:ℝ)/2 ≤ d by linarith [hd.1])
  have hsd : 23/48 ≤ Real.sin d := by nlinarith only [hs0,hs1]
  have hX : 0 ≤ forceX v d := by dsimp [forceX,beta,delta]; positivity
  have hY : 0 ≤ forceY v d := by
    dsimp [forceY,beta,delta]
    linarith [Real.sin_le_one v]
  have hp := mul_le_mul_of_nonneg_left hx hX
  have hr := mul_le_mul_of_nonneg_left hy hY
  dsimp [centerUpper]
  nlinarith only [hp,hr]

lemma profile_eq_defect {v d : ℝ}
    (hq : 1 ≤ v+d ∧ v+d ≤ 53/50) (hd : 3/5 ≤ d ∧ d ≤ 11/14) :
    profile (v+d) d=defect v d := by
  have width_formula {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
      angularWidth x=(Real.cos x+Real.sin x)/2 := by
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
    simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs]
  have hw := width_formula (x := v) (by
    constructor <;> linarith [hq.1,hq.2,hd.1,hd.2,Real.pi_gt_d2])
  have hD := width_formula (x := d) (by
    constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hQ := width_formula (x := v+d) (by
    constructor <;> linarith [hq.1,hq.2,Real.pi_gt_d2])
  dsimp [profile,defect,thresholdSum,westUpper,diagonalUpper,centerUpper,forceX,forceY,
    beta,delta,CandidateWestTail.radiusBound,CandidateWestTail.coreUpper]
  rw [hw,hD,hQ,show v+d-d=v by ring]
  ring

/-- The separations C–W, C–D and W–D are incompatible when `1 ≤ d + v ≤ 53/50`
and `3/5 ≤ d ≤ 11/14`. -/
theorem scalar_impossible {v d aw bw ad bd cx cy : ℝ}
    (hq : 1 ≤ v+d ∧ v+d ≤ 53/50) (hd : 3/5 ≤ d ∧ d ≤ 11/14)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hx : cx ≤ CandidateWestTail.coreUpper) (hy : cy ≤ CandidateWestTail.coreUpper)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCD : 1/2+angularWidth d ≤ ad+cx*Real.cos d+cy*Real.sin d)
    (hWD : 1/2+angularWidth (v+d) ≤ aw*Real.sin (v+d)-bw*Real.cos (v+d)+bd) : False := by
  have hsum : thresholdSum v d ≤
      ((beta+Real.sin (v+d))*aw-Real.cos (v+d)*bw)+(delta*ad+bd)+
      forceX v d*cx+forceY v d*cy := by
    dsimp [thresholdSum,beta,delta,forceX,forceY]
    linear_combination (27/100)*hCW+(57/25)*hCD+hWD
  have hw := west_support (q := v+d) hW
  have hdiag := diagonal_support hD
  have hc := center_support hq hd hx hy
  have hn : defect v d ≤ 0 := by
    dsimp [defect]
    linarith only [hsum,hw,hdiag,hc]
  have hp := positive hq hd
  rw [profile_eq_defect hq hd] at hp
  linarith

end SquaresInCircles.Six.Analytic.WestGapReserve
