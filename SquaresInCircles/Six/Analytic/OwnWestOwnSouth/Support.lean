module
public import SquaresInCircles.Six.Analytic.OwnWestOwnSouth.Scalar
public import SquaresInCircles.Six.Analytic.WestMixed.Support

@[expose] public section

/-!
# Actual supports for the continuous-weight two-OWN stress

The CS multiplier gamma(s)=38/25+3s is positive on the whole domain. The
resulting S support is the actual vertex support, not an assumed maximizer.
Both central force components are nonnegative by the displayed angle bounds.
Thus the polynomial scalar proof applies to four genuine separator inequalities.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestOwnSouth
open Normalization WestMixed

def southUpper (s : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*Real.sqrt ((gamma s)^2+nu^2)-(gamma s+nu)/2

def diagonalUpper (r : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*(rootSlope*halfDifference r+rootError)-
    (nu*Real.cos r+1-nu*Real.sin r)/2

def forceX (v s : ℝ) : ℝ := beta*Real.cos v-gamma s*Real.sin s
def forceY (v s : ℝ) : ℝ := gamma s*Real.cos s-beta*Real.sin v

def centerUpper (v s : ℝ) : ℝ := CandidateWestTail.coreUpper*(forceX v s+forceY v s)

def thresholdSum (v s d : ℝ) : ℝ :=
  beta*(1/2+angularWidth v)+gamma s*(1/2+angularWidth s)+
    (1/2+angularWidth (v+d))+nu*(1/2+angularWidth (d-s))

def defect (v s d : ℝ) : ℝ :=
  thresholdSum v s d-CandidateWestTail.rhoBound*(beta+Real.sin (v+d))-
    southUpper s-diagonalUpper (d-s)-centerUpper v s

lemma gamma_bounds {s : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25) :
    38/25 ≤ gamma s ∧ gamma s ≤ 74/25 := by
  dsimp [gamma]
  constructor <;> linarith [hs.1,hs.2]

lemma south_support {a b s : ℝ} (hc : ContainedChart a |b|)
    (hs : 0 ≤ s ∧ s ≤ 12/25) : gamma s*a+nu*b ≤ southUpper s := by
  have hg : 0 ≤ gamma s := by linarith [(gamma_bounds hs).1]
  have hn : 0 ≤ nu := by norm_num [nu]
  have h := CandidateWestTail.local_vertex_support hc (gamma s) nu
  rw [abs_of_nonneg hg,abs_of_nonneg hn] at h
  have hm := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.1
    (Real.sqrt_nonneg ((gamma s)^2+nu^2))
  dsimp [southUpper]
  linarith

lemma central_forces {v s : ℝ} (hv : 0 ≤ v ∧ v ≤ 31/50)
    (hs : 0 ≤ s ∧ s ≤ 12/25) : 0 ≤ forceX v s ∧ 0 ≤ forceY v s := by
  have hv2 := mul_nonneg (sub_nonneg.mpr hv.2)
    (show 0 ≤ 31/50+v by linarith [hv.1])
  have hs2 := mul_nonneg (sub_nonneg.mpr hs.2)
    (show 0 ≤ 12/25+s by linarith [hs.1])
  have hcv : 4039/5000 ≤ Real.cos v := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have hcs : 553/625 ≤ Real.cos s := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have hsv : Real.sin v ≤ 31/50 := (Real.sin_le hv.1).trans hv.2
  have hss : Real.sin s ≤ 12/25 := (Real.sin_le hs.1).trans hs.2
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_gt_d2])
  have hg := gamma_bounds hs
  have hprodS := mul_le_mul hg.2 hss hs0 (by norm_num : (0:ℝ) ≤ 74/25)
  have hprodC := mul_le_mul hg.1 hcs (by norm_num : (0:ℝ) ≤ 553/625)
    (show 0 ≤ gamma s by linarith [hg.1])
  dsimp [forceX,forceY,beta]
  constructor <;> nlinarith only [hcv,hsv,hprodS,hprodC]

lemma profile_eq_defect {v s d : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25)
    (hd : 16/25 ≤ d ∧ d ≤ 11/14) (hv : 53/50-d ≤ v ∧ v ≤ 31/50) :
    profile v s d=defect v s d := by
  have hW := width_formula (x := v) (by
    constructor <;> linarith [hv.1,hv.2,hd.2,Real.pi_gt_d2])
  have hS := width_formula (x := s) ⟨hs.1,by linarith [hs.2,Real.pi_gt_d2]⟩
  have hQ := width_formula (x := v+d) (by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2])
  have hR := width_formula (x := d-s) (by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2,Real.pi_gt_d2])
  dsimp [profile,base,wing,gapWave,diagonalWave,defect,thresholdSum,southUpper,
    diagonalUpper,centerUpper,forceX,forceY,constantTerm,beta,nu,A,B,
    waveCoefficient,rootSlope,rootError,halfDifference,CandidateWestTail.radiusBound,
    CandidateWestTail.rhoBound,CandidateWestTail.coreUpper]
  rw [hW,hS,hQ,hR]
  ring

/-- The south weight varies continuously, and its nonnegativity is proved here. -/
theorem scalar_impossible {v s d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hs : 0 ≤ s ∧ s ≤ 12/25) (hd : 16/25 ≤ d ∧ d ≤ 11/14)
    (hv : 53/50-d ≤ v ∧ v ≤ 31/50)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart asouth |bsouth|)
    (hx : cx ≤ CandidateWestTail.coreUpper) (hy : cy ≤ CandidateWestTail.coreUpper)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth s ≤ asouth-cx*Real.sin s+cy*Real.cos s)
    (hWD : 1/2+angularWidth (v+d) ≤ aw*Real.sin (v+d)-bw*Real.cos (v+d)+bd)
    (hDS : 1/2+angularWidth (d-s) ≤ bsouth+ad*Real.cos (d-s)-bd*Real.sin (d-s)) : False := by
  have hg : 0 ≤ gamma s := by linarith [(gamma_bounds hs).1]
  have hsum : thresholdSum v s d ≤
      ((beta+Real.sin (v+d))*aw-Real.cos (v+d)*bw)+
      (gamma s*asouth+nu*bsouth)+
      (nu*Real.cos (d-s)*ad+(1-nu*Real.sin (d-s))*bd)+
      forceX v s*cx+forceY v s*cy := by
    dsimp [thresholdSum,forceX,forceY,beta,nu]
    linear_combination (41/20)*hCW+(gamma s)*hCS+hWD+(211/200)*hDS
  have hv0 : 0 ≤ v := by linarith [hv.1,hd.2]
  have hq : 1 ≤ v+d ∧ v+d ≤ Real.pi/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hr : 0 ≤ d-s ∧ d-s ≤ 6/5 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2]
  have hw := WestMixed.west_support hW hq
  have hdiag := WestMixed.support hD hr
  have hsouth := south_support hS hs
  have hforce := central_forces ⟨hv0,hv.2⟩ hs
  have hc := WestMixed.central_support hforce.1 hforce.2 hx hy
  have hn : defect v s d ≤ 0 := by
    dsimp [defect,diagonalUpper,centerUpper]
    linarith only [hsum,hw,hdiag,hsouth,hc]
  have hp := positive hs hd hv
  rw [profile_eq_defect hs hd hv] at hp
  linarith

end SquaresInCircles.Six.Analytic.OwnWestOwnSouth
