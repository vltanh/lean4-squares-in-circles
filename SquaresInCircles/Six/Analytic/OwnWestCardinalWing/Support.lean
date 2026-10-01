import SquaresInCircles.Six.Analytic.OwnWestCardinalWing.Scalar
import SquaresInCircles.Six.Analytic.WestMixed.Support

/-!
# Four actual separators supply the cardinal-S mixed-west scalar

The W force uses the proved axial cone. D uses the global half-angle majorant.
The S root uses one tangent at 37/20, whose validity follows from a square.
Both central force components are positive on the refined actual domain.
No candidate W-sourced inequality or classification theorem is a premise.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestCardinalWing
open Normalization WestMixed

def southUpper (s : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*(rootIntercept-rootSin*Real.sin s)-
    (gamma*Real.cos s+nu-gamma*Real.sin s)/2

def diagonalUpper (r : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*(rootSlope*halfDifference r+rootError)-
    (nu*Real.cos r+1-nu*Real.sin r)/2

def centerUpper (v : ℝ) : ℝ :=
  CandidateWestTail.coreUpper*(WestMixed.beta*Real.cos v+gamma-WestMixed.beta*Real.sin v)

def thresholdSum (v s d : ℝ) : ℝ :=
  WestMixed.beta*(1/2+angularWidth v)+gamma*(1/2+angularWidth s)+
    (1/2+angularWidth (v+d))+nu*(1/2+angularWidth (d-s))

def defect (v s d : ℝ) : ℝ :=
  thresholdSum v s d-CandidateWestTail.rhoBound*(WestMixed.beta+Real.sin (v+d))-
    southUpper s-diagonalUpper (d-s)-centerUpper v

lemma south_root (s : ℝ) :
    Real.sqrt (gamma^2+nu^2-2*gamma*nu*Real.sin s) ≤ rootIntercept-rootSin*Real.sin s := by
  have hr : 0 ≤ gamma^2+nu^2-2*gamma*nu*Real.sin s := by
    dsimp [gamma,nu]
    linarith [Real.sin_le_one s]
  have hs := Real.sq_sqrt hr
  have hp := sq_nonneg (Real.sqrt (gamma^2+nu^2-2*gamma*nu*Real.sin s)-37/20)
  dsimp [gamma,nu,rootIntercept,rootSin] at *
  nlinarith only [hs,hp]

lemma south_support {a b s : ℝ} (hc : ContainedChart a |b|) :
    gamma*Real.cos s*a+(nu-gamma*Real.sin s)*b ≤ southUpper s := by
  have h := CandidateWestTail.local_vertex_support hc (gamma*Real.cos s) (nu-gamma*Real.sin s)
  have hi : (gamma*Real.cos s)^2+(nu-gamma*Real.sin s)^2 =
      gamma^2+nu^2-2*gamma*nu*Real.sin s := by
    linear_combination gamma^2*(Real.sin_sq_add_cos_sq s)
  rw [hi] at h
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 (south_root s) (Real.sqrt_nonneg _)
    (by norm_num [CandidateWestTail.radiusBound])
  have hw : gamma*Real.cos s+nu-gamma*Real.sin s ≤
      |gamma*Real.cos s|+|nu-gamma*Real.sin s| := by
    linarith [le_abs_self (gamma*Real.cos s),le_abs_self (nu-gamma*Real.sin s)]
  dsimp [southUpper]
  linarith

lemma center_support {v cx cy : ℝ} (hv : 0 ≤ v ∧ v ≤ 31/50)
    (hx : cx ≤ CandidateWestTail.coreUpper) (hy : cy ≤ CandidateWestTail.coreUpper) :
    WestMixed.beta*Real.cos v*cx+(gamma-WestMixed.beta*Real.sin v)*cy ≤ centerUpper v := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hX : 0 ≤ WestMixed.beta*Real.cos v := by dsimp [WestMixed.beta]; positivity
  have hs := Real.sin_le hv.1
  have hY : 0 ≤ gamma-WestMixed.beta*Real.sin v := by dsimp [gamma,WestMixed.beta]; linarith [hv.2]
  refine (WestMixed.central_support hX hY hx hy).trans_eq ?_
  dsimp [centerUpper]
  ring

lemma profile_eq_defect (negative : Bool) {v x d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 2/5) (hd : 16/25 ≤ d ∧ d ≤ 11/14)
    (hv : 53/50-d ≤ v ∧ v ≤ 31/50) :
    profile negative v x d=defect v (side negative*x) d := by
  have hv0 : 0 ≤ v := by linarith [hv.1,hd.2]
  have hW := width_formula (x := v) ⟨hv0,by linarith [hv.2,Real.pi_gt_d2]⟩
  have hQ := width_formula (x := v+d) (by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2])
  have hr : 0 ≤ d-side negative*x ∧ d-side negative*x ≤ Real.pi/2 := by
    cases negative <;> dsimp [side] <;> constructor <;>
      linarith [hx.1,hx.2,hd.1,hd.2,Real.pi_gt_d2]
  have hR := width_formula hr
  have hcx := Real.cos_nonneg_of_mem_Icc
    (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hx.1,hx.2,Real.pi_gt_d2])
  have hsx := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_d2])
  have hS : angularWidth (side negative*x)=(Real.cos x+Real.sin x)/2 := by
    cases negative <;> simp [side,angularWidth,abs_of_nonneg hcx,abs_of_nonneg hsx]
  dsimp [profile,base,wing,gapWave,diagonalWave,southTerm,defect,thresholdSum,
    southUpper,diagonalUpper,centerUpper,constantTerm,rootIntercept,rootSin,
    WestMixed.beta,gamma,nu,A,B,waveCoefficient,rootSlope,rootError,halfDifference,
    CandidateWestTail.radiusBound,CandidateWestTail.rhoBound,CandidateWestTail.coreUpper]
  rw [hW,hQ,hR,hS]
  cases negative <;> simp only [side,sineCoefficient,Bool.false_eq_true,if_true,if_false,
    neg_one_mul,one_mul,Real.cos_neg,Real.sin_neg] <;> ring

/-- The candidate south inequality and the actual D-sourced west inequality suffice. -/
theorem scalar_impossible {v s d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hs : -(2/5) ≤ s ∧ s ≤ 2/5) (hd : 16/25 ≤ d ∧ d ≤ 11/14)
    (hv : 53/50-d ≤ v ∧ v ≤ 31/50)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart asouth |bsouth|)
    (hx : cx ≤ CandidateWestTail.coreUpper) (hy : cy ≤ CandidateWestTail.coreUpper)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth s ≤ asouth*Real.cos s-bsouth*Real.sin s+cy)
    (hWD : 1/2+angularWidth (v+d) ≤ aw*Real.sin (v+d)-bw*Real.cos (v+d)+bd)
    (hDS : 1/2+angularWidth (d-s) ≤ bsouth+ad*Real.cos (d-s)-bd*Real.sin (d-s)) : False := by
  have hsum : thresholdSum v s d ≤
      ((WestMixed.beta+Real.sin (v+d))*aw-Real.cos (v+d)*bw)+
      (gamma*Real.cos s*asouth+(nu-gamma*Real.sin s)*bsouth)+
      (nu*Real.cos (d-s)*ad+(1-nu*Real.sin (d-s))*bd)+
      WestMixed.beta*Real.cos v*cx+(gamma-WestMixed.beta*Real.sin v)*cy := by
    dsimp [thresholdSum,WestMixed.beta,gamma,nu]
    linear_combination (41/20)*hCW+(38/25)*hCS+hWD+(211/200)*hDS
  have hv0 : 0 ≤ v := by linarith [hv.1,hd.2]
  have hq : 1 ≤ v+d ∧ v+d ≤ Real.pi/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hr : 0 ≤ d-s ∧ d-s ≤ 6/5 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2]
  have hw := WestMixed.west_support hW hq
  have hdiag := WestMixed.support hD hr
  have hsouth := south_support (s := s) hS
  have hc := center_support ⟨hv0,hv.2⟩ hx hy
  have hn : defect v s d ≤ 0 := by
    dsimp [defect,diagonalUpper]
    linarith only [hsum,hw,hdiag,hsouth,hc]
  by_cases hs0 : 0 ≤ s
  · have hp := positive false ⟨hs0,hs.2⟩ hd hv
    rw [profile_eq_defect false ⟨hs0,hs.2⟩ hd hv] at hp
    simp only [side,Bool.false_eq_true,if_false,one_mul] at hp
    exact (not_lt_of_ge hn) hp
  · have hx' : 0 ≤ -s ∧ -s ≤ 2/5 := by constructor <;> linarith [hs.1]
    have hp := positive true hx' hd hv
    rw [profile_eq_defect true hx' hd hv] at hp
    simp only [side,if_true,neg_one_mul,neg_neg] at hp
    linarith

end SquaresInCircles.Six.Analytic.OwnWestCardinalWing
