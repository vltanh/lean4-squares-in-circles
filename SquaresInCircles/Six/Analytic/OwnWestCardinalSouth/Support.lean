import SquaresInCircles.Six.Analytic.OwnWestCardinalSouth.Scalar

/-!
# The actual OWN-W / cardinal-S five-edge contradiction

Weights 2,1,3/10,1,1 multiply CW, CS, CD, W-sourced WD and D-sourced DS.
The S resultant is handled by the single proved smooth-support cone. Its
angle is then eliminated by SouthAngle.lean. W and D use their exact global
support bounds. Both signs of the central y force are retained.
No candidate S-sourced DS inequality or finite-checker result is assumed.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestCardinalSouth
open Normalization

def westUpper : ℝ := CandidateWestTail.radiusBound*(27951/12500)-3/2

def diagonalUpper (q : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*RadialChordSupport.majorant diagonalWeight q-
    (diagonalWeight+Real.sin q+1-Real.cos q)/2

def southUpper (s d : ℝ) : ℝ :=
  CandidateWestTail.rhoBound*southRadial s d+(3/25)*(southTransverse s d)^2

def forceX (v d : ℝ) : ℝ := westWeight*Real.cos v+diagonalWeight*Real.cos d

def forceY (v d : ℝ) : ℝ := -westWeight*Real.sin v+1+diagonalWeight*Real.sin d

def centerUpper (upper : Bool) (v d : ℝ) : ℝ :=
  CandidateWestTail.coreUpper*forceX v d+centerY upper*forceY v d

def thresholdSum (v s d : ℝ) : ℝ :=
  westWeight*(1/2+angularWidth v)+(1/2+angularWidth s)+
    diagonalWeight*(1/2+angularWidth d)+(1/2+angularWidth (d+v))+(1/2+angularWidth (d-s))

def defect (upper : Bool) (v s d : ℝ) : ℝ :=
  thresholdSum v s d-westUpper-diagonalUpper (d+v)-southUpper s d-centerUpper upper v d

lemma west_support {a b : ℝ} (hc : ContainedChart a |b|) :
    westWeight*a-b ≤ westUpper := by
  have h := CandidateWestTail.local_vertex_support hc (2:ℝ) (-1)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5:ℝ)
  have hroot : Real.sqrt (5:ℝ) ≤ 27951/12500 := by nlinarith only [hs,hn]
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 hroot hn
    (by norm_num [CandidateWestTail.radiusBound])
  norm_num at h
  dsimp [westUpper,westWeight]
  linarith

lemma diagonal_support {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 0 ≤ q ∧ q ≤ Real.pi) :
    (diagonalWeight+Real.sin q)*a+(Real.cos q-1)*b ≤ diagonalUpper q := by
  have hz : 0 ≤ diagonalWeight := by norm_num [diagonalWeight]
  have h := RadialChordSupport.support hc hz hq
  have hm := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.1
    (RadialChordSupport.majorant_nonnegative hz hq)
  dsimp [diagonalUpper]
  linarith

lemma center_support {v d cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hx : cx ≤ CandidateWestTail.coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ CandidateWestTail.coreUpper) :
    ∃ upper : Bool, forceX v d*cx+forceY v d*cy ≤ centerUpper upper v d := by
  have hcv := Real.cos_nonneg_of_mem_Icc
    (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show d ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hX : 0 ≤ forceX v d := by dsimp [forceX,westWeight,diagonalWeight]; positivity
  have hx' := mul_le_mul_of_nonneg_left hx hX
  by_cases hY : 0 ≤ forceY v d
  · refine ⟨true,?_⟩
    have hy' := mul_le_mul_of_nonneg_left hy.2 hY
    dsimp [centerUpper,centerY,CandidateWestTail.coreUpper] at *
    nlinarith only [hx',hy']
  · refine ⟨false,?_⟩
    have hy' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hY) hy.1
    dsimp [centerUpper,centerY]
    nlinarith only [hx',hy']

lemma profile_le_defect (upper : Bool) {v s d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : -(2/5) ≤ s ∧ s ≤ 2/5)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (hr : d-s ≤ Real.pi/4) :
    profile upper v d ≤ defect upper v s d := by
  have hd' : 1/2 ≤ d ∧ d ≤ 11/14 := ⟨hd.1,by linarith [hd.2,Real.pi_lt_d4]⟩
  have hr' : d-s ≤ 11/14 := by linarith [hr,Real.pi_lt_d4]
  have hangle := south_angle_lower hd' hs.2 hr'
  have width_formula {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
      angularWidth x=(Real.cos x+Real.sin x)/2 := by
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
    simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hsin]
  have hw := width_formula (x := v) ⟨hv.1,by linarith [hv.2,Real.pi_gt_d2]⟩
  have hD := width_formula (x := d) ⟨by linarith [hd.1],by linarith [hd.2,Real.pi_pos]⟩
  have hq := width_formula
    (show 0 ≤ d+v ∧ d+v ≤ Real.pi/2 by
      constructor <;> linarith [hd.1,hd.2,hv.1,hv.2,Real.pi_gt_d2])
  have hR := width_formula
    (show 0 ≤ d-s ∧ d-s ≤ Real.pi/2 by
      constructor <;> linarith [hd.1,hs.2,hr,Real.pi_pos])
  have hcosS := Real.cos_nonneg_of_mem_Icc
    (show s ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have hS : angularWidth s=(Real.cos s+|Real.sin s|)/2 := by
    simp only [angularWidth,abs_of_nonneg hcosS]
  have hid : defect upper v s d-profile upper v d =
      southContribution s d-halfLinear d+1/250 := by
    dsimp [defect,thresholdSum,westUpper,diagonalUpper,southUpper,centerUpper,
      profile,constantTerm,westTerm,diagonalTerm,chord,forceX,forceY,southContribution,
      southRadial,southTransverse,westWeight,diagonalWeight,wingCos,southB,
      chordSin,chordCos,CandidateWestTail.radiusBound,CandidateWestTail.rhoBound,
      CandidateWestTail.coreUpper,RadialChordSupport.majorant]
    rw [hw,hS,hD,hq,hR]
    ring
  linarith

/-- Every premise here is an actual central or pair-separation inequality. -/
theorem scalar_impossible {v s d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : -(2/5) ≤ s ∧ s ≤ 2/5)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (hr : d-s ≤ Real.pi/4)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart asouth |bsouth|)
    (hx : cx ≤ CandidateWestTail.coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ CandidateWestTail.coreUpper)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth s ≤ asouth*Real.cos s-bsouth*Real.sin s+cy)
    (hCD : 1/2+angularWidth d ≤ ad+cx*Real.cos d+cy*Real.sin d)
    (hWD : 1/2+angularWidth (d+v) ≤ ad*Real.sin (d+v)+bd*Real.cos (d+v)-bw)
    (hDS : 1/2+angularWidth (d-s) ≤ asouth*Real.cos (d-s)+bsouth*Real.sin (d-s)-bd) : False := by
  have hsum : thresholdSum v s d ≤
      (westWeight*aw-bw)+
      ((diagonalWeight+Real.sin (d+v))*ad+(Real.cos (d+v)-1)*bd)+
      (southRadial s d*asouth+southTransverse s d*bsouth)+forceX v d*cx+forceY v d*cy := by
    dsimp [thresholdSum,westWeight,diagonalWeight,southRadial,southTransverse,forceX,forceY]
    linear_combination 2*hCW+hCS+(3/10)*hCD+hWD+hDS
  have hw := west_support hW
  have hq : 0 ≤ d+v ∧ d+v ≤ Real.pi := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hdiag := diagonal_support hD hq
  have hsouth := south_support hS hd hs.2 hr
  obtain ⟨upper,hcenter⟩ := center_support hv hd hx hy
  have hn : defect upper v s d ≤ 0 := by
    dsimp [defect,southUpper]
    linarith only [hsum,hw,hdiag,hsouth,hcenter]
  have hp := (positive upper hv
    (show 1/2 ≤ d ∧ d ≤ 11/14 by constructor <;> linarith [hd.1,hd.2,Real.pi_lt_d4])).trans_le
      (profile_le_defect upper hv hs hd hr)
  linarith

end SquaresInCircles.Six.Analytic.OwnWestCardinalSouth
