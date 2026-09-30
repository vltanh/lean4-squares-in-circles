module
public import SquaresInCircles.Six.Analytic.CardinalWestOwnSouth.Scalar

@[expose] public section

/-!
# Actual supports for the reflected cardinal-W / OWN-S case

The reflected cardinal-S variables obey 0<=s<=2/5 and 0<=d-s<=4/7.
Consequently its resultant U=cos s+cos(d-s), V=sin(d-s)-sin s has
U>=7/4 and |V|<=541/1000<31U/100. Its support is exactly bounded by rho0 U,
with no quadratic penalty. The remaining S angle disappears because the
coefficient of cos(d/2-s) is negative.
The W/D phase may exceed pi/2; its width is only bounded below here, never
incorrectly replaced by an unsigned formula. Compilation remains unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.CardinalWestOwnSouth
open Normalization

def westUpper : ℝ :=
  CandidateWestTail.radiusBound*(56730553/25000000)-(westWeight+1)/2

def diagonalUpper (q : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*RadialChordSupport.majorant diagonalWeight q-
    (diagonalWeight+Real.sin q+1-Real.cos q)/2

def southUpper (s d : ℝ) : ℝ :=
  CandidateWestTail.rhoBound*OwnWestCardinalSouth.southRadial s d

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
  have h := CandidateWestTail.local_vertex_support hc westWeight (-1)
  have hroot : Real.sqrt (westWeight^2+1) ≤ 56730553/25000000 := by
    have h := Real.sqrt_le_sqrt
      (show westWeight^2+1 ≤ ((56730553:ℝ)/25000000)^2 by norm_num [westWeight])
    simpa only [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 56730553/25000000)] using h
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 hroot (Real.sqrt_nonneg _)
    (by norm_num [CandidateWestTail.radiusBound])
  simp only [neg_one_sq,abs_neg,abs_one,
    abs_of_nonneg (by norm_num [westWeight] : 0 ≤ westWeight),neg_one_mul] at h
  dsimp [westUpper]
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

lemma south_force_axial {s d : ℝ} (hs : 0 ≤ s ∧ s ≤ 2/5)
    (hr : 0 ≤ d-s ∧ d-s ≤ 4/7) :
    7/4 ≤ OwnWestCardinalSouth.southRadial s d ∧
    |OwnWestCardinalSouth.southTransverse s d| ≤
      (31/100)*OwnWestCardinalSouth.southRadial s d := by
  have hssq := mul_nonneg (sub_nonneg.mpr hs.2)
    (show 0 ≤ 2/5+s by linarith [hs.1])
  have hrsq := mul_nonneg (sub_nonneg.mpr hr.2)
    (show 0 ≤ 4/7+(d-s) by linarith [hr.1])
  have hU : 7/4 ≤ OwnWestCardinalSouth.southRadial s d := by
    dsimp [OwnWestCardinalSouth.southRadial]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := s),
      Real.one_sub_sq_div_two_le_cos (x := d-s)]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_gt_d2])
  have hs1 : Real.sin s ≤ 2/5 := (Real.sin_le hs.1).trans hs.2
  have hr0 := Real.sin_nonneg_of_nonneg_of_le_pi hr.1
    (by linarith [hr.2,Real.pi_gt_d2])
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ d-s by linarith [hr.1,Real.pi_pos])
    (show (4:ℝ)/7 ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hr.2
  have ht := Seven.sin_upper_five (x := (4:ℝ)/7) (by norm_num)
  have hr1 : Real.sin (d-s) ≤ 541/1000 := by nlinarith only [hmono,ht]
  have hV : |OwnWestCardinalSouth.southTransverse s d| ≤ 541/1000 := by
    dsimp [OwnWestCardinalSouth.southTransverse]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  exact ⟨hU,by linarith⟩

lemma south_support {a b s d : ℝ} (hc : ContainedChart a |b|)
    (hs : 0 ≤ s ∧ s ≤ 2/5) (hr : 0 ≤ d-s ∧ d-s ≤ 4/7) :
    OwnWestCardinalSouth.southRadial s d*a+
      OwnWestCardinalSouth.southTransverse s d*b ≤ southUpper s d := by
  have hcone := south_force_axial hs hr
  have hU : 0 ≤ OwnWestCardinalSouth.southRadial s d := by linarith [hcone.1]
  have hrad := radial_transverse_quadratic hc
  have hp := mul_nonneg hU
    (show 0 ≤ rho0-a-(31/100)*|b| by nlinarith [sq_nonneg b])
  have hV := mul_le_mul_of_nonneg_right hcone.2 (abs_nonneg b)
  have hprod : OwnWestCardinalSouth.southTransverse s d*b ≤
      |OwnWestCardinalSouth.southTransverse s d|*|b| := by
    simpa only [abs_mul] using le_abs_self (OwnWestCardinalSouth.southTransverse s d*b)
  have hR := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.2.1 hU
  dsimp [southUpper]
  nlinarith only [hp,hV,hprod,hR]

lemma south_angle_lower {s d : ℝ} (hd : 157/200 ≤ d ∧ d ≤ 34/35) :
    OwnWestCardinalSouth.halfLinear d ≤
      -southB*OwnWestCardinalSouth.southRadial s d+(Real.sin s+Real.sin (d-s))/2 := by
  have hsq := mul_nonneg
    (show 0 ≤ 1/2-d/2 by linarith [hd.2])
    (show 0 ≤ 1/2+d/2 by linarith [hd.1])
  have hc : 7/8 ≤ Real.cos (d/2) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := d/2)]
  have hC : OwnWestCardinalSouth.halfLinear d ≤ 0 := by
    dsimp [OwnWestCardinalSouth.halfLinear,OwnWestCardinalSouth.southB]
    linarith [Real.sin_le_one (d/2)]
  have hp := mul_nonneg (neg_nonneg.mpr hC)
    (show 0 ≤ 1-Real.cos (d/2-s) by linarith [Real.cos_le_one (d/2-s)])
  have hU := (OwnWestCardinalSouth.south_half_angle s d).1
  have h0 := Real.sin_sub (d/2) (d/2-s)
  have h1 := Real.sin_add (d/2) (d/2-s)
  rw [show d/2-(d/2-s)=s by ring] at h0
  rw [show d/2+(d/2-s)=d-s by ring] at h1
  have hid : -southB*OwnWestCardinalSouth.southRadial s d+(Real.sin s+Real.sin (d-s))/2 =
      OwnWestCardinalSouth.halfLinear d*Real.cos (d/2-s) := by
    rw [hU]
    dsimp [OwnWestCardinalSouth.halfLinear,OwnWestCardinalSouth.southB,southB]
    nlinarith only [h0,h1]
  rw [hid]
  nlinarith only [hp]

lemma center_support {v d cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hd : 157/200 ≤ d ∧ d ≤ 34/35)
    (hx : cx ≤ CandidateWestTail.coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ CandidateWestTail.coreUpper) :
    ∃ upper : Bool, forceX v d*cx+forceY v d*cy ≤ centerUpper upper v d := by
  have hcv := Real.cos_nonneg_of_mem_Icc
    (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show d ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
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
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 2/5)
    (hd : 157/200 ≤ d ∧ d ≤ 34/35) (hr : 0 ≤ d-s ∧ d-s ≤ 4/7) :
    profile upper v d ≤ defect upper v s d := by
  have width_formula {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
      angularWidth x=(Real.cos x+Real.sin x)/2 := by
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
    have hs' := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
    simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs']
  have hw := width_formula (x := v) ⟨hv.1,by linarith [hv.2,Real.pi_gt_d2]⟩
  have hS := width_formula (x := s) ⟨hs.1,by linarith [hs.2,Real.pi_gt_d2]⟩
  have hD := width_formula (x := d) ⟨by linarith [hd.1],by linarith [hd.2,Real.pi_gt_d2]⟩
  have hR := width_formula (x := d-s) ⟨hr.1,by linarith [hr.2,Real.pi_gt_d2]⟩
  have hq : (Real.cos (d+v)+Real.sin (d+v))/2 ≤ angularWidth (d+v) := by
    dsimp [angularWidth]
    linarith [le_abs_self (Real.cos (d+v)),le_abs_self (Real.sin (d+v))]
  have hangle := south_angle_lower (s := s) hd
  have hid : defect upper v s d-profile upper v d =
      angularWidth (d+v)-(Real.cos (d+v)+Real.sin (d+v))/2-
      southB*OwnWestCardinalSouth.southRadial s d+(Real.sin s+Real.sin (d-s))/2-
      OwnWestCardinalSouth.halfLinear d := by
    dsimp [defect,thresholdSum,westUpper,diagonalUpper,southUpper,centerUpper,
      profile,constantTerm,westTerm,diagonalTerm,chord,forceX,forceY,
      OwnWestCardinalSouth.southRadial,westWeight,diagonalWeight,wingCos,southB,
      chordSin,chordCos,CandidateWestTail.radiusBound,CandidateWestTail.rhoBound,
      CandidateWestTail.coreUpper,RadialChordSupport.majorant]
    rw [hw,hS,hD,hR]
    ring
  linarith

/-- These are reflected scalar inequalities; no reflected NormalizedPacking is postulated. -/
theorem scalar_impossible {v s d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 2/5)
    (hd : 157/200 ≤ d ∧ d ≤ 34/35) (hr : 0 ≤ d-s ∧ d-s ≤ 4/7)
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
      (OwnWestCardinalSouth.southRadial s d*asouth+
        OwnWestCardinalSouth.southTransverse s d*bsouth)+forceX v d*cx+forceY v d*cy := by
    dsimp [thresholdSum,westWeight,diagonalWeight,OwnWestCardinalSouth.southRadial,
      OwnWestCardinalSouth.southTransverse,forceX,forceY]
    linear_combination (2037/1000)*hCW+hCS+(391/1000)*hCD+hWD+hDS
  have hw := west_support hW
  have hq : 0 ≤ d+v ∧ d+v ≤ Real.pi := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hdiag := diagonal_support hD hq
  have hsouth := south_support hS hs hr
  obtain ⟨upper,hcenter⟩ := center_support hv hd hx hy
  have hn : defect upper v s d ≤ 0 := by
    dsimp [defect]
    linarith only [hsum,hw,hdiag,hsouth,hcenter]
  have hp := (positive upper hv hd).trans_le (profile_le_defect upper hv hs hd hr)
  linarith

end SquaresInCircles.Six.Analytic.CardinalWestOwnSouth
