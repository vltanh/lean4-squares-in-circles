import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Scalar

/-!
# The west-dominant stress

The stress has weights `9/4`, `3/4`, `9/20`, `1` and `1` on the separations
C–W, C–S and C–D along the own axes of W, S and D, W–D along the secondary axis
of W, and D–S along the secondary axis of D. The support of W is bounded by its
far vertex, that of D by the radial-chord majorant with `z = 9/20`, that of S
by the smooth axial bound, whose force lies in the cone `U ≥ 7/5`,
`|V| ≤ U/2`, and that of C by the box of its centre, with the second coordinate
at the end chosen by the sign of the force. The threshold sum less these bounds
is exactly the profile, so the positivity of the profile contradicts the five
separations.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthWestDominant
open Normalization

def westUpper : ℝ := CandidateWestTail.radiusBound*(123111/50000)-(westWeight+1)/2

def diagonalUpper (q : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*RadialChordSupport.majorant diagonalWeight q-
    (diagonalWeight+Real.sin q+1-Real.cos q)/2

def southUpper (r : ℝ) : ℝ :=
  CandidateWestTail.rhoBound*(southWeight+Real.cos r)+Real.sin r^2/12

def forceX (v s d : ℝ) : ℝ :=
  westWeight*Real.cos v-southWeight*Real.sin s+diagonalWeight*Real.cos d

def forceY (v s d : ℝ) : ℝ :=
  -westWeight*Real.sin v+southWeight*Real.cos s+diagonalWeight*Real.sin d

def centerUpper (upper : Bool) (v s d : ℝ) : ℝ :=
  CandidateWestTail.coreUpper*forceX v s d+centerY upper*forceY v s d

def thresholdSum (v s d : ℝ) : ℝ :=
  westWeight*(1/2+angularWidth v)+southWeight*(1/2+angularWidth s)+
    diagonalWeight*(1/2+angularWidth d)+(1/2+angularWidth (d+v))+(1/2+angularWidth (d-s))

def defect (upper : Bool) (v s d : ℝ) : ℝ :=
  thresholdSum v s d-westUpper-diagonalUpper (d+v)-southUpper (d-s)-centerUpper upper v s d

lemma west_support {a b : ℝ} (hc : ContainedChart a |b|) :
    westWeight*a-b ≤ westUpper := by
  have h := CandidateWestTail.local_vertex_support hc westWeight (-1)
  have e : westWeight^2+(-1)^2 = (97/16:ℝ) := by norm_num [westWeight]
  have ea : |westWeight|+|(-1:ℝ)| = 13/4 := by norm_num [westWeight]
  rw [e,ea] at h
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 97/16 by norm_num)
  have hn := Real.sqrt_nonneg (97/16:ℝ)
  have hroot : Real.sqrt (97/16) ≤ 123111/50000 := by
    nlinarith only [hs,hn]
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 hroot hn
    (by norm_num [CandidateWestTail.radiusBound])
  dsimp only [westUpper,westWeight] at h hm ⊢
  linarith only [h,hm]

lemma diagonal_support {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 0 ≤ q ∧ q ≤ Real.pi) :
    (diagonalWeight+Real.sin q)*a+(Real.cos q-1)*b ≤ diagonalUpper q := by
  have hz : 0 ≤ diagonalWeight := by norm_num [diagonalWeight]
  have h := RadialChordSupport.support hc hz hq
  have hm := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.1
    (RadialChordSupport.majorant_nonnegative hz hq)
  dsimp [diagonalUpper]
  linarith

/-- The force on S lies in the cone of the smooth axial bound. -/
lemma south_force_cone {r : ℝ} (hr : 0 ≤ r ∧ r ≤ Real.pi/4) :
    7/5 ≤ southWeight+Real.cos r ∧ |Real.sin r| ≤ (southWeight+Real.cos r)/2 := by
  have hroot : (707:ℝ)/1000 ≤ Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hr.1
    (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) hr.2
  rw [Real.cos_pi_div_four] at hcos
  have hc : 707/1000 ≤ Real.cos r := hroot.trans hcos
  have hs : |Real.sin r| ≤ 708/1000 := by
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h)
      (show 0 < |Real.sin r|+708/1000 by positivity)
    have hq := mul_nonneg (show 0 ≤ Real.cos r-707/1000 by linarith)
      (show 0 ≤ Real.cos r+707/1000 by linarith)
    nlinarith [Real.sin_sq_add_cos_sq r,sq_abs (Real.sin r)]
  dsimp [southWeight]
  exact ⟨by linarith,by linarith⟩

lemma south_support {a b r : ℝ} (hc : ContainedChart a |b|)
    (hr : 0 ≤ r ∧ r ≤ Real.pi/4) :
    (southWeight+Real.cos r)*a+Real.sin r*b ≤ southUpper r := by
  have hcone := south_force_cone hr
  have h := soft_axial_support hc hcone.1 hcone.2
  have hU : 0 ≤ southWeight+Real.cos r := by linarith [hcone.1]
  have hm := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.2.1 hU
  dsimp [southUpper]
  linarith

private lemma small_trig {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 2/3) :
    7/9 ≤ Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x ≤ 2/3 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hx.2)
    (show 0 ≤ 2/3+x by linarith [hx.1])
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  exact ⟨by nlinarith,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2]),
    (Real.sin_le hx.1).trans hx.2⟩

lemma forceX_nonnegative {v s d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) : 0 ≤ forceX v s d := by
  have tv := small_trig hv
  have ts := small_trig hs
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  dsimp [forceX,westWeight,southWeight,diagonalWeight]
  linarith [tv.1,ts.2.2]

lemma center_support {v s d cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hx : cx ≤ CandidateWestTail.coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ CandidateWestTail.coreUpper) :
    ∃ upper : Bool, forceX v s d*cx+forceY v s d*cy ≤ centerUpper upper v s d := by
  have hX := mul_le_mul_of_nonneg_left hx (forceX_nonnegative hv hs hd)
  by_cases hY : 0 ≤ forceY v s d
  · refine ⟨true,?_⟩
    have hY' := mul_le_mul_of_nonneg_left hy.2 hY
    dsimp [centerUpper,centerY,CandidateWestTail.coreUpper] at *
    nlinarith only [hX,hY']
  · refine ⟨false,?_⟩
    have hY' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hY) hy.1
    dsimp [centerUpper,centerY]
    nlinarith only [hX,hY']

lemma profile_eq_defect (upper : Bool) {v s d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 12/25)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) : profile upper v s d = defect upper v s d := by
  have tv := small_trig hv
  have ts := small_trig ⟨hs.1,by linarith [hs.2]⟩
  have hq : 0 ≤ d+v ∧ d+v ≤ Real.pi/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hr : 0 ≤ d-s ∧ d-s ≤ Real.pi/2 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2,Real.pi_pos]
  have width_formula {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
      angularWidth x=(Real.cos x+Real.sin x)/2 := by
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
    have hs' := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
    simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs']
  have hw := width_formula (x := v) ⟨hv.1,by linarith [hv.2,Real.pi_gt_d2]⟩
  have hs' := width_formula (x := s) ⟨hs.1,by linarith [hs.2,Real.pi_gt_d2]⟩
  have hd' := width_formula (x := d) ⟨by linarith [hd.1],by linarith [hd.2,Real.pi_pos]⟩
  have hq' := width_formula hq
  have hr' := width_formula hr
  rw [profile,westSlice,southSlice,transverse_eq]
  dsimp [defect,thresholdSum,westUpper,diagonalUpper,southUpper,centerUpper,
    constantTerm,westTerm,southTerm,diagonalTerm,chord,forceX,forceY,
    westWeight,southWeight,diagonalWeight,wingCos,wingSin,chordSin,chordCos,
    CandidateWestTail.radiusBound,CandidateWestTail.rhoBound,CandidateWestTail.coreUpper,
    RadialChordSupport.majorant]
  rw [hw,hs',hd',hq',hr']
  ring

/-- The five separating inequalities of the west-dominant stress are
incompatible on its domain. -/
theorem scalar_impossible {v s d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hv : v ≤ 2/3) (hs : 0 ≤ s) (horder : s ≤ v) (hsum : v+s ≤ 24/25)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart asouth |bsouth|)
    (hx : cx ≤ CandidateWestTail.coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ CandidateWestTail.coreUpper)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth s ≤ asouth-cx*Real.sin s+cy*Real.cos s)
    (hCD : 1/2+angularWidth d ≤ ad+cx*Real.cos d+cy*Real.sin d)
    (hWD : 1/2+angularWidth (d+v) ≤ ad*Real.sin (d+v)+bd*Real.cos (d+v)-bw)
    (hDS : 1/2+angularWidth (d-s) ≤ asouth*Real.cos (d-s)+bsouth*Real.sin (d-s)-bd) : False := by
  have hv0 : 0 ≤ v := hs.trans horder
  have hsmax : s ≤ 12/25 := by linarith
  have hq : 0 ≤ d+v ∧ d+v ≤ Real.pi := by
    constructor <;> linarith [hv0,hv,hd.1,hd.2,Real.pi_gt_d2]
  have hr : 0 ≤ d-s ∧ d-s ≤ Real.pi/4 := by
    constructor <;> linarith [hs,hsmax,hd.1,hd.2]
  have hsum' : thresholdSum v s d ≤
      (westWeight*aw-bw)+
      ((diagonalWeight+Real.sin (d+v))*ad+(Real.cos (d+v)-1)*bd)+
      ((southWeight+Real.cos (d-s))*asouth+Real.sin (d-s)*bsouth)+
      forceX v s d*cx+forceY v s d*cy := by
    dsimp [thresholdSum,westWeight,southWeight,diagonalWeight,forceX,forceY]
    linear_combination (9/4)*hCW+(3/4)*hCS+(9/20)*hCD+hWD+hDS
  have hw := west_support hW
  have hdiag := diagonal_support hD hq
  have hsouth := south_support hS hr
  obtain ⟨upper,hcenter⟩ := center_support ⟨hv0,hv⟩ ⟨hs,by linarith [hsmax]⟩ hd hx hy
  have hn : defect upper v s d ≤ 0 := by
    dsimp [defect]
    linarith only [hsum',hw,hdiag,hsouth,hcenter]
  have hp := positive upper hv hs horder hsum
    (show 1/2 ≤ d ∧ d ≤ 11/14 by constructor <;> linarith [hd.1,hd.2,Real.pi_lt_d4])
  rw [profile_eq_defect upper ⟨hv0,hv⟩ ⟨hs,hsmax⟩ hd] at hp
  linarith

end SquaresInCircles.Six.Analytic.OwnSouthWestDominant
