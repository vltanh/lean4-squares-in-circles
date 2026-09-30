module
public import SquaresInCircles.Six.Analytic.OwnSouthOrdered.Scalar

@[expose] public section

/-!
# Four actual separators supply the ordered OWN-south obstruction

Use weights 91/50, 159/100, 109/100, 1 on CW, CS, WD and D-sourced DS.
W uses its universal far-vertex support. D uses the asymmetric chord bound.
S is on an analytically justified axial support: |sin r| <= (31/100)
(159/100+cos r) for |r| <= pi/4. Both shared central force coordinates are
nonnegative and are bounded together by the central box.

The exact weighted-sum identity leaves the scalar profile proved in Scalar.
No canonical D-edge conclusion or finite checker is a premise. Compilation
and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthOrdered
open Normalization

def westUpper : ℝ :=
  CandidateWestTail.radiusBound*(106073/50000)-(westWeight+pairWeight)/2

def diagonalUpper (q : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*(rootIntercept+rootSlope*Real.sin (q/2))-
    ((109/100)*Real.sin q+1-(109/100)*Real.cos q)/2

def southUpper (r : ℝ) : ℝ := CandidateWestTail.rhoBound*(southWeight+Real.cos r)

def centerUpper (v s : ℝ) : ℝ := CandidateWestTail.coreUpper*
  (westWeight*Real.cos v-southWeight*Real.sin s-westWeight*Real.sin v+southWeight*Real.cos s)

def thresholdSum (v s d : ℝ) : ℝ :=
  westWeight*(1/2+angularWidth v)+southWeight*(1/2+angularWidth s)+
    pairWeight*(1/2+angularWidth (d+v))+(1/2+angularWidth (d-s))

def defect (v s d : ℝ) : ℝ :=
  thresholdSum v s d-westUpper-diagonalUpper (d+v)-southUpper (d-s)-centerUpper v s

lemma west_support {a b : ℝ} (hc : ContainedChart a |b|) :
    westWeight*a-pairWeight*b ≤ westUpper := by
  have h := CandidateWestTail.local_vertex_support hc westWeight (-pairWeight)
  have hs := Real.sq_sqrt (show 0 ≤ westWeight^2+pairWeight^2 by positivity)
  have hn := Real.sqrt_nonneg (westWeight^2+pairWeight^2)
  have hroot : Real.sqrt (westWeight^2+pairWeight^2) ≤ 106073/50000 := by
    norm_num [westWeight,pairWeight] at hs
    nlinarith only [hs,hn]
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 hroot hn
    (by norm_num [CandidateWestTail.radiusBound])
  norm_num [westWeight,pairWeight] at h
  dsimp [westUpper,westWeight,pairWeight] at *
  nlinarith only [h,hm]

lemma diagonal_support {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1/2 ≤ q ∧ q ≤ 443/350) :
    (109/100)*Real.sin q*a+((109/100)*Real.cos q-1)*b ≤ diagonalUpper q := by
  have h := CandidateWestTail.local_vertex_support hc
    ((109/100)*Real.sin q) ((109/100)*Real.cos q-1)
  have hn := Real.sqrt_nonneg
    (((109/100)*Real.sin q)^2+((109/100)*Real.cos q-1)^2)
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 (chord_norm_upper hq) hn
    (by norm_num [CandidateWestTail.radiusBound])
  have hw : (109/100)*Real.sin q+1-(109/100)*Real.cos q ≤
      |(109/100)*Real.sin q|+|(109/100)*Real.cos q-1| := by
    linarith [le_abs_self ((109/100)*Real.sin q),neg_le_abs ((109/100)*Real.cos q-1)]
  dsimp [diagonalUpper]
  linarith

lemma south_slope {r : ℝ} (hr : -(Real.pi/4) ≤ r ∧ r ≤ Real.pi/4) :
    0 ≤ southWeight+Real.cos r ∧
    |Real.sin r| ≤ (31/100)*(southWeight+Real.cos r) := by
  have hroot : (707:ℝ)/1000 ≤ Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hc : 707/1000 ≤ Real.cos r := by
    by_cases hr0 : 0 ≤ r
    · have h := Real.cos_le_cos_of_nonneg_of_le_pi hr0
        (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) hr.2
      rw [Real.cos_pi_div_four] at h
      exact hroot.trans h
    · have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0 ≤ -r by linarith)
        (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos])
        (show -r ≤ Real.pi/4 by linarith [hr.1])
      rw [Real.cos_neg,Real.cos_pi_div_four] at h
      exact hroot.trans h
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
    (hr : -(Real.pi/4) ≤ r ∧ r ≤ Real.pi/4) :
    (southWeight+Real.cos r)*a+Real.sin r*b ≤ southUpper r := by
  have hq := radial_transverse_quadratic hc
  have hrad : a+(31/100)*|b| ≤ rho0 := by nlinarith [sq_nonneg b]
  have ht := south_slope hr
  have hp := mul_nonneg ht.1 (show 0 ≤ rho0-a-(31/100)*|b| by linarith)
  have hb : Real.sin r*b ≤ |Real.sin r|*|b| := by
    simpa only [abs_mul] using le_abs_self (Real.sin r*b)
  have hs := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg b)
  have hR := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.2.1 ht.1
  dsimp [southUpper]
  nlinarith only [hp,hb,hs,hR]

private lemma small_trig {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 2/3) :
    7/9 ≤ Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x ≤ 2/3 := by
  have hp := mul_nonneg (sub_nonneg.mpr hx.2)
    (show 0 ≤ 2/3+x by linarith [hx.1])
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  exact ⟨by nlinarith,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2]),
    (Real.sin_le hx.1).trans hx.2⟩

lemma center_support {v s cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 2/3)
    (hx : cx ≤ CandidateWestTail.coreUpper) (hy : cy ≤ CandidateWestTail.coreUpper) :
    (westWeight*Real.cos v-southWeight*Real.sin s)*cx+
      (-westWeight*Real.sin v+southWeight*Real.cos s)*cy ≤ centerUpper v s := by
  have tv := small_trig hv
  have ts := small_trig hs
  have hX : 0 ≤ westWeight*Real.cos v-southWeight*Real.sin s := by
    dsimp [westWeight,southWeight]
    linarith [tv.1,ts.2.2]
  have hY : 0 ≤ -westWeight*Real.sin v+southWeight*Real.cos s := by
    dsimp [westWeight,southWeight]
    linarith [tv.2.2,ts.1]
  have hp := mul_nonneg (sub_nonneg.mpr hx) hX
  have hq := mul_nonneg (sub_nonneg.mpr hy) hY
  dsimp [centerUpper]
  nlinarith only [hp,hq]

lemma profile_le_defect {v s d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 12/25) (hs : 0 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) : profile v s d ≤ defect v s d := by
  have tv := small_trig ⟨hv.1,by linarith [hv.2]⟩
  have ts := small_trig hs
  have hq : 0 ≤ d+v ∧ d+v ≤ 443/350 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2]
  have hcq := Real.cos_nonneg_of_mem_Icc
    (show d+v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_gt_d2])
  have hsq := Real.sin_nonneg_of_nonneg_of_le_pi hq.1
    (by linarith [hq.2,Real.pi_gt_d2])
  have hw : angularWidth v=(Real.cos v+Real.sin v)/2 := by
    simp only [angularWidth,abs_of_nonneg (by linarith [tv.1] : 0 ≤ Real.cos v),abs_of_nonneg tv.2.1]
  have hs' : angularWidth s=(Real.cos s+Real.sin s)/2 := by
    simp only [angularWidth,abs_of_nonneg (by linarith [ts.1] : 0 ≤ Real.cos s),abs_of_nonneg ts.2.1]
  have hq' : angularWidth (d+v)=(Real.cos (d+v)+Real.sin (d+v))/2 := by
    simp only [angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq]
  have hr : (Real.cos (d-s)+Real.sin (d-s))/2 ≤ angularWidth (d-s) := by
    dsimp [angularWidth]
    linarith [le_abs_self (Real.cos (d-s)),le_abs_self (Real.sin (d-s))]
  dsimp [profile,defect,thresholdSum,westUpper,diagonalUpper,southUpper,centerUpper,
    wing,chord,southTerm,westWeight,southWeight,pairWeight,wingCos,wingSin,
    rootIntercept,rootSlope,chordCoefficient,CandidateWestTail.radiusBound,
    CandidateWestTail.rhoBound,CandidateWestTail.coreUpper]
  rw [hw,hs',hq']
  nlinarith only [hr]

/-- Four real inequalities, not selected source indices, give the contradiction. -/
theorem scalar_impossible {v s d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hv : 0 ≤ v) (hvs : v ≤ s) (hs : s ≤ 2/3) (hsum : v+s ≤ 24/25)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart asouth |bsouth|)
    (hx : cx ≤ CandidateWestTail.coreUpper) (hy : cy ≤ CandidateWestTail.coreUpper)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth s ≤ asouth-cx*Real.sin s+cy*Real.cos s)
    (hWD : 1/2+angularWidth (d+v) ≤ ad*Real.sin (d+v)+bd*Real.cos (d+v)-bw)
    (hDS : 1/2+angularWidth (d-s) ≤ asouth*Real.cos (d-s)+bsouth*Real.sin (d-s)-bd) : False := by
  have hvmax : v ≤ 12/25 := by linarith
  have hs0 : 0 ≤ s := hv.trans hvs
  have hd' : 1/2 ≤ d ∧ d ≤ 11/14 := ⟨hd.1,by linarith [hd.2,Real.pi_lt_d4]⟩
  have hq : 1/2 ≤ d+v ∧ d+v ≤ 443/350 := by
    constructor <;> linarith [hd'.1,hd'.2,hv,hvmax]
  have hr : -(Real.pi/4) ≤ d-s ∧ d-s ≤ Real.pi/4 := by
    constructor <;> linarith [hd.1,hd.2,hs,hs0,Real.pi_gt_d2]
  have hsum' : thresholdSum v s d ≤
      (westWeight*aw-pairWeight*bw)+
      ((109/100)*Real.sin (d+v)*ad+((109/100)*Real.cos (d+v)-1)*bd)+
      ((southWeight+Real.cos (d-s))*asouth+Real.sin (d-s)*bsouth)+
      (westWeight*Real.cos v-southWeight*Real.sin s)*cx+
      (-westWeight*Real.sin v+southWeight*Real.cos s)*cy := by
    dsimp [thresholdSum,westWeight,southWeight,pairWeight]
    linear_combination (91/50)*hCW+(159/100)*hCS+(109/100)*hWD+hDS
  have hw := west_support hW
  have hdiag := diagonal_support hD hq
  have hsouth := south_support hS hr
  have hc := center_support ⟨hv,by linarith [hvmax]⟩ ⟨hs0,hs⟩ hx hy
  have hn : defect v s d ≤ 0 := by
    dsimp [defect]
    linarith only [hsum',hw,hdiag,hsouth,hc]
  have hp := (positive hv hvs hs hsum hd').trans_le
    (profile_le_defect ⟨hv,hvmax⟩ ⟨hs0,hs⟩ hd')
  linarith

end SquaresInCircles.Six.Analytic.OwnSouthOrdered
