import SquaresInCircles.Six.Analytic.ReflectedOwnWings.Scalar
import SquaresInCircles.Six.Analytic.RadialChordSupport
import SquaresInCircles.Six.Analytic.SoftAxialSupport

/-!
# The reflected case: the stress

In the reflected frame, the separators of C with W, S and D along their own
axes, of W and D along the secondary axis of W, and of D and S along the
secondary axis of D, with weights `9/4`, `3/4`, `9/20`, `1` and `1`, bound the
threshold sum. The works of the forces are bounded by supports: on W by its
far-vertex support, on D by the radial chord bound, on S by the soft axial
support with the penalty `sin² r/12`, and on C by the face of the box chosen by
the sign of the force. At `q = d + v`, which may exceed `π/2`, the width is
bounded below by `(cos q + sin q)/2`. What is left is at least the value, which
is positive.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.ReflectedOwnWings
open Normalization

def westUpper : ℝ := CandidateWestTail.radiusBound*(123111/50000)-(beta+1)/2

def diagonalUpper (q : ℝ) : ℝ :=
  CandidateWestTail.radiusBound*RadialChordSupport.majorant delta q-
    (delta+Real.sin q+1-Real.cos q)/2

def southUpper (r : ℝ) : ℝ :=
  CandidateWestTail.rhoBound*(gamma+Real.cos r)+Real.sin r^2/12

def forceX (v s d : ℝ) : ℝ := beta*Real.cos v-gamma*Real.sin s+delta*Real.cos d

def forceY (v s d : ℝ) : ℝ := -beta*Real.sin v+gamma*Real.cos s+delta*Real.sin d

def centerUpper (upper : Bool) (v s d : ℝ) : ℝ :=
  CandidateWestTail.coreUpper*forceX v s d+face upper*forceY v s d

def thresholdSum (v s d : ℝ) : ℝ :=
  beta*(1/2+angularWidth v)+gamma*(1/2+angularWidth s)+delta*(1/2+angularWidth d)+
    (1/2+angularWidth (d+v))+(1/2+angularWidth (d-s))

def defect (upper : Bool) (v s d : ℝ) : ℝ :=
  thresholdSum v s d-westUpper-diagonalUpper (d+v)-southUpper (d-s)-centerUpper upper v s d

lemma west_support {a b : ℝ} (hc : ContainedChart a |b|) : beta*a-b ≤ westUpper := by
  have h := CandidateWestTail.local_vertex_support hc beta (-1)
  have hr : Real.sqrt (beta^2+1) ≤ 123111/50000 := by
    have h := Real.sqrt_le_sqrt
      (show beta^2+1 ≤ ((123111:ℝ)/50000)^2 by norm_num [beta])
    simpa only [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 123111/50000)] using h
  have hm := mul_le_mul CandidateWestTail.ceiling_bounds.1 hr (Real.sqrt_nonneg _)
    (by norm_num [CandidateWestTail.radiusBound])
  rw [neg_one_sq,abs_neg,abs_one,abs_of_pos (show (0:ℝ) < beta by norm_num [beta])] at h
  dsimp only [westUpper]
  linarith

lemma diagonal_support {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 0 ≤ q ∧ q ≤ Real.pi) :
    (delta+Real.sin q)*a+(Real.cos q-1)*b ≤ diagonalUpper q := by
  have hz : 0 ≤ delta := by norm_num [delta]
  have h := RadialChordSupport.support hc hz hq
  have hm := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.1
    (RadialChordSupport.majorant_nonnegative hz hq)
  dsimp [diagonalUpper]
  linarith

lemma south_support {a b r : ℝ} (hc : ContainedChart a |b|)
    (hr : 0 ≤ r ∧ r ≤ 2/3) :
    (gamma+Real.cos r)*a+Real.sin r*b ≤ southUpper r := by
  have hp := mul_nonneg (sub_nonneg.mpr hr.2)
    (show 0 ≤ 2/3+r by linarith [hr.1])
  have hcos : 7/9 ≤ Real.cos r := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := r)]
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hr.1
    (by linarith [hr.2,Real.pi_gt_d2])
  have hsinU := (Real.sin_le hr.1).trans hr.2
  have hU : 7/5 ≤ gamma+Real.cos r := by dsimp [gamma]; linarith
  have hV : |Real.sin r| ≤ (gamma+Real.cos r)/2 := by
    rw [abs_of_nonneg hsin]
    dsimp [gamma]
    linarith
  have h := soft_axial_support hc hU hV
  have hm := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.2.1
    (show 0 ≤ gamma+Real.cos r by linarith)
  dsimp [southUpper]
  linarith

lemma center_support {v s d cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 48/175 ≤ s ∧ s ≤ 12/25)
    (hd : 157/200 ≤ d ∧ d ≤ 163/175)
    (hx : cx ≤ CandidateWestTail.coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ CandidateWestTail.coreUpper) :
    ∃ upper : Bool, forceX v s d*cx+forceY v s d*cy ≤ centerUpper upper v s d := by
  have hp := mul_nonneg (sub_nonneg.mpr hv.2)
    (show 0 ≤ 2/3+v by linarith [hv.1])
  have hcv : 7/9 ≤ Real.cos v := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have hss := Real.sin_le (show 0 ≤ s by linarith [hs.1])
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show d ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hX : 0 ≤ forceX v s d := by
    dsimp [forceX,beta,gamma,delta]
    linarith [hs.2]
  have hx' := mul_le_mul_of_nonneg_left hx hX
  by_cases hY : 0 ≤ forceY v s d
  · refine ⟨true,?_⟩
    have hy' := mul_le_mul_of_nonneg_left hy.2 hY
    dsimp [centerUpper,face,CandidateWestTail.coreUpper] at *
    nlinarith only [hx',hy']
  · refine ⟨false,?_⟩
    have hy' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hY) hy.1
    dsimp [centerUpper,face]
    nlinarith only [hx',hy']

lemma value_le_defect (upper : Bool) {v s d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 48/175 ≤ s ∧ s ≤ 12/25)
    (hd : 157/200 ≤ d ∧ d ≤ 163/175) : value upper v s d ≤ defect upper v s d := by
  have width_formula {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
      angularWidth x=(Real.cos x+Real.sin x)/2 := by
    have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
    have ht := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
    simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg ht]
  have hW := width_formula (x := v) ⟨hv.1,by linarith [hv.2,Real.pi_gt_d2]⟩
  have hS := width_formula (x := s) (by constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have hD := width_formula (x := d) (by constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hR := width_formula (x := d-s) (by
    constructor <;> linarith [hd.1,hd.2,hs.1,hs.2,Real.pi_gt_d2])
  have hQ : (Real.cos (d+v)+Real.sin (d+v))/2 ≤ angularWidth (d+v) := by
    dsimp [angularWidth]
    linarith [le_abs_self (Real.cos (d+v)),le_abs_self (Real.sin (d+v))]
  have hid : defect upper v s d-value upper v s d =
      angularWidth (d+v)-(Real.cos (d+v)+Real.sin (d+v))/2 := by
    rw [value,westSlice,southSlice,transverse_identity]
    dsimp [defect,thresholdSum,westUpper,diagonalUpper,southUpper,centerUpper,
      constantTerm,westTerm,southTerm,diagonalTerm,chord,forceX,forceY,
      beta,gamma,delta,A,B,chordSin,chordCos,RadialChordSupport.majorant,
      CandidateWestTail.radiusBound,CandidateWestTail.rhoBound,CandidateWestTail.coreUpper]
    rw [hW,hS,hD,hR]
    ring
  linarith

/-- On the reflected domain the five separators of the reflected frame, with the
containment of W, D and S and the box of C, cannot all hold. -/
theorem scalar_impossible {v s d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hs : 48/175 ≤ s ∧ s ≤ 12/25) (horder : s ≤ v) (hv : v ≤ 2/3)
    (hsum : v+s ≤ 24/25) (hd : 157/200 ≤ d ∧ d ≤ 163/175)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart asouth |bsouth|)
    (hx : cx ≤ CandidateWestTail.coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ CandidateWestTail.coreUpper)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth s ≤ asouth-cx*Real.sin s+cy*Real.cos s)
    (hCD : 1/2+angularWidth d ≤ ad+cx*Real.cos d+cy*Real.sin d)
    (hWD : 1/2+angularWidth (d+v) ≤ ad*Real.sin (d+v)+bd*Real.cos (d+v)-bw)
    (hDS : 1/2+angularWidth (d-s) ≤ asouth*Real.cos (d-s)+bsouth*Real.sin (d-s)-bd) : False := by
  have hv0 : 0 ≤ v := by linarith [hs.1,horder]
  have htotal : thresholdSum v s d ≤
      (beta*aw-bw)+((delta+Real.sin (d+v))*ad+(Real.cos (d+v)-1)*bd)+
      ((gamma+Real.cos (d-s))*asouth+Real.sin (d-s)*bsouth)+
      forceX v s d*cx+forceY v s d*cy := by
    dsimp [thresholdSum,beta,gamma,delta,forceX,forceY]
    linear_combination (9/4)*hCW+(3/4)*hCS+(9/20)*hCD+hWD+hDS
  have hq : 0 ≤ d+v ∧ d+v ≤ Real.pi := by
    constructor <;> linarith [hv0,hv,hd.1,hd.2,Real.pi_gt_d2]
  have hr : 0 ≤ d-s ∧ d-s ≤ 2/3 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2]
  have hw := west_support hW
  have hdiag := diagonal_support hD hq
  have hsouth := south_support hS hr
  obtain ⟨upper,hcenter⟩ := center_support ⟨hv0,hv⟩ hs hd hx hy
  have hn : defect upper v s d ≤ 0 := by
    dsimp [defect]
    linarith only [htotal,hw,hdiag,hsouth,hcenter]
  have hp := (positive upper hs horder hv hsum hd).trans_le
    (value_le_defect upper ⟨hv0,hv⟩ hs hd)
  linarith

end SquaresInCircles.Six.Analytic.ReflectedOwnWings
