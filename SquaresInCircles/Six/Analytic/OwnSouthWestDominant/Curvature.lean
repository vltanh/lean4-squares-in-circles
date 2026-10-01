import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Profile

/-!
# Coordinate concavity on the west-dominant geometric domain

For s<=v the relations r=d-s>=0 and q+r=2d+v-s>=1 are retained.
The chord and transverse curvature envelopes then give a uniform negative
bound for the d curvature. For the s curvature, the affine OWN-wing reserve
and s+r=d>=1/2 give another strictly negative constant. The v curvature is
already a negative harmonic plus the nonpositive chord curvature.

These are inequalities on whole intervals. No finite angular cover is used.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthWestDominant

private lemma small_trig {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 4/5) :
    0 ≤ Real.cos x ∧ 0 ≤ Real.sin x := by
  exact ⟨Real.cos_nonneg_of_mem_Icc
      (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [hx.1,hx.2,Real.pi_gt_d2]),
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1
      (by linarith [hx.2,Real.pi_gt_d2])⟩

lemma centerY_bounds (upper : Bool) :
    0 ≤ centerY upper ∧ centerY upper ≤ 5641/50000 := by
  cases upper <;> norm_num [centerY]

lemma west_term_nonnegative (upper : Bool) {v : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) : 0 ≤ westTerm upper v := by
  have h := small_trig ⟨hv.1,by linarith [hv.2]⟩
  have hy := (centerY_bounds upper).1
  have h1 := mul_nonneg (show (0:ℝ) ≤ 1/2+centerY upper by linarith) h.2
  dsimp [westTerm,westWeight,wingCos]
  linarith [h.1]

lemma south_term_affine_lower (upper : Bool) {s : ℝ}
    (hs : 0 ≤ s ∧ s ≤ 12/25) :
    southWeight*(wingCos+(49/100)*s) ≤ southTerm upper s := by
  have h := wing_affine_lower hs
  have hc := (small_trig ⟨hs.1,by linarith [hs.2]⟩).1
  have hcoef : 0 ≤ (1/2-centerY upper)-wingCos := by
    cases upper <;> norm_num [centerY,wingCos]
  have hp := mul_nonneg hcoef hc
  dsimp [southTerm,southWeight]
  nlinarith only [h,hp]

lemma diagonal_term_lower (upper : Bool) {d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    diagonalWeight*wingCos*(4/3) ≤ diagonalTerm upper d := by
  have h := diagonal_trig_lower hd
  have hs := (small_trig
    (show 0 ≤ d ∧ d ≤ 4/5 by constructor <;> linarith [hd.1,hd.2])).2
  have hcoef : 0 ≤ (1/2-centerY upper)-wingCos := by
    cases upper <;> norm_num [centerY,wingCos]
  have hp := mul_nonneg hcoef hs
  dsimp [diagonalTerm,diagonalWeight,wingCos] at *
  nlinarith only [h,hp]

lemma south_curvature_negative (upper : Bool) {s d : ℝ}
    (hs : 0 ≤ s ∧ s ≤ 12/25) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    -southTerm upper s+transverseSecond (d-s) < 0 := by
  have hr : 0 ≤ d-s ∧ d-s ≤ 4/5 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2]
  have hwing := south_term_affine_lower upper hs
  have htrans := transverse_second_upper hr
  have hdist : (49/100)*southWeight*(1/2) ≤
      (49/100)*southWeight*s+(2/5)*(d-s) := by
    dsimp [southWeight]
    linarith [hr.1,hd.1]
  dsimp [southWeight,wingCos,wingSin] at hwing htrans hdist
  linarith

lemma diagonal_curvature_negative (upper : Bool) {v s d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 12/25)
    (horder : s ≤ v) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    -diagonalTerm upper d+chordSecond (d+v)+transverseSecond (d-s) < 0 := by
  have hq : 1/2 ≤ d+v ∧ d+v ≤ 3/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2]
  have hr : 0 ≤ d-s ∧ d-s ≤ 4/5 := by
    constructor <;> linarith [hs.1,hs.2,hd.1,hd.2]
  have hsum : 1 ≤ (d+v)+(d-s) := by linarith [hd.1,horder]
  have hmin : 1 ≤ min (d+v) 1+(d-s) := by
    by_cases h : d+v ≤ 1
    · rw [min_eq_left h]
      exact hsum
    · rw [min_eq_right (le_of_not_ge h)]
      linarith [hr.1]
  have hweight : 3/10 ≤ (3/10)*min (d+v) 1+(2/5)*(d-s) := by
    linarith [hmin,hr.1]
  have hdiag := diagonal_term_lower upper hd
  have hchord := chord_second_envelope hq
  have htrans := transverse_second_upper hr
  dsimp [diagonalWeight,wingCos,wingSin] at hdiag htrans
  linarith

lemma west_slice_concave (upper : Bool) {d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (2/3)) (westSlice upper d) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (2/3))
    (f' := fun v => westFirst upper v+chordFirst (d+v))
    (f'' := fun v => -westTerm upper v+chordSecond (d+v))
    (fun x _ => (west_slice_hasDeriv upper d x).continuousAt.continuousWithinAt)
  · intro v _
    exact (west_slice_hasDeriv upper d v).hasDerivWithinAt
  · intro v _
    exact (west_slice_first_hasDeriv upper d v).hasDerivWithinAt
  · intro v hv
    have h := interior_subset hv
    have hq : 1/2 ≤ d+v ∧ d+v ≤ 3/2 := by
      constructor <;> linarith [h.1,h.2,hd.1,hd.2]
    linarith [west_term_nonnegative upper h,chord_second_nonpositive hq]

lemma south_slice_concave (upper : Bool) {d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (12/25)) (southSlice upper d) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (12/25))
    (f' := fun s => southFirst upper s-transverseFirst (d-s))
    (f'' := fun s => -southTerm upper s+transverseSecond (d-s))
    (fun x _ => (south_slice_hasDeriv upper d x).continuousAt.continuousWithinAt)
  · intro s _
    exact (south_slice_hasDeriv upper d s).hasDerivWithinAt
  · intro s _
    exact (south_slice_first_hasDeriv upper d s).hasDerivWithinAt
  · intro s hs
    exact (south_curvature_negative upper
      (interior_subset hs : s ∈ Set.Icc (0:ℝ) (12/25)) hd).le

lemma profile_diagonal_concave (upper : Bool) {v s : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 12/25) (horder : s ≤ v) :
    ConcaveOn ℝ (Set.Icc (1/2) (11/14)) (profile upper v s) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) (11/14))
    (f' := fun d => diagonalFirst upper d+chordFirst (d+v)+transverseFirst (d-s))
    (f'' := fun d => -diagonalTerm upper d+chordSecond (d+v)+transverseSecond (d-s))
    (fun x _ => (profile_diagonal_hasDeriv upper v s x).continuousAt.continuousWithinAt)
  · intro d _
    exact (profile_diagonal_hasDeriv upper v s d).hasDerivWithinAt
  · intro d _
    exact (profile_diagonal_first_hasDeriv upper v s d).hasDerivWithinAt
  · intro d hd
    exact (diagonal_curvature_negative upper hv hs horder
      (interior_subset hd : d ∈ Set.Icc (1/2:ℝ) (11/14))).le

end SquaresInCircles.Six.Analytic.OwnSouthWestDominant
