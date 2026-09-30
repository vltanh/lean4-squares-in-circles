module
public import SquaresInCircles.Six.Analytic.RadialChordSupport
public import SquaresInCircles.Six.Analytic.SoftAxialSupport

@[expose] public section

/-!
# A curvature envelope for the west-dominant chord

The CD weight is 9/20 and the two secondary weights are equal. The analytic
radial-chord majorant leaves H(q)=sin q-L sin(q/2)-M cos(q/2).
Taylor inequalities give H''<=p(q), where p is the explicit convex quintic
below. Its endpoint chords imply the single envelope
  H''(q) <= 3/40-(3/10)*min(q,1),  1/2<=q<=3/2.
The two pieces are analytic curvature comparisons, not a searched angle cover.
They will combine with q+r>=1 in the west-dominant geometry.
Compilation remains unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthWestDominant

def chordSin : ℝ := 27701483/8000000
def chordCos : ℝ := 75987/100000

def chord (q : ℝ) : ℝ :=
  Real.sin q-chordSin*Real.sin (q/2)-chordCos*Real.cos (q/2)
def chordFirst (q : ℝ) : ℝ :=
  Real.cos q-(chordSin/2)*Real.cos (q/2)+(chordCos/2)*Real.sin (q/2)
def chordSecond (q : ℝ) : ℝ :=
  -Real.sin q+(chordSin/4)*Real.sin (q/2)+(chordCos/4)*Real.cos (q/2)

lemma chord_hasDeriv (q : ℝ) : HasDerivAt chord (chordFirst q) q := by
  convert (((Real.hasDerivAt_sin q).sub
    ((((hasDerivAt_id q).div_const 2).sin).const_mul chordSin)).sub
    ((((hasDerivAt_id q).div_const 2).cos).const_mul chordCos)) using 1 <;>
    dsimp [chord,chordFirst] <;> ring

lemma chord_first_hasDeriv (q : ℝ) : HasDerivAt chordFirst (chordSecond q) q := by
  convert (((Real.hasDerivAt_cos q).sub
    ((((hasDerivAt_id q).div_const 2).cos).const_mul (chordSin/2))).add
    ((((hasDerivAt_id q).div_const 2).sin).const_mul (chordCos/2))) using 1 <;>
    dsimp [chordFirst,chordSecond] <;> ring

private def p (q : ℝ) : ℝ :=
  19/100-(567/1000)*q-(23/1000)*q^2+(149/1000)*q^3+
    (1/2000)*q^4-(19/2500)*q^5
private def pFirst (q : ℝ) : ℝ :=
  -567/1000-(23/500)*q+(447/1000)*q^2+(1/500)*q^3-(19/500)*q^4
private def pSecond (q : ℝ) : ℝ :=
  -23/500+(447/500)*q+(3/500)*q^2-(19/125)*q^3

private lemma polynomial_upper {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 3/2) :
    chordSecond q ≤ p q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hl := Seven.sin_lower_seven hq0
  have hu := Seven.sin_upper_five (x := q/2) (by linarith)
  have hc := Seven.cos_upper_four (x := q/2) (by linarith)
  have hsq := mul_nonneg (sub_nonneg.mpr hq.2)
    (show 0 ≤ 3/2+q by linarith)
  have h7 := mul_nonneg (show 0 ≤ 9/4-q^2 by nlinarith only [hsq])
    (show 0 ≤ q^5 by positivity)
  have h3 : 0 ≤ q^3 := by positivity
  have h5 : 0 ≤ q^5 := by positivity
  dsimp [chordSecond,chordSin,chordCos,p]
  nlinarith only [hl,hu,hc,h7,hq0,h3,h5,sq_nonneg q,sq_nonneg (q^2)]

private lemma p_hasDeriv (q : ℝ) : HasDerivAt p (pFirst q) q := by
  convert ((((((hasDerivAt_id q).const_mul (-(567/1000))).const_add (19/100)).add
    (((hasDerivAt_id q).pow 2).const_mul (-(23/1000)))).add
    (((hasDerivAt_id q).pow 3).const_mul (149/1000))).add
    (((hasDerivAt_id q).pow 4).const_mul (1/2000))).add
    (((hasDerivAt_id q).pow 5).const_mul (-(19/2500))) using 1 <;>
    dsimp [p,pFirst] <;> ring

private lemma p_first_hasDeriv (q : ℝ) : HasDerivAt pFirst (pSecond q) q := by
  convert (((((hasDerivAt_id q).const_mul (-(23/500))).const_add (-(567/1000))).add
    (((hasDerivAt_id q).pow 2).const_mul (447/1000))).add
    (((hasDerivAt_id q).pow 3).const_mul (1/500))).add
    (((hasDerivAt_id q).pow 4).const_mul (-(19/500))) using 1 <;>
    dsimp [pFirst,pSecond] <;> ring

private lemma p_second_nonnegative {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 3/2) :
    0 ≤ pSecond q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hsq := mul_nonneg (sub_nonneg.mpr hq.2)
    (show 0 ≤ 3/2+q by linarith)
  have h3 := mul_nonneg (show 0 ≤ 9/4-q^2 by nlinarith only [hsq]) hq0
  dsimp [pSecond]
  nlinarith only [h3,hq.1,sq_nonneg q]

private lemma envelope_concave (A B : ℝ) {l u : ℝ}
    (hl : 1/2 ≤ l) (hu : u ≤ 3/2) :
    ConcaveOn ℝ (Set.Icc l u) (fun q => A+B*q-p q) := by
  have hf (q : ℝ) : HasDerivAt (fun q => A+B*q-p q) (B-pFirst q) q := by
    convert (((hasDerivAt_id q).const_mul B).const_add A).sub (p_hasDeriv q) using 1 <;> ring
  have hff (q : ℝ) : HasDerivAt (fun q => B-pFirst q) (-pSecond q) q := by
    simpa only [zero_sub] using (hasDerivAt_const q B).sub (p_first_hasDeriv q)
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
    (f' := fun q => B-pFirst q) (f'' := fun q => -pSecond q)
    (by dsimp [p]; fun_prop)
  · intro q _; exact (hf q).hasDerivWithinAt
  · intro q _; exact (hff q).hasDerivWithinAt
  · intro q hq
    have h := interior_subset hq
    exact neg_nonpos.mpr (p_second_nonnegative ⟨hl.trans h.1,h.2.trans hu⟩)

/-- A continuous two-piece affine envelope, proved from three rational endpoints. -/
lemma chord_second_envelope {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 3/2) :
    chordSecond q ≤ 3/40-(3/10)*min q 1 := by
  have hp := polynomial_upper hq
  by_cases hq1 : q ≤ 1
  · rw [min_eq_left hq1]
    have h := positive_on_concave_interval
      (envelope_concave (3/40) (-(3/10)) (l := 1/2) (u := 1) (by norm_num) (by norm_num))
      ⟨hq.1,hq1⟩ (by norm_num [p]) (by norm_num [p])
    linarith
  · rw [min_eq_right (le_of_not_ge hq1)]
    have h := positive_on_concave_interval
      (envelope_concave (-(9/40)) 0 (l := 1) (u := 3/2) (by norm_num) (by norm_num))
      ⟨le_of_not_ge hq1,hq.2⟩ (by norm_num [p]) (by norm_num [p])
    linarith

lemma chord_second_nonpositive {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 3/2) :
    chordSecond q ≤ 0 := by
  have h := chord_second_envelope hq
  have hm : (1:ℝ)/2 ≤ min q 1 := le_min hq.1 (by norm_num)
  linarith

lemma chord_concave : ConcaveOn ℝ (Set.Icc (1/2) (3/2)) chord := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) (3/2))
    (f' := chordFirst) (f'' := chordSecond) (by dsimp [chord]; fun_prop)
  · intro q _; exact (chord_hasDeriv q).hasDerivWithinAt
  · intro q _; exact (chord_first_hasDeriv q).hasDerivWithinAt
  · intro q hq; exact chord_second_nonpositive (interior_subset hq)

end SquaresInCircles.Six.Analytic.OwnSouthWestDominant
