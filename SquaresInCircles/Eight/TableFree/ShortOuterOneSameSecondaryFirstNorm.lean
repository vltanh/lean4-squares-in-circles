module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameSecondaryNegativeLater

/-!
# The single multiplier for the first negative secondary owner

Uncompiled transcription of Section 5, equations (19)--(20), of
`HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md`.
The multiplier is exactly 0.94. The source endpoint support and the
full-circle target support retain the actual original weak separator.
The norm decreases on the whole angle interval and its exact curvature
identity makes the support derivative decreasing.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.FirstNorm
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport

def weight : ℝ := 47/50
abbrev radius := RoleFour.radius
def normA : ℝ := (p 0)^2+(q 0)^2+weight^2
def normB : ℝ := -2*weight*p 0
def normC : ℝ := -2*weight*q 0
def N (x : ℝ) : ℝ := CircularNorm.norm normA normB normC x
def value (x : ℝ) : ℝ :=
  Real.pi/2-x+c 0-P 0*outerAxial+(weight-p 0+q 0)/2+weight*Real.cos x-radius*N x
def first (x : ℝ) : ℝ :=
  -1-weight*Real.sin x-radius*CircularNorm.d1 normA normB normC x
def second (x : ℝ) : ℝ :=
  -weight*Real.cos x-radius*CircularNorm.d2 normA normB normC x

lemma energy_identity (x : ℝ) : CircularNorm.energy normA normB normC x=
    (p 0-weight*Real.cos x)^2+(-q 0+weight*Real.sin x)^2 := by
  dsimp [CircularNorm.energy,normA,normB,normC]
  linear_combination -weight^2*(Real.sin_sq_add_cos_sq x)

lemma energy_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<CircularNorm.energy normA normB normC x := by
  have hX : p 0-weight*Real.cos x<0 := by
    norm_num [p,weight]
    linarith [(positive_trig hx).1]
  rw [energy_identity]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_neg hX) (sq_nonneg _)

lemma norm_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<N x :=
  CircularNorm.norm_pos (energy_positive hx)

lemma norm_sq {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N x)^2=(p 0)^2+(q 0)^2+weight^2-2*weight*(p 0*Real.cos x+q 0*Real.sin x) := by
  have hh := CircularNorm.norm_sq (energy_positive hx).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy,normA,normB,normC] <;> ring

lemma norm_slope_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    CircularNorm.d1 normA normB normC x<0 := by
  have ht := positive_trig hx
  have hs : CircularNorm.slope normB normC x<0 := by
    norm_num [CircularNorm.slope,normB,normC,weight,p,q]
    linarith [ht.1,ht.2.2.2.1]
  exact div_neg_of_neg_of_pos hs (mul_pos (by norm_num) (norm_positive hx))

lemma norm_antitone : AntitoneOn N (Icc 0 (7/10)) := antiOn_of_hasDeriv_nonpos
  (fun x hx => (CircularNorm.norm_hasDerivAt (energy_positive hx)).continuousAt.continuousWithinAt)
  (fun x hx => CircularNorm.norm_hasDerivAt (energy_positive (Ioo_subset_Icc_self hx)))
  (fun x hx => (norm_slope_negative (Ioo_subset_Icc_self hx)).le)

lemma norm_upper {x : ℝ} (hx : x∈Icc 0 (7/10)) : N x<(153/125:ℝ) := by
  have h0 : (0:ℝ)∈Icc 0 (7/10) := by norm_num
  have hsq := norm_sq h0
  have hn0 : N 0<(153/125:ℝ) := by
    norm_num [p,q,weight] at hsq
    nlinarith [norm_positive h0]
  exact (norm_antitone h0 hx hx.1).trans_lt hn0

lemma value_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt value (first x) x := by
  convert (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c 0-P 0*outerAxial+(weight-p 0+q 0)/2)).add
      ((Real.hasDerivAt_cos x).const_mul weight)).sub
        ((CircularNorm.norm_hasDerivAt (energy_positive hx)).const_mul radius)) using 1 <;>
    dsimp [value,first,N] <;> ring

lemma first_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt first (second x) x := by
  convert ((((Real.hasDerivAt_sin x).const_mul weight).neg).const_add (-1)).sub
    ((CircularNorm.d1_hasDerivAt (energy_positive hx)).const_mul radius) using 1 <;>
    dsimp [first,second] <;> ring

lemma curvature {x : ℝ} (hx : x∈Icc 0 (7/10)) : second x<-(11/100:ℝ) := by
  have hnorm := CircularNorm.curvature_lower (energy_positive hx)
    (show normB^2+normC^2≤normA^2 by norm_num [normA,normB,normC,weight,p,q])
  have hmul := mul_le_mul_of_nonneg_left hnorm RoleFour.radius_positive.le
  have hrN : radius*N x<(1978788/1000000:ℝ)*(153/125) :=
    (mul_le_mul_of_nonneg_right RoleFour.radius_upper.le (norm_positive hx).le).trans_lt
      (mul_lt_mul_of_pos_left (norm_upper hx) (by norm_num))
  have hmul' : -radius*N x/4≤radius*CircularNorm.d2 normA normB normC x := by
    convert hmul using 1 <;> ring
  have hc := (positive_trig hx).1
  dsimp [second,weight]
  linarith

lemma first_antitone : AntitoneOn first (Icc 0 (7/10)) := antiOn_of_hasDeriv_nonpos
  (fun x hx => (first_hasDerivAt hx).continuousAt.continuousWithinAt)
  (fun x hx => first_hasDerivAt (Ioo_subset_Icc_self hx))
  (fun x hx => by linarith [curvature (Ioo_subset_Icc_self hx)])

lemma source_endpoint_gap : (2/625:ℝ)<(-P 0+t 0-weight)*outerDiagonal+P 0*outerAxial := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  have ha := ShortOuterZero.fine_axial_bounds
  norm_num [P,t,weight]
  linarith

lemma source_support {a b : ℝ} (hs : OuterState a b) :
    -P 0*outerAxial≤-P 0*a+(t 0-weight)*b := by
  apply outer_concave_lower hs (show 0≤-P 0 by norm_num [P]) le_rfl
  linarith [source_endpoint_gap]

lemma norm_coefficients (x : ℝ) :
    Real.sqrt ((p 0-weight*Real.cos x)^2+(-q 0+weight*Real.sin x)^2)=N x := by
  unfold N CircularNorm.norm
  rw [energy_identity]

theorem original_support {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    value x≤Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
  have hmargin := mul_le_mul_of_nonneg_left hm (show 0≤weight by norm_num [weight])
  have hsource := source_support hs
  have htarget := ShortOuterZero.Opposite.Positive.Cap.full_circle_lower
    (X:=p 0-weight*Real.cos x) (Y:=-q 0+weight*Real.sin x) ht
  rw [norm_coefficients] at htarget
  dsimp [value]
  nlinarith only [hmargin,hsource,htarget]

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.FirstNorm
