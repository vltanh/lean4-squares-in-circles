module

public import SquaresInCircles.Eight.Words.Second.Mixed.CoreCorner
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetGeometry
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetLabels

/-!
# Eight squares: the three derivatives in the negative target-contact proof

These are the diagonal function `H`, the side-boundary function `boundary` and the core-corner
function `cornerCost`, with their derivatives.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target
open CommonQuarter CorePairGeometry Arithmetic

def H (r : Row) (x : ℝ) : ℝ :=
  -x+c r+g r*CoreAngleEndpoint.diagonal+(F r).outer (diagonal x)
def H₁ (r : Row) (x : ℝ) : ℝ := -1+(F r).d1 (diagonal x)*speed x
def H₂ (r : Row) (x : ℝ) : ℝ :=
  (F r).d2 (diagonal x)*(speed x)^2+(F r).d1 (diagonal x)*(1/2-diagonal x)
def H₃ (r : Row) (x : ℝ) : ℝ :=
  speed x*((F r).d3 (diagonal x)*(speed x)^2+
    3*(F r).d2 (diagonal x)*(1/2-diagonal x)-(F r).d1 (diagonal x))

lemma diagonal_domain {x : ℝ} (hx : x∈angles) : diagonal x∈Labels.domain :=
  ⟨by linarith [(diagonal_bounds hx).1],(diagonal_bounds hx).2.le⟩

lemma H_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angles) : HasDerivAt (H r) (H₁ r x) x := by
  have hD := ((F r).outer_hasDerivAt (Labels.chart_domain (diagonal_domain hx))).comp x
    (diagonal_hasDerivAt x)
  have h : HasDerivAt (H r) _ x :=
    (((hasDerivAt_id' (x:=x)).fun_neg.add_const (c r)).add_const
      (g r*CoreAngleEndpoint.diagonal)).fun_add hD
  exact h.congr_deriv (by simp only [H₁])

lemma H₁_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angles) : HasDerivAt (H₁ r) (H₂ r x) x := by
  have h : HasDerivAt (H₁ r) _ x :=
    ((((F r).d1_hasDerivAt (Labels.chart_domain (diagonal_domain hx))).comp x
      (diagonal_hasDerivAt x)).fun_mul (speed_hasDerivAt x)).const_add (-1)
  exact h.congr_deriv (by simp only [H₂,Function.comp_apply]; ring)

lemma H₂_hasDerivAt (r : Row) {x : ℝ} (hx : x∈angles) : HasDerivAt (H₂ r) (H₃ r x) x := by
  have hd := Labels.chart_domain (diagonal_domain hx)
  have h : HasDerivAt (H₂ r) _ x :=
    ((((F r).d2_hasDerivAt hd).comp x (diagonal_hasDerivAt x)).fun_mul
      ((speed_hasDerivAt x).fun_pow 2)).fun_add
        ((((F r).d1_hasDerivAt hd).comp x (diagonal_hasDerivAt x)).fun_mul
          ((diagonal_hasDerivAt x).const_sub (1/2)))
  exact h.congr_deriv (by
    simp only [H₃,Function.comp_apply,Nat.reduceSub,pow_one,Nat.cast_ofNat]
    ring)

def inverse (a B x : ℝ) : ℝ :=
  1/2+(1/2-B)/Real.cos x+(a+1/2)*Real.sin x/Real.cos x
def boundary (r : Row) (a B x : ℝ) : ℝ :=
  -x+c r+g r*inverse a B x+(F r).outer B
def boundary₁ (r : Row) (a B x : ℝ) : ℝ :=
  ((Real.sin x)^2-g r*(B-1/2)*Real.sin x+g r*(a+1/2)-1)/(Real.cos x)^2

lemma inverse_hasDerivAt (a B : ℝ) {x : ℝ} (hx : x∈angles) :
    HasDerivAt (inverse a B)
      (((1/2-B)*Real.sin x+(a+1/2))/(Real.cos x)^2) x := by
  have hc : Real.cos x≠0 := (lt_trans (by norm_num) (cosine_bounds hx).1).ne'
  have hd := (((hasDerivAt_const x (1/2-B)).div (Real.hasDerivAt_cos x) hc).const_add (1/2)).add
      (((Real.hasDerivAt_sin x).const_mul (a+1/2)).div (Real.hasDerivAt_cos x) hc)
  convert hd using 1
  · rfl
  · field_simp [hc]
    have he : (a+1/2)*((Real.sin x)^2+(Real.cos x)^2)=a+1/2 := by
      rw [Real.sin_sq_add_cos_sq,mul_one]
    nlinarith [he]

lemma boundary_hasDerivAt (r : Row) (a B : ℝ) {x : ℝ} (hx : x∈angles) :
    HasDerivAt (boundary r a B) (boundary₁ r a B x) x := by
  have hc : Real.cos x≠0 := (lt_trans (by norm_num) (cosine_bounds hx).1).ne'
  have h : HasDerivAt (boundary r a B) _ x :=
    ((((hasDerivAt_id' (x:=x)).fun_neg.add_const (c r)).fun_add
      ((inverse_hasDerivAt a B hx).const_mul (g r))).add_const ((F r).outer B))
  refine h.congr_deriv ?_
  simp only [boundary₁]
  field_simp
  linear_combination (-2:ℝ)*Real.sin_sq_add_cos_sq x

lemma inverse_contact {a b x : ℝ} (hx : x∈angles) :
    inverse a (contact a b x) x=b := by
  have hc : Real.cos x≠0 := (lt_trans (by norm_num) (cosine_bounds hx).1).ne'
  dsimp [inverse,contact]
  field_simp [hc]
  ring

lemma boundary_zero (r : Row) (a B : ℝ) : boundary r a B 0=aligned r B := by
  simp only [boundary,inverse,Real.cos_zero,Real.sin_zero]
  dsimp [aligned]
  ring

def cornerB (x b : ℝ) : ℝ := contact (MixedCorner.a b) b x
def cornerSpeed (x b : ℝ) : ℝ := Real.cos x+MixedCorner.w b*Real.sin x
def cornerCurvature (b : ℝ) : ℝ := (1+(MixedCorner.w b)^2)/MixedCorner.z b
def cornerCost (r : Row) (x b : ℝ) : ℝ := -x+c r+g r*b+(F r).outer (cornerB x b)
def corner₁ (r : Row) (x b : ℝ) : ℝ :=
  g r-(F r).d1 (cornerB x b)*cornerSpeed x b
def corner₂ (r : Row) (x b : ℝ) : ℝ :=
  (F r).d2 (cornerB x b)*(cornerSpeed x b)^2-
    (F r).d1 (cornerB x b)*cornerCurvature b*Real.sin x

lemma cornerB_hasDerivAt (x : ℝ) {b : ℝ} (hb : b∈MixedCorner.domain) :
    HasDerivAt (cornerB x) (-cornerSpeed x b) b := by
  have h : HasDerivAt (cornerB x) _ b :=
    ((((hasDerivAt_id' (x:=b)).const_sub (1/2)).mul_const (Real.cos x)).const_add
      (1/2)).fun_add (((MixedCorner.a_hasDerivAt hb).add_const (1/2)).mul_const (Real.sin x))
  exact h.congr_deriv (by simp only [cornerSpeed]; ring)

lemma cornerSpeed_hasDerivAt (x : ℝ) {b : ℝ} (hb : b∈MixedCorner.domain) :
    HasDerivAt (cornerSpeed x) (cornerCurvature b*Real.sin x) b :=
  ((MixedCorner.w_hasDerivAt hb).mul_const (Real.sin x)).const_add (Real.cos x)

lemma cornerCost_hasDerivAt (r : Row) (x : ℝ) {b : ℝ} (hb : b∈MixedCorner.domain)
    (hB : cornerB x b∈Labels.domain) : HasDerivAt (cornerCost r x) (corner₁ r x b) b := by
  have h : HasDerivAt (cornerCost r x) _ b :=
    (((hasDerivAt_id' (x:=b)).const_mul (g r)).const_add (-x+c r)).fun_add
      (((F r).outer_hasDerivAt (Labels.chart_domain hB)).comp b (cornerB_hasDerivAt x hb))
  exact h.congr_deriv (by simp only [corner₁]; ring)

lemma corner₁_hasDerivAt (r : Row) (x : ℝ) {b : ℝ} (hb : b∈MixedCorner.domain)
    (hB : cornerB x b∈Labels.domain) : HasDerivAt (corner₁ r x) (corner₂ r x b) b := by
  have h : HasDerivAt (corner₁ r x) _ b :=
    ((((F r).d1_hasDerivAt (Labels.chart_domain hB)).comp b
      (cornerB_hasDerivAt x hb)).fun_mul (cornerSpeed_hasDerivAt x hb)).const_sub (g r)
  exact h.congr_deriv (by simp only [corner₂,Function.comp_apply]; ring)

lemma cornerSpeed_positive {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain) :
    0<cornerSpeed x b := by
  have hp := mul_nonneg (MixedCorner.w_bounds hb).1 (positive_trig (angle_subset hx)).2.2.1
  dsimp [cornerSpeed]
  linarith [(cosine_bounds hx).1]

lemma cornerB_antitone {x : ℝ} (hx : x∈angles) : AntitoneOn (cornerB x) MixedCorner.domain :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (cornerB_hasDerivAt x hb).continuousAt.continuousWithinAt)
    (fun b hb => cornerB_hasDerivAt x (Ioo_subset_Icc_self hb))
    (fun b hb => neg_nonpos.mpr (cornerSpeed_positive hx (Ioo_subset_Icc_self hb)).le)

lemma cornerB_lower {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain) :
    1-CoreAngleEndpoint.diagonal≤cornerB x b := by
  have hh := contact_lower (MixedCorner.state hb) hx
  dsimp [cornerB]
  linarith [hb.2]

lemma cornerB_upper {x b : ℝ} (hx : x∈angles) (hb : b∈MixedCorner.domain) :
    cornerB x b≤1/2+(13/12)*Real.sin x := by
  have hc := MixedCorner.chart_bounds hb
  have hs := (positive_trig (angle_subset hx)).2.2.1
  have hp := mul_nonpos_of_nonpos_of_nonneg (by linarith [hb.1] : 1/2-b≤0)
    (by linarith [(cosine_bounds hx).1] : 0≤Real.cos x)
  have ha := mul_le_mul_of_nonneg_right (show MixedCorner.a b+1/2≤13/12 by
    dsimp [MixedCorner.a]; linarith [hc.2.1]) hs
  dsimp [cornerB,contact]
  linarith

lemma cornerCurvature_bound {x b : ℝ} (_hx : x∈angles) (hb : b∈MixedCorner.domain) :
    12*(cornerSpeed x b)^2≤cornerCurvature b := by
  have hz := MixedCorner.z_positive hb
  have hu := (MixedCorner.chart_bounds hb).2.1
  have hn : (cornerSpeed x b)^2≤1+(MixedCorner.w b)^2 := by
    have he := Real.sin_sq_add_cos_sq x
    dsimp [cornerSpeed]
    nlinarith [sq_nonneg (Real.sin x-MixedCorner.w b*Real.cos x)]
  have hk : 12*(1+(MixedCorner.w b)^2)≤cornerCurvature b := by
    apply (le_div_iff₀ hz).2
    nlinarith [sq_nonneg (MixedCorner.w b)]
  linarith

lemma cornerB_join (x : ℝ) : cornerB x (1/2)=1/2+(13/12)*Real.sin x := by
  rw [cornerB,MixedCorner.join]
  dsimp [contact]
  ring

lemma cornerB_diagonal (x : ℝ) : cornerB x CoreAngleEndpoint.diagonal=diagonal x := by
  rw [cornerB,MixedCorner.diagonal]
  rfl

lemma cornerCost_diagonal (r : Row) (x : ℝ) : cornerCost r x CoreAngleEndpoint.diagonal=H r x := by
  rw [cornerCost,cornerB_diagonal]
  rfl

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target
