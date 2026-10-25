module

public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupportWide
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetGeometry
public import SquaresInCircles.Eight.Words.Second.Outer.LBounds

/-!
# Eight squares: exact expression enclosures at the reference points

The sine and cosine enclosures (`sinBox`, `cosBox`) are alternating Taylor bounds. Radicals are
bounded by the positive-root refinement used throughout the proof. Every box keeps its real
expression in its type.
-/

section
/-!
## The analytic continuation used by the written diagonal proof

The label formulas and their exact derivatives
are valid through coordinate `.9`, just beyond the physical diagonal.
The following signs are proved on that whole interval from the circle
radical.  They are the derivative signs used in the written P and L
negative-target arguments; no physical state is added to the cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.Labels
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def domain : Set ℝ := Icc 0 (9/10)

lemma chart_domain {B : ℝ} (hB : B∈domain) : B∈Icc 0 outerAxial :=
  ⟨hB.1,by linarith [hB.2,outer_endpoint_bounds.1]⟩

lemma coordinates {B : ℝ} (hB : B∈domain) :
    0<U B ∧ (1/2:ℝ)≤W B ∧ W B≤7/5 ∧ (39/20:ℝ)<(U B)^2 := by
  have hc := UW_circle (chart_domain hB)
  have hw : W B∈Icc (1/2:ℝ) (7/5) := by
    dsimp [W]
    constructor <;> linarith [hB.1,hB.2]
  have hs := pow_le_pow_left₀ (by linarith [hw.1] : 0≤W B) hw.2 2
  exact ⟨U_positive (chart_domain hB),hw.1,hw.2,by norm_num [Q0] at hc; linarith⟩

lemma ratio_signs {B : ℝ} (hB : B∈domain) :
    0<ratio B ∧ 0<ratioD B ∧ 0<ratioDD B ∧ 0<ratioDDD B ∧ 0<ratioDDDD B := by
  have hc := coordinates hB
  have hu : 0<U B := hc.1
  have hw : 0<W B := by linarith [hc.2.1]
  have hs : 0<(U B)^2 := sq_pos_of_pos hu
  change 0<W B/U B ∧ 0<Q0/(U B)^3 ∧ 0<3*Q0*W B/(U B)^5 ∧
    0<3*Q0*((U B)^2+5*(W B)^2)/(U B)^7 ∧
    0<15*Q0*W B*(3*(U B)^2+7*(W B)^2)/(U B)^9
  refine ⟨?_,?_,?_,?_,?_⟩ <;> norm_num [Q0] <;> positivity

lemma P_second_positive {B : ℝ} (hB : B∈domain) : 0<PLabel.d2 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.1.le
  norm_num [RoleLabel.d2,PLabel]
  nlinarith [hh.1]

lemma P_third_positive {B : ℝ} (hB : B∈domain) : 0<PLabel.d3 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.1.le
  norm_num [RoleLabel.d3,PLabel]
  nlinarith [hh.2.1]

lemma P_fourth_positive {B : ℝ} (hB : B∈domain) : 0<PLabel.d4 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.2.1.le
  norm_num [RoleLabel.d4,PLabel]
  nlinarith [hh.2.2.1]

lemma P_fifth_positive {B : ℝ} (hB : B∈domain) : 0<PLabel.d5 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.2.2.le
  norm_num [RoleLabel.d5,PLabel]
  nlinarith [hh.2.2.2.1]

lemma P_first_monotone : MonotoneOn PLabel.d1 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (PLabel.d1_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun _ hB => PLabel.d1_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun _ hB => (P_second_positive (Ioo_subset_Icc_self hB)).le)

lemma P_second_monotone : MonotoneOn PLabel.d2 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (PLabel.d2_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun _ hB => PLabel.d2_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun _ hB => (P_third_positive (Ioo_subset_Icc_self hB)).le)

lemma P_third_monotone : MonotoneOn PLabel.d3 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (PLabel.d3_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun _ hB => PLabel.d3_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun _ hB => (P_fourth_positive (Ioo_subset_Icc_self hB)).le)

lemma L_third_positive {B : ℝ} (hB : B∈domain) : 0<LLabel.d3 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.1.le
  norm_num [RoleLabel.d3,LLabel]
  nlinarith [hh.2.1]

lemma L_fourth_positive {B : ℝ} (hB : B∈domain) : 0<LLabel.d4 B := by
  have hh := ratio_signs hB
  have hp := mul_nonneg hB.1 hh.2.2.2.1.le
  norm_num [RoleLabel.d4,LLabel]
  nlinarith [hh.2.2.1]

lemma L_second_monotone : MonotoneOn LLabel.d2 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (LLabel.d2_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun _ hB => LLabel.d2_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun _ hB => (L_third_positive (Ioo_subset_Icc_self hB)).le)

lemma L_third_monotone : MonotoneOn LLabel.d3 domain :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (LLabel.d3_hasDerivAt (chart_domain hB)).continuousAt.continuousWithinAt)
    (fun _ hB => LLabel.d3_hasDerivAt (chart_domain (Ioo_subset_Icc_self hB)))
    (fun _ hB => (L_fourth_positive (Ioo_subset_Icc_self hB)).le)

lemma L_fifth_identity {B : ℝ} (hB : B∈domain) :
    LLabel.d5 B=LLabel.d3 B*(5/(U B)^2+35*(W B)^2/(U B)^4)-
      (15*(94721/50000)*Q0*W B)/(U B)^7 := by
  have hp := (coordinates hB).1
  dsimp [RoleLabel.d5,RoleLabel.d3,LLabel,ratioD,ratioDD,ratioDDD,ratioDDDD,U,W]
  field_simp [show arc B+1/2≠0 from hp.ne']
  ring

lemma L_fifth_upper {B : ℝ} (hB : B∈domain) : LLabel.d5 B<21*LLabel.d3 B := by
  have hc := coordinates hB
  have hu2 := sq_pos_of_pos hc.1
  have hu4 := pow_pos hc.1 4
  have hW2 : (W B)^2≤(7/5:ℝ)^2 :=
    pow_le_pow_left₀ (by linarith [hc.2.1]) hc.2.2.1 2
  have hU4 : (39/20:ℝ)^2≤(U B)^4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤39/20) hc.2.2.2.le 2
    nlinarith
  have hfirst : 5/(U B)^2≤(100/39:ℝ) := (div_le_iff₀ hu2).2 (by nlinarith [hc.2.2.2])
  have hsecond : 35*(W B)^2/(U B)^4≤(27440/1521:ℝ) :=
    (div_le_iff₀ hu4).2 (by nlinarith)
  have hsum : 5/(U B)^2+35*(W B)^2/(U B)^4<21 := by linarith
  have hprod := mul_lt_mul_of_pos_left hsum (L_third_positive hB)
  have hlast : 0<(15*(94721/50000)*Q0*W B)/(U B)^7 := by
    have hw : 0<W B := by linarith [hc.2.1]
    have hQ : (0:ℝ)<Q0 := by norm_num [Q0]
    exact div_pos (mul_pos (mul_pos (by norm_num) hQ) hw) (pow_pos hc.1 7)
  rw [L_fifth_identity hB]
  linarith

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.Labels
end
end
end

section
/-!
## The three derivatives in the negative target-contact proof

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
    (fun _ hb => (cornerB_hasDerivAt x hb).continuousAt.continuousWithinAt)
    (fun _ hb => cornerB_hasDerivAt x (Ioo_subset_Icc_self hb))
    (fun _ hb => neg_nonpos.mpr (cornerSpeed_positive hx (Ioo_subset_Icc_self hb)).le)

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.ReferenceAlgebra
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra

def coreBox : Interval CoreAngleEndpoint.diagonal :=
  Interval.of_bounds ⟨core_diagonal_bounds.1.le,core_diagonal_bounds.2.le⟩
def outerBox : Interval outerDiagonal :=
  Interval.of_bounds ⟨ShortMixedZero.fine_diagonal_bounds.1.le,
    ShortMixedZero.fine_diagonal_bounds.2.le⟩
def sinBox (x : ℝ) (hx : 0≤x) : Interval (Real.sin x) :=
  Interval.of_bounds ⟨HighOrderTaylor.S15_le_sin hx,HighOrderTaylor.sin_le_S13 hx⟩
def cosBox (x : ℝ) (hx : 0≤x) : Interval (Real.cos x) :=
  Interval.of_bounds ⟨HighOrderTaylor.C14_le_cos hx,HighOrderTaylor.cos_le_C12 hx⟩

def diagonalBox (x : ℝ) (hx : 0≤x) : Interval (diagonal x) :=
  ((Interval.point (1/2)).add (((Interval.point (1/2)).sub coreBox).mul (cosBox x hx))).add ((coreBox.add (Interval.point (1/2))).mul (sinBox x hx))
def speedBox (x : ℝ) (hx : 0≤x) : Interval (speed x) :=
  ((coreBox.sub (Interval.point (1/2))).mul (sinBox x hx)).add ((coreBox.add (Interval.point (1/2))).mul (cosBox x hx))

def HBox (r : Row) (x : ℝ) (hx : 0≤x) (X : Interval (U (diagonal x))) : Interval (H r x) :=
  ((((Interval.point (-x)).add (Interval.point (c r))).add ((Interval.point (g r)).mul coreBox)).add (labelBox (F r) (diagonalBox x hx) X))
def H₁Box (r : Row) (x : ℝ) (hx : 0≤x) (X : Interval (U (diagonal x)))
    (hX : 0<X.lo) : Interval (H₁ r x) :=
  (Interval.point (-1)).add ((firstBox (F r) (diagonalBox x hx) X hX).mul (speedBox x hx))
def H₂Box (r : Row) (x : ℝ) (hx : 0≤x) (X : Interval (U (diagonal x)))
    (hX : 0<X.lo) : Interval (H₂ r x) :=
  ((secondBox (F r) (diagonalBox x hx) X hX).mul (speedBox x hx).square).add ((firstBox (F r) (diagonalBox x hx) X hX).mul ((Interval.point (1/2)).sub (diagonalBox x hx)))

def ratioDDDBox {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (ratioDDD y) := by
  let V := Y.add (Interval.point (1/2))
  let N := (Interval.point (3*Q0)).mul (X.square.add ((Interval.point 5).mul V.square))
  let D := X.cube.mul (X.square.mul X.square)
  have hD : 0<D.lo := Interval.mul_lo_pos (Interval.cube_lo_pos hX)
    (Interval.mul_lo_pos (Interval.square_lo_pos hX) (Interval.square_lo_pos hX))
  convert N.div D hD using 1
  dsimp [ratioDDD,U,N,D,V]
  congr 1
  ring

def fourthBox (L : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (L.d4 y) :=
  (((Interval.point (-4*L.s)).mul (ratioDDBox Y X hX)).sub
    (((Interval.point L.p).add ((Interval.point L.s).mul Y)).mul (ratioDDDBox Y X hX)))

def inverseBox {a B x : ℝ} (A : Interval a) (Y : Interval B) (S : Interval (Real.sin x))
    (C : Interval (Real.cos x)) (hC : 0<C.lo) : Interval (inverse a B x) :=
  ((Interval.point (1/2)).add (((Interval.point (1/2)).sub Y).div C hC)).add (((A.add (Interval.point (1/2))).mul S).div C hC)

def outerLabelBox (r : Row) : Interval ((F r).outer outerDiagonal) := by
  have he : U outerDiagonal=outerDiagonal+1/2 := by
    rw [U,ShortOuterOne.SameContact.arc_diagonal]
  let X : Interval (U outerDiagonal) := by rw [he]; exact outerBox.add (Interval.point (1/2))
  exact labelBox (F r) outerBox X

def boundaryBox (r : Row) {a x : ℝ} (A : Interval a) (hx : 0≤x)
    (hC : 0<(cosBox x hx).lo) : Interval (boundary r a outerDiagonal x) :=
  ((((Interval.point (-x)).add (Interval.point (c r))).add
    ((Interval.point (g r)).mul (inverseBox A outerBox (sinBox x hx) (cosBox x hx) hC))).add (outerLabelBox r))

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.ReferenceAlgebra
end
end
end
