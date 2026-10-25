module

public import SquaresInCircles.Eight.Words.Common.JumpTwo
public import SquaresInCircles.Eight.Words.Second.WordData

/-!
# Eight squares: original opposite-sign outer zero-quarter contacts

The contacts `plus` and `minus` on the two angle halves, with their speeds, costs and
derivatives, serve both the asymmetric and the symmetric zero-quarter edges. Both angle halves
and both label orders keep the outer circle and its original weak separator.
-/

section
/-!
## One polynomial for the whole lower-angle support curvature

The squared comparison for the support second derivative is a single
quintic in sin x.  Translation by .645 leaves a positive polynomial
remainder over an explicit cubic lower expression.  The proof uses
only one polynomial identity and the full angle interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerSupport

open CommonQuarter CorePairGeometry Arithmetic

def g : ℝ := 83829/100000
def h : ℝ := 1061/1000
def polynomial (t : ℝ) : ℝ :=
  (1-t^2)*(g^2+h^2-2*g*h*t)^3-Q0*g^2*(g-h*t)^2*(h-g*t)^2
def lowerPolynomial (y : ℝ) : ℝ :=
  83/500+(1553/1000)*y+(623/125)*y^2+
    y^3*(2909/500-(691/500)*y-(5629/1000)*y^2)

lemma translated_identity (y : ℝ) :
    polynomial (129/200-y)-lowerPolynomial y=
      (341184490123782502305922594864415451/
        400000000000000000000000000000000000000:ℝ)+
      (40444622553420958760087623349/3125000000000000000000000000000000)*y+
      (3762689327888255944785062136869/5000000000000000000000000000000000)*y^2+
      (237507106019665678702061123/625000000000000000000000000000)*y^3+
      (225920263852122763120047611/250000000000000000000000000000)*y^4+
      (19852391049615193991/125000000000000000000000)*y^5 := by
  norm_num [polynomial,lowerPolynomial,g,h,Q0]
  ring

lemma translated_lower {y : ℝ} (hy : 0≤y) :
    lowerPolynomial y<polynomial (129/200-y) := by
  have he := translated_identity y
  have hp : 0<
      (341184490123782502305922594864415451/
        400000000000000000000000000000000000000:ℝ)+
      (40444622553420958760087623349/3125000000000000000000000000000000)*y+
      (3762689327888255944785062136869/5000000000000000000000000000000000)*y^2+
      (237507106019665678702061123/625000000000000000000000000000)*y^3+
      (225920263852122763120047611/250000000000000000000000000000)*y^4+
      (19852391049615193991/125000000000000000000000)*y^5 := by positivity
  linarith

theorem polynomial_positive {t : ℝ} (ht : t∈Icc 0 (129/200)) :
    (83/500:ℝ)<polynomial t := by
  obtain ⟨y, hyd⟩ : ∃ y : ℝ, y=129/200-t := ⟨_, rfl⟩
  have hy : y∈Icc 0 (129/200) := by rw [hyd]; constructor <;> linarith [ht.1,ht.2]
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hbracket : (5/2:ℝ)<2909/500-(691/500)*y-(5629/1000)*y^2 := by
    linarith [hy.2]
  have htail := mul_nonneg (pow_nonneg hy.1 3)
    (show 0≤2909/500-(691/500)*y-(5629/1000)*y^2 by linarith)
  have hh := translated_lower hy.1
  have he : 129/200-y=t := by rw [hyd]; ring
  rw [he] at hh
  dsimp [lowerPolynomial] at hh
  linarith [sq_nonneg y, hy.1]

end SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerSupport
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def plus (B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x-(arc B-1/2)*Real.sin x
def plusSpeed (B x : ℝ) : ℝ :=
  (arc B-1/2)*Real.cos x-(B-1/2)*Real.sin x
def plusK (B x : ℝ) : ℝ := Real.cos x-ratio B*Real.sin x
def minus (B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x+(arc B+1/2)*Real.sin x
def minusSpeed (B x : ℝ) : ℝ :=
  (arc B+1/2)*Real.cos x+(B-1/2)*Real.sin x
def minusK (B x : ℝ) : ℝ := Real.cos x+ratio B*Real.sin x
def PlusDomain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ plus B x∈Icc 0 outerDiagonal
def MinusDomain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ minus B x∈Icc 0 outerDiagonal
def plusCost (F G : RoleLabel) (B x : ℝ) : ℝ := x+F.outer (plus B x)+G.outer B
def minusCost (F G : RoleLabel) (B x : ℝ) : ℝ := -x+F.outer (minus B x)+G.outer B
def plusFirst (F : RoleLabel) (B x : ℝ) : ℝ := 1-F.d1 (plus B x)*plusSpeed B x
def minusFirst (F : RoleLabel) (B x : ℝ) : ℝ := -1+F.d1 (minus B x)*minusSpeed B x
def minusSecond (F : RoleLabel) (B x : ℝ) : ℝ :=
  F.d2 (minus B x)*(minusSpeed B x)^2-F.d1 (minus B x)*(minus B x-1/2)
def minusTarget (F G : RoleLabel) (B x : ℝ) : ℝ :=
  G.d1 B-F.d1 (minus B x)*minusK B x

lemma plus_hasDerivAt (B x : ℝ) : HasDerivAt (plus B) (-plusSpeed B x) x := by
  have h : HasDerivAt (fun t => 1/2+(1/2-B)*Real.cos t-(arc B-1/2)*Real.sin t)
      ((1/2-B)*(-Real.sin x)-(arc B-1/2)*Real.cos x) x :=
    (((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).sub
      ((Real.hasDerivAt_sin x).const_mul (arc B-1/2))
  exact h.congr_deriv (by simp only [plusSpeed]; ring)
lemma plusSpeed_hasDerivAt (B x : ℝ) :
    HasDerivAt (plusSpeed B) (plus B x-1/2) x := by
  have h : HasDerivAt (fun t => (arc B-1/2)*Real.cos t-(B-1/2)*Real.sin t)
      ((arc B-1/2)*(-Real.sin x)-(B-1/2)*Real.cos x) x :=
    ((Real.hasDerivAt_cos x).const_mul (arc B-1/2)).sub
      ((Real.hasDerivAt_sin x).const_mul (B-1/2))
  exact h.congr_deriv (by simp only [plus]; ring)
lemma minus_hasDerivAt (B x : ℝ) : HasDerivAt (minus B) (minusSpeed B x) x := by
  have h : HasDerivAt (fun t => 1/2+(1/2-B)*Real.cos t+(arc B+1/2)*Real.sin t)
      ((1/2-B)*(-Real.sin x)+(arc B+1/2)*Real.cos x) x :=
    (((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).add
      ((Real.hasDerivAt_sin x).const_mul (arc B+1/2))
  exact h.congr_deriv (by simp only [minusSpeed]; ring)
lemma minusSpeed_hasDerivAt (B x : ℝ) :
    HasDerivAt (minusSpeed B) (-(minus B x-1/2)) x := by
  have h : HasDerivAt (fun t => (arc B+1/2)*Real.cos t+(B-1/2)*Real.sin t)
      ((arc B+1/2)*(-Real.sin x)+(B-1/2)*Real.cos x) x :=
    ((Real.hasDerivAt_cos x).const_mul (arc B+1/2)).add
      ((Real.hasDerivAt_sin x).const_mul (B-1/2))
  exact h.congr_deriv (by simp only [minus]; ring)
lemma plus_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun t => plus t x) (-plusK B x) B := by
  have h : HasDerivAt (fun t => 1/2+(1/2-t)*Real.cos x-(arc t-1/2)*Real.sin x)
      (-1*Real.cos x-(-ratio B)*Real.sin x) B :=
    ((((hasDerivAt_id' B).const_sub (1/2)).mul_const (Real.cos x)).const_add (1/2)).sub
      (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).sub_const (1/2)).mul_const
        (Real.sin x))
  exact h.congr_deriv (by simp only [plusK]; ring)
lemma minus_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun t => minus t x) (-minusK B x) B := by
  have h : HasDerivAt (fun t => 1/2+(1/2-t)*Real.cos x+(arc t+1/2)*Real.sin x)
      (-1*Real.cos x+(-ratio B)*Real.sin x) B :=
    ((((hasDerivAt_id' B).const_sub (1/2)).mul_const (Real.cos x)).const_add (1/2)).add
      (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const (1/2)).mul_const
        (Real.sin x))
  exact h.congr_deriv (by simp only [minusK]; ring)

lemma positive_data {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    0<plusSpeed B x ∧ 0< minusSpeed B x ∧ 0<plusK B x ∧ 0< minusK B x := by
  have ht := positive_trig hx
  have hc : 0<Real.cos x-Real.sin x := by linarith [ht.1,ht.2.2.2.1]
  have hs := ShortOuterOne.SameContact.arc_state hB
  have ha : 0<arc B-1/2 := by linarith [(outer_bounds hs).1,fine_outer_endpoint_bounds.2]
  have hp := mul_pos ha hc
  have hq := mul_nonneg (show 0≤arc B-B from sub_nonneg.mpr hs.2.1) ht.2.2.1
  have hm := mul_pos (show 0<arc B+1/2 by linarith) hc
  have hn := mul_nonneg (show 0≤arc B+B by linarith [hB.1]) ht.2.2.1
  have hr := outer_ratio_bounds hB
  have hks := mul_le_mul_of_nonneg_right hr.2.1 ht.2.2.1
  have hms := mul_nonneg (by linarith [hr.1] : 0≤ratio B) ht.2.2.1
  dsimp [plusSpeed,minusSpeed,plusK,minusK]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

lemma plus_angle_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (plus B) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos (fun x _ => (plus_hasDerivAt B x).continuousAt.continuousWithinAt)
    (fun x _ => plus_hasDerivAt B x)
    (fun _ hx => neg_nonpos.mpr (positive_data hB (Ioo_subset_Icc_self hx)).1.le)
lemma minus_angle_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (minus B) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg (fun x _ => (minus_hasDerivAt B x).continuousAt.continuousWithinAt)
    (fun x _ => minus_hasDerivAt B x)
    (fun _ hx => (positive_data hB (Ioo_subset_Icc_self hx)).2.1.le)
lemma plus_target_antitone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    AntitoneOn (fun B => plus B x) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (plus_target_hasDerivAt hB x).continuousAt.continuousWithinAt)
    (fun _ hB => plus_target_hasDerivAt (Ioo_subset_Icc_self hB) x)
    (fun _ hB => neg_nonpos.mpr (positive_data (Ioo_subset_Icc_self hB) hx).2.2.1.le)
lemma minus_target_antitone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    AntitoneOn (fun B => minus B x) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (minus_target_hasDerivAt hB x).continuousAt.continuousWithinAt)
    (fun _ hB => minus_target_hasDerivAt (Ioo_subset_Icc_self hB) x)
    (fun _ hB => neg_nonpos.mpr (positive_data (Ioo_subset_Icc_self hB) hx).2.2.2.le)

lemma plus_norm {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    (plus B x-1/2)^2+(plusSpeed B x)^2=Q0-2*(arc B+B) := by
  have hcircle := UW_circle (outer_domain hB)
  dsimp [plus,plusSpeed,U,W] at *
  linear_combination hcircle+((arc B-1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq x)
lemma minus_norm {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    (minus B x-1/2)^2+(minusSpeed B x)^2=Q0-2*B := by
  have hcircle := UW_circle (outer_domain hB)
  dsimp [minus,minusSpeed,U,W] at *
  linear_combination hcircle+((arc B+1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq x)

lemma minus_aligned_le {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    1-B≤ minus B x := by
  have hh := minus_angle_monotone hB (by norm_num) hx hx.1
  have h0 : minus B 0=1-B := by simp only [minus,Real.cos_zero,Real.sin_zero]; ring
  linarith
lemma minus_target_lower {B x : ℝ} (hd : MinusDomain B x) : 1-outerDiagonal≤B := by
  linarith [minus_aligned_le hd.1 hd.2.1,hd.2.2.2]
lemma minus_z_bound {B x : ℝ} (hd : MinusDomain B x) :
    -(2/5:ℝ)< minus B x-1/2 ∧ minus B x-1/2<2/5 := by
  have hh := minus_aligned_le hd.1 hd.2.1
  constructor <;> linarith [hd.1.2,hd.2.2.2,outer_endpoint_bounds.2.2.2]

lemma plusCost_hasDerivAt (F G : RoleLabel) {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (plusCost F G B) (plusFirst F B x) x := by
  have h : HasDerivAt (fun t => t+F.outer (plus B t)+G.outer B)
      (1+F.d1 (plus B x)*(-plusSpeed B x)) x :=
    ((hasDerivAt_id' x).add ((F.outer_hasDerivAt (outer_domain hd.2.2)).comp x
      (plus_hasDerivAt B x))).add_const (G.outer B)
  exact h.congr_deriv (by simp only [plusFirst]; ring)
lemma minusCost_hasDerivAt (F G : RoleLabel) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (minusCost F G B) (minusFirst F B x) x := by
  have h : HasDerivAt (fun t => -t+F.outer (minus B t)+G.outer B)
      (-1+F.d1 (minus B x)*minusSpeed B x) x :=
    (((hasDerivAt_id' x).neg).add ((F.outer_hasDerivAt (outer_domain hd.2.2)).comp x
      (minus_hasDerivAt B x))).add_const (G.outer B)
  exact h.congr_deriv (by simp only [minusFirst])
lemma minusFirst_hasDerivAt (F : RoleLabel) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (minusFirst F B) (minusSecond F B x) x := by
  have h : HasDerivAt (fun t => -1+F.d1 (minus B t)*minusSpeed B t)
      (F.d2 (minus B x)*minusSpeed B x*minusSpeed B x+F.d1 (minus B x)*(-(minus B x-1/2))) x :=
    (((F.d1_hasDerivAt (outer_domain hd.2.2)).comp x (minus_hasDerivAt B x)).mul
      (minusSpeed_hasDerivAt B x)).const_add (-1)
  exact h.congr_deriv (by simp only [minusSecond]; ring)
lemma minusCost_target_hasDerivAt (F G : RoleLabel) {B x : ℝ} (hd : MinusDomain B x) :
    HasDerivAt (fun t => minusCost F G t x) (minusTarget F G B x) B := by
  have h : HasDerivAt (fun t => -x+F.outer (minus t x)+G.outer t)
      (F.d1 (minus B x)*(-minusK B x)+G.d1 B) B :=
    (((F.outer_hasDerivAt (outer_domain hd.2.2)).comp B
      (minus_target_hasDerivAt hd.1 x)).const_add (-x)).add
        (G.outer_hasDerivAt (outer_domain hd.1))
  exact h.congr_deriv (by simp only [minusTarget]; ring)

end SquaresInCircles.Eight.SecondWord.OppositeZero
end
end
end
