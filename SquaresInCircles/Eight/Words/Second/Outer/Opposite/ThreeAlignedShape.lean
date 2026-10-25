module

public import SquaresInCircles.Eight.Words.Second.Outer.LBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeAlignedReferences

/-!
# Eight squares: whole-domain curvature of both aligned opposite contacts

The first contact has decreasing second derivative on its entire arc.
The reverse contact uses a single uniformly convex auxiliary coefficient
and the exact circle relation for its slope.  All estimates hold through
the closed zero-coordinate and primary-one endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.Aligned
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma T_second_lower {y : ℝ} (hy : y∈Icc 0 outerDiagonal) :
    -(267/200:ℝ)<TLabel.d2 y :=
  T_zero_second.trans_le (T_second_monotone outer_zero_mem hy hy.1)

lemma T_inner_third {y : ℝ} (hy : y∈Icc 0 bOne) : TLabel.d3 (j y)<117/50 := by
  have he : (83/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  exact (T_third_monotone (j_mem hy) he (by linarith [(j_bounds hy).2])).trans_lt T_short_third

lemma L_inner_second {y : ℝ} (hy : y∈Icc 0 bOne) : LLabel.d2 (j y)< -(9/20:ℝ) := by
  have he : (2073/5000:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  exact (L_second_monotone (j_mem hy) he (j_bounds hy).2.le).trans_lt L_inner_end_second

lemma L_third_lower {y : ℝ} (hy : y∈Icc 0 outerDiagonal) : (317/100:ℝ)<LLabel.d3 y :=
  L_zero_third.trans_le (L_third_monotone outer_zero_mem hy hy.1)

lemma forward_third_negative {y : ℝ} (hy : y∈Icc 0 bOne) : third false y<0 := by
  have hdom := mem_outer hy
  have hj := j_mem hy
  have hu := U_positive (outer_domain hdom)
  have hw : 0<W y := by dsimp [W]; linarith [hy.1]
  have hub := (UW_bounds hdom).2.1
  have hwb := (coordinates hy).2.1
  have hcircle := UW_circle (outer_domain hdom)
  have hUW : U y*W y≤Q0/2 := by nlinarith [sq_nonneg (U y-W y)]
  have hM : (U y)^2*(W y)^3≤(383/200:ℝ)^2*(1291/1000)^3 :=
    mul_le_mul (pow_le_pow_left₀ hu.le hub.le 2)
      (pow_le_pow_left₀ hw.le hwb.le 3) (pow_nonneg hw.le 3) (by norm_num)
  have h1 := mul_le_mul (T_inner_third hy).le hM
    (mul_nonneg (sq_nonneg _) (pow_nonneg hw.le 3)) (by norm_num : (0:ℝ)≤117/50)
  have h2 := mul_le_mul
    (show -TLabel.d2 (j y)≤(267/200:ℝ) by linarith [T_second_lower hj]) hUW
    (mul_nonneg hu.le hw.le) (by norm_num : (0:ℝ)≤267/200)
  have h3 := mul_le_mul (T_first_upper hj).le hwb.le hw.le
    (by norm_num : (0:ℝ)≤1069/1000)
  have hscalar : (third false y+LLabel.d3 y)*(U y)^5=
      TLabel.d3 (j y)*(U y)^2*(W y)^3-
        3*TLabel.d2 (j y)*Q0*U y*W y+3*TLabel.d1 (j y)*Q0*W y := by
    have hr : ratio y=W y/U y := rfl
    have hD : ratioD y=Q0/(U y)^3 := rfl
    have hDD : ratioDD y=3*Q0*W y/(U y)^5 := rfl
    simp only [third,inner,outer,Bool.false_eq_true,↓reduceIte,hr,hD,hDD]
    field_simp
    ring
  have hlast := LLabel.third_numerator (outer_domain hdom)
  norm_num [LLabel,Q0] at hlast hscalar hUW h2
  have hp := pow_pos hu 5
  have hneg : third false y*(U y)^5<0 := by linarith
  exact neg_of_mul_neg_left hneg hp.le

lemma forward_second_antitone : AntitoneOn (second false) (Icc 0 bOne) :=
  antiOn_of_hasDeriv_nonpos
    (fun y hy => (second_hasDerivAt false hy).continuousAt.continuousWithinAt)
    (fun y hy => second_hasDerivAt false (Ioo_subset_Icc_self hy))
    (fun y hy => (forward_third_negative (Ioo_subset_Icc_self hy)).le)

lemma forward_curvature {y : ℝ} (hy : y∈Icc 0 bOne) : (11/50:ℝ)<second false y :=
  forward_endpoint_curvature.trans_le
    (forward_second_antitone hy ⟨OppositeTwo.bOne_mem.1,le_rfl⟩ hy.2)

lemma coefficient_hasDerivAt {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt coefficient (coefficientFirst y) y := by
  have hd := ((LLabel.d1_hasDerivAt (outer_domain (j_mem hy))).comp y
    (j_hasDerivAt hy)).fun_sub ((hasDerivAt_id' y).const_mul (95769/100000))
  exact hd.congr_deriv (by dsimp [coefficientFirst]; ring)

lemma coefficientFirst_hasDerivAt {y : ℝ} (hy : y∈Icc 0 bOne) :
    HasDerivAt coefficientFirst (coefficientSecond y) y := by
  have hi := (LLabel.d2_hasDerivAt (outer_domain (j_mem hy))).comp y (j_hasDerivAt hy)
  have hr := ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (mem_outer hy))
  exact ((hi.fun_neg.fun_mul hr).sub_const (95769/100000)).congr_deriv
    (by simp only [Function.comp_apply,coefficientSecond]; ring)

lemma coefficient_curvature {y : ℝ} (hy : y∈Icc 0 bOne) : (1/4:ℝ)<coefficientSecond y := by
  have hp := mul_nonneg (L_third_positive (j_mem hy)).le (sq_nonneg (ratio y))
  have hD := outer_ratioD_lower (mem_outer hy)
  have hl := L_inner_second hy
  have hm := mul_lt_mul''
    (show (9/20:ℝ)< -LLabel.d2 (j y) by linarith) hD
    (by norm_num : (0:ℝ)≤9/20) (by norm_num : (0:ℝ)≤557/1000)
  dsimp [coefficientSecond]
  linarith

lemma coefficient_lower {y : ℝ} (hy : y∈Icc 0 bOne) : (17/50:ℝ)<coefficient y := by
  have href : (5781/10000:ℝ)∈Icc 0 bOne :=
    ⟨by norm_num,by linarith [OppositeTwo.bOne_bounds.1]⟩
  have ht := curvature_tangent (f := coefficient) (d := coefficientFirst)
    (dd := coefficientSecond) (κ := (1/4:ℝ)) hy href
    (fun t ht => coefficient_hasDerivAt ht)
    (fun t ht => coefficientFirst_hasDerivAt ht)
    (fun t ht => (coefficient_curvature ht).le)
  have hd := abs_lt.mp coefficient_reference.2
  have hs : (coefficientFirst (5781/10000))^2<(1/10000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((y-5781/10000)/4+coefficientFirst (5781/10000))
  nlinarith [coefficient_reference.1]

lemma ratioD_quadratic_lower {y : ℝ} (hy : y∈Icc 0 outerDiagonal) :
    (1/2:ℝ)+(3/4)*(ratio y)^2<ratioD y := by
  have hu := U_positive (outer_domain hy)
  have hh := (UW_bounds hy).2.1
  have hc := UW_circle (outer_domain hy)
  have hs : (U y)^2≤(383/200:ℝ)^2 := pow_le_pow_left₀ hu.le hh.le 2
  have hb : 0≤3*Q0-(U y)^2-(383/200)*U y-(383/200)^2 := by
    norm_num [Q0]
    nlinarith
  have hp := mul_nonneg (show 0≤(383/200:ℝ)-U y by linarith) hb
  have hf : 0<Q0+(U y)^3/4-(3/4)*Q0*U y := by
    norm_num [Q0] at hp ⊢
    nlinarith
  have he : (ratioD y-1/2-(3/4)*(ratio y)^2)*(U y)^3=
      Q0+(U y)^3/4-(3/4)*Q0*U y := by
    dsimp [ratioD,ratio]
    change (Q0/(U y)^3-1/2-(3/4)*(W y/U y)^2)*(U y)^3=_
    field_simp [hu.ne']
    nlinarith [hc]
  have hp3 := pow_pos hu 3
  nlinarith

lemma reverse_curvature {y : ℝ} (hy : y∈Icc 0 bOne) : (87/100:ℝ)<second true y := by
  have hdom := mem_outer hy
  have hr := outer_ratio_bounds hdom
  have hrhi := (coordinates hy).2.2
  have hD := ratioD_quadratic_lower hdom
  have hA := coefficient_lower hy
  have hL := L_inner_second hy
  have hprod := mul_lt_mul'' hA hD
    (by norm_num : (0:ℝ)≤17/50) (by positivity : (0:ℝ)≤1/2+(3/4)*(ratio y)^2)
  have hsq := mul_nonneg
    (show 0≤-LLabel.d2 (j y)-9/20 by linarith) (sq_nonneg (ratio y))
  have he : second true y=91744/50000-(95769/50000)*ratio y-
      LLabel.d2 (j y)*(ratio y)^2+coefficient y*ratioD y := by
    simp only [second,inner,outer,coefficient,RoleLabel.d2,TLabel,↓reduceIte]
    ring
  have hpoly := mul_nonneg
    (show 0≤(861/1000:ℝ)-ratio y by linarith)
    (show 0≤95769/50000-(141/200)*(ratio y+861/1000) by linarith)
  rw [he]
  nlinarith

end SquaresInCircles.Eight.SecondWord.OppositeThree.Aligned
