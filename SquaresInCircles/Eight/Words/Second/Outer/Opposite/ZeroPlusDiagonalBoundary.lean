module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroNegativePJ
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveSpeeds

/-!
# Eight squares: the two actual endpoints of the positive diagonal exit

The first endpoint is aligned.  The second
is the original target-zero contact, whose angle exceeds .10726.
The original contact coordinates identify the explicit circle branch,
and concavity supplies both P/J order bounds on that complete branch.
-/

section
/-!
## The positive-angle source-diagonal exit

The rotated circle gives a strictly decreasing, strictly concave target coordinate `height`
(`speed_negative`, `acceleration_upper`). Its speed and acceleration are bounded on the whole
interval (`data`), and both possible target labels give concave costs (`J_curvature`,
`P_curvature`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.PlusDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def offset : ℝ := 1/2-outerDiagonal
def Z (x : ℝ) : ℝ := offset+Real.sin x+Real.cos x
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def horizontal (x : ℝ) : ℝ := Z x*Real.sin x+Y x*Real.cos x
def vertical (x : ℝ) : ℝ := Z x*Real.cos x-Y x*Real.sin x
def height (x : ℝ) : ℝ := vertical x-1/2
def factor (x : ℝ) : ℝ := 1-(Real.cos x-Real.sin x)/Y x
def factorD (x : ℝ) : ℝ :=
  ((Real.sin x+Real.cos x)*(Q0-2-offset^2)-offset*(Real.sin x+Real.cos x)^2-2*offset)/(Y x)^3
def speed (x : ℝ) : ℝ := -horizontal x*factor x
def acceleration (x : ℝ) : ℝ := -vertical x*(factor x)^2-horizontal x*factorD x
def Domain (x : ℝ) : Prop := x∈Icc 0 (27/250) ∧ 0≤height x
def cost (F G : RoleLabel) (x : ℝ) : ℝ := x+F.outer outerDiagonal+G.outer (height x)
def first (G : RoleLabel) (x : ℝ) : ℝ := 1+G.d1 (height x)*speed x
def second (G : RoleLabel) (x : ℝ) : ℝ :=
  G.d2 (height x)*(speed x)^2+G.d1 (height x)*acceleration x

lemma data {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    (3/5:ℝ)<Z x ∧ Z x<71/100 ∧ (46/25:ℝ)<Y x ∧ Y x<2 ∧
      (Y x)^2+(Z x)^2=Q0 ∧ (9/5:ℝ)<horizontal x ∧ horizontal x<2 ∧
        0<vertical x ∧ 0<factor x ∧ factor x<14/25 ∧ (9/25:ℝ)<factorD x := by
  have hxi : x∈Icc 0 (7/10) := ⟨hx.1,by linarith only [hx.2]⟩
  have ht := positive_trig hxi
  have hs := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have ho : -(2/5:ℝ)<offset ∧ offset< -(399/1000) := by
    have hd := diagonal_fine
    dsimp only [offset]; constructor <;> linarith only [hd.1,hd.2]
  have hz : (3/5:ℝ)<Z x ∧ Z x<71/100 := by
    dsimp only [Z]; constructor <;> linarith only [ht.2.2.2.2.2,ht.2.1,hx.2,hs,ho.1,ho.2]
  have hQ : Q0=9789/2500 := by norm_num [Q0]
  have hz2 : Z x^2<(71/100)^2 := pow_lt_pow_left₀ hz.2 (by linarith only [hz.1]) (by norm_num)
  have hz2' : (3/5)^2<Z x^2 := pow_lt_pow_left₀ hz.1 (by norm_num) (by norm_num)
  have hr : 0<Q0-(Z x)^2 := by rw [hQ]; linarith only [hz2]
  have hy : 0<Y x := Real.sqrt_pos.mpr hr
  have hy2 : (Y x)^2=Q0-(Z x)^2 := Real.sq_sqrt hr.le
  have hyl : (46/25:ℝ)<Y x :=
    lt_of_pow_lt_pow_left₀ 2 hy.le (by rw [hy2,hQ]; linarith only [hz2])
  have hyu : Y x<(2:ℝ) :=
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hy2,hQ]; linarith only [hz2'])
  have hx2 : x^2≤(27/250)*x := by rw [sq]; exact mul_le_mul_of_nonneg_right hx.2 hx.1
  have hcos : (497/500:ℝ)≤Real.cos x := by linarith only [hc,hx2,hx.2]
  have hprod := mul_le_mul hyl.le hcos (by norm_num) hy.le
  have hpositive := mul_nonneg (by linarith only [hz.1] : 0≤Z x) ht.2.2.1
  have hhorizontal : (9/5:ℝ)<horizontal x := by
    dsimp only [horizontal]; linarith only [hprod,hpositive]
  have hcircle : (horizontal x)^2+(vertical x)^2=Q0 := by
    dsimp only [horizontal,vertical]
    linear_combination hy2+((Y x)^2+(Z x)^2)*(Real.sin_sq_add_cos_sq x)
  have hhorizontalU : horizontal x<2 :=
    lt_of_pow_lt_pow_left₀ 2 (by norm_num)
      (by have := sq_nonneg (vertical x); linarith only [this,hcircle,hQ])
  have hv1 := mul_le_mul hz.1.le hcos (by norm_num) (by linarith only [hz.1] : 0≤Z x)
  have hv2 := mul_le_mul hyu.le hs ht.2.2.1 (by norm_num)
  have hv : 0<vertical x := by dsimp only [vertical]; linarith only [hx.2,hv1,hv2]
  have hflo : (Real.cos x-Real.sin x)/Y x<1 := by
    apply (div_lt_one hy).2
    linarith only [ht.2.1,ht.2.2.1,hyl]
  have hfhi : (11/25:ℝ)<(Real.cos x-Real.sin x)/Y x := by
    apply (lt_div_iff₀ hy).2
    linarith only [hx.2,hyu,hcos,hs]
  have hsum := ht.2.2.2.2.2
  have hn : (72/25:ℝ)<(Real.sin x+Real.cos x)*(Q0-2-offset^2)-
      offset*(Real.sin x+Real.cos x)^2-2*offset := by
    have ho2 : offset^2<4/25 := by
      have h := pow_lt_pow_left₀ (show -offset<2/5 by linarith only [ho.1])
        (by linarith only [ho.2]) (n := 2) (by norm_num)
      rw [neg_sq] at h
      linarith only [h]
    have h1 := mul_le_mul_of_nonneg_right hsum
      (show 0≤Q0-2-offset^2 by rw [hQ]; linarith only [ho2])
    have h2 := mul_le_mul_of_nonneg_left
      (one_le_pow₀ hsum : (1:ℝ)≤(Real.sin x+Real.cos x)^2)
      (by linarith only [ho.2] : 0≤-offset)
    rw [hQ] at h1 ⊢
    linarith only [ho.2,h1,h2,ho2]
  have hfd : (9/25:ℝ)<factorD x := by
    apply (lt_div_iff₀ (pow_pos hy 3)).2
    have hpow := pow_lt_pow_left₀ hyu hy.le (n := 3) (by norm_num)
    linarith only [hpow,hn]
  exact ⟨hz.1,hz.2,hyl,hyu,by linarith only [hy2],hhorizontal,
    hhorizontalU,hv,by dsimp only [factor]; linarith only [hflo],
    by dsimp only [factor]; linarith only [hfhi],hfd⟩

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    HasDerivAt Y (-Z x*(Real.cos x-Real.sin x)/Y x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hz : HasDerivAt Z (Real.cos x-Real.sin x) x :=
    (((Real.hasDerivAt_sin x).const_add offset).add (Real.hasDerivAt_cos x)).congr_deriv (by ring)
  have hr : Q0-(Z x)^2≠0 := by nlinarith [(data hx).2.2.2.2.1]
  refine (((hz.fun_pow 2).const_sub Q0).sqrt hr).congr_deriv ?_
  rw [show Real.sqrt (Q0-Z x^2)=Y x from rfl]
  field_simp
  ring

lemma horizontal_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    HasDerivAt horizontal (vertical x*factor x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hz : HasDerivAt Z (Real.cos x-Real.sin x) x :=
    (((Real.hasDerivAt_sin x).const_add offset).add (Real.hasDerivAt_cos x)).congr_deriv (by ring)
  refine ((hz.fun_mul (Real.hasDerivAt_sin x)).fun_add ((Y_hasDerivAt hx).fun_mul
    (Real.hasDerivAt_cos x))).congr_deriv ?_
  simp only [vertical,factor]
  field_simp
  ring

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) : HasDerivAt height (speed x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hz : HasDerivAt Z (Real.cos x-Real.sin x) x :=
    (((Real.hasDerivAt_sin x).const_add offset).add (Real.hasDerivAt_cos x)).congr_deriv (by ring)
  refine (((hz.fun_mul (Real.hasDerivAt_cos x)).fun_sub ((Y_hasDerivAt hx).fun_mul
    (Real.hasDerivAt_sin x))).sub_const (1/2)).congr_deriv ?_
  simp only [speed,horizontal,factor]
  field_simp
  ring

lemma factor_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) : HasDerivAt factor (factorD x) x := by
  have hy : 0<Y x := by linarith [(data hx).2.2.1]
  have hr := (data hx).2.2.2.2.1
  have key : (Real.sin x+Real.cos x)*(Y x)^2-Z x*(Real.cos x-Real.sin x)^2=
      (Real.sin x+Real.cos x)*(Q0-2-offset^2)-offset*(Real.sin x+Real.cos x)^2-2*offset := by
    simp only [Z] at hr ⊢
    linear_combination (Real.sin x+Real.cos x)*hr-
      2*(offset+Real.sin x+Real.cos x)*(Real.sin_sq_add_cos_sq x)
  refine ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).fun_div
    (Y_hasDerivAt hx) hy.ne').const_sub 1).congr_deriv ?_
  simp only [factorD]
  rw [←key]
  field_simp
  ring
lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (27/250)) : HasDerivAt speed (acceleration x) x := by
  refine ((horizontal_hasDerivAt hx).fun_neg.fun_mul (factor_hasDerivAt hx)).congr_deriv ?_
  simp only [acceleration]
  ring

lemma speed_negative {x : ℝ} (hx : x∈Icc 0 (27/250)) : speed x<0 := by
  have h := data hx
  have hp := mul_pos (by linarith [h.2.2.2.2.2.1] : 0<horizontal x) h.2.2.2.2.2.2.2.2.1
  simp only [speed]
  linarith
lemma acceleration_upper {x : ℝ} (hx : x∈Icc 0 (27/250)) :
    acceleration x< -(81/125:ℝ) ∧ (speed x)^2<(784/625:ℝ) := by
  have h := data hx
  have hV := h.2.2.2.2.2.2.2.1
  have hU := h.2.2.2.2.2.1
  have hUu := h.2.2.2.2.2.2.1
  have hf := h.2.2.2.2.2.2.2.2.1
  have hfu := h.2.2.2.2.2.2.2.2.2.1
  have hfd := h.2.2.2.2.2.2.2.2.2.2
  have h1 := mul_lt_mul hU hfd.le (by norm_num) (by linarith : 0≤horizontal x)
  have h2 := mul_lt_mul hUu hfu.le hf (by norm_num)
  have h3 := mul_nonneg hV.le (sq_nonneg (factor x))
  constructor
  · dsimp only [acceleration]
    linarith
  · rw [show (speed x)^2=(horizontal x*factor x)^2 by simp only [speed]; ring]
    have h4 := pow_lt_pow_left₀ h2 (mul_pos (by linarith) hf).le (n := 2) (by norm_num)
    linarith

lemma height_zero : height 0=1-outerDiagonal := by norm_num [height,vertical,Z,offset]; ring
lemma height_antitone : AntitoneOn height (Icc 0 (27/250)) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hx => (height_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun _ hx => height_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun _ hx => (speed_negative (Ioo_subset_Icc_self hx)).le)
lemma target_bounds {x : ℝ} (hx : Domain x) : height x∈Icc 0 (101/1000) := by
  have hh := height_antitone (by norm_num) hx.1 hx.1.1
  rw [height_zero] at hh
  exact ⟨hx.2,by linarith [diagonal_fine.1]⟩

lemma cost_hasDerivAt (F G : RoleLabel) {x : ℝ} (hx : Domain x) : HasDerivAt (cost F G) (first G x) x := by
  have ht : height x∈Icc 0 outerDiagonal :=
    ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  refine (((hasDerivAt_id' x).add_const (F.outer outerDiagonal)).fun_add
    ((G.outer_hasDerivAt (outer_domain ht)).comp x (height_hasDerivAt hx.1))).congr_deriv ?_
  simp only [first]
lemma first_hasDerivAt (G : RoleLabel) {x : ℝ} (hx : Domain x) : HasDerivAt (first G) (second G x) x := by
  have ht : height x∈Icc 0 outerDiagonal :=
    ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  refine ((((G.d1_hasDerivAt (outer_domain ht)).comp x (height_hasDerivAt hx.1)).fun_mul
    (speed_hasDerivAt hx.1)).const_add 1).congr_deriv ?_
  simp only [second,Function.comp_apply]
  ring

lemma J_curvature {x : ℝ} (hx : Domain x) : second JLabel x<0 := by
  have ht : height x∈Icc 0 outerDiagonal := ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  have h1 := mul_nonpos_of_nonpos_of_nonneg (by linarith [J_second_upper ht] : JLabel.d2 (height x)≤0)
    (sq_nonneg (speed x))
  have h2 := mul_neg_of_pos_of_neg (by linarith [(J_first_bounds ht).1] : 0<JLabel.d1 (height x))
    (by linarith [(acceleration_upper hx.1).1] : acceleration x<0)
  dsimp [second]
  linarith
lemma P_curvature {x : ℝ} (hx : Domain x) : second PLabel x<0 := by
  have ht : height x∈Icc 0 outerDiagonal := ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  have hP2 := (P_second_monotone ht (Asymmetric.rational_outer_mem (by norm_num)) (target_bounds hx).2).trans_lt Reference.P_101_second
  have hspeed := acceleration_upper hx.1
  have h1 := mul_le_mul hP2.le hspeed.2.le (sq_nonneg _) (by norm_num)
  have h2 := mul_lt_mul_of_pos_left hspeed.1 (by linarith [(P_first_bounds ht).1] : 0<PLabel.d1 (height x))
  have h3 := mul_lt_mul_of_pos_right (P_first_bounds ht).1 (by norm_num : (0:ℝ)<81/125)
  dsimp [second]
  nlinarith

end SquaresInCircles.Eight.SecondWord.OppositeZero.PlusDiagonal
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.PlusDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra
open SameZero.PJ.Reference (sinBox cosBox dBox dUBox aBox)

private lemma r62_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r62_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r62_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
private lemma r62_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl
private lemma r62_rootAt_lo {b : ℝ} (hb : b∈Icc 0 (9/10)) : (Reference.rootAt b hb).lo =
    (rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2) (by linarith [hb.2])
      (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).lo := by
  unfold Reference.rootAt
  rw [r62_mpr_lo, r62_mp_lo]
  all_goals simp [U,ShortOuterOne.SameContact.arc]
private lemma r62_rootAt_hi {b : ℝ} (hb : b∈Icc 0 (9/10)) : (Reference.rootAt b hb).hi =
    (rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2) (by linarith [hb.2])
      (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).hi := by
  unfold Reference.rootAt
  rw [r62_mpr_hi, r62_mp_hi]
  all_goals simp [U,ShortOuterOne.SameContact.arc]
private lemma r62_dUBox_lo : dUBox.lo = (dBox.add (Interval.point (1/2))).lo := by
  unfold dUBox
  rw [r62_mpr_lo, r62_mpr_lo]
  · rw [ShortOuterOne.SameContact.arc_diagonal]
  · rfl
private lemma r62_dUBox_hi : dUBox.hi = (dBox.add (Interval.point (1/2))).hi := by
  unfold dUBox
  rw [r62_mpr_hi, r62_mpr_hi]
  · rw [ShortOuterOne.SameContact.arc_diagonal]
  · rfl
private lemma r62_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r62_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r62_mpr_lo r62_coordinate_eq (congrArg _ r62_coordinate_eq) _
private lemma r62_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r62_mpr_hi r62_coordinate_eq (congrArg _ r62_coordinate_eq) _
private lemma r62_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r62_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r62_mpr_lo (r62_label_eq H) (congrArg _ (r62_label_eq H)) _
private lemma r62_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r62_mpr_hi (r62_label_eq H) (congrArg _ (r62_label_eq H)) _

local macro "r62_arith" : tactic => `(tactic|
  norm_num [r62_rootAt_lo,r62_rootAt_hi,rootThree,rootStep,Reference.plusBox,
    r62_coordinate_lo,r62_coordinate_hi,r62_labelBox_lo,r62_labelBox_hi,r62_dUBox_lo,r62_dUBox_hi,
    SameZero.PJ.Reference.sinBox,SameZero.PJ.Reference.cosBox,
    SameZero.PJ.Reference.dBox,SameZero.PJ.Reference.aBox,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.cube,Interval.div,Interval.inv,HighOrderTaylor.S17,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    PLabel,JLabel,LLabel,Q0,SameZero.PJ.Diagonal.start])

lemma endpoint_references : plus 0 (27/250)<outerDiagonal ∧ height (27/250)<0 ∧
    (44889/50000:ℝ)<SameZero.PJ.Diagonal.start+PLabel.outer outerDiagonal+JLabel.outer 0 ∧
    (44889/50000:ℝ)<SameZero.PJ.Diagonal.start+JLabel.outer outerDiagonal+PLabel.outer 0 := by
  let S := sinBox (27/250) (by norm_num)
  let C := cosBox (27/250) (by norm_num)
  let ZB := (((Interval.point (1/2)).sub dBox).add S).add C
  let Q := (Interval.point Q0).sub ZB.square
  have hQ : 0≤Q.lo := by dsimp [Q,ZB,S,C]; r62_arith
  let YB := rootThree Q 2 (by norm_num) hQ
  let HB := ((ZB.mul C).sub (YB.mul S)).sub (Interval.point (1/2))
  let PB := Reference.plusBox 0 (27/250) (by norm_num) (by norm_num)
  let J0 := (Interval.point (-(13/50000))).mul aBox
  let V1 := ((Interval.point SameZero.PJ.Diagonal.start).add (labelBox PLabel dBox dUBox)).add J0
  let V2 := ((Interval.point SameZero.PJ.Diagonal.start).add (labelBox JLabel dBox dUBox)).add
    (Interval.point (1239/50000))
  have hPB : PB.hi<(899214065:ℝ)/1000000000 := by dsimp [PB]; r62_arith
  have hHB : HB.hi<0 := by dsimp [HB,YB,Q,ZB,S,C]; r62_arith
  have hV1 : (44889/50000:ℝ)<V1.lo := by
    dsimp only [V1,J0]; r62_arith
  have hV2 : (44889/50000:ℝ)<V2.lo := by
    dsimp only [V2]; r62_arith
  refine ⟨by linarith [PB.mem.2,diagonal_fine.1],HB.mem.2.trans_lt hHB,?_,?_⟩
  · have hh := hV1.trans_le V1.mem.1
    have hJ := J_zero
    change JLabel.outer 0= -(13/50000)*outerAxial at hJ
    simpa [hJ] using hh
  · have hh := hV2.trans_le V2.mem.1
    have hP0 : PLabel.outer 0=1239/50000 := by
      norm_num [RoleLabel.outer,RoleLabel.eval,PLabel]
    rw [hP0]
    exact hh

lemma contact {x : ℝ} (hx : Domain x) : plus (height x) x=outerDiagonal := by
  have htarget : height x∈Icc 0 outerDiagonal :=
    ⟨hx.2,by linarith [(target_bounds hx).2,fine_outer_endpoint_bounds.2]⟩
  have hc : (horizontal x)^2+(vertical x)^2=Q0 := by
    have hr := (data hx.1).2.2.2.2.1
    dsimp only [horizontal,vertical]
    linear_combination hr+((Z x)^2+(Y x)^2)*(Real.sin_sq_add_cos_sq x)
  have hactual := UW_circle (outer_domain htarget)
  have hU := U_positive (outer_domain htarget)
  have hV : W (height x)=vertical x := by dsimp only [W,height]; ring
  have heU : U (height x)=horizontal x := by
    rw [hV] at hactual
    have hH := (data hx.1).2.2.2.2.2.1
    have hprod : (U (height x)-horizontal x)*(U (height x)+horizontal x)=0 := by
      linear_combination hactual-hc
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  have hplus : plus (height x) x=
      1/2+(1-W (height x))*Real.cos x-(U (height x)-1)*Real.sin x := by
    simp only [plus,U,W]; ring
  rw [hplus,hV,heU]
  dsimp only [horizontal,vertical,Z,offset]
  linear_combination (-(1/2-outerDiagonal+Real.sin x+Real.cos x))*(Real.sin_sq_add_cos_sq x)

lemma original {B x : ℝ} (hd : PlusDomain B x) (he : plus B x=outerDiagonal) :
    Domain x ∧ height x=B := by
  have h0 : plus B x≤plus 0 x := plus_target_antitone hd.2.1 outer_zero_mem hd.1 hd.1.1
  have hx : x≤27/250 := by
    by_contra! hn
    have hh : plus 0 x≤plus 0 (27/250) :=
      plus_angle_antitone outer_zero_mem (by norm_num) hd.2.1 hn.le
    rw [he] at h0
    linarith [endpoint_references.1]
  have hxi : x∈Icc 0 (27/250) := ⟨hd.2.1.1,hx⟩
  have hZ : Z x=W B*Real.cos x+U B*Real.sin x := by
    dsimp only [plus,U,W] at he
    dsimp only [Z,offset,U,W]
    linarith
  have hY : Y x=U B*Real.cos x-W B*Real.sin x := by
    have hnorm := UW_circle (outer_domain hd.1)
    have hr := (data hxi).2.2.2.2.1
    have htrig := positive_trig hd.2.1
    have hstate := ShortOuterOne.SameContact.arc_state hd.1
    have hUc : 0<U B*(Real.cos x-Real.sin x) :=
      mul_pos (U_positive (outer_domain hd.1)) (by linarith [htrig.1,htrig.2.2.2.1])
    have hmore := mul_nonneg (show 0≤U B-W B by dsimp only [U,W]; linarith [hstate.2.1])
      htrig.2.2.1
    have hpositive : 0<U B*Real.cos x-W B*Real.sin x := by linarith
    have heq : (U B*Real.cos x-W B*Real.sin x)^2+(Z x)^2=Q0 := by
      rw [hZ]
      linear_combination hnorm+((U B)^2+(W B)^2)*(Real.sin_sq_add_cos_sq x)
    have hy := (data hxi).2.2.1
    exact (pow_left_inj₀ (by linarith) hpositive.le (two_ne_zero)).mp (by linarith)
  have hheight : height x=B := by
    dsimp only [height,vertical]
    rw [hZ,hY]
    dsimp only [W]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)
  exact ⟨⟨hxi,by rw [hheight]; exact hd.1.1⟩,hheight⟩

lemma speed_upper {x : ℝ} (hx : x∈Icc 0 (27/250)) : speed x< -(7/10:ℝ) := by
  have h := data hx
  have ht := positive_trig (show x∈Icc 0 (7/10) from ⟨hx.1,by linarith [hx.2]⟩)
  have hf : (2/5:ℝ)<factor x := by
    have hh : (Real.cos x-Real.sin x)/Y x<(3/5:ℝ) := by
      apply (div_lt_iff₀ (by linarith [h.2.2.1] : 0<Y x)).2
      linarith [ht.2.1,ht.2.2.1,h.2.2.1]
    dsimp only [factor]; linarith
  have hm := mul_lt_mul h.2.2.2.2.2.1 hf.le (by norm_num)
    (by linarith [h.2.2.2.2.2.1] : 0≤horizontal x)
  dsimp only [speed]
  linarith

lemma shifted_height_antitone : AntitoneOn (fun x => height x+(7/10)*x) (Icc 0 (27/250)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x hx => ((height_hasDerivAt hx).add ((hasDerivAt_id x).const_mul (7/10))).continuousAt.continuousWithinAt)
    (fun x hx => (height_hasDerivAt (Ioo_subset_Icc_self hx)).add ((hasDerivAt_id x).const_mul (7/10)))
    (fun x hx => by linarith [speed_upper (Ioo_subset_Icc_self hx)])

theorem lower (reverse : Bool) {x : ℝ} (hx : Domain x) :
    (44889/50000:ℝ)<cost (if reverse then JLabel else PLabel)
      (if reverse then PLabel else JLabel) x := by
  have hc : ContinuousOn height (Icc 0 (27/250)) :=
    fun y hy => (height_hasDerivAt hy).continuousAt.continuousWithinAt
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (show (0:ℝ)≤27/250 by norm_num)
    hc.neg (show (0:ℝ)∈Icc (-height 0) (-height (27/250)) by
      rw [height_zero]; constructor <;> linarith [diagonal_fine.2,endpoint_references.2.1])
  have htzero : height t=0 := by rw [Pi.neg_apply] at he; linarith
  have htd : Domain t := ⟨ht,htzero.ge⟩
  have hcontact := contact htd
  rw [htzero] at hcontact
  have hstart : SameZero.PJ.Diagonal.start<t := by
    by_contra! hn
    have hh : plus 0 SameZero.PJ.Diagonal.start≤plus 0 t := plus_angle_antitone outer_zero_mem
      ⟨ht.1,by linarith [ht.2]⟩ (by norm_num [SameZero.PJ.Diagonal.start]) hn
    have h := SameZero.PJ.Reference.zero_start
    have hb : plus 0 SameZero.PJ.Diagonal.start=SameZero.b 0 SameZero.PJ.Diagonal.start := by
      dsimp only [plus,SameZero.b]; ring
    rw [←hb] at h
    linarith
  have hxt : x≤t := by
    by_contra! hn
    have hh : height x+(7/10)*x≤height t+(7/10)*t := shifted_height_antitone ht hx.1 hn.le
    rw [htzero] at hh
    linarith [hx.2]
  have hdom : ∀y∈Icc 0 t,Domain y := by
    intro y hy
    have hyi : y∈Icc 0 (27/250) := ⟨hy.1,hy.2.trans ht.2⟩
    have hh := height_antitone hyi ht hy.2
    rw [htzero] at hh
    exact ⟨hyi,hh⟩
  have hconc : ConcaveOn ℝ (Icc 0 t)
      (cost (if reverse then JLabel else PLabel) (if reverse then PLabel else JLabel)) :=
    concave_of_deriv2
      (fun y hy => cost_hasDerivAt _ _ (hdom y hy))
      (fun y hy => first_hasDerivAt _ (hdom y hy))
      (fun y hy => by
        cases reverse
        · exact (J_curvature (hdom y hy)).le
        · exact (P_curvature (hdom y hy)).le)
  apply concave_gt_of_endpoints hconc ⟨hx.1.1,hxt⟩
  · have hB : 1-outerDiagonal∈Icc 0 outerDiagonal := by
      constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]
    cases reverse
    · simpa [cost,height_zero] using AlignedPJ.original ⟨outer_zero_mem.2,le_rfl⟩ hB (by ring)
    · simpa [cost,height_zero,add_comm] using
        AlignedPJ.original hB ⟨outer_zero_mem.2,le_rfl⟩ (by ring)
  · cases reverse <;> simp only [Bool.false_eq_true,↓reduceIte,cost,htzero]
    · linarith [endpoint_references.2.2.1]
    · linarith [endpoint_references.2.2.2]

end SquaresInCircles.Eight.SecondWord.OppositeZero.PlusDiagonal
end
end
end
