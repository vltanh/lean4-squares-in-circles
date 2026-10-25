module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroData
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJBoundaryReferences

/-!
# Eight squares: the positive-contact speed estimates in the written proof

The sum a(B)+B is monotone, so the exact
circle identity gives the stated whole-range speed bounds.  The P
angular derivative is positive throughout its two analytic ranges;
the first J range is controlled by its target or source coordinate.
-/

section
/-!
## Scalar and contact references for the opposite zero rows

The labels, the contacts and their speeds are enclosed at fixed rational points (`rootAt`,
`valueAt`, `plusBox`, `speedBox`). Positive square-root refinements and alternating Taylor
polynomials keep the exact expression in each enclosure; the tactic
`opposite_reference_arithmetic` proves the resulting rational inequalities by `norm_num`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Reference
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra
open SameZero.PJ.Reference (sinBox cosBox dBox dUBox aBox)

def rootAt (b : ℝ) (hb : b∈Icc 0 (9/10)) : Interval (U b) := by
  have hs : 0<2-b/2 := by linarith [hb.2]
  have hrad : 0<Q0-(b+1/2)^2 := by norm_num [Q0]; nlinarith [hb.1,hb.2]
  have hh := rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2) hs hrad.le
  simpa [U,ShortOuterOne.SameContact.arc] using hh

private lemma r62_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r62_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r62_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
private lemma r62_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl

private lemma r62_rootAt_lo {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).lo =
    (rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2) (by linarith [hb.2])
      (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).lo := by
  unfold rootAt
  rw [r62_mpr_lo, r62_mp_lo]
  all_goals simp [U,ShortOuterOne.SameContact.arc]
private lemma r62_rootAt_hi {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).hi =
    (rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2) (by linarith [hb.2])
      (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).hi := by
  unfold rootAt
  rw [r62_mpr_hi, r62_mp_hi]
  all_goals simp [U,ShortOuterOne.SameContact.arc]

lemma rootAt_lo_positive {b : ℝ} (hb : b∈Icc 0 (9/10)) : 0<(rootAt b hb).lo := by
  have hs : 0<2-b/2 := by linarith [hb.2]
  have hrad : 0<Q0-(b+1/2)^2 := by norm_num [Q0]; nlinarith [hb.1,hb.2]
  rw [r62_rootAt_lo]
  dsimp only [rootThree,rootStep,Interval.point]
  positivity

def valueAt (F : RoleLabel) (b : ℝ) (hb : b∈Icc 0 (9/10)) : Interval (F.outer b) :=
  labelBox F (Interval.point b) (rootAt b hb)
def firstAt (F : RoleLabel) (b : ℝ) (hb : b∈Icc 0 (9/10)) : Interval (F.d1 b) :=
  firstBox F (Interval.point b) (rootAt b hb) (rootAt_lo_positive hb)
def secondAt (F : RoleLabel) (b : ℝ) (hb : b∈Icc 0 (9/10)) : Interval (F.d2 b) :=
  secondBox F (Interval.point b) (rootAt b hb) (rootAt_lo_positive hb)

def plusBox (B x : ℝ) (hB : B∈Icc 0 (9/10)) (hx : 0≤x) : Interval (plus B x) :=
  let W := ((Interval.point (1/2)).add ((Interval.point (1/2-B)).mul (cosBox x hx))).sub
    (((rootAt B hB).sub (Interval.point 1)).mul (sinBox x hx))
  ⟨W.lo,W.hi,by
    have h : plus B x=1/2+(1/2-B)*Real.cos x-(U B-1)*Real.sin x := by
      simp only [plus,U]; ring
    rw [h]; exact W.mem⟩
def speedBox (B x : ℝ) (hB : B∈Icc 0 (9/10)) (hx : 0≤x) : Interval (plusSpeed B x) :=
  let W := (((rootAt B hB).sub (Interval.point 1)).mul (cosBox x hx)).sub
    ((Interval.point (B-1/2)).mul (sinBox x hx))
  ⟨W.lo,W.hi,by
    have h : plusSpeed B x=(U B-1)*Real.cos x-(B-1/2)*Real.sin x := by
      simp only [plusSpeed,U]; ring
    rw [h]; exact W.mem⟩

macro "opposite_reference_arithmetic" : tactic => `(tactic|
  norm_num [rootAt,rootThree,rootStep,valueAt,firstAt,secondAt,plusBox,speedBox,
    shifted,radicand,coordinate,labelBox,firstBox,secondBox,ratioBox,ratioDBox,
    SameZero.PJ.Reference.sinBox,SameZero.PJ.Reference.cosBox,
    SameZero.PJ.Reference.dBox,SameZero.PJ.Reference.dUBox,SameZero.PJ.Reference.aBox,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.cube,Interval.div,Interval.inv,HighOrderTaylor.S17,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    PLabel,JLabel,LLabel,Q0])

private lemma r62_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by
  dsimp [U,ShortOuterOne.SameContact.arc]; ring
private lemma r62_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r62_mpr_lo r62_shifted_eq (congrArg _ r62_shifted_eq) _
private lemma r62_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r62_mpr_hi r62_shifted_eq (congrArg _ r62_shifted_eq) _
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
  norm_num [r62_rootAt_lo,r62_rootAt_hi,rootThree,rootStep,valueAt,firstAt,secondAt,plusBox,
    speedBox,r62_shifted_lo,r62_shifted_hi,radicand,r62_coordinate_lo,r62_coordinate_hi,
    r62_labelBox_lo,r62_labelBox_hi,firstBox,secondBox,ratioBox,ratioDBox,
    SameZero.PJ.Reference.sinBox,SameZero.PJ.Reference.cosBox,
    SameZero.PJ.Reference.dBox,SameZero.PJ.Reference.aBox,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.cube,Interval.div,Interval.inv,HighOrderTaylor.S17,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    PLabel,JLabel,LLabel,Q0])

lemma P_708 : PLabel.d1 (177/250)<(907/1000:ℝ) := by
  have h := (firstAt PLabel (177/250) (by norm_num)).mem.2
  have hr : (firstAt PLabel (177/250) (by norm_num)).hi<(907/1000:ℝ) := by r62_arith
  exact h.trans_lt hr
lemma P_101_second : PLabel.d2 (101/1000)<(1/8:ℝ) := by
  have h := (secondAt PLabel (101/1000) (by norm_num)).mem.2
  have hr : (secondAt PLabel (101/1000) (by norm_num)).hi<(1/8:ℝ) := by r62_arith
  exact h.trans_lt hr
lemma J_35 : JLabel.d1 (7/20)<(947/1000:ℝ) := by
  have h := (firstAt JLabel (7/20) (by norm_num)).mem.2
  have hr : (firstAt JLabel (7/20) (by norm_num)).hi<(947/1000:ℝ) := by r62_arith
  exact h.trans_lt hr
lemma J_501 : (437/500:ℝ)<JLabel.d1 (501/1000) ∧
    -(257/500:ℝ)<JLabel.d2 (501/1000) := by
  have h := (firstAt JLabel (501/1000) (by norm_num)).mem.1
  have k := (secondAt JLabel (501/1000) (by norm_num)).mem.1
  have hr : (437/500:ℝ)<(firstAt JLabel (501/1000) (by norm_num)).lo := by r62_arith
  have kr : -(257/500:ℝ)<(secondAt JLabel (501/1000) (by norm_num)).lo := by r62_arith
  exact ⟨hr.trans_le h,kr.trans_le k⟩
lemma J_293 : JLabel.d1 (293/1000)<(243/250:ℝ) := by
  have h := (firstAt JLabel (293/1000) (by norm_num)).mem.2
  have hr : (firstAt JLabel (293/1000) (by norm_num)).hi<(243/250:ℝ) := by r62_arith
  exact h.trans_lt hr

lemma plus_references : plus 0 (3/10)<(177/250:ℝ) ∧
    (7/20:ℝ)<plus (1/5) (1/2) ∧ plus 0 (1/2)<(501/1000:ℝ) ∧
      (1/10:ℝ)<plus (3/10) (7/10) ∧ (1/5:ℝ)<plus (3/20) (7/10) ∧
        plus 0 (1/4)<(19/25:ℝ) := by
  have h1 := (plusBox 0 (3/10) (by norm_num) (by norm_num)).mem
  have h2 := (plusBox (1/5) (1/2) (by norm_num) (by norm_num)).mem
  have h3 := (plusBox 0 (1/2) (by norm_num) (by norm_num)).mem
  have h4 := (plusBox (3/10) (7/10) (by norm_num) (by norm_num)).mem
  have h5 := (plusBox (3/20) (7/10) (by norm_num) (by norm_num)).mem
  have h6 := (plusBox 0 (1/4) (by norm_num) (by norm_num)).mem
  have r1 : (plusBox 0 (3/10) (by norm_num) (by norm_num)).hi<(177/250:ℝ) := by r62_arith
  have r2 : (7/20:ℝ)<(plusBox (1/5) (1/2) (by norm_num) (by norm_num)).lo := by r62_arith
  have r3 : (plusBox 0 (1/2) (by norm_num) (by norm_num)).hi<(501/1000:ℝ) := by r62_arith
  have r4 : (1/10:ℝ)<(plusBox (3/10) (7/10) (by norm_num) (by norm_num)).lo := by r62_arith
  have r5 : (1/5:ℝ)<(plusBox (3/20) (7/10) (by norm_num) (by norm_num)).lo := by r62_arith
  have r6 : (plusBox 0 (1/4) (by norm_num) (by norm_num)).hi<(19/25:ℝ) := by r62_arith
  exact ⟨h1.2.trans_lt r1,r2.trans_le h2.1,h3.2.trans_lt r3,
    r4.trans_le h4.1,r5.trans_le h5.1,h6.2.trans_lt r6⟩

lemma mass_references :
    Q0-2*(ShortOuterOne.SameContact.arc 0)<(1043/1000:ℝ)^2 ∧
    Q0-2*(ShortOuterOne.SameContact.arc (1/5)+1/5)<(903/1000:ℝ)^2 ∧
    Q0-2*(ShortOuterOne.SameContact.arc (3/20)+3/20)<(47/50:ℝ)^2 ∧
    Q0-2*(ShortOuterOne.SameContact.arc (3/10)+3/10)<(21/25:ℝ)^2 := by
  have h0 := (rootAt 0 (by norm_num)).mem
  have h1 := (rootAt (1/5) (by norm_num)).mem
  have h2 := (rootAt (3/20) (by norm_num)).mem
  have h3 := (rootAt (3/10) (by norm_num)).mem
  have r0 : Q0-2*((rootAt 0 (by norm_num)).lo-1/2)<(1043/1000:ℝ)^2 := by r62_arith
  have r1 : Q0-2*((rootAt (1/5) (by norm_num)).lo-1/2+1/5)<(903/1000:ℝ)^2 := by r62_arith
  have r2 : Q0-2*((rootAt (3/20) (by norm_num)).lo-1/2+3/20)<(47/50:ℝ)^2 := by r62_arith
  have r3 : Q0-2*((rootAt (3/10) (by norm_num)).lo-1/2+3/10)<(21/25:ℝ)^2 := by r62_arith
  dsimp [U] at h0 h1 h2 h3
  exact ⟨by linarith [h0.1],by linarith [h1.1],by linarith [h2.1],by linarith [h3.1]⟩

lemma zero_speed_references :
    (973/1000)*((183/200)*Real.cos (3/10)+(1/2)*Real.sin (3/10))<(1:ℝ) ∧
      (51/50:ℝ)<plusSpeed 0 (1/2) ∧ (51/50:ℝ)<plusSpeed 0 (7/10) ∧
        JLabel.d1 (plus 0 (7/10))*plusSpeed 0 (7/10)<(993/1000:ℝ) := by
  let T := ((cosBox (3/10) (by norm_num)).mul (Interval.point (183/200))).add
    ((sinBox (3/10) (by norm_num)).mul (Interval.point (1/2)))
  let S := plusBox 0 (7/10) (by norm_num) (by norm_num)
  have hr : 0≤(radicand S).lo := by dsimp [S]; r62_arith
  let A := shifted S (9/5) (by norm_num) hr
  have ha : 0<A.lo := by dsimp [A,S]; r62_arith
  let G := (firstBox JLabel S A ha).mul (speedBox 0 (7/10) (by norm_num) (by norm_num))
  have hT : (973/1000)*T.hi<(1:ℝ) := by dsimp [T]; r62_arith
  have h1 : (51/50:ℝ)<(speedBox 0 (1/2) (by norm_num) (by norm_num)).lo := by r62_arith
  have h2 : (51/50:ℝ)<(speedBox 0 (7/10) (by norm_num) (by norm_num)).lo := by r62_arith
  have hG : G.hi<(993/1000:ℝ) := by dsimp [G,A,S]; r62_arith
  refine ⟨?_,h1.trans_le (speedBox 0 (1/2) (by norm_num) (by norm_num)).mem.1,
    h2.trans_le (speedBox 0 (7/10) (by norm_num) (by norm_num)).mem.1,G.mem.2.trans_lt hG⟩
  have hh := T.mem.2
  nlinarith

end SquaresInCircles.Eight.SecondWord.OppositeZero.Reference
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.PositivePJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma mass_monotone : MonotoneOn (fun B => arc B+B) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add
      (hasDerivAt_id B)).continuousAt.continuousWithinAt)
    (fun B hB => (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain (Ioo_subset_Icc_self hB))).add
      (hasDerivAt_id B))
    (fun B hB => by linarith [(outer_ratio_bounds (Ioo_subset_Icc_self hB)).2.1])

lemma speed_bound {B x t M : ℝ} (hB : B∈Icc 0 outerDiagonal) (_hx : x∈Icc 0 (7/10))
    (ht : t∈Icc 0 outerDiagonal) (hBt : t≤B) (hM : 0<M)
    (hm : Q0-2*(arc t+t)<M^2) : plusSpeed B x<M := by
  have hh := mass_monotone ht hB hBt
  have hn := plus_norm hB x
  nlinarith [sq_nonneg (plus B x-1/2)]
lemma speed_upper {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    plusSpeed B x<(1043/1000:ℝ) :=
  speed_bound hB hx outer_zero_mem hB.1 (by norm_num)
    (by simpa using Reference.mass_references.1)
lemma speed_fifth {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10))
    (hBt : 1/5≤B) : plusSpeed B x<(903/1000:ℝ) :=
  speed_bound hB hx (Asymmetric.rational_outer_mem (by norm_num)) hBt (by norm_num)
    Reference.mass_references.2.1

lemma P_early {B x : ℝ} (hd : PlusDomain B x) (hx : x≤3/10) : 0<plusFirst PLabel B x := by
  let f : ℝ→ℝ := fun t => (183/200)*Real.cos t+(1/2)*Real.sin t
  have hm : MonotoneOn f (Icc 0 (3/10)) :=
    monoOn_of_hasDeriv_nonneg (d := fun t => (183/200)*(-Real.sin t)+(1/2)*Real.cos t)
      (by dsimp only [f]; fun_prop)
      (fun t _ => ((Real.hasDerivAt_cos t).const_mul (183/200)).add
          ((Real.hasDerivAt_sin t).const_mul (1/2)))
      (fun t ht => by
        have hs := Real.sin_le ht.1.le
        have hc := Real.one_sub_sq_div_two_le_cos (x := t)
        have ht2 : t^2≤(3/10)*t := by nlinarith [ht.1,ht.2]
        linarith [ht.2])
  have hspeed : plusSpeed B x≤f x := by
    have ha := outer_bounds (ShortOuterOne.SameContact.arc_state hd.1)
    have ht := positive_trig hd.2.1
    have h1 := mul_le_mul_of_nonneg_right
      (show arc B-1/2≤(183/200:ℝ) by linarith [ha.2.1,outer_endpoint_bounds.2.1])
        (by linarith [ht.1] : 0≤Real.cos x)
    have h2 := mul_le_mul_of_nonneg_right
      (show -(B-1/2)≤(1/2:ℝ) by linarith [hd.1.1]) ht.2.2.1
    dsimp [plusSpeed,f]
    linarith
  have hupper := hspeed.trans (hm ⟨hd.2.1.1,hx⟩ (by norm_num) hx)
  have hp := (P_first_bounds hd.2.2).2
  have hpos := (positive_data hd.1 hd.2.1).1
  have hprod := mul_lt_mul_of_pos_right hp hpos
  have hmul := mul_le_mul_of_nonneg_left hupper (by norm_num : (0:ℝ)≤973/1000)
  have href := Reference.zero_speed_references.1
  dsimp [f] at hmul
  dsimp [plusFirst]
  linarith

lemma P_late {B x : ℝ} (hd : PlusDomain B x) (hx : 3/10≤x) : 0<plusFirst PLabel B x := by
  have h1 := plus_target_antitone hd.2.1 outer_zero_mem hd.1 hd.1.1
  have h2 := plus_angle_antitone outer_zero_mem
    (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num) hd.2.1 hx
  have hb : plus B x<177/250 := by linarith [Reference.plus_references.1]
  have hP := P_first_monotone hd.2.2 (Asymmetric.rational_outer_mem (by norm_num)) hb.le
  have hp : PLabel.d1 (plus B x)<907/1000 := hP.trans_lt Reference.P_708
  have hv := speed_upper hd.1 hd.2.1
  have hh := mul_lt_mul hp hv.le (positive_data hd.1 hd.2.1).1 (by norm_num)
  dsimp [plusFirst]
  norm_num at hh
  linarith

theorem P_positive {B x : ℝ} (hd : PlusDomain B x) : 0<plusFirst PLabel B x := by
  rcases le_total x (3/10) with hx | hx
  · exact P_early hd hx
  · exact P_late hd hx

lemma J_early {B x : ℝ} (hd : PlusDomain B x) (hx : x≤1/2) : 0<plusFirst JLabel B x := by
  by_cases hB : 1/5≤B
  · have hJ := (J_first_bounds hd.2.2).2
    have hv := speed_fifth hd.1 hd.2.1 hB
    have hh := mul_lt_mul hJ hv.le (positive_data hd.1 hd.2.1).1 (by norm_num)
    norm_num at hh
    dsimp [plusFirst]
    linarith
  · have hB' : B≤1/5 := le_of_not_ge hB
    have h1 := plus_target_antitone hd.2.1 hd.1
      (Asymmetric.rational_outer_mem (by norm_num : (1/5:ℝ)∈Icc 0 (899/1000))) hB'
    have h2 := plus_angle_antitone
      (Asymmetric.rational_outer_mem (by norm_num : (1/5:ℝ)∈Icc 0 (899/1000)))
      hd.2.1 (by norm_num : (1/2:ℝ)∈Icc 0 (7/10)) hx
    have hb : 7/20<plus B x := by linarith [Reference.plus_references.2.1]
    have hJ := (J_first_antitone (Asymmetric.rational_outer_mem (by norm_num)) hd.2.2
      hb.le).trans_lt Reference.J_35
    have hh := mul_lt_mul hJ (speed_upper hd.1 hd.2.1).le (positive_data hd.1 hd.2.1).1
      (by norm_num)
    norm_num at hh
    dsimp [plusFirst]
    linarith

end SquaresInCircles.Eight.SecondWord.OppositeZero.PositivePJ
end
end
end
