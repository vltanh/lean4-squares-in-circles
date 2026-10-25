module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroPlusDiagonal

/-!
# The two actual endpoints of the positive diagonal exit

Uncompiled source draft.  The first endpoint is aligned.  The second
is the original target-zero contact, whose angle exceeds .10726.
The original contact coordinates identify the explicit circle branch,
and concavity supplies both P/J order bounds on that complete branch.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.PlusDiagonal
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

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.PlusDiagonal
