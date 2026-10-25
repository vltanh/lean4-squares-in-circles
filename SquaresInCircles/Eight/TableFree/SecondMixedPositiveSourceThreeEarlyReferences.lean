module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeContact
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveEarlyPolynomial
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeReferenceAlgebra

/-!
# Exact references for the early transverse quadratic

The reference target is B=.24. Its actual radical, label and slope
determine all five harmonic coefficients of the quadratic minimum.
Every coefficient cage is proved from that fixed physical circle point.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Early
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open PositiveThree (Lower lowerAngle lower_trig)
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

def r : ℝ := 6/25
def m : ℝ := 143/100
def G (φ : ℝ) : ℝ := F r φ-(FB r φ)^2/(2*m)
def c0 : ℝ := -e+g/2-L r-g^2*(1+(ratio r)^2)/(4*m)-(LLabel.d1 r)^2/(2*m)
def cSin : ℝ := g*(1-U r)+g*LLabel.d1 r*ratio r/m
def cCos : ℝ := g*(r+1/2)+g*LLabel.d1 r/m
def cTwo : ℝ := -g^2*(1-(ratio r)^2)/(4*m)
def cMix : ℝ := -g^2*ratio r/(2*m)

lemma harmonic (φ : ℝ) : G φ=φ+c0+cSin*Real.sin φ+cCos*Real.cos φ+
    cTwo*Real.cos (2*φ)+cMix*Real.sin (2*φ) := by
  dsimp [G,F,source,FB,c0,cSin,cCos,cTwo,cMix,U,m]
  rw [Real.cos_two_mul,Real.sin_two_mul]
  linear_combination -(50/143)*g^2*(ratio r)^2*(Real.sin_sq_add_cos_sq φ)

private lemma r35_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r35_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

/-! Endpoint equations for each enclosure, used to evaluate the enclosures by rewriting
instead of unfolding the definitions (which carry their membership proofs). -/

private lemma r35_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by dsimp [U,arc]; ring
private lemma r35_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r35_mpr_lo r35_shifted_eq (congrArg _ r35_shifted_eq) _
private lemma r35_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r35_mpr_hi r35_shifted_eq (congrArg _ r35_shifted_eq) _

private lemma r35_coordinate_eq {y : ℝ} : arc y = U y-1/2 := by dsimp [U]; ring
private lemma r35_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r35_mpr_lo r35_coordinate_eq (congrArg _ r35_coordinate_eq) _
private lemma r35_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r35_mpr_hi r35_coordinate_eq (congrArg _ r35_coordinate_eq) _

private lemma r35_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(arc y)+H.q*y+H.r*y^2+H.s*(arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r35_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r35_mpr_lo (r35_label_eq H) (congrArg _ (r35_label_eq H)) _
private lemma r35_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r35_mpr_hi (r35_label_eq H) (congrArg _ (r35_label_eq H)) _

private lemma r35_ratioBox_lo {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioBox Y X hX).lo = ((Y.add (Interval.point (1/2))).div X hX).lo := rfl
private lemma r35_ratioBox_hi {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioBox Y X hX).hi = ((Y.add (Interval.point (1/2))).div X hX).hi := rfl
private lemma r35_ratioDBox_lo {y : ℝ} (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDBox X hX).lo = ((Interval.point Q0).div X.cube (Interval.cube_lo_pos hX)).lo := rfl
private lemma r35_ratioDBox_hi {y : ℝ} (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDBox X hX).hi = ((Interval.point Q0).div X.cube (Interval.cube_lo_pos hX)).hi := rfl
private lemma r35_firstBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) :
    (firstBox H Y X hX).lo = ((((Interval.point H.q).add ((Interval.point (2*H.r)).mul Y)).add
      ((Interval.point H.s).mul (coordinate X))).sub
        (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioBox Y X hX))).lo := rfl
private lemma r35_firstBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) :
    (firstBox H Y X hX).hi = ((((Interval.point H.q).add ((Interval.point (2*H.r)).mul Y)).add
      ((Interval.point H.s).mul (coordinate X))).sub
        (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioBox Y X hX))).hi := rfl
private lemma r35_secondBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) :
    (secondBox H Y X hX).lo = (((Interval.point (2*H.r)).sub
      ((Interval.point (2*H.s)).mul (ratioBox Y X hX))).sub
        (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDBox X hX))).lo := rfl
private lemma r35_secondBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) :
    (secondBox H Y X hX).hi = (((Interval.point (2*H.r)).sub
      ((Interval.point (2*H.s)).mul (ratioBox Y X hX))).sub
        (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDBox X hX))).hi := rfl

private lemma r35_rootStep_lo {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootStep X s hs hX).lo = X.lo/((s+X.hi/s)/2) := rfl
private lemma r35_rootStep_hi {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootStep X s hs hX).hi = (s+X.hi/s)/2 := rfl
private lemma r35_rootThree_lo {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootThree X s hs hX).lo = (rootStep X _
      (rootStep_hi_pos X _ (rootStep_hi_pos X s hs hX) hX) hX).lo := rfl
private lemma r35_rootThree_hi {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootThree X s hs hX).hi = (rootStep X _
      (rootStep_hi_pos X _ (rootStep_hi_pos X s hs hX) hX) hX).hi := rfl
private lemma r35_radicand_lo {y : ℝ} (Y : Interval y) :
    (radicand Y).lo = ((Interval.point Q0).sub ((Y.add (Interval.point (1/2))).square)).lo := rfl
private lemma r35_radicand_hi {y : ℝ} (Y : Interval y) :
    (radicand Y).hi = ((Interval.point Q0).sub ((Y.add (Interval.point (1/2))).square)).hi := rfl

private lemma r35_mul_lo {x y : ℝ} (X : Interval x) (Y : Interval y) :
    (X.mul Y).lo = min (min (X.lo*Y.lo) (X.lo*Y.hi)) (min (X.hi*Y.lo) (X.hi*Y.hi)) := rfl
private lemma r35_mul_hi {x y : ℝ} (X : Interval x) (Y : Interval y) :
    (X.mul Y).hi = max (max (X.lo*Y.lo) (X.lo*Y.hi)) (max (X.hi*Y.lo) (X.hi*Y.hi)) := rfl
private lemma r35_square_lo {x : ℝ} (X : Interval x) : X.square.lo = (X.mul X).lo := rfl
private lemma r35_square_hi {x : ℝ} (X : Interval x) : X.square.hi = (X.mul X).hi := rfl
private lemma r35_cube_lo {x : ℝ} (X : Interval x) : X.cube.lo = (X.square.mul X).lo := rfl
private lemma r35_cube_hi {x : ℝ} (X : Interval x) : X.cube.hi = (X.square.mul X).hi := rfl
private lemma r35_inv_lo {x : ℝ} (X : Interval x) (h : 0<X.lo) : (X.inv h).lo = 1/X.hi := rfl
private lemma r35_inv_hi {x : ℝ} (X : Interval x) (h : 0<X.lo) : (X.inv h).hi = 1/X.lo := rfl
private lemma r35_div_lo {x y : ℝ} (X : Interval x) (Y : Interval y) (h : 0<Y.lo) :
    (X.div Y h).lo = (X.mul (Y.inv h)).lo := rfl
private lemma r35_div_hi {x y : ℝ} (X : Interval x) (Y : Interval y) (h : 0<Y.lo) :
    (X.div Y h).hi = (X.mul (Y.inv h)).hi := rfl
private lemma r35_add_lo {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.add Y).lo = X.lo+Y.lo := rfl
private lemma r35_add_hi {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.add Y).hi = X.hi+Y.hi := rfl
private lemma r35_sub_lo {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.sub Y).lo = X.lo-Y.hi := rfl
private lemma r35_sub_hi {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.sub Y).hi = X.hi-Y.lo := rfl
private lemma r35_point_lo (x : ℝ) : (Interval.point x).lo = x := rfl
private lemma r35_point_hi (x : ℝ) : (Interval.point x).hi = x := rfl

local macro "expand_reference" : tactic => `(tactic|
  simp only [r35_shifted_lo,r35_shifted_hi,r35_coordinate_lo,r35_coordinate_hi,r35_labelBox_lo,
    r35_labelBox_hi,r35_ratioBox_lo,r35_ratioBox_hi,r35_ratioDBox_lo,r35_ratioDBox_hi,
    r35_firstBox_lo,r35_firstBox_hi,r35_secondBox_lo,r35_secondBox_hi,
    r35_radicand_lo,r35_radicand_hi,r35_rootThree_lo,r35_rootThree_hi,r35_rootStep_lo,
    r35_rootStep_hi,r35_mul_lo,r35_mul_hi,r35_square_lo,r35_square_hi,r35_cube_lo,r35_cube_hi,
    r35_inv_lo,r35_inv_hi,r35_div_lo,r35_div_hi,r35_add_lo,r35_add_hi,r35_sub_lo,r35_sub_hi,
    r35_point_lo,r35_point_hi])

local macro "eval_reference" : tactic => `(tactic|
  norm_num [r,m,g,e,EdgeThreeAligned.gp,EdgeThreeAligned.ep,LLabel,Q0])

local macro "coefficient_reference" : tactic => `(tactic|
  (expand_reference; eval_reference))

lemma coefficients :
    -(204013/1000000:ℝ)<c0 ∧ -(159591/250000:ℝ)<cSin ∧
    (168423/125000:ℝ)<cCos ∧ cTwo< -(79539/500000:ℝ) ∧
    -(153197/1000000:ℝ)<cMix := by
  let X := shifted (Interval.point r) (9/5) (by norm_num) (by coefficient_reference)
  have hXlo : X.lo=266866018209/145414339285 := by dsimp only [X]; coefficient_reference
  have hXhi : X.hi=29082867857/15847150725 := by dsimp only [X]; coefficient_reference
  have hX : 0<X.lo := by rw [hXlo]; norm_num
  let R := ratioBox (Interval.point r) X hX
  let J := labelBox LLabel (Interval.point r) X
  let D := firstBox LLabel (Interval.point r) X hX
  let C₀ := (((Interval.point (-e+g/2)).sub J).sub
    (((Interval.point (g^2)).mul ((Interval.point 1).add R.square)).div
      (Interval.point (4*m)) (by norm_num [Interval.point,m]))).sub
        (D.square.div (Interval.point (2*m)) (by norm_num [Interval.point,m]))
  let C₁ := ((Interval.point g).mul ((Interval.point 1).sub X)).add
    ((((Interval.point g).mul D).mul R).div (Interval.point m) (by norm_num [Interval.point,m]))
  let C₂ := (Interval.point (g*(r+1/2))).add
    (((Interval.point g).mul D).div (Interval.point m) (by norm_num [Interval.point,m]))
  let C₃ := ((Interval.point (-g^2)).mul ((Interval.point 1).sub R.square)).div
    (Interval.point (4*m)) (by norm_num [Interval.point,m])
  let C₄ := ((Interval.point (-g^2)).mul R).div
    (Interval.point (2*m)) (by norm_num [Interval.point,m])
  have h0 : -(204013/1000000:ℝ)<C₀.lo := by
    dsimp only [C₀,D,J,R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h1 : -(159591/250000:ℝ)<C₁.lo := by
    dsimp only [C₁,D,R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h2 : (168423/125000:ℝ)<C₂.lo := by
    dsimp only [C₂,D]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h3 : C₃.hi< -(79539/500000:ℝ) := by
    dsimp only [C₃,R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h4 : -(153197/1000000:ℝ)<C₄.lo := by
    dsimp only [C₄,R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  exact ⟨h0.trans_le C₀.mem.1,h1.trans_le C₁.mem.1,h2.trans_le C₂.mem.1,
    C₃.mem.2.trans_lt h3,h4.trans_le C₄.mem.1⟩

lemma trig_13 : (9635581/10000000:ℝ)<Real.sin (13/10) ∧
    (2674988/10000000:ℝ)<Real.cos (13/10) := by
  have hs := HighOrderTaylor.S15_le_sin (x := (13/10:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (13/10:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma reference_31 :
    (2243/5000:ℝ)<ratio (31/100) ∧ (133/200:ℝ)<ratioD (31/100) ∧
    LLabel.d1 (31/100)<(1793/2500:ℝ) ∧ LLabel.d2 (31/100)< -(113/125:ℝ) := by
  let X := shifted (Interval.point (31/100:ℝ)) (9/5) (by norm_num) (by coefficient_reference)
  have hXlo : X.lo=25455775424175432/14099731360386005 := by dsimp only [X]; coefficient_reference
  have hXhi : X.hi=2819946272077201/1561943575651200 := by dsimp only [X]; coefficient_reference
  have hX : 0<X.lo := by rw [hXlo]; norm_num
  let R := ratioBox (Interval.point (31/100:ℝ)) X hX
  let R₁ := ratioDBox X hX
  let D := firstBox LLabel (Interval.point (31/100:ℝ)) X hX
  let D₁ := secondBox LLabel (Interval.point (31/100:ℝ)) X hX
  have h0 : (2243/5000:ℝ)<R.lo := by
    dsimp only [R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h1 : (133/200:ℝ)<R₁.lo := by
    dsimp only [R₁]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h2 : D.hi<(1793/2500:ℝ) := by
    dsimp only [D]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h3 : D₁.hi< -(113/125:ℝ) := by
    dsimp only [D₁]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  exact ⟨h0.trans_le R.mem.1,h1.trans_le R₁.mem.1,D.mem.2.trans_lt h2,D₁.mem.2.trans_lt h3⟩

lemma derivative_references : 0<FB (31/100) (13/10) ∧ 0<FB outerDiagonal (13/10) := by
  have hh := reference_31
  have ht := trig_13
  have hp := mul_le_mul hh.1.le ht.1.le (by norm_num : (0:ℝ)≤9635581/10000000)
    (by linarith [hh.1] : 0≤ratio (31/100))
  constructor
  · dsimp [FB,g,EdgeThreeAligned.gp]
    nlinarith [hh.2.2.1,ht.2]
  · rw [FB,ratio_diagonal,L_first_diagonal]
    dsimp [g,EdgeThreeAligned.gp]
    linarith [ht.1,ht.2,fine_outer_endpoint_bounds.2]

lemma curvature_reference : m<g*ratioD (31/100)*(19121/25000)-LLabel.d2 (31/100) := by
  have hh := reference_31
  dsimp [m,g,EdgeThreeAligned.gp]
  linarith [hh.2.1,hh.2.2.2]

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Early
