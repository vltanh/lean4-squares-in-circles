module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetReferenceAlgebra

/-!
# Eight squares: the negative-target diagonal references in §§8–10

The only angles are the written cap `.44152`,
the initial L cut `.3`, and its single tangent reference `.3832`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.DiagonalReferences
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra Target.ReferenceAlgebra

local macro "diagonal_reference" : tactic => `(tactic|
  norm_num [coreBox,outerBox,sinBox,cosBox,diagonalBox,speedBox,HBox,H₁Box,H₂Box,
    labelBox,firstBox,secondBox,thirdBox,ratioBox,ratioDBox,ratioDDBox,
    coordinate,shifted,radicand,rootThree,rootStep,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    F,c,g,PLabel,JLabel,LLabel,Q0,cap])

def capU : Interval (U (diagonal cap)) :=
  shifted (diagonalBox cap (by norm_num [cap])) (7/5) (by norm_num) (by diagonal_reference)
def threeU : Interval (U (diagonal (3/10))) :=
  shifted (diagonalBox (3/10) (by norm_num)) (3/2) (by norm_num) (by diagonal_reference)
def minimumU : Interval (U (diagonal (479/1250))) :=
  shifted (diagonalBox (479/1250) (by norm_num)) (3/2) (by norm_num) (by diagonal_reference)

private lemma r96_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r96_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r96_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by
  dsimp [U,ShortOuterOne.SameContact.arc]; ring
private lemma r96_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r96_mpr_lo r96_shifted_eq (congrArg _ r96_shifted_eq) _
private lemma r96_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r96_mpr_hi r96_shifted_eq (congrArg _ r96_shifted_eq) _

private lemma r96_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r96_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r96_mpr_lo r96_coordinate_eq (congrArg _ r96_coordinate_eq) _
private lemma r96_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r96_mpr_hi r96_coordinate_eq (congrArg _ r96_coordinate_eq) _

private lemma r96_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r96_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r96_mpr_lo (r96_label_eq H) (congrArg _ (r96_label_eq H)) _
private lemma r96_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r96_mpr_hi (r96_label_eq H) (congrArg _ (r96_label_eq H)) _

attribute [local simp ↓] r96_shifted_lo r96_shifted_hi r96_coordinate_lo r96_coordinate_hi
  r96_labelBox_lo r96_labelBox_hi

lemma J_cap : (9353/10000:ℝ)<H 0 cap := by
  let V := HBox 0 cap (by norm_num [cap]) capU
  have hv : (9353/10000:ℝ)<V.lo := by dsimp [V,capU]; diagonal_reference
  exact hv.trans_le V.mem.1

lemma P_cap : (79/10000:ℝ)<H₂ 1 cap ∧ H₁ 1 cap< -(11/250:ℝ) ∧
    (89779/100000:ℝ)<H 1 cap := by
  have hu : 0<capU.lo := by dsimp [capU]; diagonal_reference
  let V := HBox 1 cap (by norm_num [cap]) capU
  let D := H₁Box 1 cap (by norm_num [cap]) capU hu
  let E := H₂Box 1 cap (by norm_num [cap]) capU hu
  have hv : (89779/100000:ℝ)<V.lo := by dsimp [V,capU]; diagonal_reference
  have hd : D.hi< -(11/250:ℝ) := by dsimp [D,capU]; diagonal_reference
  have he : (79/10000:ℝ)<E.lo := by dsimp [E,capU]; diagonal_reference
  exact ⟨he.trans_le E.mem.1,D.mem.2.trans_lt hd,hv.trans_le V.mem.1⟩

lemma L_three : (4523/5000:ℝ)<H 2 (3/10) ∧
    LLabel.d1 (diagonal (3/10))<41/50 ∧
    (169/100:ℝ)<LLabel.d2 (diagonal (3/10)) ∧
    (3/4:ℝ)<diagonal (3/10) := by
  have hu : 0<threeU.lo := by dsimp [threeU]; diagonal_reference
  let Y := diagonalBox (3/10) (by norm_num)
  let V := HBox 2 (3/10) (by norm_num) threeU
  let D := firstBox LLabel Y threeU hu
  let E := secondBox LLabel Y threeU hu
  have hv : (4523/5000:ℝ)<V.lo := by dsimp [V,threeU]; diagonal_reference
  have hd : D.hi<(41/50:ℝ) := by dsimp [D,Y,threeU]; diagonal_reference
  have he : (169/100:ℝ)<E.lo := by dsimp [E,Y,threeU]; diagonal_reference
  have hy : (3/4:ℝ)<Y.lo := by dsimp [Y]; diagonal_reference
  exact ⟨hv.trans_le V.mem.1,D.mem.2.trans_lt hd,he.trans_le E.mem.1,hy.trans_le Y.mem.1⟩

lemma L_minimum : (8977797/10000000:ℝ)<H 2 (479/1250) ∧
    |H₁ 2 (479/1250)|<(1/12500:ℝ) := by
  have hu : 0 < minimumU.lo := by dsimp [minimumU]; diagonal_reference
  let V := HBox 2 (479/1250) (by norm_num) minimumU
  let D := H₁Box 2 (479/1250) (by norm_num) minimumU hu
  have hv : (8977797/10000000:ℝ)<V.lo := by dsimp [V,minimumU]; diagonal_reference
  have hl : -(1/12500:ℝ)<D.lo := by dsimp [D,minimumU]; diagonal_reference
  have hu : D.hi<(1/12500:ℝ) := by dsimp [D,minimumU]; diagonal_reference
  exact ⟨hv.trans_le V.mem.1,abs_lt.mpr ⟨hl.trans_le D.mem.1,D.mem.2.trans_lt hu⟩⟩

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.DiagonalReferences
