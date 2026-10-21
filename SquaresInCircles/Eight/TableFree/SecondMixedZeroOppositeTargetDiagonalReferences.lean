module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetShape

/-!
# The negative-target diagonal references in §§8–10

Uncompiled source draft.  The only angles are the written cap `.44152`,
the initial L cut `.3`, and its single tangent reference `.3832`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.DiagonalReferences
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

lemma J_cap : (9353/10000:ℝ)<H 0 cap := by
  let V := HBox 0 cap (by norm_num [cap]) capU
  have hv : (9353/10000:ℝ)<V.lo := by dsimp [V,capU]; diagonal_reference
  exact hv.trans_le V.mem.1

lemma P_cap : (79/10000:ℝ)<H₂ 1 cap ∧ H₁ 1 cap<-(11/250:ℝ) ∧
    (89779/100000:ℝ)<H 1 cap := by
  have hu : 0<capU.lo := by dsimp [capU]; diagonal_reference
  let V := HBox 1 cap (by norm_num [cap]) capU
  let D := H₁Box 1 cap (by norm_num [cap]) capU hu
  let E := H₂Box 1 cap (by norm_num [cap]) capU hu
  have hv : (89779/100000:ℝ)<V.lo := by dsimp [V,capU]; diagonal_reference
  have hd : D.hi<-(11/250:ℝ) := by dsimp [D,capU]; diagonal_reference
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
  have hu : 0<minimumU.lo := by dsimp [minimumU]; diagonal_reference
  let V := HBox 2 (479/1250) (by norm_num) minimumU
  let D := H₁Box 2 (479/1250) (by norm_num) minimumU hu
  have hv : (8977797/10000000:ℝ)<V.lo := by dsimp [V,minimumU]; diagonal_reference
  have hl : -(1/12500:ℝ)<D.lo := by dsimp [D,minimumU]; diagonal_reference
  have hu : D.hi<(1/12500:ℝ) := by dsimp [D,minimumU]; diagonal_reference
  exact ⟨hv.trans_le V.mem.1,abs_lt.mpr ⟨hl.trans_le D.mem.1,D.mem.2.trans_lt hu⟩⟩

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.DiagonalReferences
