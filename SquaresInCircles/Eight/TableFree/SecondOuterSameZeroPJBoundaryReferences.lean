module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJDiagonalData
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoSourceRatio

/-!
# The three named P/J boundary references

Uncompiled source draft.  Every enclosure below carries the actual
trigonometric or radical expression.  Only the named angles .10726,
.18909, .7 and the named target .34621 are evaluated; these are the
reference points in the hand proof, not a subdivision of any domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ.Reference
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

def dBox : Interval outerDiagonal := Interval.of_bounds ⟨diagonal_fine.1.le,diagonal_fine.2.le⟩
def dUBox : Interval (U outerDiagonal) := by
  rw [U,ShortOuterOne.SameContact.arc_diagonal]
  exact dBox.add (Interval.point (1/2))
def aBox : Interval outerAxial := Interval.of_bounds
  ⟨ShortOuterZero.fine_axial_bounds.1.le,ShortOuterZero.fine_axial_bounds.2.le⟩
def sinBox (x : ℝ) (hx : 0≤x) : Interval (Real.sin x) :=
  Interval.of_bounds ⟨HighOrderTaylor.S15_le_sin hx,HighOrderTaylor.sin_le_S17 hx⟩
def cosBox (x : ℝ) (hx : 0≤x) : Interval (Real.cos x) :=
  Interval.of_bounds ⟨HighOrderTaylor.C18_le_cos hx,HighOrderTaylor.cos_le_C16 hx⟩
def zeroSourceBox (x : ℝ) (hx : 0≤x) : Interval (b 0 x) := by
  have hh := ((Interval.point (1/2)).add ((Interval.point (1/2)).mul (cosBox x hx))).sub
    ((aBox.sub (Interval.point (1/2))).mul (sinBox x hx))
  simpa [b,ShortOuterOne.SameContact.arc_zero] using hh

def ZBox (x : ℝ) (hx : 0≤x) : Interval (Diagonal.Z x) :=
  (dBox.sub (Interval.point (1/2))).sub (sinBox x hx)
def YRadBox (x : ℝ) (hx : 0≤x) : Interval (Q0-(Diagonal.Z x)^2) :=
  (Interval.point Q0).sub (ZBox x hx).square
def YBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo) : Interval (Diagonal.Y x) :=
  rootThree (YRadBox x hx) 2 (by norm_num) hr
def UBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo) : Interval (Diagonal.horizontal x) :=
  ((YBox x hx hr).mul (cosBox x hx)).sub ((ZBox x hx).mul (sinBox x hx))
def VBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo) : Interval (Diagonal.vertical x) :=
  ((YBox x hx hr).mul (sinBox x hx)).add ((ZBox x hx).mul (cosBox x hx))
def BBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo) : Interval (Diagonal.height x) :=
  (VBox x hx hr).sub (Interval.point (1/2))
def speedBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo)
    (hy : 0<(YBox x hx hr).lo) : Interval (Diagonal.speed x) :=
  (UBox x hx hr).mul ((Interval.point 1).sub ((cosBox x hx).div (YBox x hx hr) hy))

private macro "reference_arithmetic" : tactic => `(tactic|
  norm_num [dBox,dUBox,aBox,sinBox,cosBox,zeroSourceBox,ZBox,YRadBox,YBox,UBox,VBox,BBox,
    speedBox,rootThree,rootStep,shifted,radicand,coordinate,labelBox,firstBox,ratioBox,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.cube,Interval.div,Interval.inv,HighOrderTaylor.S17,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    PLabel,JLabel,Q0,Diagonal.start])

lemma zero_start : outerDiagonal<b 0 Diagonal.start := by
  have hh := (zeroSourceBox Diagonal.start (by norm_num [Diagonal.start])).mem
  have hlo : (899214066:ℝ)/1000000000 <
      (zeroSourceBox Diagonal.start (by norm_num [Diagonal.start])).lo := by reference_arithmetic
  linarith [hh.1,diagonal_fine.2]

lemma zero_start_cost : (1797/2000:ℝ)<Diagonal.start+PLabel.outer outerDiagonal-JLabel.outer 0 := by
  have hP := (labelBox PLabel dBox dUBox).mem
  have hp : (7909016/10000000:ℝ)<(labelBox PLabel dBox dUBox).lo := by reference_arithmetic
  have hJ := J_zero
  change JLabel.outer 0= -(13/50000)*outerAxial at hJ
  rw [hJ]
  norm_num [Diagonal.start] at *
  linarith [hP.1,ShortOuterZero.fine_axial_bounds.1]

lemma diagonal_endpoint_bounds :
    (33/20:ℝ)<Diagonal.horizontal (7/10) ∧
      Diagonal.horizontal Diagonal.start<383/200 ∧
      Diagonal.height (7/10)<outerDiagonal := by
  have hr0 : 0≤(YRadBox Diagonal.start (by norm_num [Diagonal.start])).lo := by reference_arithmetic
  have hr1 : 0≤(YRadBox (7/10) (by norm_num)).lo := by reference_arithmetic
  have h0 := (UBox Diagonal.start (by norm_num [Diagonal.start]) hr0).mem
  have h1 := (UBox (7/10) (by norm_num) hr1).mem
  have h2 := (BBox (7/10) (by norm_num) hr1).mem
  have h0' : (UBox Diagonal.start (by norm_num [Diagonal.start]) hr0).hi<383/200 := by reference_arithmetic
  have h1' : (33/20:ℝ)<(UBox (7/10) (by norm_num) hr1).lo := by reference_arithmetic
  have h2' : (BBox (7/10) (by norm_num) hr1).hi<899/1000 := by reference_arithmetic
  exact ⟨h1'.trans_le h1.1,h0.2.trans_lt h0',h2.2.trans_lt
    (h2'.trans fine_outer_endpoint_bounds.2)⟩

def diagonalReference : ℝ := 18909/100000

lemma diagonal_reference : Diagonal.Domain diagonalReference ∧
    (17955521/20000000:ℝ)<Diagonal.cost diagonalReference ∧
      |Diagonal.first diagonalReference|<(1/1000000:ℝ) := by
  let x := diagonalReference
  have hx : 0≤x := by norm_num [x,diagonalReference]
  have hr : 0≤(YRadBox x hx).lo := by dsimp [x,diagonalReference]; reference_arithmetic
  let B := BBox x hx hr
  have hrad : 0≤(radicand B).lo := by dsimp [B,x,diagonalReference]; reference_arithmetic
  let T := shifted B (19/10) (by norm_num) hrad
  have hT : 0<T.lo := by dsimp [T,B,x,diagonalReference]; reference_arithmetic
  have hY : 0<(YBox x hx hr).lo := by dsimp [x,diagonalReference]; reference_arithmetic
  let V := ((Interval.point x).add (labelBox PLabel dBox dUBox)).sub (labelBox JLabel B T)
  let D := (Interval.point 1).sub ((firstBox JLabel B T hT).mul (speedBox x hx hr hY))
  have hB : 0<B.lo := by dsimp [B,x,diagonalReference]; reference_arithmetic
  have hV : (17955521/20000000:ℝ)<V.lo := by dsimp [V,T,B,x,diagonalReference]; reference_arithmetic
  have hDl : -(1/1000000:ℝ)<D.lo := by dsimp [D,T,B,x,diagonalReference]; reference_arithmetic
  have hDu : D.hi<(1/1000000:ℝ) := by dsimp [D,T,B,x,diagonalReference]; reference_arithmetic
  refine ⟨⟨by norm_num [diagonalReference,Diagonal.start],hB.le.trans B.mem.1⟩,
    hV.trans_le V.mem.1,?_⟩
  rw [abs_lt]
  exact ⟨hDl.trans_le D.mem.1,D.mem.2.trans_lt hDu⟩

def capReference : ℝ := 34621/100000

lemma cap_reference : Domain capReference (7/10) ∧
    (22444717/25000000:ℝ)<value PLabel JLabel capReference (7/10) ∧
      |targetFirst PLabel JLabel capReference (7/10)|<(1/100000:ℝ) := by
  let T := Interval.point capReference
  have hrad : 0≤(radicand T).lo := by norm_num [radicand,T,capReference,Interval.point,Interval.add,Interval.sub,Interval.square,Interval.mul,Q0]
  let U := shifted T (9/5) (by norm_num) hrad
  have hU : 0<U.lo := by dsimp [U,T,capReference]; reference_arithmetic
  let S := sinBox (7/10) (by norm_num)
  let C := cosBox (7/10) (by norm_num)
  let B : Interval (b capReference (7/10)) :=
    ((Interval.point (1/2)).add ((T.add (Interval.point (1/2))).mul C)).sub
      ((U.sub (Interval.point 1)).mul S)
  have hbr : 0≤(radicand B).lo := by dsimp [B,U,T,S,C,capReference]; reference_arithmetic
  let A := shifted B (8/5) (by norm_num) hbr
  have hA : 0<A.lo := by dsimp [A,B,U,T,S,C,capReference]; reference_arithmetic
  let K := C.add ((ratioBox T U hU).mul S)
  let V := ((Interval.point (7/10)).add (labelBox PLabel B A)).sub (labelBox JLabel T U)
  let D := ((firstBox PLabel B A hA).mul K).sub (firstBox JLabel T U hU)
  have hb0 : 0<B.lo := by dsimp [B,U,T,S,C,capReference]; reference_arithmetic
  have hb1 : B.hi<899/1000 := by dsimp [B,U,T,S,C,capReference]; reference_arithmetic
  have hv : (22444717/25000000:ℝ)<V.lo := by dsimp [V,A,B,U,T,S,C,capReference]; reference_arithmetic
  have hdl : -(1/100000:ℝ)<D.lo := by dsimp [D,K,A,B,U,T,S,C,capReference]; reference_arithmetic
  have hdu : D.hi<(1/100000:ℝ) := by dsimp [D,K,A,B,U,T,S,C,capReference]; reference_arithmetic
  refine ⟨⟨Asymmetric.rational_outer_mem (by norm_num [capReference]),by norm_num,
    ⟨hb0.le.trans B.mem.1,(B.mem.2.trans_lt (hb1.trans fine_outer_endpoint_bounds.2)).le⟩⟩,
      hv.trans_le V.mem.1,?_⟩
  rw [abs_lt]
  exact ⟨hdl.trans_le D.mem.1,D.mem.2.trans_lt hdu⟩

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ.Reference
