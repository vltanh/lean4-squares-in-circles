module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameSecondaryDiagonalData

/-!
# The three named late-arc substitutions

Uncompiled transcription of the fixed comparisons in Section 4.2 of
`HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md`.
The exact circle radical is retained in every enclosure. The references
are the left event bracket, the single speed reference 0.68, and the
right endpoint 0.7; there is no subdivision of the moving arc.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal.Reference
open CommonQuarter CorePairGeometry Arithmetic
open Diagonal (Z Y horizontal vertical factor factorD)
open StationaryPrimitives (Interval)
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)
open SecondWord.OppositeThree.ReferenceAlgebra (rootThree rootStep)

def offsetBox : Interval offset := (Interval.point (1/2)).sub RoleFour.dBox
def zBox (x : ℝ) (hx : 0≤x) : Interval (Z x) := (cosBox x hx).add offsetBox
def radBox (x : ℝ) (hx : 0≤x) : Interval (Q0-(Z x)^2) :=
  (Interval.point Q0).sub (zBox x hx).square
def yBox (x : ℝ) (hx : 0≤x) (hr : 0≤(radBox x hx).lo) : Interval (Y x) :=
  rootThree (radBox x hx) 2 (by norm_num) hr
def horizontalBox (x : ℝ) (hx : 0≤x) (hr : 0≤(radBox x hx).lo) :
    Interval (horizontal x) :=
  ((yBox x hx hr).mul (cosBox x hx)).sub ((zBox x hx).mul (sinBox x hx))
def verticalBox (x : ℝ) (hx : 0≤x) (hr : 0≤(radBox x hx).lo) :
    Interval (vertical x) :=
  ((yBox x hx hr).mul (sinBox x hx)).add ((zBox x hx).mul (cosBox x hx))
def factorBox (x : ℝ) (hx : 0≤x) (hr : 0≤(radBox x hx).lo)
    (hy : 0<(yBox x hx hr).lo) : Interval (factor x) :=
  (Interval.point 1).sub ((sinBox x hx).div (yBox x hx hr) hy)
def numeratorBox (x : ℝ) (hx : 0≤x) : Interval (numerator x) :=
  ((((Interval.point (1-Q0)).add offsetBox.square).mul (cosBox x hx))).add
    (offsetBox.mul ((Interval.point 1).add (cosBox x hx).square))
def factorDBox (x : ℝ) (hx : x∈Icc 0 (7/10)) (hr : 0≤(radBox x hx.1).lo)
    (hy : 0<(yBox x hx.1 hr).lo) : Interval (factorD x) := by
  have hY : 0<Y x := hy.trans_le (yBox x hx.1 hr).mem.1
  have he : numerator x/(Y x)^3=factorD x := by
    apply (div_eq_iff (pow_ne_zero _ hY.ne')).2
    exact (numerator_identity hx).symm
  rw [←he]
  exact (numeratorBox x hx.1).div (yBox x hx.1 hr).cube (Interval.cube_lo_pos hy)
def speedBox (x : ℝ) (hx : 0≤x) (hr : 0≤(radBox x hx).lo)
    (hy : 0<(yBox x hx hr).lo) : Interval (speed x) :=
  (verticalBox x hx hr).mul (factorBox x hx hr hy)
def speedDBox (x : ℝ) (hx : x∈Icc 0 (7/10)) (hr : 0≤(radBox x hx.1).lo)
    (hy : 0<(yBox x hx.1 hr).lo) : Interval (speedD x) :=
  ((horizontalBox x hx.1 hr).mul (factorBox x hx.1 hr hy).square).add
    ((verticalBox x hx.1 hr).mul (factorDBox x hx hr hy))
def costBox (r : Row) (x : ℝ) (hx : 0≤x) (hr : 0≤(radBox x hx).lo) :
    Interval (cost r x) := by
  convert ((((((RoleFour.piBox.mul (Interval.point (1/2))).sub (Interval.point x)).add
    (Interval.point (c r))).add ((Interval.point (t r-P r)).mul RoleFour.dBox)).add
      ((Interval.point (p r)).mul ((verticalBox x hx hr).sub (Interval.point (1/2))))).sub
        ((Interval.point (q r)).mul ((horizontalBox x hx hr).sub (Interval.point (1/2))))
    using 1 <;> dsimp [cost] <;> ring

private macro "secondary_diagonal_reference" : tactic => `(tactic|
  norm_num [offsetBox,zBox,radBox,yBox,horizontalBox,verticalBox,factorBox,numeratorBox,
    factorDBox,speedBox,speedDBox,costBox,RoleFour.dBox,RoleFour.piBox,
    SecondWord.SameZero.PJ.Reference.sinBox,SecondWord.SameZero.PJ.Reference.cosBox,
    rootThree,rootStep,Interval.of_bounds,Interval.point,Interval.add,Interval.sub,
    Interval.neg,Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8,Q0,c,p,q,P,t])

lemma left_cos : Real.cos (2779/5000)<(17/20:ℝ) := by
  have hhi : (cosBox (2779/5000) (by norm_num)).hi<(17/20:ℝ) := by
    secondary_diagonal_reference
  exact (cosBox (2779/5000) (by norm_num)).mem.2.trans_lt hhi

lemma left_factor : factor (2779/5000)<(727/1000:ℝ) := by
  have hr : 0≤(radBox (2779/5000) (by norm_num)).lo := by secondary_diagonal_reference
  have hy : 0<(yBox (2779/5000) (by norm_num) hr).lo := by secondary_diagonal_reference
  have hhi : (factorBox (2779/5000) (by norm_num) hr hy).hi<(727/1000:ℝ) := by
    secondary_diagonal_reference
  exact (factorBox (2779/5000) (by norm_num) hr hy).mem.2.trans_lt hhi

lemma cap_geometry : vertical (7/10)<(1533/1000:ℝ) ∧
    (1251/1000:ℝ)<horizontal (7/10) ∧ (167/250:ℝ)<factor (7/10) ∧
    factorD (7/10)<-(93/250:ℝ) := by
  have hr : 0≤(radBox (7/10) (by norm_num)).lo := by secondary_diagonal_reference
  have hy : 0<(yBox (7/10) (by norm_num) hr).lo := by secondary_diagonal_reference
  have hv : (verticalBox (7/10) (by norm_num) hr).hi<(1533/1000:ℝ) := by
    secondary_diagonal_reference
  have hh : (1251/1000:ℝ)<(horizontalBox (7/10) (by norm_num) hr).lo := by
    secondary_diagonal_reference
  have hf : (167/250:ℝ)<(factorBox (7/10) (by norm_num) hr hy).lo := by
    secondary_diagonal_reference
  have hfd : (factorDBox (7/10) (by norm_num) hr hy).hi<-(93/250:ℝ) := by
    secondary_diagonal_reference
  exact ⟨(verticalBox (7/10) (by norm_num) hr).mem.2.trans_lt hv,
    hh.trans_le (horizontalBox (7/10) (by norm_num) hr).mem.1,
    hf.trans_le (factorBox (7/10) (by norm_num) hr hy).mem.1,
    (factorDBox (7/10) (by norm_num) hr hy).mem.2.trans_lt hfd⟩

lemma speed_reference : speed (17/25)<(41/40:ℝ) ∧ |speedD (17/25)|<(7/1000:ℝ) := by
  have hr : 0≤(radBox (17/25) (by norm_num)).lo := by secondary_diagonal_reference
  have hy : 0<(yBox (17/25) (by norm_num) hr).lo := by secondary_diagonal_reference
  have hhi : (speedBox (17/25) (by norm_num) hr hy).hi<(41/40:ℝ) := by
    secondary_diagonal_reference
  have hlo' : -(7/1000:ℝ)<(speedDBox (17/25) (by norm_num) hr hy).lo := by
    secondary_diagonal_reference
  have hhi' : (speedDBox (17/25) (by norm_num) hr hy).hi<(7/1000:ℝ) := by
    secondary_diagonal_reference
  exact ⟨(speedBox (17/25) (by norm_num) hr hy).mem.2.trans_lt hhi,
    abs_lt.2 ⟨hlo'.trans_le (speedDBox (17/25) (by norm_num) hr hy).mem.1,
      (speedDBox (17/25) (by norm_num) hr hy).mem.2.trans_lt hhi'⟩⟩

lemma final_cost (r : Row) (hr : r=1 ∨ r=2) : (8981/10000:ℝ)<cost r (7/10) := by
  have hrad : 0≤(radBox (7/10) (by norm_num)).lo := by secondary_diagonal_reference
  have hlo : (8981/10000:ℝ)<(costBox r (7/10) (by norm_num) hrad).lo := by
    rcases hr with rfl | rfl <;> secondary_diagonal_reference
  exact hlo.trans_le (costBox r (7/10) (by norm_num) hrad).mem.1

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal.Reference
