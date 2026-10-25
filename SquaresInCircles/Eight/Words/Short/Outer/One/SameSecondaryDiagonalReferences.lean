module

public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryDiagonalData

/-!
# Eight squares: the three late-arc substitutions

The exact circle radical is kept in every enclosure. The references are the left event bracket
(`left_cos`, `left_factor`), the single speed reference `0.68` (`speed_reference`) and the right
endpoint `0.7` (`cap_geometry`, `final_cost`); the moving arc is not subdivided.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal.Reference
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
        ((Interval.point (q r)).mul ((horizontalBox x hx hr).sub (Interval.point (1/2)))))
    using 1 <;> dsimp [cost] <;> ring

private lemma r87_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r87_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r87_factorD_eq {x : ℝ} (hx : x∈Icc 0 (7/10)) (hr : 0≤(radBox x hx.1).lo)
    (hy : 0<(yBox x hx.1 hr).lo) : factorD x=numerator x/(Y x)^3 := by
  have hY : 0<Y x := hy.trans_le (yBox x hx.1 hr).mem.1
  exact ((div_eq_iff (pow_ne_zero _ hY.ne')).2 (numerator_identity hx).symm).symm
private lemma r87_factorDBox_lo (x : ℝ) (hx : x∈Icc 0 (7/10)) (hr : 0≤(radBox x hx.1).lo)
    (hy : 0<(yBox x hx.1 hr).lo) : (factorDBox x hx hr hy).lo =
      ((numeratorBox x hx.1).div (yBox x hx.1 hr).cube (Interval.cube_lo_pos hy)).lo := by
  dsimp only [factorDBox]
  exact r87_mpr_lo (r87_factorD_eq hx hr hy) _ _
private lemma r87_factorDBox_hi (x : ℝ) (hx : x∈Icc 0 (7/10)) (hr : 0≤(radBox x hx.1).lo)
    (hy : 0<(yBox x hx.1 hr).lo) : (factorDBox x hx hr hy).hi =
      ((numeratorBox x hx.1).div (yBox x hx.1 hr).cube (Interval.cube_lo_pos hy)).hi := by
  dsimp only [factorDBox]
  exact r87_mpr_hi (r87_factorD_eq hx hr hy) _ _

private lemma r87_cost_eq (r : Row) (x : ℝ) : cost r x=Real.pi*(1/2)-x+c r+(t r-P r)*outerDiagonal+
    p r*(vertical x-1/2)-q r*(horizontal x-1/2) := by
  simp only [cost]; ring
private lemma r87_costBox_lo (r : Row) (x : ℝ) (hx : 0≤x) (hr : 0≤(radBox x hx).lo) :
    (costBox r x hx hr).lo = ((((((RoleFour.piBox.mul (Interval.point (1/2))).sub
      (Interval.point x)).add (Interval.point (c r))).add
        ((Interval.point (t r-P r)).mul RoleFour.dBox)).add
          ((Interval.point (p r)).mul ((verticalBox x hx hr).sub (Interval.point (1/2))))).sub
            ((Interval.point (q r)).mul ((horizontalBox x hx hr).sub (Interval.point (1/2))))).lo :=
  r87_mpr_lo (r87_cost_eq r x) (congrArg _ (r87_cost_eq r x)) _

local macro "secondary_diagonal_reference" : tactic => `(tactic|
  norm_num [offsetBox,zBox,radBox,yBox,horizontalBox,verticalBox,factorBox,numeratorBox,
    r87_factorDBox_lo,r87_factorDBox_hi,speedBox,speedDBox,r87_costBox_lo,RoleFour.dBox,
    RoleFour.piBox,
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
    factorD (7/10)< -(93/250:ℝ) := by
  have hr : 0≤(radBox (7/10) (by norm_num)).lo := by secondary_diagonal_reference
  have hy : 0<(yBox (7/10) (by norm_num) hr).lo := by secondary_diagonal_reference
  have hv : (verticalBox (7/10) (by norm_num) hr).hi<(1533/1000:ℝ) := by
    secondary_diagonal_reference
  have hh : (1251/1000:ℝ)<(horizontalBox (7/10) (by norm_num) hr).lo := by
    secondary_diagonal_reference
  have hf : (167/250:ℝ)<(factorBox (7/10) (by norm_num) hr hy).lo := by
    secondary_diagonal_reference
  have hfd : (factorDBox (7/10) (by norm_num) hr hy).hi< -(93/250:ℝ) := by
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
  have hb : -(7/1000:ℝ)<(speedDBox (17/25) (by norm_num) hr hy).lo ∧
      (speedDBox (17/25) (by norm_num) hr hy).hi<(7/1000:ℝ) := by
    secondary_diagonal_reference
  exact ⟨(speedBox (17/25) (by norm_num) hr hy).mem.2.trans_lt hhi,
    abs_lt.2 ⟨hb.1.trans_le (speedDBox (17/25) (by norm_num) hr hy).mem.1,
      (speedDBox (17/25) (by norm_num) hr hy).mem.2.trans_lt hb.2⟩⟩

lemma final_cost (r : Row) (hr : r=1 ∨ r=2) : (8981/10000:ℝ)<cost r (7/10) := by
  have hrad : 0≤(radBox (7/10) (by norm_num)).lo := by secondary_diagonal_reference
  have hlo : (8981/10000:ℝ)<(costBox r (7/10) (by norm_num) hrad).lo := by
    rcases hr with rfl | rfl <;> secondary_diagonal_reference
  exact hlo.trans_le (costBox r (7/10) (by norm_num) hrad).mem.1

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.SourceDiagonal.Reference
