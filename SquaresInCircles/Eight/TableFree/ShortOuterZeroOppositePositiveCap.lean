module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveSourceDiagonal

/-!
# The six final-angle opposite-sign short-word supports

Uncompiled transcription of Section 3.4. The six displayed multipliers
are evaluated only at the physical final angle .7. Positive source
coefficients use the two circle endpoints; negative source coefficients
use the written full-circle lower support. The target support is axial.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Cap
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (sinBox cosBox dBox aBox)

abbrev radius : ℝ := Real.sqrt Q0
def weight : Row→ℝ := ![94766/100000,96135/100000,9994/10000,93/100,45181/50000,45181/50000]
def sourceBound (r : Row) : ℝ :=
  if 0≤p r then min (p r*outerAxial) ((p r+q r-weight r)*outerDiagonal)
  else -(p r+q r-weight r)/2-radius*Real.sqrt ((p r)^2+(q r-weight r)^2)
def scalar (r : Row) : ℝ := 7/10+c r+sourceBound r+weight r/2+v r*outerAxial+
  (weight r/2)*Real.cos (7/10)+weight r*(1/2-outerAxial)*Real.sin (7/10)

lemma full_circle_lower {a b X Y : ℝ} (hs : OuterState a b) :
    -(X+Y)/2-radius*Real.sqrt (X^2+Y^2)≤X*a+Y*b := by
  have hR0 := Real.sqrt_nonneg Q0
  have hR2 := Real.sq_sqrt (show 0≤Q0 by norm_num [Q0])
  have hN0 := Real.sqrt_nonneg (X^2+Y^2)
  have hN2 := Real.sq_sqrt (show 0≤X^2+Y^2 by positivity)
  have hproj : (X*(a+1/2)+Y*(b+1/2))^2≤Q0*(X^2+Y^2) := by
    have hsquare := sq_nonneg (X*(b+1/2)-Y*(a+1/2))
    have he : (X*(a+1/2)+Y*(b+1/2))^2+
        (X*(b+1/2)-Y*(a+1/2))^2=Q0*(X^2+Y^2) := by
      linear_combination (X^2+Y^2)*hs.2.2
    linarith
  have hproduct : 0≤radius*Real.sqrt (X^2+Y^2) := mul_nonneg hR0 hN0
  have hproduct2 : (radius*Real.sqrt (X^2+Y^2))^2=Q0*(X^2+Y^2) := by
    rw [mul_pow]
    exact congrArg₂ (·*·) hR2 hN2
  have hlower : -radius*Real.sqrt (X^2+Y^2)≤X*(a+1/2)+Y*(b+1/2) := by
    nlinarith
  linarith

lemma source_lower (r : Row) {a b : ℝ} (hs : OuterState a b) :
    sourceBound r≤p r*a+(q r-weight r)*b := by
  unfold sourceBound
  split_ifs with hp
  · apply outer_concave_lower hs hp (min_le_left _ _)
    have hh := min_le_right (p r*outerAxial) ((p r+q r-weight r)*outerDiagonal)
    nlinarith
  · exact full_circle_lower hs

lemma target_signs (r : Row) :
    v r-weight r*Real.sin (7/10)<0 ∧ 0<t r-weight r*Real.cos (7/10) := by
  have ht := CommonQuarter.cap_trig
  fin_cases r <;> norm_num [weight,v,t] <;>
    constructor <;> linarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

lemma target_lower (r : Row) {A B : ℝ} (ht : OuterState A B) :
    (v r-weight r*Real.sin (7/10))*outerAxial≤
      (v r-weight r*Real.sin (7/10))*A+(t r-weight r*Real.cos (7/10))*B := by
  have hs := target_signs r
  apply outer_axial_lower ht hs.1.le
  have hp := mul_nonneg (show 0≤outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) hs.2.le
  linarith

def intervalMin {x y : ℝ} (X : Interval x) (Y : Interval y) : Interval (min x y) :=
  Interval.of_bounds ⟨min_le_min X.mem.1 Y.mem.1,min_le_min X.mem.2 Y.mem.2⟩

def radiusBox : Interval radius := rootThree (Interval.point Q0) 2
  (by norm_num) (by norm_num [Interval.point,Q0])
def normSeed (r : Row) : ℝ := if r=3 then 1/8 else 1/4

def normBox (r : Row) : Interval (Real.sqrt ((p r)^2+(q r-weight r)^2)) :=
  rootThree (Interval.point ((p r)^2+(q r-weight r)^2)) (normSeed r)
    (by unfold normSeed; split_ifs <;> norm_num)
    (by dsimp [Interval.point]; positivity)

def sourceBox (r : Row) : Interval (sourceBound r) := by
  unfold sourceBound
  split_ifs with hp
  · exact intervalMin ((Interval.point (p r)).mul aBox)
      ((Interval.point (p r+q r-weight r)).mul dBox)
  · exact (Interval.point (-(p r+q r-weight r)/2)).sub (radiusBox.mul (normBox r))

def scalarBox (r : Row) : Interval (scalar r) :=
  ((((((Interval.point ((7/10:ℝ)+c r)).add (sourceBox r)).add (Interval.point (weight r/2))).
    add ((Interval.point (v r)).mul aBox)).add
      ((Interval.point (weight r/2)).mul (cosBox (7/10) (by norm_num)))).add
        (((Interval.point (weight r)).mul ((Interval.point (1/2)).sub aBox)).
          mul (sinBox (7/10) (by norm_num)))

lemma scalar_lower (r : Row) : (923/1000:ℝ)<scalar r := by
  have hh : (923/1000:ℝ)<(scalarBox r).lo := by
    fin_cases r <;>
      norm_num [scalarBox,sourceBox,sourceBound,intervalMin,radiusBox,normBox,normSeed,
        rootThree,rootStep,weight,c,p,q,v,t,Q0,
        SecondWord.SameZero.PJ.Reference.dBox,SecondWord.SameZero.PJ.Reference.aBox,
        SecondWord.SameZero.PJ.Reference.sinBox,SecondWord.SameZero.PJ.Reference.cosBox,
        Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
        Interval.mul,Interval.square,Interval.div,Interval.inv,HighOrderTaylor.S17,
        HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,
        HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
  exact hh.trans_le (scalarBox r).mem.1

lemma original_projection (r : Row) {a b A B : ℝ} (hs : OuterState a b)
    (ht : OuterState A B)
    (hm : (1+Real.sin (7/10)+Real.cos (7/10))/2≤
      b+A*Real.sin (7/10)+B*Real.cos (7/10)) :
    (923/1000:ℝ)<7/10+c r+p r*a+q r*b+v r*A+t r*B := by
  have hsource := source_lower r hs
  have htarget := target_lower r ht
  have hw : 0≤weight r := by fin_cases r <;> norm_num [weight]
  have hsep := mul_le_mul_of_nonneg_left hm hw
  have hvalue := scalar_lower r
  dsimp [scalar] at hvalue
  nlinarith only [hsource,htarget,hsep,hvalue]

/-- Each whole final-angle contact uses its literal source and target labels. -/
theorem lower (r : Row) {B : ℝ} (hd : PlusDomain B (7/10)) :
    (89809/100000:ℝ)<plusCost r B (7/10) := by
  have hs := ShortOuterOne.SameContact.arc_state hd.2.2
  have ht := ShortOuterOne.SameContact.arc_state hd.1
  have he : (1+Real.sin (7/10)+Real.cos (7/10))/2=
      plus B (7/10)+arc B*Real.sin (7/10)+B*Real.cos (7/10) := by
    dsimp [plus,SecondWord.OppositeZero.plus]
    ring
  have hh := original_projection r hs ht he.le
  dsimp [plusCost,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval]
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Cap
