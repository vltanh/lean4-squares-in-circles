module

public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJDiagonalGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameEvent

/-!
# Eight squares: the named diagonal boundary references

Only the initial event and angle .3 are used.
The rotated-circle coordinates and all speed enclosures remain attached
to their actual real expressions.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (dBox aBox sinBox cosBox ZBox YRadBox YBox UBox VBox)

abbrev Geometry := SecondWord.SameZero.PJ.Diagonal.Domain
abbrev Z := SecondWord.SameZero.PJ.Diagonal.Z
abbrev Y := SecondWord.SameZero.PJ.Diagonal.Y
abbrev horizontal := SecondWord.SameZero.PJ.Diagonal.horizontal
abbrev vertical := SecondWord.SameZero.PJ.Diagonal.vertical
abbrev height := SecondWord.SameZero.PJ.Diagonal.height
abbrev factor := SecondWord.SameZero.PJ.Diagonal.factor
abbrev factorD := SecondWord.SameZero.PJ.Diagonal.factorD
abbrev speed := SecondWord.SameZero.PJ.Diagonal.speed
abbrev acceleration := SecondWord.SameZero.PJ.Diagonal.acceleration
abbrev start := SecondWord.SameZero.PJ.Diagonal.start

def cost (r : Row) (x : ℝ) : ℝ :=
  x+c r+(p r+q r)*outerDiagonal-P r*ShortOuterOne.SameContact.arc (height x)-t r*height x
def targetSlope (r : Row) (x : ℝ) : ℝ :=
  (q r-p r)*Real.cos x+((q r-p r)*Real.sin x+P r)*vertical x/horizontal x-t r

def targetSlopeBox (r : Row) (x : ℝ) (hx : 0≤x)
    (hr : 0≤(YRadBox x hx).lo) (hu : 0<(UBox x hx hr).lo) : Interval (targetSlope r x) :=
  (((Interval.point (q r-p r)).mul (cosBox x hx)).add
    ((((Interval.point (q r-p r)).mul (sinBox x hx)).add (Interval.point (P r))).mul (VBox x hx hr) |>.div (UBox x hx hr) hu)).sub (Interval.point (t r))

def factorDBox (x : ℝ) (hx : 0≤x) (hr : 0≤(YRadBox x hx).lo)
    (hy : 0<(YBox x hx hr).lo) : Interval (factorD x) := by
  let z₀ := dBox.sub (Interval.point (1/2))
  let N := ((sinBox x hx).mul ((Interval.point (Q0-1)).sub z₀.square)).add
    (z₀.mul ((Interval.point 1).add (sinBox x hx).square))
  exact N.div (YBox x hx hr).cube (Interval.cube_lo_pos hy)

macro "diagonal_reference_arithmetic" : tactic => `(tactic|
  norm_num [targetSlopeBox,factorDBox,
    SecondWord.SameZero.PJ.Reference.ZBox,SecondWord.SameZero.PJ.Reference.YRadBox,
    SecondWord.SameZero.PJ.Reference.YBox,SecondWord.SameZero.PJ.Reference.UBox,
    SecondWord.SameZero.PJ.Reference.VBox,rootThree,rootStep,c,p,q,P,t,Q0]
  <;> event_reference_arithmetic)

lemma three_tenths : (37/20:ℝ)<horizontal (3/10) ∧ factorD (3/10)<81/500 ∧
    ∀r, Coupled r → (1/125:ℝ)<targetSlope r (3/10) := by
  have hr : 0≤(YRadBox (3/10) (by norm_num)).lo := by diagonal_reference_arithmetic
  have hu : 0<(UBox (3/10) (by norm_num) hr).lo := by diagonal_reference_arithmetic
  have hy : 0<(YBox (3/10) (by norm_num) hr).lo := by diagonal_reference_arithmetic
  have hU : (37/20:ℝ)<(UBox (3/10) (by norm_num) hr).lo := by diagonal_reference_arithmetic
  have hD : (factorDBox (3/10) (by norm_num) hr hy).hi<(81/500:ℝ) := by
    diagonal_reference_arithmetic
  refine ⟨hU.trans_le (UBox (3/10) (by norm_num) hr).mem.1,
    (factorDBox (3/10) (by norm_num) hr hy).mem.2.trans_lt hD,?_⟩
  intro r hrc
  have hS : (1/125:ℝ)<(targetSlopeBox r (3/10) (by norm_num) hr hu).lo := by
    fin_cases r <;> norm_num [Coupled] at hrc <;> diagonal_reference_arithmetic
  exact hS.trans_le (targetSlopeBox r (3/10) (by norm_num) hr hu).mem.1

lemma event_geometry {e : ℝ} (he : Event.IsEvent e) : Geometry e ∧ height e=0 := by
  have hd : Domain 0 e := ⟨SecondWord.outer_zero_mem,Event.angle_mem he,
    by
      show SecondWord.SameZero.b 0 e∈Icc 0 outerDiagonal
      rw [show SecondWord.SameZero.b 0 e=outerDiagonal from he.2]
      exact ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩⟩
  exact SecondWord.SameZero.PJ.Diagonal.original_coordinates hd he.2

def eventZ {e : ℝ} (he : Event.IsEvent e) : Interval (Z e) :=
  (dBox.sub (Interval.point (1/2))).sub (Event.eventSin he)
def eventRad {e : ℝ} (he : Event.IsEvent e) : Interval (Q0-(Z e)^2) :=
  (Interval.point Q0).sub (eventZ he).square

def eventY {e : ℝ} (he : Event.IsEvent e) : Interval (Y e) :=
  rootThree (eventRad he) 2 (by norm_num) (by
    dsimp [eventRad,eventZ,Event.eventSin]
    diagonal_reference_arithmetic)

def eventU {e : ℝ} (he : Event.IsEvent e) : Interval (horizontal e) :=
  ((eventY he).mul (Event.eventCos he)).sub ((eventZ he).mul (Event.eventSin he))

def eventSpeed {e : ℝ} (he : Event.IsEvent e) : Interval (speed e) :=
  (eventU he).mul ((Interval.point 1).sub
    ((Event.eventCos he).div (eventY he) (by
      dsimp [eventY,eventRad,eventZ,Event.eventSin]
      diagonal_reference_arithmetic)))

lemma initial_speed {e : ℝ} (he : Event.IsEvent e) : speed e<(471/500:ℝ) := by
  have h : (eventSpeed he).hi<(471/500:ℝ) := by
    dsimp [eventSpeed,eventU,eventY,eventRad,eventZ,Event.eventSin,Event.eventCos]
    diagonal_reference_arithmetic
  exact (eventSpeed he).mem.2.trans_lt h

end SquaresInCircles.Eight.ShortOuterZero.Same.Diagonal
