module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeAlignedCalculus
public import SquaresInCircles.Eight.TableFree.StationaryIntervalAlgebra

/-!
# Exact radical enclosures at named opposite edge-three references

A positive rational seed gives a rational upper square-root bound by
the arithmetic-geometric mean identity; division gives the matching
lower bound.  Three explicit refinements are used at individual fixed
references.  Each enclosure remains attached to its actual expression.
There is no domain subdivision or evaluated certificate.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.ReferenceAlgebra
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)

def rootStep {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    Interval (Real.sqrt x) := by
  let u : ℝ := (s+X.hi/s)/2
  have hx : 0≤x := hX.trans X.mem.1
  have hhi : 0≤X.hi := hx.trans X.mem.2
  have hu : 0<u := by dsimp [u]; positivity
  have he : 4*u^2-4*X.hi=(s-X.hi/s)^2 := by
    dsimp [u]
    field_simp [hs.ne']
    ring
  have hu2 : X.hi≤u^2 := by nlinarith [sq_nonneg (s-X.hi/s)]
  have hr := Real.sqrt_nonneg x
  have hr2 := Real.sq_sqrt hx
  have hrhi : Real.sqrt x≤u := by nlinarith [X.mem.2]
  refine ⟨X.lo/u,u,?_,hrhi⟩
  apply (div_le_iff₀ hu).2
  have hp := mul_le_mul_of_nonneg_left hrhi hr
  nlinarith [X.mem.1]

lemma rootStep_hi_pos {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    0<(rootStep X s hs hX).hi := by
  have hh : 0≤X.hi := hX.trans (X.mem.1.trans X.mem.2)
  dsimp [rootStep]
  positivity

def rootThree {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    Interval (Real.sqrt x) := by
  let X₀ := rootStep X s hs hX
  have h₀ : 0<X₀.hi := rootStep_hi_pos X s hs hX
  let X₁ := rootStep X X₀.hi h₀ hX
  have h₁ : 0<X₁.hi := rootStep_hi_pos X X₀.hi h₀ hX
  exact rootStep X X₁.hi h₁ hX

def radicand {y : ℝ} (Y : Interval y) : Interval (Q0-(y+1/2)^2) :=
  (Interval.point Q0).sub ((Y.add (Interval.point (1/2))).square)

def shifted {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) : Interval (U y) := by
  have hh := rootThree (radicand Y) s hs hr
  convert hh using 1
  dsimp [U,arc]
  ring

def coordinate {y : ℝ} (Y : Interval (U y)) : Interval (arc y) := by
  have hh := Y.sub (Interval.point (1/2))
  convert hh using 1
  dsimp [U]
  ring

def ratioBox {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (ratio y) :=
  (Y.add (Interval.point (1/2))).div X hX

def ratioDBox {y : ℝ} (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (ratioD y) :=
  (Interval.point Q0).div X.cube (Interval.cube_lo_pos hX)

def ratioDDBox {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (ratioDD y) := by
  let Z := ((Interval.point (3*Q0)).mul (Y.add (Interval.point (1/2)))).div
    (X.cube.mul X.square)
    (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hX))
  convert Z using 1
  dsimp [ratioDD,U]
  congr 1
  ring

def labelBox (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    Interval (H.outer y) := by
  let Z := ((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).
    add ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).
      add ((Interval.point H.s).mul ((coordinate X).mul Y))
  convert Z using 1
  dsimp [RoleLabel.outer,RoleLabel.eval]
  ring

def firstBox (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) : Interval (H.d1 y) :=
  ((((Interval.point H.q).add ((Interval.point (2*H.r)).mul Y)).
    add ((Interval.point H.s).mul (coordinate X))).sub
      (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioBox Y X hX)))

def secondBox (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) : Interval (H.d2 y) :=
  (((Interval.point (2*H.r)).sub ((Interval.point (2*H.s)).mul (ratioBox Y X hX))).
    sub (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDBox X hX)))

def thirdBox (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) : Interval (H.d3 y) :=
  (((Interval.point (-3*H.s)).mul (ratioDBox X hX)).sub
    (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDDBox Y X hX)))

def piBox : Interval Real.pi :=
  Interval.of_bounds ⟨pi_hand_enclosure.1.le,pi_hand_enclosure.2.le⟩

def jBox {y : ℝ} (X : Interval (U y)) : Interval (Aligned.j y) := by
  have hh := X.sub (Interval.point (3/2))
  convert hh using 1
  dsimp [Aligned.j,U]
  ring

def alignedBox (reverse : Bool) {y : ℝ}
    (Y : Interval y) (X : Interval (U y)) (J : Interval (U (Aligned.j y))) :
    Interval (Aligned.cost reverse y) :=
  (((piBox.div (Interval.point 2) (by norm_num [Interval.point])).
    sub (labelBox (Aligned.inner reverse) (jBox X) J)).
      sub (labelBox (Aligned.outer reverse) Y X))

def alignedFirstBox (reverse : Bool) {y : ℝ}
    (Y : Interval y) (X : Interval (U y)) (J : Interval (U (Aligned.j y)))
    (hX : 0<X.lo) (hJ : 0<J.lo) : Interval (Aligned.first reverse y) :=
  (((firstBox (Aligned.inner reverse) (jBox X) J hJ).mul (ratioBox Y X hX)).
    sub (firstBox (Aligned.outer reverse) Y X hX))

def alignedSecondBox (reverse : Bool) {y : ℝ}
    (Y : Interval y) (X : Interval (U y)) (J : Interval (U (Aligned.j y)))
    (hX : 0<X.lo) (hJ : 0<J.lo) : Interval (Aligned.second reverse y) :=
  (((((secondBox (Aligned.inner reverse) (jBox X) J hJ).neg).
    mul (ratioBox Y X hX).square).
      add ((firstBox (Aligned.inner reverse) (jBox X) J hJ).mul (ratioDBox X hX))).
        sub (secondBox (Aligned.outer reverse) Y X hX))

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.ReferenceAlgebra
