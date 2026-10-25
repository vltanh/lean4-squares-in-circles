module

public import SquaresInCircles.Eight.TableFree.StationaryPrimitiveForces

/-!
# Elementary algebra for the whole-rectangle derivative comparisons

Uncompiled reconstruction.  `Interval` records a proved closed enclosure
of one actual real expression.  Its operations are ordinary ordered-field
inequalities.  The final construction substitutes the actual circle
coordinates into the position derivative and its two derivatives.  It
does not subdivide a domain or search for a root.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryPrimitives
open ExactFamily.FiveCornerGeometry

structure Interval (x : ℝ) where
  lo : ℝ
  hi : ℝ
  mem : x∈Icc lo hi

namespace Interval

def point (x : ℝ) : Interval x := ⟨x,x,le_rfl,le_rfl⟩

def of_bounds {x a b : ℝ} (h : x∈Icc a b) : Interval x := ⟨a,b,h⟩

def add {x y : ℝ} (X : Interval x) (Y : Interval y) : Interval (x+y) :=
  ⟨X.lo+Y.lo,X.hi+Y.hi,add_le_add X.mem.1 Y.mem.1,add_le_add X.mem.2 Y.mem.2⟩

def neg {x : ℝ} (X : Interval x) : Interval (-x) :=
  ⟨-X.hi,-X.lo,neg_le_neg X.mem.2,neg_le_neg X.mem.1⟩

def sub {x y : ℝ} (X : Interval x) (Y : Interval y) : Interval (x-y) :=
  ⟨X.lo-Y.hi,X.hi-Y.lo,sub_le_sub X.mem.1 Y.mem.2,sub_le_sub X.mem.2 Y.mem.1⟩

theorem mul_upper {x y a b c d M : ℝ}
    (hx : x∈Icc a b) (hy : y∈Icc c d)
    (hac : a*c≤M) (had : a*d≤M) (hbc : b*c≤M) (hbd : b*d≤M) : x*y≤M := by
  by_cases hy0 : 0≤y
  · calc
      x*y ≤ b*y := mul_le_mul_of_nonneg_right hx.2 hy0
      _ ≤ M := by
        by_cases hb0 : 0≤b
        · exact (mul_le_mul_of_nonneg_left hy.2 hb0).trans hbd
        · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb0)).trans hbc
  · calc
      x*y ≤ a*y := mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy0)
      _ ≤ M := by
        by_cases ha0 : 0≤a
        · exact (mul_le_mul_of_nonneg_left hy.2 ha0).trans had
        · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha0)).trans hac

def mul {x y : ℝ} (X : Interval x) (Y : Interval y) : Interval (x*y) := by
  let l := min (min (X.lo*Y.lo) (X.lo*Y.hi)) (min (X.hi*Y.lo) (X.hi*Y.hi))
  let u := max (max (X.lo*Y.lo) (X.lo*Y.hi)) (max (X.hi*Y.lo) (X.hi*Y.hi))
  have hu : x*y≤u := mul_upper X.mem Y.mem
    ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
  have hll : l≤X.lo*Y.lo := (min_le_left _ _).trans (min_le_left _ _)
  have hlr : l≤X.lo*Y.hi := (min_le_left _ _).trans (min_le_right _ _)
  have hrl : l≤X.hi*Y.lo := (min_le_right _ _).trans (min_le_left _ _)
  have hrr : l≤X.hi*Y.hi := (min_le_right _ _).trans (min_le_right _ _)
  have hneg : (-x)*y≤-l := mul_upper X.neg.mem Y.mem
    (by dsimp [neg]; nlinarith) (by dsimp [neg]; nlinarith) (by dsimp [neg]; nlinarith)
    (by dsimp [neg]; nlinarith)
  exact ⟨l,u,by nlinarith,hu⟩

def square {x : ℝ} (X : Interval x) : Interval (x^2) := by
  have h := X.mul X
  exact ⟨h.lo,h.hi,by simpa only [pow_two] using h.mem⟩

def cube {x : ℝ} (X : Interval x) : Interval (x^3) := by
  have h := X.square.mul X
  exact ⟨h.lo,h.hi,by simpa only [pow_succ] using h.mem⟩

def inv {x : ℝ} (X : Interval x) (h : 0<X.lo) : Interval (1/x) :=
  ⟨1/X.hi,1/X.lo,quotient_bounds (show (1:ℝ)∈Icc 1 1 from ⟨le_rfl,le_rfl⟩)
    X.mem (by norm_num) h⟩

def div {x y : ℝ} (X : Interval x) (Y : Interval y) (h : 0<Y.lo) : Interval (x/y) := by
  have H := X.mul (Y.inv h)
  exact ⟨H.lo,H.hi,by simpa only [div_eq_mul_inv,one_mul] using H.mem⟩

theorem hi_pos {x : ℝ} {X : Interval x} (h : 0<X.lo) : 0<X.hi :=
  lt_of_lt_of_le h (le_trans X.mem.1 X.mem.2)

theorem mul_lo_pos {x y : ℝ} {X : Interval x} {Y : Interval y}
    (hx : 0<X.lo) (hy : 0<Y.lo) : 0<(X.mul Y).lo := by
  dsimp [mul]
  exact lt_min (lt_min (mul_pos hx hy) (mul_pos hx (hi_pos hy)))
    (lt_min (mul_pos (hi_pos hx) hy) (mul_pos (hi_pos hx) (hi_pos hy)))

theorem square_lo_pos {x : ℝ} {X : Interval x} (hx : 0<X.lo) : 0<X.square.lo :=
  mul_lo_pos hx hx

theorem cube_lo_pos {x : ℝ} {X : Interval x} (hx : 0<X.lo) : 0<X.cube.lo :=
  mul_lo_pos (square_lo_pos hx) hx

def tighten {x : ℝ} (X : Interval x) (a b : ℝ)
    (ha : a≤X.lo) (hb : X.hi≤b) : Interval x :=
  ⟨a,b,ha.trans X.mem.1,X.mem.2.trans hb⟩

end Interval

structure DifferentialIntervals (q c s u : ℝ) where
  first : Interval (2*positionHalf q c s u)
  position : Interval (positionSecond q c s u)
  mixed : Interval (mixedSecond q c s u)

/-- Substitution into the two exact derivative formulas.  The enclosures
are attached to the actual coordinate functions in the argument types. -/
def differentialIntervals {q c s u : ℝ}
    (Q : Interval q) (X : Interval u)
    (R : Interval (lowerRight q u)) (U : Interval (topRight q u))
    (V : Interval (topLeft q u)) (Y : Interval (topHeight q u))
    (v : Interval (lowerHeight q u)) (W : Interval (lowerLeft q u))
    (C : Interval c) (S : Interval s)
    (hr : 0<R.lo) (hU : 0<U.lo) (hV : 0<V.lo) (hY : 0<Y.lo)
    (hw : 0<W.lo) (hl : 0<2-X.hi) : DifferentialIntervals q c s u := by
  let one := Interval.point 1
  let two := Interval.point 2
  let L := two.sub X
  have hL : 0<L.lo := hl
  let P := (L.mul V).div (U.mul Y) (Interval.mul_lo_pos hU hY)
  let Z := (Q.div (L.mul U.square) (Interval.mul_lo_pos hL (Interval.square_lo_pos hU))).add
    ((P.mul Q).div (Y.mul V.square) (Interval.mul_lo_pos hY (Interval.square_lo_pos hV)))
  let A := S.add ((C.mul X).div R hr)
  let B := C.add ((S.mul v).div W hw)
  let b := P.mul B
  let k1 := (two.sub (C.mul (R.sub one))).add (S.mul X)
  let k2 := (one.add (C.mul v)).sub (S.mul (W.sub one))
  let d := (S.mul (R.sub one)).add (C.mul X)
  let E := (C.mul (W.sub one)).add (S.mul v)
  let At := C.sub ((S.mul X).div R hr)
  let Bt := P.mul ((S.neg).add ((C.mul v).div W hw))
  let right := (C.mul Q).div R.cube (Interval.cube_lo_pos hr)
  let left := ((P.mul Z).mul B).add
    (((S.mul Q).mul P.square).div W.cube (Interval.cube_lo_pos hw))
  let first := two.mul ((k1.mul A).sub (k2.mul b))
  let position := two.mul ((A.square.add b.square).add ((k1.mul right).add (k2.mul left)))
  let mixed := two.mul ((((A.mul d).add (k1.mul At)).add (E.mul b)).sub (k2.mul Bt))
  refine ⟨⟨first.lo,first.hi,?_⟩,⟨position.lo,position.hi,?_⟩,⟨mixed.lo,mixed.hi,?_⟩⟩
  · convert first.mem using 1 <;>
      dsimp [positionHalf,firstComponent,secondComponent,slopeRatio] <;> ring
  · convert position.mem using 1 <;>
      dsimp [positionSecond,positionNorm,positionNormal,positionA,positionb,positionB,
        rightSecond,leftSecond,firstComponent,secondComponent,slopeRatio,curvatureRatio] <;> ring
  · convert mixed.mem using 1 <;>
      dsimp [mixedSecond,mixedNormal,positionA,positionb,positionB,firstTilt,secondTilt,
        firstComponent,secondComponent,slopeRatio] <;> ring

end SquaresInCircles.Eight.TableFree.StationaryPrimitives
