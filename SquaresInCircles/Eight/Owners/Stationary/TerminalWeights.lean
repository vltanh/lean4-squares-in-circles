module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import SquaresInCircles.Eight.Owners.Canonical.NominalFlux
public import SquaresInCircles.Eight.Stationary.CriticalHessian

/-!
# Eight squares: normalized force weights from the actual circle chain

The five raw masses and all edge weights
below are explicit functions of the nested positive radicals.  Their
positivity and normalization are proved on the full terminal rectangle.
Position stationarity is used only in the separate cancellation identity.
-/

section
/-!
## The actual radical coordinates on the terminal rectangle

Every bound below concerns the successive
positive circle roots themselves.  The radius and position range is one
rectangle, and each root enclosure follows by positive squaring.  The
trigonometric bounds likewise concern the actual angle `arctan h`.
No stationarity equation, fitted coordinate, or root-cover hypothesis is
used in these primitive estimates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryPrimitives
open Stationary.FiveCornerGeometry

/-- Positive interval arithmetic used only for the displayed continuous
algebraic comparisons. -/
theorem product_bounds {x y a b c d : ℝ}
    (hx : x∈Icc a b) (hy : y∈Icc c d) (ha : 0≤a) (hc : 0≤c) :
    x*y∈Icc (a*c) (b*d) := by
  exact ⟨mul_le_mul hx.1 hy.1 hc (le_trans ha hx.1),
    mul_le_mul hx.2 hy.2 (le_trans hc hy.1) (le_trans ha (le_trans hx.1 hx.2))⟩

theorem quotient_bounds {x y a b c d : ℝ}
    (hx : x∈Icc a b) (hy : y∈Icc c d) (ha : 0≤a) (hc : 0<c) :
    x/y∈Icc (a/d) (b/c) := by
  have hdp : 0<d := lt_of_lt_of_le hc (le_trans hy.1 hy.2)
  have hyp : 0<y := lt_of_lt_of_le hc hy.1
  have hbp : 0≤b := le_trans ha (le_trans hx.1 hx.2)
  constructor
  · apply (le_div_iff₀ hyp).2
    calc
      (a/d)*y ≤ (a/d)*d := mul_le_mul_of_nonneg_left hy.2 (div_nonneg ha hdp.le)
      _ = a := div_mul_cancel₀ a hdp.ne'
      _ ≤ x := hx.1
  · apply (div_le_iff₀ hyp).2
    calc
      x ≤ b := hx.2
      _ = (b/c)*c := (div_mul_cancel₀ b hc.ne').symm
      _ ≤ (b/c)*y := mul_le_mul_of_nonneg_left hy.1 (div_nonneg hbp hc.le)

theorem square_bounds {x a b : ℝ} (hx : x∈Icc a b) (ha : 0≤a) :
    x^2∈Icc (a^2) (b^2) := by
  exact ⟨square_mono_nonneg ha hx.1,
    square_mono_nonneg (le_trans ha hx.1) hx.2⟩

theorem sqrt_bounds {x a b l r : ℝ} (hx : x∈Icc l r)
    (_ha : 0≤a) (hb : 0≤b) (hl : a^2<l) (hr : r<b^2) :
    Real.sqrt x∈Ioo a b :=
  sqrt_between hb (lt_of_lt_of_le hl hx.1) (lt_of_le_of_lt hx.2 hr)

structure RadicalBounds (q u : ℝ) : Prop where
  r_lower : 1741/1000<lowerRight q u
  r_upper : lowerRight q u<353/200
  U_lower : 1641/1000<topRight q u
  U_upper : topRight q u<1671/1000
  V_lower : 1329/1000<topLeft q u
  V_upper : topLeft q u<1359/1000
  Y_lower : 719/500<topHeight q u
  Y_upper : topHeight q u<1467/1000
  v_lower : 533/1000<lowerHeight q u
  v_upper : lowerHeight q u<281/500
  w_lower : 1897/1000<lowerLeft q u
  w_upper : lowerLeft q u<953/500

/-- One successive-square calculation for the full terminal rectangle. -/
theorem radical_bounds {q u : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50)) : RadicalBounds q u := by
  have hu2 := square_bounds hu (by norm_num)
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  have hl2 := square_bounds hl (by norm_num)
  have hr : lowerRight q u∈Ioo (1741/1000:ℝ) (353/200) := by
    apply sqrt_bounds (l:=15159/5000) (r:=124583/40000)
      (show q-u^2∈Icc (15159/5000:ℝ) (124583/40000) from
        ⟨by linarith [hq.1,hu2.2],by linarith [hq.2,hu2.1]⟩) <;> norm_num
  have hU : topRight q u∈Ioo (1641/1000:ℝ) (1671/1000) := by
    apply sqrt_bounds (l:=4311/1600) (r:=349/125)
      (show q-(2-u)^2∈Icc (4311/1600:ℝ) (349/125) from
        ⟨by linarith [hq.1,hl2.2],by linarith [hq.2,hl2.1]⟩) <;> norm_num
  have hV : topLeft q u∈Ioo (1329/1000:ℝ) (1359/1000) := by
    dsimp [topLeft]
    exact ⟨by linarith [hU.2],by linarith [hU.1]⟩
  have hV2 := square_bounds ⟨hV.1.le,hV.2.le⟩ (by norm_num)
  have hY : topHeight q u∈Ioo (719/500:ℝ) (1467/1000) := by
    apply sqrt_bounds (l:=2068519/1000000) (r:=2149359/1000000)
      (show q-topLeft q u^2∈Icc (2068519/1000000:ℝ) (2149359/1000000) from
        ⟨by linarith [hq.1,hV2.2],by linarith [hq.2,hV2.1]⟩) <;> norm_num
  have hv : lowerHeight q u∈Ioo (533/1000:ℝ) (281/500) := by
    dsimp [lowerHeight]
    exact ⟨by linarith [hY.2],by linarith [hY.1]⟩
  have hv2 := square_bounds ⟨hv.1.le,hv.2.le⟩ (by norm_num)
  have hw : lowerLeft q u∈Ioo (1897/1000:ℝ) (953/500) := by
    apply sqrt_bounds (l:=899889/250000) (r:=3631511/1000000)
      (show q-lowerHeight q u^2∈Icc (899889/250000:ℝ) (3631511/1000000) from
        ⟨by linarith [hq.1,hv2.2],by linarith [hq.2,hv2.1]⟩) <;> norm_num
  exact ⟨hr.1,hr.2,hU.1,hU.2,hV.1,hV.2,hY.1,hY.2,hv.1,hv.2,hw.1,hw.2⟩

theorem RadicalBounds.r {q u : ℝ} (h : RadicalBounds q u) :
    lowerRight q u∈Icc (1741/1000:ℝ) (353/200) := ⟨h.r_lower.le,h.r_upper.le⟩
theorem RadicalBounds.U {q u : ℝ} (h : RadicalBounds q u) :
    topRight q u∈Icc (1641/1000:ℝ) (1671/1000) := ⟨h.U_lower.le,h.U_upper.le⟩
theorem RadicalBounds.V {q u : ℝ} (h : RadicalBounds q u) :
    topLeft q u∈Icc (1329/1000:ℝ) (1359/1000) := ⟨h.V_lower.le,h.V_upper.le⟩
theorem RadicalBounds.Y {q u : ℝ} (h : RadicalBounds q u) :
    topHeight q u∈Icc (719/500:ℝ) (1467/1000) := ⟨h.Y_lower.le,h.Y_upper.le⟩
theorem RadicalBounds.v {q u : ℝ} (h : RadicalBounds q u) :
    lowerHeight q u∈Icc (533/1000:ℝ) (281/500) := ⟨h.v_lower.le,h.v_upper.le⟩
theorem RadicalBounds.w {q u : ℝ} (h : RadicalBounds q u) :
    lowerLeft q u∈Icc (1897/1000:ℝ) (953/500) := ⟨h.w_lower.le,h.w_upper.le⟩

theorem RadicalBounds.smoothDomain {q u : ℝ} (h : RadicalBounds q u)
    (hq : q<4) (hu : 0≤u) : SmoothDomain q u := by
  have hr : 0<lowerRight q u := by linarith [h.r_lower]
  have hU : 0<topRight q u := by linarith [h.U_lower]
  have hY : 0<topHeight q u := by linarith [h.Y_lower]
  have hw : 0<lowerLeft q u := by linarith [h.w_lower]
  have hr2 : 0<q-u^2 := Real.sqrt_pos.mp hr
  have hU2 : 0<q-(2-u)^2 := Real.sqrt_pos.mp hU
  have hY2 : 0<q-topLeft q u^2 := Real.sqrt_pos.mp hY
  have hw2 : 0<q-lowerHeight q u^2 := Real.sqrt_pos.mp hw
  exact ⟨⟨hu,by linarith,by linarith,by linarith,by linarith⟩,hq,hr,hU,hY,hw⟩

def cosine (h : ℝ) : ℝ := Real.cos (Real.arctan h)
def sine (h : ℝ) : ℝ := Real.sin (Real.arctan h)

theorem cosine_pos (h : ℝ) : 0<cosine h :=
  Real.cos_pos_of_mem_Ioo (Real.arctan_mem_Ioo h)

theorem sine_eq (h : ℝ) : sine h=h*cosine h := by
  rw [sine,cosine,Real.sin_arctan,Real.cos_arctan]
  ring

theorem unit (h : ℝ) : cosine h^2+sine h^2=1 := by
  dsimp [cosine,sine]
  nlinarith [Real.sin_sq_add_cos_sq (Real.arctan h)]

structure TrigBounds (h : ℝ) : Prop where
  c_lower : 2467/2500<cosine h
  c_upper : cosine h<9951/10000
  s_lower : 199/2000<sine h
  s_upper : sine h<81/500

theorem trig_bounds {h : ℝ} (hh : h∈Icc (1/10:ℝ) (41/250)) : TrigBounds h := by
  let D : ℝ := Real.sqrt (1+h^2)
  have hrad : 0<1+h^2 := by positivity
  have hD : 0<D := Real.sqrt_pos.mpr hrad
  have hD2 : D^2=1+h^2 := Real.sq_sqrt hrad.le
  have hh2 := square_bounds hh (by norm_num)
  have hDb : D∈Ioo (10000/9951:ℝ) (2500/2467) := by
    apply sqrt_bounds (l:=101/100) (r:=64181/62500)
      (show 1+h^2∈Icc (101/100:ℝ) (64181/62500) from
        ⟨by linarith [hh2.1],by linarith [hh2.2]⟩) <;> norm_num
  have hc : (2467/2500:ℝ)<cosine h ∧ cosine h<9951/10000 := by
    change (2467/2500:ℝ)<Real.cos (Real.arctan h) ∧
      Real.cos (Real.arctan h)<9951/10000
    rw [Real.cos_arctan]
    constructor
    · apply (lt_div_iff₀ hD).2
      linarith [hDb.2]
    · apply (div_lt_iff₀ hD).2
      linarith [hDb.1]
  have hsL : (199/2000:ℝ)*D<h := by
    by_contra! hbad
    have hsq := square_mono_nonneg (by linarith [hh.1] : 0≤h) hbad
    nlinarith [hh2.1]
  have hsU : h<(81/500:ℝ)*D := by
    by_contra! hbad
    have hsq := square_mono_nonneg (by positivity : 0≤(81/500:ℝ)*D) hbad
    nlinarith [hh2.2]
  refine ⟨hc.1,hc.2,?_,?_⟩
  · change (199/2000:ℝ)<Real.sin (Real.arctan h)
    rw [Real.sin_arctan]
    exact (lt_div_iff₀ hD).2 hsL
  · change Real.sin (Real.arctan h)<81/500
    rw [Real.sin_arctan]
    exact (div_lt_iff₀ hD).2 hsU

theorem TrigBounds.c {h : ℝ} (hT : TrigBounds h) :
    cosine h∈Icc (2467/2500:ℝ) (9951/10000) := ⟨hT.c_lower.le,hT.c_upper.le⟩
theorem TrigBounds.s {h : ℝ} (hT : TrigBounds h) :
    sine h∈Icc (199/2000:ℝ) (81/500) := ⟨hT.s_lower.le,hT.s_upper.le⟩

end SquaresInCircles.Eight.StationaryPrimitives
end
end
end

section
/-!
## Elementary algebra for the whole-rectangle derivative comparisons

`Interval` records a proved closed enclosure
of one actual real expression.  Its operations are ordinary ordered-field
inequalities.  The final construction substitutes the actual circle
coordinates into the position derivative and its two derivatives.  It
does not subdivide a domain or search for a root.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryPrimitives
open Stationary.FiveCornerGeometry

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
  · convert first.mem using 1
    dsimp [positionHalf,firstComponent,secondComponent,slopeRatio]
    ring
  · convert position.mem using 1
    dsimp [positionSecond,positionNorm,positionNormal,positionA,positionb,positionB,
      rightSecond,leftSecond,firstComponent,secondComponent,slopeRatio,curvatureRatio]
  · convert mixed.mem using 1
    dsimp [mixedSecond,mixedNormal,positionA,positionb,positionB,firstTilt,secondTilt,
      firstComponent,secondComponent,slopeRatio]
    ring

end SquaresInCircles.Eight.StationaryPrimitives
end
end
end

section
/-!
## Force primitives of the actual stationary-position family

These estimates are substitutions into the
one radical rectangle, before any stationary equation is imposed.  In
particular the position derivatives and the two corner components are
the original nested-circle formulas, not auxiliary interval variables.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryPrimitives
open Stationary.FiveCornerGeometry

structure ForceBounds (q u h : ℝ) : Prop where
  p_lower : 287/500<slopeRatio q u
  p_upper : slopeRatio q u<637/1000
  a_lower : 599/1000<positionA q (cosine h) (sine h) u
  a_upper : positionA q (cosine h) (sine h) u<7/10
  b_lower : 291/500<positionb q (cosine h) (sine h) u
  b_upper : positionb q (cosine h) (sine h) u<133/200
  k1_lower : 1327/1000<firstComponent q (cosine h) (sine h) u
  k1_upper : firstComponent q (cosine h) (sine h) u<711/500
  k2_lower : 1379/1000<secondComponent q (cosine h) (sine h) u
  k2_upper : secondComponent q (cosine h) (sine h) u<147/100
  E_lower : 469/500< -secondTilt q (cosine h) (sine h) u
  E_upper : -secondTilt q (cosine h) (sine h) u<993/1000

theorem force_bounds_of_primitives {q u h : ℝ}
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hr : RadicalBounds q u) (ht : TrigBounds h) : ForceBounds q u h := by
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  have hnum := product_bounds hl hr.V (by norm_num) (by norm_num)
  have hden := product_bounds hr.U hr.Y (by norm_num) (by norm_num)
  have hp0 := quotient_bounds hnum hden (by norm_num) (by norm_num)
  have hp : slopeRatio q u∈Ioo (287/500:ℝ) (637/1000) := by
    dsimp [slopeRatio]
    exact ⟨by linarith [hp0.1],by linarith [hp0.2]⟩
  have hcu := product_bounds ht.c hu (by norm_num) (by norm_num)
  have hcur := quotient_bounds hcu hr.r (by norm_num) (by norm_num)
  have ha : positionA q (cosine h) (sine h) u∈Ioo (599/1000:ℝ) (7/10) := by
    dsimp [positionA]
    exact ⟨by linarith [ht.s_lower,hcur.1],by linarith [ht.s_upper,hcur.2]⟩
  have hsv := product_bounds ht.s hr.v (by norm_num) (by norm_num)
  have hsvw := quotient_bounds hsv hr.w (by norm_num) (by norm_num)
  have hB : positionB q (cosine h) (sine h) u∈
      Icc ((2467/2500:ℝ)+(199/2000)*(533/1000)/(953/500))
        ((9951/10000:ℝ)+(81/500)*(281/500)/(1897/1000)) := by
    dsimp [positionB]
    exact ⟨by linarith [ht.c_lower,hsvw.1],by linarith [ht.c_upper,hsvw.2]⟩
  have hb0 := product_bounds ⟨hp.1.le,hp.2.le⟩ hB (by norm_num) (by norm_num)
  have hb : positionb q (cosine h) (sine h) u∈Ioo (291/500:ℝ) (133/200) := by
    dsimp [positionb]
    exact ⟨by linarith [hb0.1],by linarith [hb0.2]⟩
  have hrm : lowerRight q u-1∈Icc (741/1000:ℝ) (153/200) :=
    ⟨by linarith [hr.r_lower],by linarith [hr.r_upper]⟩
  have hcrm := product_bounds ht.c hrm (by norm_num) (by norm_num)
  have hsu := product_bounds ht.s hu (by norm_num) (by norm_num)
  have hk1 : firstComponent q (cosine h) (sine h) u∈Ioo (1327/1000:ℝ) (711/500) := by
    dsimp [firstComponent]
    exact ⟨by linarith [hcrm.2,hsu.1],by linarith [hcrm.1,hsu.2]⟩
  have hwm : lowerLeft q u-1∈Icc (897/1000:ℝ) (453/500) :=
    ⟨by linarith [hr.w_lower],by linarith [hr.w_upper]⟩
  have hcv := product_bounds ht.c hr.v (by norm_num) (by norm_num)
  have hswm := product_bounds ht.s hwm (by norm_num) (by norm_num)
  have hk2 : secondComponent q (cosine h) (sine h) u∈Ioo (1379/1000:ℝ) (147/100) := by
    dsimp [secondComponent]
    exact ⟨by linarith [hcv.1,hswm.2],by linarith [hcv.2,hswm.1]⟩
  have hcwm := product_bounds ht.c hwm (by norm_num) (by norm_num)
  have hE : -secondTilt q (cosine h) (sine h) u∈Ioo (469/500:ℝ) (993/1000) := by
    dsimp [secondTilt]
    exact ⟨by linarith [hcwm.1,hsv.1],by linarith [hcwm.2,hsv.2]⟩
  exact ⟨hp.1,hp.2,ha.1,ha.2,hb.1,hb.2,hk1.1,hk1.2,hk2.1,hk2.2,hE.1,hE.2⟩

theorem force_bounds {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : ForceBounds q u h :=
  force_bounds_of_primitives hu (radical_bounds hq hu) (trig_bounds hh)

theorem ForceBounds.p {q u h : ℝ} (hf : ForceBounds q u h) :
    slopeRatio q u∈Icc (287/500:ℝ) (637/1000) := ⟨hf.p_lower.le,hf.p_upper.le⟩
theorem ForceBounds.a {q u h : ℝ} (hf : ForceBounds q u h) :
    positionA q (cosine h) (sine h) u∈Icc (599/1000:ℝ) (7/10) :=
  ⟨hf.a_lower.le,hf.a_upper.le⟩
theorem ForceBounds.b {q u h : ℝ} (hf : ForceBounds q u h) :
    positionb q (cosine h) (sine h) u∈Icc (291/500:ℝ) (133/200) :=
  ⟨hf.b_lower.le,hf.b_upper.le⟩
theorem ForceBounds.k1 {q u h : ℝ} (hf : ForceBounds q u h) :
    firstComponent q (cosine h) (sine h) u∈Icc (1327/1000:ℝ) (711/500) :=
  ⟨hf.k1_lower.le,hf.k1_upper.le⟩
theorem ForceBounds.k2 {q u h : ℝ} (hf : ForceBounds q u h) :
    secondComponent q (cosine h) (sine h) u∈Icc (1379/1000:ℝ) (147/100) :=
  ⟨hf.k2_lower.le,hf.k2_upper.le⟩
theorem ForceBounds.E {q u h : ℝ} (hf : ForceBounds q u h) :
    -secondTilt q (cosine h) (sine h) u∈Icc (469/500:ℝ) (993/1000) :=
  ⟨hf.E_lower.le,hf.E_upper.le⟩

end SquaresInCircles.Eight.StationaryPrimitives
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.StationaryTerminal
open Stationary.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

def rawAlpha (q u h : ℝ) : ℝ := positionA q (cosine h) (sine h) u
def rawBeta (q u h : ℝ) : ℝ := rawAlpha q u h*topRight q u/(2-u)
def rawEpsilon (q u h : ℝ) : ℝ :=
  secondComponent q (cosine h) (sine h) u/firstComponent q (cosine h) (sine h) u

/-- The mass order is the original-anchor order A,B,D,E,H. -/
def rawMass (q u h : ℝ) : Fin 5 → ℝ := ![
  cosine h/(2*lowerRight q u),
  rawAlpha q u h/(2*(2-u)),
  rawBeta q u h/(2*topLeft q u),
  sine h*rawEpsilon q u h/(2*lowerLeft q u),
  1/(2*firstComponent q (cosine h) (sine h) u)]

def rawMassSum (q u h : ℝ) : ℝ := ∑i : Fin 5,rawMass q u h i
def omega (q u h : ℝ) : ℝ := 1/rawMassSum q u h

def weights (q u h : ℝ) : CanonicalNegativeStress.Parameters where
  a := omega q u h*rawAlpha q u h
  beta := omega q u h*rawBeta q u h
  delta := omega q u h*rawBeta q u h*topHeight q u/topLeft q u
  epsilon := omega q u h*rawEpsilon q u h
  omega := omega q u h
  mu := fun i => omega q u h*rawMass q u h i

theorem massSum_formula (q u h : ℝ) :
    rawMassSum q u h=rawMass q u h 0+rawMass q u h 1+rawMass q u h 2+
      rawMass q u h 3+rawMass q u h 4 := by
  simp [rawMassSum,Fin.sum_univ_succ]
  ring

/-- The single normalization estimate, before using stationarity. -/
theorem raw_mass_bounds {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    (∀i,(1/40:ℝ)<rawMass q u h i) ∧
      5/4<rawMassSum q u h ∧ rawMassSum q u h<3/2 := by
  have hr := radical_bounds hq hu
  have ht := trig_bounds hh
  have hf := force_bounds hq hu hh
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  let two := Interval.point 2
  let one := Interval.point 1
  let L := Interval.of_bounds hl
  let R := Interval.of_bounds hr.r
  let U := Interval.of_bounds hr.U
  let V := Interval.of_bounds hr.V
  let W := Interval.of_bounds hr.w
  let C := Interval.of_bounds ht.c
  let S := Interval.of_bounds ht.s
  let A := Interval.of_bounds hf.a
  let K1 := Interval.of_bounds hf.k1
  let K2 := Interval.of_bounds hf.k2
  let B : Interval (rawBeta q u h) := (A.mul U).div L (by norm_num [L,Interval.of_bounds])
  let E : Interval (rawEpsilon q u h) := K2.div K1 (by norm_num [K1,Interval.of_bounds])
  let mA : Interval (rawMass q u h 0) := C.div (two.mul R)
    (by norm_num [two,R,Interval.point,Interval.of_bounds,Interval.mul])
  let mB : Interval (rawMass q u h 1) := A.div (two.mul L)
    (by norm_num [two,L,Interval.point,Interval.of_bounds,Interval.mul])
  let mD : Interval (rawMass q u h 2) := B.div (two.mul V)
    (by norm_num [two,V,Interval.point,Interval.of_bounds,Interval.mul])
  let mE : Interval (rawMass q u h 3) := (S.mul E).div (two.mul W)
    (by norm_num [two,W,Interval.point,Interval.of_bounds,Interval.mul])
  let mH : Interval (rawMass q u h 4) := one.div (two.mul K1)
    (by norm_num [two,K1,Interval.point,Interval.of_bounds,Interval.mul])
  have hA := mA.mem
  have hB := mB.mem
  have hD := mD.mem
  have hE := mE.mem
  have hH := mH.mem
  have hsum := ((((mA.add mB).add mD).add mE).add mH).mem
  norm_num [mA,mB,mD,mE,mH,B,E,L,R,U,V,W,C,S,A,K1,K2,two,one,
    Interval.of_bounds,Interval.point,Interval.add,Interval.mul,Interval.div,Interval.inv]
    at hA hB hD hE hH hsum
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact lt_of_lt_of_le (by norm_num) hA.1
    · exact lt_of_lt_of_le (by norm_num) hB.1
    · exact lt_of_lt_of_le (by norm_num) hD.1
    · exact lt_of_lt_of_le (by norm_num) hE.1
    · exact lt_of_lt_of_le (by norm_num) hH.1
  · rw [massSum_formula]
    linarith [hsum.1]
  · rw [massSum_formula]
    linarith [hsum.2]

theorem omega_bounds {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    2/3<omega q u h ∧ omega q u h<4/5 := by
  obtain ⟨_,hmL,hmU⟩ := raw_mass_bounds hq hu hh
  have hm : 0<rawMassSum q u h := by linarith
  dsimp [omega]
  constructor
  · apply (lt_div_iff₀ hm).2
    linarith
  · apply (div_lt_iff₀ hm).2
    linarith

theorem positive {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : (weights q u h).Positive := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  have hm := (raw_mass_bounds hq hu hh).1
  have ho : 0<omega q u h := by linarith [(omega_bounds hq hu hh).1]
  have ha : 0<rawAlpha q u h := by dsimp [rawAlpha]; linarith [hf.a_lower]
  have hl : 0<2-u := by linarith [hu.2]
  have hU : 0<topRight q u := by linarith [hr.U_lower]
  have hV : 0<topLeft q u := by linarith [hr.V_lower]
  have hY : 0<topHeight q u := by linarith [hr.Y_lower]
  have hb : 0<rawBeta q u h := div_pos (mul_pos ha hU) hl
  have he : 0<rawEpsilon q u h := div_pos (by linarith [hf.k2_lower]) (by linarith [hf.k1_lower])
  refine ⟨(mul_pos ho ha).le,(mul_pos ho hb).le,?_,(mul_pos ho he).le,ho.le,?_⟩
  · exact (div_pos (mul_pos (mul_pos ho hb) hY) hV).le
  · intro i
    exact mul_pos ho (by linarith [hm i])

theorem mass_one {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : massSum (weights q u h)=1 := by
  have hm : rawMassSum q u h≠0 := ne_of_gt (by linarith [(raw_mass_bounds hq hu hh).2.1])
  dsimp [massSum,weights]
  rw [← Finset.mul_sum]
  change (1/rawMassSum q u h)*rawMassSum q u h=1
  field_simp [hm]

theorem mass_lower {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) (i : Fin 5) :
    1/60<(weights q u h).mu i := by
  have hm := (raw_mass_bounds hq hu hh).1 i
  have ho := (omega_bounds hq hu hh).1
  have hp := mul_lt_mul_of_pos_left hm (by linarith : 0<omega q u h)
  dsimp [weights]
  nlinarith

/-- Exact cancellation at a position stationary point.  No tilt
stationarity or zero-defect equation is required. -/
theorem rawBeta_cancellation {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    rawBeta q u h=rawEpsilon q u h*(topLeft q u/topHeight q u)*
      cosine h*(1+h*lowerHeight q u/lowerLeft q u) := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  have hL : 2-u≠0 := ne_of_gt (by linarith [hu.2])
  have hU : topRight q u≠0 := ne_of_gt (by linarith [hr.U_lower])
  have hY : topHeight q u≠0 := ne_of_gt (by linarith [hr.Y_lower])
  have hK : firstComponent q (cosine h) (sine h) u≠0 := ne_of_gt (by linarith [hf.k1_lower])
  have ha : rawAlpha q u h=
      secondComponent q (cosine h) (sine h) u*slopeRatio q u*
        positionB q (cosine h) (sine h) u/firstComponent q (cosine h) (sine h) u := by
    apply (eq_div_iff hK).2
    dsimp [rawAlpha,positionA,positionB,positionHalf] at hz ⊢
    nlinarith
  rw [rawBeta,ha]
  dsimp [rawEpsilon,slopeRatio,positionB]
  rw [sine_eq]
  field_simp [hL,hU,hY,hK,ne_of_gt (by linarith [hr.w_lower] : 0<lowerLeft q u)]

end SquaresInCircles.Eight.StationaryTerminal
end
end
end
