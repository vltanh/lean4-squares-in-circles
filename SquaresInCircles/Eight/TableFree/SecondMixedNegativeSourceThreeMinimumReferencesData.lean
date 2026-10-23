module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreeMinimumShape

/-!
# Exact reference algebra for the negative-core minimum

Every enclosure remains attached to its actual real expression. Circle
heights and stationary roots use integer-square comparisons. Arctangent
arguments are first rounded outwards to explicit rational endpoints;
the proved alternating polynomials are evaluated only at those points.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum.References
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

def widen {x : ℝ} (X : Interval x) (l u : ℝ) (hl : l≤X.lo) (hu : X.hi≤u) : Interval x :=
  ⟨l,u,hl.trans X.mem.1,X.mem.2.trans hu⟩

def heightBox {B : ℝ} (hB : B∈targets) (l u : ℝ) (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2+(B+1/2)^2<Q0) (hhi : Q0<u^2+(B+1/2)^2) : Interval (U B) := by
  have hh := shifted_chart_reference (outer_domain (target_domain hB)) hl hu hlo hhi
  exact Interval.of_bounds ⟨hh.1.le,hh.2.le⟩

def tBox {B : ℝ} (X : Interval (U B)) : Interval (T B) :=
  (Interval.point (Q0+1)).sub ((Interval.point 2).mul X)

def vBox {B : ℝ} (Y : Interval B) : Interval (V B) := Y.add (Interval.point (1/2))

def stationaryBox {h B : ℝ} (hh : h∈slopes) (hB : B∈targets)
    (X : Interval (U B)) (l u : ℝ) (hl : 0≤l) (hu : 0≤u)
    (hlo : l^2<h^2*(Q0+1-2*X.hi)-1)
    (hhi : h^2*(Q0+1-2*X.lo)-1<u^2) : Interval (S h B) := by
  have hs := S_positive hh hB
  have hsq := S_sq hh hB
  have hp := mul_nonneg (sq_nonneg h) (show 0≤X.hi-U B by linarith [X.mem.2])
  have hq := mul_nonneg (sq_nonneg h) (show 0≤U B-X.lo by linarith [X.mem.1])
  dsimp [T] at hsq
  exact ⟨l,u,by nlinarith,by nlinarith⟩

def arg (B : ℝ) : ℝ := (V B-P B)/(V B+P B)

lemma phase_identity {B : ℝ} (hB : B∈targets) : beta B=Real.pi/4+Real.arctan (arg B) := by
  have hv : 0≤V B := by dsimp [V]; linarith [hB.1]
  have hh := CoreAngleEndpoint.arctan_complement (P_positive hB) hv
  have hid : (P B-V B)/(P B+V B)= -arg B := by dsimp [arg]; ring
  rw [hid,Real.arctan_neg] at hh
  dsimp [beta]
  linarith

def argumentBox {B : ℝ} (Y : Interval B) (X : Interval (U B))
    (hden : 0<((vBox Y).add (X.sub (Interval.point 1))).lo) : Interval (arg B) :=
  ((vBox Y).sub (X.sub (Interval.point 1))).div
    ((vBox Y).add (X.sub (Interval.point 1))) hden

def atanLo (x : ℝ) : ℝ := if 0≤x then atanLower x else -atanUpper (-x)
def atanHi (x : ℝ) : ℝ := if 0≤x then atanUpper x else -atanLower (-x)

lemma atanLo_le (x : ℝ) : atanLo x≤Real.arctan x := by
  by_cases hx : 0≤x
  · simpa [atanLo,hx] using atanLower_le hx
  · have hh := arctan_le_atanUpper (show 0≤ -x by linarith)
    rw [Real.arctan_neg] at hh
    dsimp [atanLo]
    rw [if_neg hx]
    linarith

lemma le_atanHi (x : ℝ) : Real.arctan x≤atanHi x := by
  by_cases hx : 0≤x
  · simpa [atanHi,hx] using arctan_le_atanUpper hx
  · have hh := atanLower_le (show 0≤ -x by linarith)
    rw [Real.arctan_neg] at hh
    dsimp [atanHi]
    rw [if_neg hx]
    linarith

def atanBox {x : ℝ} (X : Interval x) : Interval (Real.arctan x) :=
  ⟨atanLo X.lo,atanHi X.hi,
    (atanLo_le X.lo).trans (Real.arctan_le_arctan X.mem.1),
    (Real.arctan_le_arctan X.mem.2).trans (le_atanHi X.hi)⟩

def betaBox {B : ℝ} (hB : B∈targets) (A : Interval (arg B)) : Interval (beta B) := by
  let H := (piBox.div (Interval.point 4) (by norm_num [Interval.point])).add (atanBox A)
  exact ⟨H.lo,H.hi,by rw [phase_identity hB]; exact H.mem⟩

def baseBox {B : ℝ} (X : Interval (U B)) : Interval (baseE (U B)) :=
  (((Interval.point 2).mul X.square).sub ((Interval.point (4*Q0)).mul X)).add
    (Interval.point (Q0*(Q0+1)))

def phaseFirstBox {B : ℝ} (X : Interval (U B)) (hX : 0<X.lo)
    (hT : 0<(tBox X).lo) : Interval (betaD B) :=
  ((Interval.point Q0).sub X).div (X.mul (tBox X)) (Interval.mul_lo_pos hX hT)

def phaseSecondBox {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo)
    (hT : 0<(tBox X).lo) : Interval (betaDD B) :=
  ((baseBox X).mul (vBox Y)).div (X.cube.mul (tBox X).square)
    (Interval.mul_lo_pos (Interval.cube_lo_pos hX) (Interval.square_lo_pos hT))

def stationaryFirstBox {h B : ℝ} (Y : Interval B) (X : Interval (U B)) (W : Interval (S h B))
    (hX : 0<X.lo) (hT : 0<(tBox X).lo) : Interval (R h B) :=
  ((ratioBox Y X hX).mul W).div (tBox X) hT

def stationarySecondBox {h B : ℝ} (Y : Interval B) (X : Interval (U B)) (W : Interval (S h B))
    (hX : 0<X.lo) (hT : 0<(tBox X).lo) (hW : 0<W.lo) : Interval (RD h B) :=
  ((((ratioDBox X hX).mul W).div (tBox X) hT).add
    (((Interval.point (h^2)).mul (ratioBox Y X hX).square).div (W.mul (tBox X))
      (Interval.mul_lo_pos hW hT))).sub
        ((((Interval.point 2).mul (ratioBox Y X hX).square).mul W).div (tBox X).square
          (Interval.square_lo_pos hT))

def valueBox {h B : ℝ} (Y : Interval B) (X : Interval (U B))
    (W : Interval (S h B)) (A : Interval (beta B)) : Interval (E h B) :=
  ((((((A.add (atanBox W)).sub W).sub (Interval.point e)).sub
    (Interval.point (epsilon h))).add (Interval.point (h/2))).sub (labelBox LLabel Y X))

def firstBox {h B : ℝ} (Y : Interval B) (X : Interval (U B)) (W : Interval (S h B))
    (hX : 0<X.lo) (hT : 0<(tBox X).lo) : Interval (E1 h B) :=
  (((phaseFirstBox X hX hT).sub (stationaryFirstBox Y X W hX hT)).sub
    (OppositeThree.ReferenceAlgebra.firstBox LLabel Y X hX))

def secondBox {h B : ℝ} (Y : Interval B) (X : Interval (U B)) (W : Interval (S h B))
    (hX : 0<X.lo) (hT : 0<(tBox X).lo) (hW : 0<W.lo) : Interval (E2 h B) :=
  (((phaseSecondBox Y X hX hT).sub (stationarySecondBox Y X W hX hT hW)).sub
    (OppositeThree.ReferenceAlgebra.secondBox LLabel Y X hX))

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum.References
