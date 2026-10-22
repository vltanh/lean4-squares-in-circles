module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeEndpoint

/-!
# The named references for the twelve negative-core endpoint curves

Uncompiled source. Eight references bound H-H'^2/1.3, and the other
four curves use their initial positive derivative. Every radical is
enclosed on its actual expression by positive rational square bounds.
The whole-interval curvature was proved before these substitutions.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Endpoint
open CommonQuarter Arithmetic StationaryPrimitives Reference

def AABox (diagonal : Bool) : Interval (AA diagonal) := by
  cases diagonal
  · exact Interval.point _
  · exact coreDiagonal.add (Interval.point (1/2))
def BBBox (diagonal : Bool) : Interval (BB diagonal) := by
  cases diagonal
  · exact Interval.point _
  · exact coreDiagonal.sub (Interval.point (1/2))
def bCBox (diagonal : Bool) : Interval (bC diagonal) := by
  cases diagonal
  · exact Interval.point _
  · exact coreDiagonal

def heightBox (diagonal : Bool) {φ : ℝ} (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ)) :
    Interval (height diagonal φ) :=
  ((Interval.point 1).add ((AABox diagonal).mul C)).sub ((BBBox diagonal).mul S)
def radicandBox {u : ℝ} (U : Interval u) : Interval (Q0-u^2) :=
  (Interval.point Q0).sub U.square
def radicalBox {u : ℝ} (U : Interval u) (hU : 0≤(radicandBox U).lo) : Interval (v u) :=
  rootSix (radicandBox U) (3/2) (by norm_num) hU
def valueBox (r : Row) (diagonal : Bool) {φ : ℝ} (Phi : Interval φ)
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) :
    Interval (H r diagonal φ) := by
  convert ((((Phi.add (Interval.point (ocC r))).add
    ((Interval.point (ocP r)).mul (U.sub (Interval.point (1/2))))).sub
      ((Interval.point (ocQ r)).mul (V.sub (Interval.point (1/2))))).add
        ((Interval.point (ocG r)).mul (bCBox diagonal)) using 1 <;>
    dsimp [H,M] <;> simp only [sub_add_cancel] <;> ring
def firstBox (r : Row) (diagonal : Bool) {φ : ℝ}
    (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ))
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) (hV : 0<V.lo) :
    Interval (Hd r diagonal φ) := by
  convert (Interval.point 1).sub
    (((Interval.point (ocP r)).add (((Interval.point (ocQ r)).mul U).div V hV)).mul
      (((AABox diagonal).mul S).add ((BBBox diagonal).mul C))) using 1 <;>
    dsimp [Hd,M1,speed] <;> simp only [sub_add_cancel] <;> ring

def reference (r : Row) (diagonal : Bool) : ℝ :=
  if r=0 then (if diagonal then 43/40 else 117/100)
  else if r=4 then (if diagonal then 1047/1000 else 1149/1000)
  else if r=11 then (if diagonal then 481/500 else 1061/1000)
  else if r=23 then (if diagonal then 132/125 else 287/250)
  else 1
theorem reference_positive (r : Row) (diagonal : Bool) : 0≤reference r diagonal := by
  fin_cases r <;> cases diagonal <;> norm_num [reference]
theorem reference_mem (r : Row) (diagonal : Bool) : reference r diagonal∈earlyAngles := by
  fin_cases r <;> cases diagonal <;> norm_num [reference,earlyAngles,lowerAngle] <;>
    linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]
def refS (r : Row) (diagonal : Bool) : Interval (Real.sin (reference r diagonal)) :=
  sine (reference_positive r diagonal)
def refC (r : Row) (diagonal : Bool) : Interval (Real.cos (reference r diagonal)) :=
  cosine (reference_positive r diagonal)
def refU (r : Row) (diagonal : Bool) : Interval (height diagonal (reference r diagonal)) :=
  heightBox diagonal (refS r diagonal) (refC r diagonal)
theorem ref_radicand (r : Row) (diagonal : Bool) : 0≤(radicandBox (refU r diagonal)).lo := by
  fin_cases r <;> cases diagonal <;>
    dsimp [radicandBox,refU,heightBox,AABox,BBBox,refS,refC,reference,AA,BB] <;> mixed_fixed
def refV (r : Row) (diagonal : Bool) : Interval (v (height diagonal (reference r diagonal))) :=
  radicalBox (refU r diagonal) (ref_radicand r diagonal)
theorem refV_positive (r : Row) (diagonal : Bool) : 0<(refV r diagonal).lo := by
  fin_cases r <;> cases diagonal <;>
    dsimp [refV,radicalBox,radicandBox,refU,heightBox,AABox,BBBox,refS,refC,reference,AA,BB] <;> mixed_fixed
def refH (r : Row) (diagonal : Bool) : Interval (H r diagonal (reference r diagonal)) :=
  valueBox r diagonal (Interval.point _) (refU r diagonal) (refV r diagonal)
def refHd (r : Row) (diagonal : Bool) : Interval (Hd r diagonal (reference r diagonal)) :=
  firstBox r diagonal (refS r diagonal) (refC r diagonal) (refU r diagonal) (refV r diagonal)
    (refV_positive r diagonal)
def refQuadratic (r : Row) (diagonal : Bool) :
    Interval (H r diagonal (reference r diagonal)-(Hd r diagonal (reference r diagonal))^2/(13/10)) :=
  (refH r diagonal).sub ((refHd r diagonal).square.div (Interval.point (13/10)) (by norm_num [Interval.point]))

theorem reference_reserve (r : Row) (hr : r=0∨r=4∨r=11∨r=23) (diagonal : Bool) :
    (89809/100000:ℝ)<H r diagonal (reference r diagonal)-(Hd r diagonal (reference r diagonal))^2/(13/10) := by
  have hbound : (89809/100000:ℝ)<(refQuadratic r diagonal).lo := by
    rcases hr with rfl|rfl|rfl|rfl <;> cases diagonal <;>
      dsimp [refQuadratic,refH,refHd,valueBox,firstBox,refV,radicalBox,radicandBox,
        refU,heightBox,AABox,BBBox,bCBox,refS,refC,reference,AA,BB,bC] <;> mixed_fixed
  exact hbound.trans_le (refQuadratic r diagonal).mem.1

def initialPhi : Interval lowerAngle := halfPi.sub (Interval.point (7/10))
def initialS : Interval (Real.sin lowerAngle) := by
  convert cosine (by norm_num : (0:ℝ)≤7/10) using 1
  simpa [lowerAngle,angle,direction] using angle_sin false (7/10)
def initialC : Interval (Real.cos lowerAngle) := by
  convert sine (by norm_num : (0:ℝ)≤7/10) using 1
  simpa [lowerAngle,angle,direction] using angle_cos false (7/10)
def initialU (diagonal : Bool) : Interval (height diagonal lowerAngle) := heightBox diagonal initialS initialC
theorem initial_radicand (diagonal : Bool) : 0≤(radicandBox (initialU diagonal)).lo := by
  cases diagonal <;> dsimp [radicandBox,initialU,heightBox,AABox,BBBox,initialS,initialC,AA,BB] <;> mixed_fixed
def initialV (diagonal : Bool) : Interval (v (height diagonal lowerAngle)) :=
  radicalBox (initialU diagonal) (initial_radicand diagonal)
theorem initialV_positive (diagonal : Bool) : 0<(initialV diagonal).lo := by
  cases diagonal <;> dsimp [initialV,radicalBox,radicandBox,initialU,heightBox,AABox,BBBox,initialS,initialC,AA,BB] <;> mixed_fixed
def initialH (r : Row) (diagonal : Bool) : Interval (H r diagonal lowerAngle) :=
  valueBox r diagonal initialPhi (initialU diagonal) (initialV diagonal)
def initialHd (r : Row) (diagonal : Bool) : Interval (Hd r diagonal lowerAngle) :=
  firstBox r diagonal initialS initialC (initialU diagonal) (initialV diagonal) (initialV_positive diagonal)

theorem initial_reserve (r : Row) (hr : r=12∨r=19) (diagonal : Bool) :
    (89809/100000:ℝ)<H r diagonal lowerAngle ∧ 0<Hd r diagonal lowerAngle := by
  have hv : (89809/100000:ℝ)<(initialH r diagonal).lo := by
    rcases hr with rfl|rfl <;> cases diagonal <;>
      dsimp [initialH,valueBox,initialPhi,initialV,radicalBox,radicandBox,initialU,
        heightBox,AABox,BBBox,bCBox,initialS,initialC,AA,BB,bC] <;> mixed_fixed
  have hd : 0<(initialHd r diagonal).lo := by
    rcases hr with rfl|rfl <;> cases diagonal <;>
      dsimp [initialHd,firstBox,initialV,radicalBox,radicandBox,initialU,
        heightBox,AABox,BBBox,initialS,initialC,AA,BB] <;> mixed_fixed
  exact ⟨hv.trans_le (initialH r diagonal).mem.1,hd.trans_le (initialHd r diagonal).mem.1⟩

theorem lower (r : Row) (hr : Remaining r) (diagonal : Bool) {φ : ℝ}
    (hφ : φ∈earlyAngles) : (89809/100000:ℝ)<H r diagonal φ := by
  by_cases hi : r=12∨r=19
  · have h := curvature_tangent (κ:=(13/20:ℝ)) hφ early_left
      (fun t ht => H_hasDerivAt r diagonal ht)
      (fun t ht => Hd_hasDerivAt r diagonal ht)
      (fun t ht => (curvature r hr diagonal ht).le)
    have hinit := initial_reserve r hi diagonal
    have hp := mul_nonneg hinit.2.le (sub_nonneg.mpr hφ.1)
    nlinarith [sq_nonneg (φ-lowerAngle)]
  · have hrows : r=0∨r=4∨r=11∨r=23 := by
      rcases (remaining_iff r).1 hr with h|h|h|h|h|h <;> simp_all
    have href := reference_reserve r hrows diagonal
    have h := positive_of_curvature (f:=fun t => H r diagonal t-89809/100000)
      (d:=Hd r diagonal) (dd:=Hdd r diagonal) (κ:=(13/20:ℝ)) (by norm_num)
      hφ (reference_mem r diagonal)
      (fun t ht => (H_hasDerivAt r diagonal ht).sub_const (89809/100000))
      (fun t ht => Hd_hasDerivAt r diagonal ht)
      (fun t ht => (curvature r hr diagonal ht).le) (by nlinarith)
    linarith

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.Endpoint
