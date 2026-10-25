module

public import SquaresInCircles.Eight.TableFree.SecondMixedHeightLabel
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeReferenceAlgebra

/-!
# Individual references for the whole L-height derivative argument

Every radical enclosure is evaluated at a named analytic reference.
Whole-interval monotonicity and convexity, rather than a continuous
cover, propagate these comparisons.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.LHeightReference
open CommonQuarter CorePairGeometry Arithmetic HeightLabel
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra (rootStep rootThree)

def rootAt (u s : ℝ) (hs : 0<s) (hu : 0≤Q0-u^2) : Interval (root u) :=
  rootThree (Interval.point (Q0-u^2)) s hs hu

def firstBox (u : ℝ) (R : Interval (root u)) (hR : 0<R.lo) : Interval (LHeight.d1 u) :=
  (Interval.point (-2*LHeight.v*u-LHeight.k/2)).add
    ((Interval.point (LHeight.k*Q0+LHeight.w*u-2*LHeight.k*u^2)).div R hR)

def secondBox (u : ℝ) (R : Interval (root u)) (hR : 0<R.lo) : Interval (LHeight.d2 u) :=
  (Interval.point (-2*LHeight.v)).add
    ((Interval.point (LHeight.w*Q0-3*LHeight.k*Q0*u+2*LHeight.k*u^3)).div R.cube
      (Interval.cube_lo_pos hR))

def thirdBox (u : ℝ) (R : Interval (root u)) (hR : 0<R.lo) : Interval (LHeight.d3 u) := by
  let P := R.square.mul R.cube
  have hP : 0<P.lo := Interval.mul_lo_pos (Interval.square_lo_pos hR) (Interval.cube_lo_pos hR)
  convert (Interval.point (3*Q0*(LHeight.w*u-LHeight.k*Q0))).div P hP using 1 <;>
    dsimp [HeightLabel.d3] <;> congr 1 <;> ring

local macro "height_reference" : tactic => `(tactic|
  norm_num [rootAt,rootThree,rootStep,firstBox,secondBox,thirdBox,LHeight,Q0,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

/-- The enclosure of a transported interval is the transported enclosure. -/
private lemma r29_cast_lo {v w : ℝ} (hvw : v=w) (h : Interval v=Interval w) (x : Interval v) :
    (cast h x).lo=x.lo := by
  subst hvw
  rfl

private lemma r29_thirdBox_lo (u : ℝ) (R : Interval (root u)) (hR : 0<R.lo) :
    (thirdBox u R hR).lo=((Interval.point (3*Q0*(LHeight.w*u-LHeight.k*Q0))).div
      (R.square.mul R.cube)
      (Interval.mul_lo_pos (Interval.square_lo_pos hR) (Interval.cube_lo_pos hR))).lo := by
  unfold thirdBox
  dsimp only
  exact r29_cast_lo (by dsimp [HeightLabel.d3]; ring) _ _

lemma initial_third : (47/20:ℝ)<LHeight.d3 (171/125) := by
  let R := rootAt (171/125) (143/100) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let D := thirdBox (171/125) R hR
  have hh : (47/20:ℝ)<D.lo := by
    dsimp only [D]
    rw [r29_thirdBox_lo]
    dsimp [R]; height_reference
  exact hh.trans_le D.mem.1

lemma stationary_reference : (479/500:ℝ)<LHeight.d1 (161/100) ∧
    |LHeight.d2 (161/100)|<(61/1000:ℝ) := by
  let R := rootAt (161/100) (23/20) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let F := firstBox (161/100) R hR
  let D := secondBox (161/100) R hR
  have hf : (479/500:ℝ)<F.lo := by dsimp [F,R]; height_reference
  have hl : -(61/1000:ℝ)<D.lo := by dsimp [D,R]; height_reference
  have hu : D.hi<(61/1000:ℝ) := by dsimp [D,R]; height_reference
  exact ⟨hf.trans_le F.mem.1,abs_lt.mpr ⟨hl.trans_le D.mem.1,D.mem.2.trans_lt hu⟩⟩

lemma low_second : LHeight.d2 (8/5)<(-9/100:ℝ) := by
  let R := rootAt (8/5) (117/100) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let D := secondBox (8/5) R hR
  have hh : D.hi<(-9/100:ℝ) := by dsimp [D,R]; height_reference
  exact D.mem.2.trans_lt hh

lemma high_second : (4/5:ℝ)<LHeight.d2 (33/20) := by
  let R := rootAt (33/20) (11/10) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let D := secondBox (33/20) R hR
  have hh : (4/5:ℝ)<D.lo := by dsimp [D,R]; height_reference
  exact hh.trans_le D.mem.1

lemma late_second : LHeight.d2 (81/50)<(23/100:ℝ) := by
  let R := rootAt (81/50) (57/50) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let D := secondBox (81/50) R hR
  have hh : D.hi<(23/100:ℝ) := by dsimp [D,R]; height_reference
  exact D.mem.2.trans_lt hh

lemma zero_initial : LHeight.d1 (159/100)<1 ∧ LHeight.d2 (159/100)<0 ∧
    (13:ℝ)<LHeight.d3 (159/100) := by
  let R := rootAt (159/100) (59/50) (by norm_num) (by norm_num [Q0])
  have hR : 0<R.lo := by dsimp [R]; height_reference
  let F := firstBox (159/100) R hR
  let D := secondBox (159/100) R hR
  let T := thirdBox (159/100) R hR
  have hf : F.hi<(1:ℝ) := by dsimp [F,R]; height_reference
  have hd : D.hi<(0:ℝ) := by dsimp [D,R]; height_reference
  have ht : (13:ℝ)<T.lo := by
    dsimp only [T]
    rw [r29_thirdBox_lo]
    dsimp [R]; height_reference
  exact ⟨F.mem.2.trans_lt hf,D.mem.2.trans_lt hd,ht.trans_le T.mem.1⟩

end SquaresInCircles.Eight.TableFree.SecondWord.LHeightReference
