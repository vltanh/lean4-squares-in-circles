module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameStationaryData
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroReferences

/-!
# Named stationary references from Sections 5.2--5.3

Uncompiled source draft. Every box carries its actual expression. The
only source coordinates evaluated are .293, .6, .77, and .78, exactly
as in the written coupled proof. The variable source intervals are not
partitioned and no sampled minimum is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Stationary.References
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.OppositeZero.Reference (rootAt rootAt_lo_positive)

abbrev referenceDomain : Set ℝ := Icc 0 (9/10)

def slopeBox (r : Row) (b : ℝ) (hb : b∈referenceDomain) : Interval (l r b) :=
  (Interval.point (q r)).sub ((Interval.point (p r)).mul
    (ratioBox (Interval.point b) (rootAt b hb) (rootAt_lo_positive hb)))
def alphaBox (r : Row) (b : ℝ) (hb : b∈referenceDomain) : Interval (alpha r b) :=
  (Interval.point (-p r)).mul (ratioDBox (rootAt b hb) (rootAt_lo_positive hb))
def massBox (r : Row) (b : ℝ) (hb : b∈referenceDomain)
    (hl : 0<(slopeBox r b hb).lo) : Interval (mass r b) :=
  (Interval.point (b-1/2)).square.add
    ((Interval.point 1).div (slopeBox r b hb).square (Interval.square_lo_pos hl))
def heightBox (r : Row) (b : ℝ) (hb : b∈referenceDomain)
    (hl : 0<(slopeBox r b hb).lo) : Interval (height r b) :=
  ((Interval.point (Q0+1)).sub (massBox r b hb hl)).div (Interval.point 2)
    (by norm_num [Interval.point])
def GBox (r : Row) (b : ℝ) (hb : b∈referenceDomain)
    (hl : 0<(slopeBox r b hb).lo) : Interval (G r b) :=
  (Interval.point (b-1/2)).sub ((alphaBox r b hb).div
    (slopeBox r b hb).cube (Interval.cube_lo_pos hl))

macro "stationary_reference_arithmetic" : tactic => `(tactic|
  norm_num [slopeBox,alphaBox,massBox,heightBox,GBox,
    SecondWord.OppositeZero.Reference.rootAt,rootThree,rootStep,ratioBox,ratioDBox,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.cube,Interval.div,Interval.inv,p,q,Q0])

lemma initial_slopes : (23/25:ℝ)<l 1 (293/1000) ∧ (17/20:ℝ)<l 3 (293/1000) := by
  have h1 := (slopeBox 1 (293/1000) (by norm_num)).mem.1
  have h3 := (slopeBox 3 (293/1000) (by norm_num)).mem.1
  have r1 : (23/25:ℝ)<(slopeBox 1 (293/1000) (by norm_num)).lo := by
    stationary_reference_arithmetic
  have r3 : (17/20:ℝ)<(slopeBox 3 (293/1000) (by norm_num)).lo := by
    stationary_reference_arithmetic
  exact ⟨r1.trans_le h1,r3.trans_le h3⟩

lemma row_one_end : (19/5000:ℝ)<G 1 (3/5) ∧ |G 1 (3/5)|<(1/250:ℝ) ∧
    (923/500:ℝ)<height 1 (3/5) ∧ height 1 (3/5)<4723/2500 ∧
      l 1 (3/5)<943/1000 := by
  have hl : 0<(slopeBox 1 (3/5) (by norm_num)).lo := by stationary_reference_arithmetic
  let D := GBox 1 (3/5) (by norm_num) hl
  let H := heightBox 1 (3/5) (by norm_num) hl
  have rD : (19/5000:ℝ)<D.lo ∧ D.hi<(1/250:ℝ) := by
    dsimp [D]
    constructor <;> stationary_reference_arithmetic
  have rH : (923/500:ℝ)<H.lo ∧ H.hi<(4723/2500:ℝ) := by
    dsimp [H]
    constructor <;> stationary_reference_arithmetic
  have rL : (slopeBox 1 (3/5) (by norm_num)).hi<(943/1000:ℝ) := by
    stationary_reference_arithmetic
  exact ⟨rD.1.trans_le D.mem.1,abs_lt.mpr ⟨by linarith [D.mem.1],D.mem.2.trans_lt rD.2⟩,
    rH.1.trans_le H.mem.1,H.mem.2.trans_lt rH.2,
    (slopeBox 1 (3/5) (by norm_num)).mem.2.trans_lt rL⟩

lemma row_one_initial : (923/500:ℝ)<height 1 (293/1000) := by
  have hl : 0<(slopeBox 1 (293/1000) (by norm_num)).lo := by stationary_reference_arithmetic
  let H := heightBox 1 (293/1000) (by norm_num) hl
  have h : (923/500:ℝ)<H.lo := by dsimp [H]; stationary_reference_arithmetic
  exact h.trans_le H.mem.1

lemma row_three_end : (73/10000:ℝ)<G 3 (39/50) ∧
    (46057/25000:ℝ)<height 3 (39/50) ∧ l 3 (39/50)<233/250 := by
  have hl : 0<(slopeBox 3 (39/50) (by norm_num)).lo := by stationary_reference_arithmetic
  let D := GBox 3 (39/50) (by norm_num) hl
  let H := heightBox 3 (39/50) (by norm_num) hl
  have hD : (73/10000:ℝ)<D.lo := by dsimp [D]; stationary_reference_arithmetic
  have hH : (46057/25000:ℝ)<H.lo := by dsimp [H]; stationary_reference_arithmetic
  have hL : (slopeBox 3 (39/50) (by norm_num)).hi<(233/250:ℝ) := by
    stationary_reference_arithmetic
  exact ⟨hD.trans_le D.mem.1,hH.trans_le H.mem.1,
    (slopeBox 3 (39/50) (by norm_num)).mem.2.trans_lt hL⟩

lemma row_three_initial : (4369/2500:ℝ)<height 3 (293/1000) := by
  have hl : 0<(slopeBox 3 (293/1000) (by norm_num)).lo := by stationary_reference_arithmetic
  let H := heightBox 3 (293/1000) (by norm_num) hl
  have h : (4369/2500:ℝ)<H.lo := by dsimp [H]; stationary_reference_arithmetic
  exact h.trans_le H.mem.1

lemma row_three_tangent : height 3 (77/100)<1842327/1000000 ∧
    |G 3 (77/100)|<(1/125000:ℝ) := by
  have hl : 0<(slopeBox 3 (77/100) (by norm_num)).lo := by stationary_reference_arithmetic
  let D := GBox 3 (77/100) (by norm_num) hl
  let H := heightBox 3 (77/100) (by norm_num) hl
  have hH : H.hi<(1842327/1000000:ℝ) := by dsimp [H]; stationary_reference_arithmetic
  have hDl : -(1/125000:ℝ)<D.lo := by dsimp [D]; stationary_reference_arithmetic
  have hDu : D.hi<(1/125000:ℝ) := by dsimp [D]; stationary_reference_arithmetic
  exact ⟨H.mem.2.trans_lt hH,abs_lt.mpr ⟨hDl.trans_le D.mem.1,D.mem.2.trans_lt hDu⟩⟩

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Stationary.References
