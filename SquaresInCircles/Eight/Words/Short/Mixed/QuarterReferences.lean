module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeReferenceAlgebra
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterData

/-!
# Eight squares: exact fixed arithmetic for the short mixed quarter contacts

These are enclosures of individual expressions at the geometric endpoints and at fixed
reference points. They use the Machin bound for `π` (`piBox`), adjacent alternating Taylor
polynomials (`sine`, `cosine`) and positive rational square-root refinements (`rootSix`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.Reference
open CommonQuarter Arithmetic HighOrderTaylor StationaryPrimitives
open SecondWord.OppositeThree.ReferenceAlgebra (rootStep rootStep_hi_pos rootThree)

def piBox : Interval Real.pi := Interval.of_bounds
  ⟨pi_hand_enclosure.1.le,pi_hand_enclosure.2.le⟩
def halfPi : Interval (Real.pi/2) := piBox.div (Interval.point 2) (by norm_num [Interval.point])
def axial : Interval outerAxial := Interval.of_bounds
  ⟨ShortOuterZero.fine_axial_bounds.1.le,ShortOuterZero.fine_axial_bounds.2.le⟩
def diagonal : Interval outerDiagonal := Interval.of_bounds
  ⟨ShortMixedZero.fine_diagonal_bounds.1.le,ShortMixedZero.fine_diagonal_bounds.2.le⟩
def coreDiagonal : Interval CoreAngleEndpoint.diagonal := Interval.of_bounds
  ⟨CoreAngleEndpoint.diagonal_bounds.1.le,CoreAngleEndpoint.diagonal_bounds.2.le⟩

theorem radius_fine : (1978787/1000000:ℝ)<CommonQuarter.radius ∧ CommonQuarter.radius<494697/250000 := by
  have hR := radius_bounds
  have hs := radius_sq
  norm_num [Q0] at hs
  constructor <;> nlinarith
def circleRadius : Interval CommonQuarter.radius := Interval.of_bounds ⟨radius_fine.1.le,radius_fine.2.le⟩

def sine {x : ℝ} (hx : 0≤x) : Interval (Real.sin x) :=
  Interval.of_bounds ⟨S15_le_sin hx,sin_le_S13 hx⟩
def cosine {x : ℝ} (hx : 0≤x) : Interval (Real.cos x) :=
  Interval.of_bounds ⟨C14_le_cos hx,cos_le_C16 hx⟩

theorem rootThree_hi_pos {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s)
    (hX : 0≤X.lo) : 0<(rootThree X s hs hX).hi := by
  unfold rootThree
  exact rootStep_hi_pos _ _ _ _

/-- Six fixed positive-square refinements keep the narrow endpoint reserves without a decimal
value for the radical. -/
def rootSix {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    Interval (Real.sqrt x) :=
  rootThree X (rootThree X s hs hX).hi (rootThree_hi_pos X s hs hX) hX

macro "mixed_fixed" : tactic => `(tactic|
  norm_num [Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    piBox,halfPi,axial,diagonal,coreDiagonal,circleRadius,sine,cosine,
    rootSix,rootThree,rootStep,S15,S13,S11,C16,C14,C12,sin9,sin7,cos10,cos8,
    coC,coP,coQ,coG,ocC,ocP,ocQ,ocG,Q0])

end SquaresInCircles.Eight.ShortWord.MixedQuarter.Reference
