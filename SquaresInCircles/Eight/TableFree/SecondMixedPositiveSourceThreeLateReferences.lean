module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeLateShape

/-!
# The two endpoints of the late affine dividing curve

Only its left endpoint needs a trigonometric reference. Its aligned
derivative follows from concavity on a fixed physical target interval.
All radical comparisons use exact rational interval algebra.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Late
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

local macro "late_reference" : tactic => `(tactic|
  norm_num [PrimarySupport.sinBox,PrimarySupport.cosBox,shifted,radicand,rootThree,rootStep,
    coordinate,ratioBox,firstBox,LLabel,RoleLabel.eval,Q0,cut,g,e,EdgeThreeAligned.gp,EdgeThreeAligned.ep,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,
    HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

lemma left_reference : 0<f (13/10) ∧ 0<D (13/10) := by
  let S := PrimarySupport.sinBox (x := (13/10:ℝ)) (by norm_num)
  let C := PrimarySupport.cosBox (x := (13/10:ℝ)) (by norm_num)
  let X := shifted (Interval.point (cut (13/10))) (7/4) (by norm_num) (by late_reference)
  have hX : 0<X.lo := by dsimp [X]; late_reference
  let R := ratioBox (Interval.point (cut (13/10))) X hX
  let J := firstBox LLabel (Interval.point (cut (13/10))) X hX
  let F₀ := ((Interval.point (1/2)).add (((Interval.point 1).sub X).mul S)).add
    ((Interval.point (cut (13/10)+1/2)).mul C)
  let D₀ : Interval (D (13/10)) := ((Interval.point g).mul ((R.mul S).add C)).sub J
  have hf : 0<F₀.lo := by dsimp [F₀,X,S,C]; late_reference
  have hd : 0<D₀.lo := by dsimp [D₀,J,R,X,S,C]; late_reference
  constructor
  · have hh := hf.trans_le F₀.mem.1
    convert hh using 1
    dsimp [f,source,U]
    ring
  · exact hd.trans_le D₀.mem.1

lemma reference_794 : 0<FB (397/500) (Real.pi/2) := by
  let X := shifted (Interval.point (397/500:ℝ)) (3/2) (by norm_num) (by late_reference)
  have hX : 0<X.lo := by dsimp [X]; late_reference
  let R := ratioBox (Interval.point (397/500:ℝ)) X hX
  let J := firstBox LLabel (Interval.point (397/500:ℝ)) X hX
  let D₀ := ((Interval.point g).mul R).sub J
  have hd : 0<D₀.lo := by dsimp [D₀,J,R,X]; late_reference
  have hh := hd.trans_le D₀.mem.1
  simpa [FB] using hh

lemma terminal_derivative : 0<D (Real.pi/2) := by
  have hlo : (13/20:ℝ)≤cut (Real.pi/2) := by dsimp [cut]; linarith [pi_hand_enclosure.1]
  have hhi := (cut_bounds terminal_angle).2.le
  have hleft : (13/20:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hright : (397/500:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hh := (FB_concave (Real.pi/2)).min_le_of_mem_Icc hleft hright ⟨hlo,hhi⟩
  exact (lt_min Primary.reference_65 reference_794).trans_le hh

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Late
