module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetDiagonalReferences

/-!
# The two first-feasible corner references

Uncompiled source draft.  These are the fixed `.41` J comparison and
the `.377` L comparison from §§8.2 and 10.3 of the written proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.BoundaryReferences
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra Target.ReferenceAlgebra

local macro "boundary_reference" : tactic => `(tactic|
  norm_num [coreBox,outerBox,sinBox,cosBox,outerLabelBox,inverseBox,boundaryBox,
    labelBox,coordinate,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    F,c,g,JLabel,LLabel,Q0,cap])

lemma J_first :
    (4528/5000:ℝ)<-(41/100)+c 0+J outerDiagonal+g 0/2 ∧
    (8999/10000:ℝ)<-cap+c 0+J outerDiagonal+g 0*(5249/10000) ∧
    (5249/10000:ℝ)<inverse CoreAngleEndpoint.diagonal outerDiagonal (41/100) := by
  let V₀ := (((Interval.point (-(41/100:ℝ))).add (Interval.point (c 0))).
    add (outerLabelBox 0)).add (Interval.point (g 0/2))
  let V₁ := (((Interval.point (-cap)).add (Interval.point (c 0))).
    add (outerLabelBox 0)).add (Interval.point (g 0*(5249/10000)))
  have hc : 0<(cosBox (41/100) (by norm_num)).lo := by boundary_reference
  let I := inverseBox coreBox outerBox (sinBox (41/100) (by norm_num))
    (cosBox (41/100) (by norm_num)) hc
  have h0 : (4528/5000:ℝ)<V₀.lo := by dsimp [V₀]; boundary_reference
  have h1 : (8999/10000:ℝ)<V₁.lo := by dsimp [V₁]; boundary_reference
  have hI : (5249/10000:ℝ)<I.lo := by dsimp [I]; boundary_reference
  exact ⟨h0.trans_le V₀.mem.1,h1.trans_le V₁.mem.1,hI.trans_le I.mem.1⟩

lemma L_first : (1126/1250:ℝ)<boundary 2 CoreAngleEndpoint.diagonal outerDiagonal (377/1000) ∧
    0<(Real.sin (377/1000))^2-g 2*(outerDiagonal-1/2)*Real.sin (377/1000)+
      g 2*(CoreAngleEndpoint.diagonal+1/2)-1 ∧
    (9/25:ℝ)<Real.sin (377/1000) ∧
    1/2+(13/12)*Real.sin (377/1000)<outerDiagonal := by
  have hc : 0<(cosBox (377/1000) (by norm_num)).lo := by boundary_reference
  let V := boundaryBox 2 coreBox (by norm_num : (0:ℝ)≤377/1000) hc
  let S := sinBox (377/1000) (by norm_num)
  let N := ((S.square.sub (((Interval.point (g 2)).mul
    (outerBox.sub (Interval.point (1/2)))).mul S)).
      add ((Interval.point (g 2)).mul (coreBox.add (Interval.point (1/2))))).
        sub (Interval.point 1)
  let J := (Interval.point (1/2)).add ((Interval.point (13/12)).mul S)
  have hv : (1126/1250:ℝ)<V.lo := by dsimp [V]; boundary_reference
  have hn : (0:ℝ)<N.lo := by dsimp [N,S]; boundary_reference
  have hs : (9/25:ℝ)<S.lo := by dsimp [S]; boundary_reference
  have hj : J.hi<outerBox.lo := by dsimp [J,S]; boundary_reference
  exact ⟨hv.trans_le V.mem.1,hn.trans_le N.mem.1,hs.trans_le S.mem.1,
    J.mem.2.trans_lt (hj.trans_le outerBox.mem.1)⟩

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.BoundaryReferences
