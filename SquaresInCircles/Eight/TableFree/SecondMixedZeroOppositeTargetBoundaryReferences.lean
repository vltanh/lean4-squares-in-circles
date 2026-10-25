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

private lemma r94_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r94_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r94_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r94_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r94_mpr_lo r94_coordinate_eq (congrArg _ r94_coordinate_eq) _
private lemma r94_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r94_mpr_hi r94_coordinate_eq (congrArg _ r94_coordinate_eq) _

private lemma r94_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r94_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r94_mpr_lo (r94_label_eq H) (congrArg _ (r94_label_eq H)) _
private lemma r94_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r94_mpr_hi (r94_label_eq H) (congrArg _ (r94_label_eq H)) _

private lemma r94_U_diagonal : U outerDiagonal=outerDiagonal+1/2 := by
  rw [U,ShortOuterOne.SameContact.arc_diagonal]

/-- The outer coordinate box at the diagonal, with explicit endpoints. -/
private def r94_UBox : Interval (U outerDiagonal) :=
  ⟨outerBox.lo+1/2,outerBox.hi+1/2,by
    rw [r94_U_diagonal]; exact ⟨by linarith [outerBox.mem.1],by linarith [outerBox.mem.2]⟩⟩

private lemma r94_interval_eq {x : ℝ} (I J : Interval x) (h1 : I.lo=J.lo) (h2 : I.hi=J.hi) :
    I=J := by
  cases I; cases J; simp_all

private lemma r94_outerLabelBox_eq (r : Row) :
    outerLabelBox r=labelBox (F r) outerBox r94_UBox := by
  unfold outerLabelBox
  dsimp only
  congr 1
  apply r94_interval_eq
  · rw [r94_mpr_lo r94_U_diagonal]; rfl
  · rw [r94_mpr_hi r94_U_diagonal]; rfl

private lemma r94_outerLabelBox_lo (r : Row) :
    (outerLabelBox r).lo=(labelBox (F r) outerBox r94_UBox).lo := by
  rw [r94_outerLabelBox_eq]
private lemma r94_outerLabelBox_hi (r : Row) :
    (outerLabelBox r).hi=(labelBox (F r) outerBox r94_UBox).hi := by
  rw [r94_outerLabelBox_eq]
private lemma r94_UBox_lo : r94_UBox.lo=outerBox.lo+1/2 := rfl
private lemma r94_UBox_hi : r94_UBox.hi=outerBox.hi+1/2 := rfl

attribute [local simp ↓] r94_coordinate_lo r94_coordinate_hi r94_labelBox_lo r94_labelBox_hi
  r94_outerLabelBox_lo r94_outerLabelBox_hi r94_UBox_lo r94_UBox_hi

lemma J_first :
    (4528/5000:ℝ)< -(41/100)+c 0+J outerDiagonal+g 0/2 ∧
    (8999/10000:ℝ)< -cap+c 0+J outerDiagonal+g 0*(5249/10000) ∧
    (5249/10000:ℝ)< inverse CoreAngleEndpoint.diagonal outerDiagonal (41/100) := by
  let V₀ := (((Interval.point (-(41/100:ℝ))).add (Interval.point (c 0))).add
    (outerLabelBox 0)).add (Interval.point (g 0/2))
  let V₁ := (((Interval.point (-cap)).add (Interval.point (c 0))).add
    (outerLabelBox 0)).add (Interval.point (g 0*(5249/10000)))
  have hc : 0<(cosBox (41/100) (by norm_num)).lo := by boundary_reference
  let I := inverseBox coreBox outerBox (sinBox (41/100) (by norm_num))
    (cosBox (41/100) (by norm_num)) hc
  have h0 : (4528/5000:ℝ)<V₀.lo := by dsimp only [V₀]; boundary_reference
  have h1 : (8999/10000:ℝ)<V₁.lo := by dsimp only [V₁]; boundary_reference
  have hI : (5249/10000:ℝ)<I.lo := by dsimp only [I]; boundary_reference
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
    (outerBox.sub (Interval.point (1/2)))).mul S)).add
      ((Interval.point (g 2)).mul (coreBox.add (Interval.point (1/2))))).sub
        (Interval.point 1)
  let J := (Interval.point (1/2)).add ((Interval.point (13/12)).mul S)
  have hv : (1126/1250:ℝ)<V.lo := by dsimp only [V]; boundary_reference
  have hn : (0:ℝ)<N.lo := by dsimp only [N,S]; boundary_reference
  have hs : (9/25:ℝ)<S.lo := by dsimp only [S]; boundary_reference
  have hj : J.hi<outerBox.lo := by dsimp only [J,S]; boundary_reference
  exact ⟨hv.trans_le V.mem.1,hn.trans_le N.mem.1,hs.trans_le S.mem.1,
    J.mem.2.trans_lt (hj.trans_le outerBox.mem.1)⟩

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.BoundaryReferences
