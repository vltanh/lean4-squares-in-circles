module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetReferenceAlgebra

/-!
# The named label comparisons in the written negative-target proof

Uncompiled source draft.  These references are the left diagonal,
the half-coordinate, and `.9`.  All estimates are proved by substitution
in exact expression enclosures, including the fourth derivative in the
single logarithmic-derivative reference.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.LabelReferences
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra Target.ReferenceAlgebra

local macro "label_reference" : tactic => `(tactic|
  norm_num [coreBox,outerBox,sinBox,cosBox,diagonalBox,speedBox,HBox,H₁Box,H₂Box,
    ratioDDDBox,fourthBox,labelBox,firstBox,secondBox,thirdBox,
    ratioBox,ratioDBox,ratioDDBox,coordinate,shifted,radicand,rootThree,rootStep,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    F,c,g,PLabel,JLabel,LLabel,Q0])

def zeroU : Interval (U (diagonal 0)) :=
  shifted (diagonalBox 0 (by norm_num)) (7/4) (by norm_num) (by label_reference)
def halfU : Interval (U (1/2)) :=
  shifted (Interval.point (1/2)) (17/10) (by norm_num) (by label_reference)
def nineU : Interval (U (9/10)) :=
  shifted (Interval.point (9/10)) (7/5) (by norm_num) (by label_reference)

lemma initial : (21/25:ℝ)<PLabel.d1 (diagonal 0) ∧
    JLabel.d1 (diagonal 0)<181/200 ∧ JLabel.d2 (diagonal 0)<-(97/200:ℝ) ∧
    LLabel.d1 (diagonal 0)<41/50 ∧ (51/50:ℝ)<H 0 0 := by
  have hu : 0<zeroU.lo := by dsimp [zeroU]; label_reference
  let P₁ := firstBox PLabel (diagonalBox 0 (by norm_num)) zeroU hu
  let J₁ := firstBox JLabel (diagonalBox 0 (by norm_num)) zeroU hu
  let J₂ := secondBox JLabel (diagonalBox 0 (by norm_num)) zeroU hu
  let L₁ := firstBox LLabel (diagonalBox 0 (by norm_num)) zeroU hu
  let V := HBox 0 0 (by norm_num) zeroU
  have hP : (21/25:ℝ)<P₁.lo := by dsimp [P₁,zeroU]; label_reference
  have hJ : J₁.hi<(181/200:ℝ) := by dsimp [J₁,zeroU]; label_reference
  have hJJ : J₂.hi<-(97/200:ℝ) := by dsimp [J₂,zeroU]; label_reference
  have hL : L₁.hi<(41/50:ℝ) := by dsimp [L₁,zeroU]; label_reference
  have hV : (51/50:ℝ)<V.lo := by dsimp [V,zeroU]; label_reference
  exact ⟨hP.trans_le P₁.mem.1,J₁.mem.2.trans_lt hJ,J₂.mem.2.trans_lt hJJ,
    L₁.mem.2.trans_lt hL,hV.trans_le V.mem.1⟩

lemma P_half : (213/250:ℝ)<PLabel.d1 (1/2) ∧
    (11/50:ℝ)<PLabel.d2 (1/2) ∧ PLabel.d2 (1/2)<221/1000 ∧
    PLabel.d3 (1/2)<153/500 := by
  have hu : 0<halfU.lo := by dsimp [halfU]; label_reference
  let P₁ := firstBox PLabel (Interval.point (1/2)) halfU hu
  let P₂ := secondBox PLabel (Interval.point (1/2)) halfU hu
  let P₃ := thirdBox PLabel (Interval.point (1/2)) halfU hu
  have h1 : (213/250:ℝ)<P₁.lo := by dsimp [P₁,halfU]; label_reference
  have h2 : (11/50:ℝ)<P₂.lo := by dsimp [P₂,halfU]; label_reference
  have h3 : P₂.hi<(221/1000:ℝ) := by dsimp [P₂,halfU]; label_reference
  have h4 : P₃.hi<(153/500:ℝ) := by dsimp [P₃,halfU]; label_reference
  exact ⟨h1.trans_le P₁.mem.1,h2.trans_le P₂.mem.1,P₂.mem.2.trans_lt h3,
    P₃.mem.2.trans_lt h4⟩

lemma nine : PLabel.d3 (9/10)<781/1000 ∧
    (3/5:ℝ)<JLabel.d1 (9/10) ∧ LLabel.d1 (9/10)<233/200 := by
  have hu : 0<nineU.lo := by dsimp [nineU]; label_reference
  let P₃ := thirdBox PLabel (Interval.point (9/10)) nineU hu
  let J₁ := firstBox JLabel (Interval.point (9/10)) nineU hu
  let L₁ := firstBox LLabel (Interval.point (9/10)) nineU hu
  have hP : P₃.hi<(781/1000:ℝ) := by dsimp [P₃,nineU]; label_reference
  have hJ : (3/5:ℝ)<J₁.lo := by dsimp [J₁,nineU]; label_reference
  have hL : L₁.hi<(233/200:ℝ) := by dsimp [L₁,nineU]; label_reference
  exact ⟨P₃.mem.2.trans_lt hP,hJ.trans_le J₁.mem.1,L₁.mem.2.trans_lt hL⟩

lemma L_half : 5<LLabel.d3 (1/2) ∧ LLabel.d2 (1/2)<0 ∧
    (31/1000:ℝ)<-LLabel.d2 (1/2) ∧
    (42/25:ℝ)<(144/13)*LLabel.d1 (1/2)-LLabel.d3 (1/2) ∧
    |(288/13)*LLabel.d2 (1/2)-LLabel.d4 (1/2)|<9 := by
  have hu : 0<halfU.lo := by dsimp [halfU]; label_reference
  let L₁ := firstBox LLabel (Interval.point (1/2)) halfU hu
  let L₂ := secondBox LLabel (Interval.point (1/2)) halfU hu
  let L₃ := thirdBox LLabel (Interval.point (1/2)) halfU hu
  let L₄ := fourthBox LLabel (Interval.point (1/2)) halfU hu
  let D₀ := L₂.neg
  let D₁ := ((Interval.point (144/13)).mul L₁).sub L₃
  let D₂ := ((Interval.point (288/13)).mul L₂).sub L₄
  have h3 : (5:ℝ)<L₃.lo := by dsimp [L₃,halfU]; label_reference
  have h0 : (31/1000:ℝ)<D₀.lo := by dsimp [D₀,L₂,halfU]; label_reference
  have h1 : (42/25:ℝ)<D₁.lo := by dsimp [D₁,L₁,L₃,halfU]; label_reference
  have h2l : (-9:ℝ)<D₂.lo := by dsimp [D₂,L₂,L₄,halfU]; label_reference
  have h2u : D₂.hi<(9:ℝ) := by dsimp [D₂,L₂,L₄,halfU]; label_reference
  have hd : (31/1000:ℝ)<-LLabel.d2 (1/2) := h0.trans_le D₀.mem.1
  exact ⟨h3.trans_le L₃.mem.1,by linarith,hd,h1.trans_le D₁.mem.1,
    abs_lt.mpr ⟨h2l.trans_le D₂.mem.1,D₂.mem.2.trans_lt h2u⟩⟩

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.LabelReferences
