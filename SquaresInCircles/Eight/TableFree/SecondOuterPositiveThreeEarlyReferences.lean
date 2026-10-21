module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeEarlyCoefficients
public import SquaresInCircles.Eight.TableFree.SecondOuterPointProducts

/-!
# Three fixed references for the early-angle support

Only the angles `1.085`, `1.257` and `1.3` occur.  The first two control
the curvature and slope of one analytic minorant; the last is its
endpoint value.  The slightly weakened reserves leave ample room for
the uniform curvature argument.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig

lemma coefficient_boxes :
    a1∈Icc (-563592126648/1000000000000) (-563592126647/1000000000000) ∧
    b1∈Icc (-1329332289459/1000000000000) (-1329332289458/1000000000000) ∧
    a2∈Icc (305824407767/1000000000000) (305824407768/1000000000000) ∧
    b2∈Icc (-314490550356/1000000000000) (-314490550355/1000000000000) :=
  ⟨⟨a1_bounds.1.le,a1_bounds.2.le⟩,⟨b1_bounds.1.le,b1_bounds.2.le⟩,
    ⟨a2_bounds.1.le,a2_bounds.2.le⟩,⟨b2_bounds.1.le,b2_bounds.2.le⟩⟩

lemma third_reference : third (217/200)<(-7/25:ℝ) ∧
    |fourth (217/200)|<29/50 := by
  have h := coefficient_boxes
  have ht := PointProducts.trig (show (0:ℝ)≤217/200 by norm_num)
  have htwo := PointProducts.trig (show (0:ℝ)≤217/100 by norm_num)
  have p1 := PointProducts.product h.1 ht.2
  have p2 := PointProducts.product h.2.1 ht.1
  have p3 := PointProducts.product h.2.2.1 htwo.1
  have p4 := PointProducts.product h.2.2.2 htwo.2
  have q1 := PointProducts.product h.1 ht.1
  have q2 := PointProducts.product h.2.1 ht.2
  have q3 := PointProducts.product h.2.2.1 htwo.2
  have q4 := PointProducts.product h.2.2.2 htwo.1
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at p1 p2 p3 p4 q1 q2 q3 q4
  dsimp [third,fourth]
  rw [show (2:ℝ)*(217/200)=217/100 by norm_num]
  constructor
  · linarith [p1.1,p1.2,p2.1,p2.2,p3.1,p3.2,p4.1,p4.2]
  · rw [abs_lt]
    constructor <;> linarith [q1.1,q1.2,q2.1,q2.2,q3.1,q3.2,q4.1,q4.2]

lemma first_reference : first (1257/1000)<(-39/10000:ℝ) ∧
    |second (1257/1000)|<1/1000 := by
  have h := coefficient_boxes
  have ht := PointProducts.trig (show (0:ℝ)≤1257/1000 by norm_num)
  have htwo := PointProducts.trig (show (0:ℝ)≤1257/500 by norm_num)
  have p1 := PointProducts.product h.1 ht.2
  have p2 := PointProducts.product h.2.1 ht.1
  have p3 := PointProducts.product h.2.2.1 htwo.1
  have p4 := PointProducts.product h.2.2.2 htwo.2
  have q1 := PointProducts.product h.1 ht.1
  have q2 := PointProducts.product h.2.1 ht.2
  have q3 := PointProducts.product h.2.2.1 htwo.2
  have q4 := PointProducts.product h.2.2.2 htwo.1
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at p1 p2 p3 p4 q1 q2 q3 q4
  dsimp [first,second]
  rw [show (2:ℝ)*(1257/1000)=1257/500 by norm_num]
  constructor
  · linarith [p1.1,p1.2,p2.1,p2.2,p3.1,p3.2,p4.1,p4.2]
  · rw [abs_lt]
    constructor <;> linarith [q1.1,q1.2,q2.1,q2.2,q3.1,q3.2,q4.1,q4.2]

lemma end_support : (566/625:ℝ)<support star (13/10) ∧
    |targetFirst star (13/10)|<12/125 := by
  have ht := PointProducts.trig (show (0:ℝ)≤13/10 by norm_num)
  have hu := PointProducts.product ⟨uStar_bounds.1.le,uStar_bounds.2.le⟩ ht.1
  have hr := PointProducts.product ⟨rStar_bounds.1.le,rStar_bounds.2.le⟩ ht.1
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at ht hu hr
  have he : support star (13/10)=13/10-29/2000+g/2+g*Real.sin (13/10)-
      L star-g*uStar*Real.sin (13/10)+g*wStar*Real.cos (13/10) := by
    dsimp [support,uStar,wStar,W,star]
    ring
  have hd : targetFirst star (13/10)=
      g*(rStar*Real.sin (13/10)+Real.cos (13/10))-dStar := rfl
  rw [he,hd]
  norm_num [g,wStar]
  constructor
  · linarith [ht.1.1,ht.1.2,ht.2.1,ht.2.2,hu.1,hu.2,star_labels.1,star_labels.2.1]
  · rw [abs_lt]
    constructor <;> linarith [ht.2.1,ht.2.2,hr.1,hr.2,star_labels.2.2.1,star_labels.2.2.2]

lemma minorant_end : (451/500:ℝ)<minorant (13/10) := by
  have hb := abs_lt.mp end_support.2
  have hs : (targetFirst star (13/10))^2<(12/125:ℝ)^2 := by nlinarith
  dsimp [minorant,m]
  nlinarith [end_support.1]

lemma end_cos_lower : (267/1000:ℝ)<Real.cos (13/10) := by
  have hh := cos10_le_cos (show (0:ℝ)≤13/10 by norm_num)
  norm_num [cos10,cos8] at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.Early
