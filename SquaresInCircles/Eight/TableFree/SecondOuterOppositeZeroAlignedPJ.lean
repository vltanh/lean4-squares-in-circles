module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroData

/-!
# The asymmetric aligned P/J comparison

Uncompiled source draft.  The third derivative of P(b)+J(1-b) is
positive and the right endpoint first derivative is negative.  The
endpoint-minimum lemma therefore applies without asserting concavity
of the value itself.  The two endpoint comparisons are the named
references in Section 2 of the asymmetric hand proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.AlignedPJ
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

def cost (b : ℝ) : ℝ := PLabel.outer b+JLabel.outer (1-b)
def first (b : ℝ) : ℝ := PLabel.d1 b-JLabel.d1 (1-b)
def second (b : ℝ) : ℝ := PLabel.d2 b+JLabel.d2 (1-b)
def third (b : ℝ) : ℝ := PLabel.d3 b-JLabel.d3 (1-b)

lemma domains {b : ℝ} (hb : b∈Icc (1-outerDiagonal) outerDiagonal) :
    b∈Icc 0 outerDiagonal ∧ 1-b∈Icc 0 outerDiagonal := by
  refine ⟨⟨?_,hb.2⟩,⟨?_,?_⟩⟩ <;> linarith [hb.1,hb.2,outer_endpoint_bounds.2.2.2]
lemma cost_hasDerivAt {b : ℝ} (hb : b∈Icc (1-outerDiagonal) outerDiagonal) :
    HasDerivAt cost (first b) b := by
  convert (PLabel.outer_hasDerivAt (outer_domain (domains hb).1)).add
    ((JLabel.outer_hasDerivAt (outer_domain (domains hb).2)).comp b
      ((hasDerivAt_id b).const_sub 1)) using 1 <;> dsimp [cost,first] <;> ring
lemma first_hasDerivAt {b : ℝ} (hb : b∈Icc (1-outerDiagonal) outerDiagonal) :
    HasDerivAt first (second b) b := by
  convert (PLabel.d1_hasDerivAt (outer_domain (domains hb).1)).sub
    ((JLabel.d1_hasDerivAt (outer_domain (domains hb).2)).comp b
      ((hasDerivAt_id b).const_sub 1)) using 1 <;> dsimp [first,second] <;> ring
lemma second_hasDerivAt {b : ℝ} (hb : b∈Icc (1-outerDiagonal) outerDiagonal) :
    HasDerivAt second (third b) b := by
  convert (PLabel.d2_hasDerivAt (outer_domain (domains hb).1)).add
    ((JLabel.d2_hasDerivAt (outer_domain (domains hb).2)).comp b
      ((hasDerivAt_id b).const_sub 1)) using 1 <;> dsimp [second,third] <;> ring

def sourceBox : Interval (1-outerDiagonal) :=
  (Interval.point 1).sub SameZero.PJ.Reference.dBox
def sourceUBox : Interval (U (1-outerDiagonal)) :=
  shifted sourceBox (19/10) (by norm_num)
    (by norm_num [radicand,sourceBox,SameZero.PJ.Reference.dBox,Interval.of_bounds,
      Interval.point,Interval.add,Interval.sub,Interval.square,Interval.mul,Q0])

private macro "aligned_arithmetic" : tactic => `(tactic|
  norm_num [sourceBox,sourceUBox,SameZero.PJ.Reference.dBox,SameZero.PJ.Reference.dUBox,
    shifted,radicand,rootThree,rootStep,labelBox,firstBox,coordinate,ratioBox,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.div,Interval.inv,PLabel,JLabel,Q0])

lemma references : (44889/50000:ℝ)<cost (1-outerDiagonal) ∧
    (44889/50000:ℝ)<cost outerDiagonal ∧ first outerDiagonal<0 := by
  let D := SameZero.PJ.Reference.dBox
  let DU := SameZero.PJ.Reference.dUBox
  have hS : 0<sourceUBox.lo := by aligned_arithmetic
  have hD : 0<DU.lo := by dsimp [DU]; aligned_arithmetic
  let L := (labelBox PLabel sourceBox sourceUBox).add (labelBox JLabel D DU)
  let R := (labelBox PLabel D DU).add (labelBox JLabel sourceBox sourceUBox)
  let F := (firstBox PLabel D DU hD).sub (firstBox JLabel sourceBox sourceUBox hS)
  have hl : (44889/50000:ℝ)<L.lo := by dsimp [L,D,DU]; aligned_arithmetic
  have hr : (44889/50000:ℝ)<R.lo := by dsimp [R,D,DU]; aligned_arithmetic
  have hf : F.hi<0 := by dsimp [F,D,DU]; aligned_arithmetic
  refine ⟨?_,hr.trans_le R.mem.1,F.mem.2.trans_lt hf⟩
  simpa [cost,sub_sub_cancel] using hl.trans_le L.mem.1

theorem lower {b : ℝ} (hb : b∈Icc (1-outerDiagonal) outerDiagonal) :
    (44889/50000:ℝ)<cost b := by
  have hh := MinimumCalculus.endpoint_minimum hb
    (fun t ht => cost_hasDerivAt ht) (fun t ht => first_hasDerivAt ht)
    (fun t ht => second_hasDerivAt ht)
    (fun t ht => by dsimp [third]; linarith [P_third_positive (domains ht).1,
      J_third_negative (domains ht).2]) references.2.2
  exact (lt_min references.1 references.2.1).trans_le hh

theorem original {b B : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (he : b+B=1) : (44889/50000:ℝ)<PLabel.outer b+JLabel.outer B := by
  have hd : b∈Icc (1-outerDiagonal) outerDiagonal := ⟨by linarith [hB.2],hb.2⟩
  have hh := lower hd
  have hB' : B=1-b := by linarith
  simpa [cost,hB'] using hh

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.AlignedPJ
