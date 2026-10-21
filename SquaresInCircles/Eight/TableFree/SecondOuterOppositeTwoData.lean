module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoContactInverse

/-!
# Original-coordinate data for opposite outer edge two

The four cuts below are rearrangements of the original weak axes.  The
source and target keep their literal edge-two labels and their common
circle.  The shortened bounds lemma is local to this contact family.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma outer_bounds {a b : ℝ} (hs : OuterState a b) :
    outerDiagonal≤a ∧ a≤outerAxial ∧ b≤outerDiagonal :=
  ⟨(CommonQuarter.outer_bounds hs).1,(CommonQuarter.outer_bounds hs).2.1,
    (CommonQuarter.outer_bounds hs).2.2.2.1⟩

def value (b B φ : ℝ) : ℝ := φ-P b-V B
def lowerCut (a b x : ℝ) : ℝ :=
  (a-1/2)*Real.cos x-(b+1/2)*Real.sin x-1/2
def upperCut (a b x : ℝ) : ℝ :=
  (a-1/2)*Real.cos x+(b-1/2)*Real.sin x-1/2
def lowerPrimary (a b x : ℝ) : ℝ :=
  1/2+(a+1/2)*Real.sin x+(b+1/2)*Real.cos x
def upperPrimary (a b x : ℝ) : ℝ :=
  1/2+(b+1/2)*Real.cos x-(a-1/2)*Real.sin x
def k (b x : ℝ) : ℝ := Real.cos x+ratio b*Real.sin x
def v (b x : ℝ) : ℝ := W b*Real.sin x+(U b-1)*Real.cos x

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 2 .outer .outer false true a b A B φ=value b B φ := by
  rw [show P b=PLabel.eval a b from PLabel.outer_actual hs,
    show V B=VLabel.eval A B from VLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,value,PLabel,VLabel,RoleLabel.eval]
  ring

lemma upper_width {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    pairWidth (Real.pi/2+x)=(1+Real.cos x+Real.sin x)/2 := by
  rw [quarter_width (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩),
    abs_of_nonneg (positive_trig hx).2.2.1]

lemma lower_width {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    pairWidth (Real.pi/2-x)=(1+Real.cos x+Real.sin x)/2 := by
  have hh := quarter_width (x := -x)
    (abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  simpa only [sub_eq_add_neg,Real.cos_neg,Real.sin_neg,abs_neg,
    abs_of_nonneg (positive_trig hx).2.2.1] using hh

lemma source_mem {a b : ℝ} (hs : OuterState a b) : b∈Icc 0 outerDiagonal :=
  ⟨hs.1,(outer_bounds hs).2.2⟩

lemma primary_mem {a b : ℝ} (hs : OuterState a b) : a∈Icc outerDiagonal outerAxial :=
  ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo
