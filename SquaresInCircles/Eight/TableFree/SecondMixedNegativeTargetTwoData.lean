module

public import SquaresInCircles.Eight.TableFree.SecondMixedPHeightTaylorBounds
public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeTwoLabels
public import SquaresInCircles.Eight.TableFree.SecondMixedCoreCorner

/-!
# Original data for negative outer to negative core at edge two

The whole core has one affine lower label bound, and its corner has
the sharper join lower bound. These give the complete direct tails.
The primary separator is transferred only to a polynomial lower
bound at the original outer height. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget
open CommonQuarter CorePairGeometry Arithmetic

def γ : ℝ := 17953/20000
def e : ℝ := 11021/50000-(8623/25000)*(7/12)
def g : ℝ := 98439/100000
def h : ℝ := 8623/25000
def z : ℝ := 2667/50000
def value (b A B φ : ℝ) : ℝ := φ-P b+MixedThree.negativeCore A B

lemma core_transverse {A B : ℝ} (ht : CoreState A B) : 0≤B ∧ B<(559/1000:ℝ) :=
  ⟨(CoreAngleEndpoint.state_bounds ht).2.2.1,
    (CoreAngleEndpoint.state_bounds ht).2.2.2.2.trans_lt (by linarith [CoreAngleEndpoint.diagonal_bounds.2])⟩

lemma core_affine {A B : ℝ} (ht : CoreState A B) : e+(1909/2000)*B≤MixedThree.negativeCore A B := by
  have hh := core_transverse ht
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hp := mul_nonneg hh.1 (show 0≤98439/100000-1909/2000-(2667/50000)*B by linarith [hh.2])
  dsimp [e,MixedThree.negativeCore]
  nlinarith

lemma core_minimum {A B : ℝ} (ht : CoreState A B) : e≤MixedThree.negativeCore A B := by
  have hh := core_affine ht
  linarith [(core_transverse ht).1]

lemma corner_minimum {A B : ℝ} (ht : CoreState A B) (hB : 1/2≤B) :
    (49807/100000:ℝ)<MixedThree.negativeCore A B := by
  have hh := core_transverse ht
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hp := mul_nonneg (show 0≤B-1/2 by linarith)
    (show 0≤98439/100000-(2667/50000)*(B+1/2) by linarith [hh.2])
  dsimp [MixedThree.negativeCore]
  nlinarith

lemma source_upper {a b : ℝ} (hs : OuterState a b) : P b<(79091/100000:ℝ) := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(CommonQuarter.outer_bounds hs).2.2.2.1⟩
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨by linarith [fine_outer_endpoint_bounds.2],le_rfl⟩
  exact (P_monotone hb hd hb.2).trans_lt P_diagonal_upper

lemma tail {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B) (hφ : (167/100:ℝ)≤φ) :
    γ<value b A B φ := by
  have hh := core_minimum ht
  dsimp [value,e,γ] at *
  linarith [source_upper hs]

lemma corner_tail {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hB : 1/2≤B) (hφ : (1191/1000:ℝ)≤φ) : γ<value b A B φ := by
  have hh := corner_minimum ht hB
  dsimp [value,γ]
  linarith [source_upper hs]

lemma primary_height_lower {a b A B φ : ℝ} (hs : OuterState a b)
    (hu : 1+(A+1/2)*Real.cos φ+(1/2-B)*Real.sin φ∈PHeightBounds.heights)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) :
    φ+PHeightTaylor.poly (1+(A+1/2)*Real.cos φ+(1/2-B)*Real.sin φ)+
      MixedThree.negativeCore A B<value b A B φ := by
  have hh := PHeightTaylor.original_lower hs hu (by nlinarith)
  dsimp [value]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget
