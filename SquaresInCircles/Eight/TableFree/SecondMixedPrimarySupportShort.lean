module

public import SquaresInCircles.Eight.TableFree.SecondMixedPrimarySupport

/-!
# Exact derivatives of the lower primary circle support

These formulas retain the unsquared norm and are valid for every real
angle whenever the primary multiplier is positive. Uncompiled draft.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedPrimarySupport
open CommonQuarter CorePairGeometry Arithmetic

def minusD (g p K x : ℝ) : ℝ :=
  (13*g/12-1)*Real.cos x-(K-x)*Real.sin x-radius*ND g p x
def minusDD (g p K x : ℝ) : ℝ :=
  -(K-x)*Real.cos x+(2-13*g/12)*Real.sin x-radius*NDD g p x

lemma minus_hasDerivAt {g p K x : ℝ} (hg : 0<g) :
    HasDerivAt (minus g p K) (minusD g p K x) x := by
  convert ((((hasDerivAt_id x).const_sub K).mul (Real.hasDerivAt_cos x)).add
    ((((Real.hasDerivAt_sin x).const_mul (13/12)).const_add 1).const_mul g)).sub
      ((N_hasDerivAt (p := p) hg).const_mul radius) using 1 <;> dsimp [minus,minusD] <;> ring

lemma minusD_hasDerivAt {g p K x : ℝ} (hg : 0<g) :
    HasDerivAt (minusD g p K) (minusDD g p K x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (13*g/12-1)).sub
    (((hasDerivAt_id x).const_sub K).mul (Real.hasDerivAt_sin x))).sub
      ((ND_hasDerivAt (p := p) hg).const_mul radius)) using 1 <;> dsimp [minusD,minusDD] <;> ring

end SquaresInCircles.Eight.TableFree.SecondWord.MixedPrimarySupport
