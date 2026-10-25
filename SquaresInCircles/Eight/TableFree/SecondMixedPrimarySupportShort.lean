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
  (13*g/12-1)*Real.cos x-(K-x)*Real.sin x-CommonQuarter.radius*ND g p x
def minusDD (g p K x : ℝ) : ℝ :=
  -(K-x)*Real.cos x+(2-13*g/12)*Real.sin x-CommonQuarter.radius*NDD g p x

lemma minus_hasDerivAt {g p K x : ℝ} (hg : 0<g) :
    HasDerivAt (minus g p K) (minusD g p K x) x := by
  have h1 : HasDerivAt (fun y => (K-y)*Real.cos y) ((-1)*Real.cos x+(K-x)*(-Real.sin x)) x :=
    ((hasDerivAt_id' x).const_sub K).mul (Real.hasDerivAt_cos x)
  have h2 : HasDerivAt (fun y => g*(1+(13/12)*Real.sin y)) (g*((13/12)*Real.cos x)) x :=
    (((Real.hasDerivAt_sin x).const_mul (13/12)).const_add 1).const_mul g
  have h3 : HasDerivAt (fun y => CommonQuarter.radius*N g p y) (CommonQuarter.radius*ND g p x) x :=
    (N_hasDerivAt (p := p) hg).const_mul CommonQuarter.radius
  refine ((h1.add h2).sub h3).congr_deriv ?_
  simp only [minusD]
  ring

lemma minusD_hasDerivAt {g p K x : ℝ} (hg : 0<g) :
    HasDerivAt (minusD g p K) (minusDD g p K x) x := by
  have h1 : HasDerivAt (fun y => (13*g/12-1)*Real.cos y) ((13*g/12-1)*(-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul (13*g/12-1)
  have h2 : HasDerivAt (fun y => (K-y)*Real.sin y) ((-1)*Real.sin x+(K-x)*Real.cos x) x :=
    ((hasDerivAt_id' x).const_sub K).mul (Real.hasDerivAt_sin x)
  have h3 : HasDerivAt (fun y => CommonQuarter.radius*ND g p y) (CommonQuarter.radius*NDD g p x) x :=
    (ND_hasDerivAt (p := p) hg).const_mul CommonQuarter.radius
  refine ((h1.sub h2).sub h3).congr_deriv ?_
  simp only [minusDD]
  ring

end SquaresInCircles.Eight.TableFree.SecondWord.MixedPrimarySupport
