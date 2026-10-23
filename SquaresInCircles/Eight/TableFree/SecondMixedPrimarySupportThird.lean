module

public import SquaresInCircles.Eight.TableFree.SecondMixedPrimarySupportShort

/-!
# The third derivative of the unsquared primary support

The norm derivative is bounded on the complete lower deviation half.
The estimate retains its positive denominator and uses only the common
whole-window trigonometric bounds. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedPrimarySupport
open CommonQuarter CorePairGeometry Arithmetic

def NDDD (g p x : ℝ) : ℝ :=
  4*p^2*Real.sin x*Real.cos x/N g p x-
    3*p^4*Real.sin x*Real.cos x*((Real.cos x)^2-(Real.sin x)^2)/(N g p x)^3-
    3*p^6*(Real.sin x)^3*(Real.cos x)^3/(N g p x)^5
def minusDDD (g p K x : ℝ) : ℝ :=
  (3-13*g/12)*Real.cos x+(K-x)*Real.sin x-radius*NDDD g p x

lemma NDD_hasDerivAt {g p x : ℝ} (hg : 0<g) : HasDerivAt (NDD g p) (NDDD g p x) x := by
  have hn := N_positive (p := p) (x := x) hg
  have hd0 := ((((Real.hasDerivAt_cos x).pow 2).sub ((Real.hasDerivAt_sin x).pow 2)).const_mul (-p^2)).div
    (N_hasDerivAt hg) hn.ne'
  have hd1 := ((((Real.hasDerivAt_sin x).pow 2).mul ((Real.hasDerivAt_cos x).pow 2)).const_mul (p^4)).div
    ((N_hasDerivAt hg).pow 3) (pow_ne_zero 3 hn.ne')
  convert hd0.sub hd1 using 1
  · ext y
    dsimp [NDD]
    ring
  · dsimp [NDDD,ND]
    field_simp [hn.ne']
    ring

lemma minusDD_hasDerivAt {g p K x : ℝ} (hg : 0<g) :
    HasDerivAt (minusDD g p K) (minusDDD g p K x) x := by
  convert (((((hasDerivAt_id x).const_sub K).mul (Real.hasDerivAt_cos x)).neg).add
    ((Real.hasDerivAt_sin x).const_mul (2-13*g/12))).sub
      ((NDD_hasDerivAt (p := p) hg).const_mul radius) using 1 <;>
    dsimp [minusDD,minusDDD] <;> ring

lemma NDDD_upper {g p x : ℝ} (hg : 0<g) (hx : x∈Icc (0:ℝ) (7/10)) :
    NDDD g p x≤4*p^2*Real.sin x*Real.cos x/g := by
  have ht := positive_trig hx
  have hs := ht.2.2.1
  have hc : 0≤Real.cos x := by linarith [ht.1]
  have hdiff : 0≤(Real.cos x)^2-(Real.sin x)^2 := by
    have hp := mul_nonneg (show 0≤Real.cos x-Real.sin x by linarith [ht.1,ht.2.2.2.1])
      (add_nonneg hc hs)
    nlinarith
  have hN := N_positive (p := p) (x := x) hg
  have hNg := N_lower (p := p) (x := x) hg
  have hnum : 0≤4*p^2*Real.sin x*Real.cos x := by positivity
  have hfirst : 4*p^2*Real.sin x*Real.cos x/N g p x≤4*p^2*Real.sin x*Real.cos x/g := by
    apply (div_le_div_iff₀ hN hg).2
    exact mul_le_mul_of_nonneg_left hNg hnum
  have hsecond : 0≤3*p^4*Real.sin x*Real.cos x*((Real.cos x)^2-(Real.sin x)^2)/(N g p x)^3 := by positivity
  have hthird : 0≤3*p^6*(Real.sin x)^3*(Real.cos x)^3/(N g p x)^5 := by positivity
  dsimp [NDDD]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedPrimarySupport
