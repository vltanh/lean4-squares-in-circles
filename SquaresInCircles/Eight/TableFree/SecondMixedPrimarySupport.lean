module

public import SquaresInCircles.Eight.TableFree.SecondMixedAffineScalars

/-!
# Unsquared primary circle support on a complete quarter half

The radical is positive for every real angle.  Its exact second
derivative gives a uniform concavity criterion for the upper support.
The criterion involves only the fixed support coefficients and is
proved on the entire closed angle interval.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedPrimarySupport
open CommonQuarter CorePairGeometry Arithmetic

def N (g p x : ℝ) : ℝ := Real.sqrt (g^2+p^2*(Real.cos x)^2)
def ND (g p x : ℝ) : ℝ := -p^2*Real.sin x*Real.cos x/N g p x
def NDD (g p x : ℝ) : ℝ :=
  -p^2*((Real.cos x)^2-(Real.sin x)^2)/N g p x-
    p^4*(Real.sin x)^2*(Real.cos x)^2/(N g p x)^3
def plus (g p K x : ℝ) : ℝ :=
  (K+x)*Real.cos x+g*(1-Real.sin x/12)-radius*N g p x
def plusD (g p K x : ℝ) : ℝ :=
  (1-g/12)*Real.cos x-(K+x)*Real.sin x-radius*ND g p x
def plusDD (g p K x : ℝ) : ℝ :=
  -(K+x)*Real.cos x-(2-g/12)*Real.sin x-radius*NDD g p x
def minus (g p K x : ℝ) : ℝ :=
  (K-x)*Real.cos x+g*(1+(13/12)*Real.sin x)-radius*N g p x

lemma radicand_positive {g p x : ℝ} (hg : 0<g) : 0<g^2+p^2*(Real.cos x)^2 := by
  have hh := sq_pos_of_pos hg
  have hp := mul_nonneg (sq_nonneg p) (sq_nonneg (Real.cos x))
  linarith

lemma N_positive {g p x : ℝ} (hg : 0<g) : 0<N g p x := Real.sqrt_pos.mpr (radicand_positive hg)
lemma N_sq {g p x : ℝ} (hg : 0<g) : (N g p x)^2=g^2+p^2*(Real.cos x)^2 :=
  Real.sq_sqrt (radicand_positive hg).le

lemma N_lower {g p x : ℝ} (hg : 0<g) : g≤N g p x := by
  have hp := N_positive (p := p) (x := x) hg
  have he := N_sq (p := p) (x := x) hg
  nlinarith [mul_nonneg (sq_nonneg p) (sq_nonneg (Real.cos x))]

lemma N_hasDerivAt {g p x : ℝ} (hg : 0<g) : HasDerivAt (N g p) (ND g p x) x := by
  convert ((((Real.hasDerivAt_cos x).pow 2).const_mul (p^2)).const_add (g^2)).sqrt
    (radicand_positive (p := p) (x := x) hg).ne' using 1 <;> dsimp [N,ND] <;> ring

lemma ND_hasDerivAt {g p x : ℝ} (hg : 0<g) : HasDerivAt (ND g p) (NDD g p x) x := by
  have hn := N_positive (p := p) (x := x) hg
  have hd := (((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)).const_mul (-p^2)).div
    (N_hasDerivAt hg) hn.ne'
  convert hd using 1
  · ext y
    dsimp [ND]
    ring
  · dsimp [NDD,ND]
    field_simp [hn.ne']
    ring

lemma negative_curvature_upper {g p x : ℝ} (hg : 0<g) :
    -NDD g p x≤p^2/g+p^4*(Real.sin x)^2/g^3 := by
  have hn := N_positive (p := p) (x := x) hg
  have hng := N_lower (p := p) (x := x) hg
  have hc : (Real.cos x)^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq x,sq_nonneg (Real.sin x)]
  have hdiff : (Real.cos x)^2-(Real.sin x)^2≤1 := by nlinarith [sq_nonneg (Real.sin x)]
  have hfirst : p^2*((Real.cos x)^2-(Real.sin x)^2)/N g p x≤p^2/g := by
    apply (div_le_div_iff₀ hn hg).2
    have hh := mul_le_mul_of_nonneg_left hdiff hg.le
    have hbase : g*((Real.cos x)^2-(Real.sin x)^2)≤N g p x := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hbase (sq_nonneg p)
    nlinarith
  have hcube := pow_le_pow_left₀ hg.le hng 3
  have hsecond : p^4*(Real.sin x)^2*(Real.cos x)^2/(N g p x)^3≤
      p^4*(Real.sin x)^2/g^3 := by
    apply (div_le_div_iff₀ (pow_pos hn 3) (pow_pos hg 3)).2
    have hh := mul_le_mul_of_nonneg_left hc (pow_pos hg 3).le
    have hbase : g^3*(Real.cos x)^2≤(N g p x)^3 := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hbase
      (mul_nonneg (show 0≤p^4 by positivity) (sq_nonneg (Real.sin x)))
    nlinarith
  dsimp [NDD]
  linarith

lemma plus_hasDerivAt {g p K x : ℝ} (hg : 0<g) :
    HasDerivAt (plus g p K) (plusD g p K x) x := by
  convert ((((hasDerivAt_id x).const_add K).mul (Real.hasDerivAt_cos x)).add
    ((((Real.hasDerivAt_sin x).div_const 12).const_sub 1).const_mul g)).sub
      ((N_hasDerivAt (p := p) hg).const_mul radius) using 1 <;> dsimp [plus,plusD] <;> ring

lemma plusD_hasDerivAt {g p K x : ℝ} (hg : 0<g) :
    HasDerivAt (plusD g p K) (plusDD g p K x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (1-g/12)).sub
    (((hasDerivAt_id x).const_add K).mul (Real.hasDerivAt_sin x))).sub
      ((ND_hasDerivAt (p := p) hg).const_mul radius)) using 1 <;> dsimp [plusD,plusDD] <;> ring

lemma plusDD_negative {g p K x : ℝ} (hg : 0<g) (hK : 0≤K)
    (hconstant : radius*p^2/g<K)
    (hslope : (129/200)*(K+radius*p^4/g^3)<2-g/12)
    (hx : x∈Icc (0:ℝ) (7/10)) : plusDD g p K x<0 := by
  have ht := positive_trig hx
  have hcos : 0≤Real.cos x := by linarith [ht.1]
  have hsin := ht.2.2.1
  have hsinu : Real.sin x≤129/200 := by linarith [ht.2.2.2.1]
  have hcLower : 1-(Real.sin x)^2≤Real.cos x := by
    have hh := mul_nonneg hcos (show 0≤1-Real.cos x by linarith [ht.2.1])
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hradius : 0≤radius := by linarith [radius_bounds.1]
  have hcurv := mul_le_mul_of_nonneg_left (negative_curvature_upper (p := p) (x := x) hg) hradius
  have hKcos := mul_le_mul_of_nonneg_left hcLower hK
  have hxc := mul_nonneg hx.1 hcos
  have hb : 0≤radius*p^4/g^3 := div_nonneg (mul_nonneg hradius (by positivity)) (pow_pos hg 3).le
  have hsq := mul_nonneg (sub_nonneg.mpr hsinu)
    (mul_nonneg (add_nonneg hK hb) hsin)
  have hlinear := mul_nonneg (sub_nonneg.mpr hslope.le) hsin
  dsimp [plusDD]
  nlinarith

theorem plus_concave {g p K : ℝ} (hg : 0<g) (hK : 0≤K)
    (hconstant : radius*p^2/g<K)
    (hslope : (129/200)*(K+radius*p^4/g^3)<2-g/12) :
    ConcaveOn ℝ (Icc (0:ℝ) (7/10)) (plus g p K) :=
  concave_of_deriv2 (fun _ _ => plus_hasDerivAt hg)
    (fun _ _ => plusD_hasDerivAt hg)
    (fun _ hx => (plusDD_negative hg hK hconstant hslope hx).le)

end SquaresInCircles.Eight.TableFree.SecondWord.MixedPrimarySupport
