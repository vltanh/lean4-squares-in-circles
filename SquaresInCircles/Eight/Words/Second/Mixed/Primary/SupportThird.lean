module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Words.Common.QuarterState
public import SquaresInCircles.Eight.Words.Common.ZeroEndpoint

/-!
# Eight squares: the third derivative of the unsquared primary support

The norm derivative is bounded on the complete lower deviation half.
The estimate retains its positive denominator and uses only the common
whole-window trigonometric bounds.
-/

section
/-!
## Unsquared primary circle support on a complete quarter half

The radical is positive for every real angle.  Its exact second
derivative gives a uniform concavity criterion for the upper support.
The criterion involves only the fixed support coefficients and is
proved on the entire closed angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedPrimarySupport
open CommonQuarter CorePairGeometry Arithmetic

def N (g p x : ℝ) : ℝ := Real.sqrt (g^2+p^2*(Real.cos x)^2)
def ND (g p x : ℝ) : ℝ := -p^2*Real.sin x*Real.cos x/N g p x
def NDD (g p x : ℝ) : ℝ :=
  -p^2*((Real.cos x)^2-(Real.sin x)^2)/N g p x-
    p^4*(Real.sin x)^2*(Real.cos x)^2/(N g p x)^3
def plus (g p K x : ℝ) : ℝ :=
  (K+x)*Real.cos x+g*(1-Real.sin x/12)-CommonQuarter.radius*N g p x
def plusD (g p K x : ℝ) : ℝ :=
  (1-g/12)*Real.cos x-(K+x)*Real.sin x-CommonQuarter.radius*ND g p x
def plusDD (g p K x : ℝ) : ℝ :=
  -(K+x)*Real.cos x-(2-g/12)*Real.sin x-CommonQuarter.radius*NDD g p x
def minus (g p K x : ℝ) : ℝ :=
  (K-x)*Real.cos x+g*(1+(13/12)*Real.sin x)-CommonQuarter.radius*N g p x

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
  have hn := N_positive (p := p) (x := x) hg
  have h : HasDerivAt (fun y => Real.sqrt (g^2+p^2*(Real.cos y)^2))
      ((p^2*((2:ℕ)*(Real.cos x)^(2-1)*(-Real.sin x)))/(2*Real.sqrt (g^2+p^2*(Real.cos x)^2))) x :=
    ((((Real.hasDerivAt_cos x).pow 2).const_mul (p^2)).const_add (g^2)).sqrt
      (radicand_positive (p := p) (x := x) hg).ne'
  refine h.congr_deriv ?_
  have hN : Real.sqrt (g^2+p^2*(Real.cos x)^2)=N g p x := rfl
  rw [hN]
  simp only [ND]
  field_simp
  norm_num
  ring

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
  have he : -NDD g p x=p^2*((Real.cos x)^2-(Real.sin x)^2)/N g p x+
      p^4*(Real.sin x)^2*(Real.cos x)^2/(N g p x)^3 := by
    dsimp [NDD]
    ring
  rw [he]
  linarith

lemma plus_hasDerivAt {g p K x : ℝ} (hg : 0<g) :
    HasDerivAt (plus g p K) (plusD g p K x) x := by
  have h1 : HasDerivAt (fun y => (K+y)*Real.cos y) (1*Real.cos x+(K+x)*(-Real.sin x)) x :=
    ((hasDerivAt_id' x).const_add K).mul (Real.hasDerivAt_cos x)
  have h2 : HasDerivAt (fun y => g*(1-Real.sin y/12)) (g*(-(Real.cos x/12))) x :=
    (((Real.hasDerivAt_sin x).div_const 12).const_sub 1).const_mul g
  have h3 : HasDerivAt (fun y => CommonQuarter.radius*N g p y) (CommonQuarter.radius*ND g p x) x :=
    (N_hasDerivAt (p := p) hg).const_mul CommonQuarter.radius
  refine ((h1.add h2).sub h3).congr_deriv ?_
  simp only [plusD]
  ring

lemma plusD_hasDerivAt {g p K x : ℝ} (hg : 0<g) :
    HasDerivAt (plusD g p K) (plusDD g p K x) x := by
  have h1 : HasDerivAt (fun y => (1-g/12)*Real.cos y) ((1-g/12)*(-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul (1-g/12)
  have h2 : HasDerivAt (fun y => (K+y)*Real.sin y) (1*Real.sin x+(K+x)*Real.cos x) x :=
    ((hasDerivAt_id' x).const_add K).mul (Real.hasDerivAt_sin x)
  have h3 : HasDerivAt (fun y => CommonQuarter.radius*ND g p y) (CommonQuarter.radius*NDD g p x) x :=
    (ND_hasDerivAt (p := p) hg).const_mul CommonQuarter.radius
  refine ((h1.sub h2).sub h3).congr_deriv ?_
  simp only [plusDD]
  ring

lemma plusDD_negative {g p K x : ℝ} (hg : 0<g) (hK : 0≤K)
    (hconstant : CommonQuarter.radius*p^2/g<K)
    (hslope : (129/200)*(K+CommonQuarter.radius*p^4/g^3)<2-g/12)
    (hx : x∈Icc (0:ℝ) (7/10)) : plusDD g p K x<0 := by
  have ht := positive_trig hx
  have hcos : 0≤Real.cos x := by linarith [ht.1]
  have hsin := ht.2.2.1
  have hsinu : Real.sin x≤129/200 := by linarith [ht.2.2.2.1]
  have hcLower : 1-(Real.sin x)^2≤Real.cos x := by
    have hh := mul_nonneg hcos (show 0≤1-Real.cos x by linarith [ht.2.1])
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hradius : 0≤CommonQuarter.radius := by linarith [radius_bounds.1]
  have hcurv : -(CommonQuarter.radius*NDD g p x)≤CommonQuarter.radius*p^2/g+(CommonQuarter.radius*p^4/g^3)*(Real.sin x)^2 := by
    have hh := mul_le_mul_of_nonneg_left (negative_curvature_upper (p := p) (x := x) hg) hradius
    have he : CommonQuarter.radius*(p^2/g+p^4*(Real.sin x)^2/g^3)=
        CommonQuarter.radius*p^2/g+(CommonQuarter.radius*p^4/g^3)*(Real.sin x)^2 := by ring
    linarith
  have hKcos := mul_le_mul_of_nonneg_left hcLower hK
  have hxc := mul_nonneg hx.1 hcos
  have hb : 0≤CommonQuarter.radius*p^4/g^3 := div_nonneg (mul_nonneg hradius (by positivity)) (pow_pos hg 3).le
  have hsq := mul_nonneg (sub_nonneg.mpr hsinu)
    (mul_nonneg (add_nonneg hK hb) hsin)
  have hlinear := mul_nonneg (sub_nonneg.mpr hslope.le) hsin
  dsimp [plusDD]
  linarith

theorem plus_concave {g p K : ℝ} (hg : 0<g) (hK : 0≤K)
    (hconstant : CommonQuarter.radius*p^2/g<K)
    (hslope : (129/200)*(K+CommonQuarter.radius*p^4/g^3)<2-g/12) :
    ConcaveOn ℝ (Icc (0:ℝ) (7/10)) (plus g p K) :=
  concave_of_deriv2 (fun _ _ => plus_hasDerivAt hg)
    (fun _ _ => plusD_hasDerivAt hg)
    (fun _ hx => (plusDD_negative hg hK hconstant hslope hx).le)

end SquaresInCircles.Eight.SecondWord.MixedPrimarySupport
end
end
end

section
/-!
## One square completion for the lower primary circle support

The square-root tangent and ordinary alternating Taylor inequalities
give one seventh-degree expression on the full angle half.  Its
remainder above a cubic is an explicit sum of nonnegative products.
A single quadratic discriminant then proves strict positivity.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedPrimarySupport
open CommonQuarter CorePairGeometry Arithmetic

def gain (g p : ℝ) : ℝ := CommonQuarter.radius*p^2/(2*N g p 0)
def linearCoefficient (g : ℝ) : ℝ := 13*g/12-1
def quadraticCoefficient (g p K : ℝ) : ℝ := K/2-gain g p
def cubicCoefficient (g p K : ℝ) : ℝ :=
  1/2-13*g/72+(7/10)*(K/24-gain g p/3)+
    (49/100)*(13*g/1440-1/24)-(343/1000)*K/720
def lowerPolynomial (g p K x : ℝ) : ℝ :=
  minus g p K 0+(13*g/12-1)*x+(gain g p-K/2)*x^2+
    (1/2-13*g/72)*x^3+(K/24-gain g p/3)*x^4+
      (13*g/1440-1/24)*x^5-K*x^6/720+(1/720-13*g/60480)*x^7

lemma minus_zero (g p K : ℝ) : minus g p K 0=K+g-CommonQuarter.radius*N g p 0 := by
  simp [minus]

lemma norm_tangent {g p x : ℝ} (hg : 0<g) :
    N g p x≤N g p 0-p^2*(Real.sin x)^2/(2*N g p 0) := by
  have h0 := N_sq (p := p) (x := 0) hg
  norm_num at h0
  have hx := N_sq (p := p) (x := x) hg
  have hp := N_positive (p := p) (x := 0) hg
  have he : (N g p 0)^2-(N g p x)^2=p^2*(Real.sin x)^2 := by
    linear_combination h0-hx-p^2*(Real.sin_sq_add_cos_sq x)
  have hh : p^2*(Real.sin x)^2/(2*N g p 0)≤N g p 0-N g p x := by
    apply (div_le_iff₀ (by positivity : 0<2*N g p 0)).2
    nlinarith [sq_nonneg (N g p 0-N g p x)]
  linarith

lemma sine_square_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) :
    x^2-x^4/3≤(Real.sin x)^2 := by
  have hs := Real.sin_ge_sub_cube hx.1
  have h2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h3 := mul_le_mul_of_nonneg_left h2 hx.1
  have hbase : 0≤x-x^3/6 := by linarith [hx.1]
  have hsquare := pow_le_pow_left₀ hbase hs 2
  nlinarith [sq_nonneg (x^3)]

lemma lower_polynomial {g p K x : ℝ} (hg : 0<g) (hK : (7/10:ℝ)≤K)
    (hx : x∈Icc (0:ℝ) (7/10)) : lowerPolynomial g p K x≤ minus g p K x := by
  have hR : 0≤CommonQuarter.radius := by linarith [radius_bounds.1]
  have hp := N_positive (p := p) (x := 0) hg
  have hgain : 0≤gain g p := div_nonneg (mul_nonneg hR (sq_nonneg p)) (by positivity)
  have hc := mul_le_mul_of_nonneg_left (cos_lower_six hx.1)
    (show 0≤K-x by linarith [hx.2])
  have hs := mul_le_mul_of_nonneg_left (sin_lower_seven hx.1)
    (show (0:ℝ)≤13*g/12 by positivity)
  have hs2 := mul_le_mul_of_nonneg_left (sine_square_lower hx) hgain
  have hn : CommonQuarter.radius*N g p x≤CommonQuarter.radius*N g p 0-gain g p*(Real.sin x)^2 := by
    have hh := mul_le_mul_of_nonneg_left (norm_tangent (p := p) (x := x) hg) hR
    have he : CommonQuarter.radius*(N g p 0-p^2*(Real.sin x)^2/(2*N g p 0))=
        CommonQuarter.radius*N g p 0-gain g p*(Real.sin x)^2 := by
      dsimp [gain]
      ring
    linarith
  have he : (K-x)*(1-x^2/2+x^4/24-x^6/720)+g+(13*g/12)*(x-x^3/6+x^5/120-x^7/5040)-
      CommonQuarter.radius*N g p 0+gain g p*(x^2-x^4/3)=lowerPolynomial g p K x := by
    rw [lowerPolynomial,minus_zero]
    ring
  rw [←he]
  dsimp only [minus]
  linarith

lemma polynomial_remainder (g p K x : ℝ) :
    lowerPolynomial g p K x-
      (minus g p K 0+x*(linearCoefficient g-quadraticCoefficient g p K*x+cubicCoefficient g p K*x^2))=
    -(K/24-gain g p/3)*x^3*(7/10-x)-
      (13*g/1440-1/24)*x^3*(49/100-x^2)+
        (K/720)*x^3*(343/1000-x^3)+(1/720-13*g/60480)*x^7 := by
  dsimp [lowerPolynomial,linearCoefficient,quadraticCoefficient,cubicCoefficient]
  ring

lemma cubic_minorant {g p K x : ℝ} (hg : 0<g) (hK : (7/10:ℝ)≤K)
    (hfour : K/24-gain g p/3≤0) (hfive : 13*g/1440-1/24≤0)
    (hseven : 0≤1/720-13*g/60480) (hx : x∈Icc (0:ℝ) (7/10)) :
    minus g p K 0+x*(linearCoefficient g-quadraticCoefficient g p K*x+cubicCoefficient g p K*x^2)
      ≤ minus g p K x := by
  have h2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h3 := pow_le_pow_left₀ hx.1 hx.2 3
  have hterm4 := mul_nonneg (mul_nonneg (neg_nonneg.mpr hfour) (pow_nonneg hx.1 3))
    (show 0≤7/10-x by linarith [hx.2])
  have hterm5 := mul_nonneg (mul_nonneg (neg_nonneg.mpr hfive) (pow_nonneg hx.1 3))
    (show 0≤49/100-x^2 by norm_num at h2; linarith)
  have hterm6 := mul_nonneg (mul_nonneg (show 0≤K/720 by linarith) (pow_nonneg hx.1 3))
    (show 0≤343/1000-x^3 by norm_num at h3; linarith)
  have hterm7 := mul_nonneg hseven (pow_nonneg hx.1 7)
  have he := polynomial_remainder g p K x
  have hh := lower_polynomial (p := p) hg hK hx
  linarith

theorem minus_positive {g p K α β ε x : ℝ} (hg : 0<g) (hK : (7/10:ℝ)≤K)
    (hfour : K/24-gain g p/3≤0) (hfive : 13*g/1440-1/24≤0)
    (hseven : 0≤1/720-13*g/60480) (hzero : 0< minus g p K 0)
    (hα : α≤linearCoefficient g) (hβ : quadraticCoefficient g p K≤β)
    (hε : ε≤cubicCoefficient g p K) (hεpos : 0<ε) (hdisc : β^2<4*α*ε)
    (hx : x∈Icc (0:ℝ) (7/10)) : 0< minus g p K x := by
  have hquad : 0<α-β*x+ε*x^2 := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hεpos.le (le_of_not_gt hn)
    nlinarith [sq_nonneg (2*ε*x-β)]
  have hb := mul_nonneg (sub_nonneg.mpr hβ) hx.1
  have he := mul_nonneg (sub_nonneg.mpr hε) (sq_nonneg x)
  have hcoeff : 0<linearCoefficient g-quadraticCoefficient g p K*x+cubicCoefficient g p K*x^2 := by
    nlinarith
  have hpaid := mul_nonneg hx.1 hcoeff.le
  have hlower := cubic_minorant hg hK hfour hfive hseven hx
  linarith

end SquaresInCircles.Eight.SecondWord.MixedPrimarySupport
end
end
end

section
/-!
## Exact derivatives of the lower primary circle support

These formulas retain the unsquared norm and are valid for every real
angle whenever the primary multiplier is positive.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedPrimarySupport
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

end SquaresInCircles.Eight.SecondWord.MixedPrimarySupport
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedPrimarySupport
open CommonQuarter CorePairGeometry Arithmetic

def NDDD (g p x : ℝ) : ℝ :=
  4*p^2*Real.sin x*Real.cos x/N g p x-
    3*p^4*Real.sin x*Real.cos x*((Real.cos x)^2-(Real.sin x)^2)/(N g p x)^3-
    3*p^6*(Real.sin x)^3*(Real.cos x)^3/(N g p x)^5
def minusDDD (g p K x : ℝ) : ℝ :=
  (3-13*g/12)*Real.cos x+(K-x)*Real.sin x-CommonQuarter.radius*NDDD g p x

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
  have h1 : HasDerivAt (fun y => -(K-y)*Real.cos y)
      ((-(-1))*Real.cos x+(-(K-x))*(-Real.sin x)) x :=
    ((hasDerivAt_id' x).const_sub K).neg.mul (Real.hasDerivAt_cos x)
  have h2 : HasDerivAt (fun y => (2-13*g/12)*Real.sin y) ((2-13*g/12)*Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul (2-13*g/12)
  have h3 : HasDerivAt (fun y => CommonQuarter.radius*NDD g p y) (CommonQuarter.radius*NDDD g p x) x :=
    (NDD_hasDerivAt (p := p) hg).const_mul CommonQuarter.radius
  refine ((h1.add h2).sub h3).congr_deriv ?_
  simp only [minusDDD]
  ring

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

end SquaresInCircles.Eight.SecondWord.MixedPrimarySupport
end
end
end
