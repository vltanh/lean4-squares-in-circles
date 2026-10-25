module

public import SquaresInCircles.Eight.TableFree.SecondMixedPrimarySupport

/-!
# One square completion for the lower primary circle support

The square-root tangent and ordinary alternating Taylor inequalities
give one seventh-degree expression on the full angle half.  Its
remainder above a cubic is an explicit sum of nonnegative products.
A single quadratic discriminant then proves strict positivity.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedPrimarySupport
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

end SquaresInCircles.Eight.TableFree.SecondWord.MixedPrimarySupport
