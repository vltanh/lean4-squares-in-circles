module

public import Mathlib.Algebra.Order.Ring.Star
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2NegativeSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection

/-!
# Eight squares: the coefficient comparison in the low-DE positive surplus

The larger coefficient is increased first (`larger_comparison`). With that coefficient fixed at
`1.864`, the smaller one is increased to `1.352` (`smaller_comparison`). That step uses the
decreasing trigonometric quotient `ratioModel` (`ratio_antitone`); the pair of the stress itself
does not change.
-/

section
/-!
## The two positive-angle quartics

Each quartic is a positive combination of the products `(r - a)^i (b - r)^(4 - i)` on its
interval `[a, b]` (its Bernstein coefficients are positive), which `linarith` finds
(`PU_positive`, `PA_positive`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.PositivePolynomial

theorem PU_positive {r : ℝ} (hr : r∈Set.Icc (1/2:ℝ) 1) :
    0<(3/5+(557/1000)*r)^2*(1+r^2+(741/1000)*r)-(1839/1000)^2*r^2 := by
  have h1 : 0≤r-1/2 := sub_nonneg.2 hr.1
  have h2 : 0≤1-r := sub_nonneg.2 hr.2
  linarith [pow_nonneg h1 4,mul_nonneg (pow_nonneg h1 3) h2,
    mul_nonneg (pow_nonneg h1 2) (pow_nonneg h2 2),mul_nonneg h1 (pow_nonneg h2 3),pow_nonneg h2 4]

theorem PA_positive {r : ℝ} (hr : r∈Set.Icc (4/5:ℝ) (27/25:ℝ)) :
    0<(13/12+371/1000+(557/1000)*r)^2*(1+(861/1000)*r^2)-
      qCap*(371/1000+r)^2 := by
  have h1 : 0≤r-4/5 := sub_nonneg.2 hr.1
  have h2 : 0≤27/25-r := sub_nonneg.2 hr.2
  simp only [qCap]
  linarith [pow_nonneg h1 4,mul_nonneg (pow_nonneg h1 3) h2,
    mul_nonneg (pow_nonneg h1 2) (pow_nonneg h2 2),mul_nonneg h1 (pow_nonneg h2 3),pow_nonneg h2 4]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.PositivePolynomial
end
end
end

section
/-!
## Positive-angle derivative bounds at .38 and .5

Concavity moves the
angle to its actual endpoint. The .38 coefficient interval uses the
displayed quartic; the .5 interval uses the displayed decreasing function.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.PositiveSlope
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryCurvatureBounds
open NegativeSlope

def Ud (p q t : ℝ) : ℝ := mixedPDerivative R p q t 0

theorem U_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) : HasDerivAt (U R p q) (Ud p q t) t := by
  have h := mixedP_hasDerivAt (R:=R) (N:=0) hp hq ht
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  simp only [mixedBlock_zero_right] at h
  exact h

theorem Ud_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (Ud p q) (curvature R p q t-p*PositiveAngularEnvelope.phi t) t := by
  have h := mixedPDerivative_hasDerivAt (R:=R) (N:=0) hp hq ht
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  simp only [sub_zero] at h
  exact h

theorem Ud_antitone {p q : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    AntitoneOn (Ud p q) (Icc 0 frameCap) := by
  have hq := hp.trans_le hpq
  apply antiOn_of_hasDeriv_nonpos
    (fun t ht => (Ud_hasDerivAt hp hq ht).continuousAt.continuousWithinAt)
    (fun t ht => Ud_hasDerivAt hp hq (Ioo_subset_Icc_self ht))
  intro t ht
  have hh := mixedP_second_lt (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (by norm_num [qCap])).le hp hpq hqp (Ioo_subset_Icc_self ht)
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  simp only [sub_zero] at hh
  linarith

theorem Ud_normalized {p q : ℝ} (hq : 0<q) (t : ℝ) :
    Ud p q t=q*((p/q)*(Real.cos t-Real.sin t)-
      R*(p/q)*Real.cos t/pairNorm (p/q) 1 t) := by
  have he : pairNorm p q t=q*pairNorm (p/q) 1 t := by
    have hh := pairNorm_homogeneous hq.le (p/q) 1 t
    rwa [mul_div_cancel₀ p hq.ne',mul_one] at hh
  dsimp [Ud,mixedPDerivative,normD1,pairProduct]
  rw [sub_zero,he]
  field_simp [hq.ne']

theorem short_endpoint_trig :
    (557/1000:ℝ)<Real.cos (19/50:ℝ)-Real.sin (19/50:ℝ) ∧
    R*Real.cos (19/50:ℝ)<(1839/1000:ℝ) ∧
    (741/1000:ℝ)<2*Real.sin (19/50:ℝ) := by
  obtain ⟨hsl,hsh,hcl,hch⟩ := rational_taylor (t:=19/50)
    (show ((19/50:ℚ):ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  rw [show ((19/50:ℚ):ℝ)=19/50 by norm_num] at hsl hsh hcl hch
  have hc0 : 0≤Real.cos (19/50:ℝ) := by
    linarith [(transport_trig (show (19/50:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1]
  norm_num [sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,
    PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at hsl hsh hcl hch
  have hprod := mul_le_mul radius_tight.2.le hch hc0 (by norm_num : (0:ℝ)≤494697/250000)
  exact ⟨by linarith,by linarith,by linarith⟩

theorem short_normalized_endpoint {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    -(3/5:ℝ)<r*(Real.cos (19/50:ℝ)-Real.sin (19/50:ℝ))-
      R*r*Real.cos (19/50:ℝ)/pairNorm r 1 (19/50:ℝ) := by
  have hr0 : 0<r := by linarith [hr.1]
  have hN0 := pairNorm_pos hr0 (by norm_num : (0:ℝ)<1)
    (show |(19/50:ℝ)|≤frameCap by norm_num [frameCap])
  have hN2 := pairNorm_sq hr0 (by norm_num : (0:ℝ)<1)
    (show |(19/50:ℝ)|≤frameCap by norm_num [frameCap])
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one] at hN2
  obtain ⟨hphi,hcos,hsin⟩ := short_endpoint_trig
  have hNlower : 1+r^2+(741/1000)*r≤(pairNorm r 1 (19/50:ℝ))^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsin.le hr0.le]
  have hpoly := PositivePolynomial.PU_positive hr
  have hmul := mul_le_mul_of_nonneg_left hNlower (sq_nonneg (3/5+(557/1000)*r))
  have hcross : (1839/1000)*r<(3/5+(557/1000)*r)*pairNorm r 1 (19/50:ℝ) := by
    have hright : 0≤(3/5+(557/1000)*r)*pairNorm r 1 (19/50:ℝ) := by positivity
    have hleft : 0≤(1839/1000)*r := by positivity
    nlinarith
  have hnum := mul_lt_mul_of_pos_right hcos hr0
  have hquot : R*r*Real.cos (19/50:ℝ)/pairNorm r 1 (19/50:ℝ)<3/5+(557/1000)*r := by
    apply (div_lt_iff₀ hN0).2
    nlinarith only [hcross,hnum]
  have hphim := mul_lt_mul_of_pos_left hphi hr0
  linarith

theorem short_bound {p q t : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (ht : t∈Icc 0 (19/50:ℝ)) : -(3/5)*q<Ud p q t := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (1/2:ℝ) 1 :=
    ⟨(le_div_iff₀ hq).2 (by linarith),(div_le_one hq).2 hpq⟩
  have he : -(3/5)*q<Ud p q (19/50:ℝ) := by
    rw [Ud_normalized hq]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (short_normalized_endpoint hr) hq
  exact he.trans_le (Ud_antitone hp hpq hqp
    ⟨ht.1,by norm_num [frameCap] at ⊢; linarith [ht.2]⟩
    (show (19/50:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht.2)

def halfRoot (r : ℝ) : ℝ := Real.sqrt (1+r^2+(479/500)*r)
def halfLower (r : ℝ) : ℝ := (199/500)*r-(869/500)*r/halfRoot r

theorem halfRoot_data {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    0<halfRoot r ∧ (halfRoot r)^2=1+r^2+(479/500)*r ∧ halfRoot r<(43/25:ℝ) := by
  have hr0 : 0≤r := by linarith [hr.1]
  have hrad : 0<1+r^2+(479/500)*r := by positivity
  have hn0 : 0<halfRoot r := Real.sqrt_pos.mpr hrad
  have hn2 : (halfRoot r)^2=1+r^2+(479/500)*r := Real.sq_sqrt hrad.le
  have hr2 : r^2≤1 := by simpa using pow_le_pow_left₀ hr0 hr.2 2
  exact ⟨hn0,hn2,by nlinarith [hr.2]⟩

theorem halfRoot_hasDerivAt {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    HasDerivAt halfRoot ((2*r+479/500)/(2*halfRoot r)) r := by
  have hrad : 1+r^2+(479/500)*r≠0 := by
    have hh := (halfRoot_data hr).2.1
    nlinarith [(halfRoot_data hr).1]
  have hh := (((hasDerivAt_const r (1:ℝ)).add ((hasDerivAt_id r).pow 2)).add
    ((hasDerivAt_id r).const_mul (479/500))).sqrt hrad
  convert hh using 1
  · rfl
  · dsimp [halfRoot]
    ring

theorem halfLower_hasDerivAt {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    HasDerivAt halfLower
      (199/500-(869/500)*(1+(479/1000)*r)/(halfRoot r)^3) r := by
  have hn := halfRoot_data hr
  have hh := ((hasDerivAt_id r).const_mul (199/500:ℝ)).fun_sub
    (((hasDerivAt_id r).const_mul (869/500:ℝ)).fun_div (halfRoot_hasDerivAt hr) hn.1.ne')
  refine hh.congr_deriv ?_
  simp only [id,mul_one]
  field_simp
  linear_combination (-869000000*(halfRoot r)⁻¹^3)*hn.2.1

theorem halfLower_antitone : AntitoneOn halfLower (Icc (1/2:ℝ) 1) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun r hr => (halfLower_hasDerivAt hr).continuousAt.continuousWithinAt)
    (fun r hr => halfLower_hasDerivAt (Ioo_subset_Icc_self hr))
  intro r hr
  have hn := halfRoot_data (Ioo_subset_Icc_self hr)
  have hp := pow_le_pow_left₀ hn.1.le hn.2.2.le 3
  have hleft : (199/500)*(halfRoot r)^3≤(869/500)*(1+(479/1000)*r) := by
    linarith [hr.1]
  have hdiv := (le_div_iff₀ (pow_pos hn.1 3)).2 hleft
  linarith

theorem halfLower_endpoint : -(31/50:ℝ)<halfLower 1 := by
  have hn := halfRoot_data (r:=1) (by norm_num)
  have hnL : (1719/1000:ℝ)<halfRoot 1 := by nlinarith [hn.2.1]
  have hnum : (869/500:ℝ)<(199/500+31/50)*halfRoot 1 := by linarith
  have hh := (div_lt_iff₀ hn.1).2 hnum
  dsimp [halfLower]
  norm_num
  linarith

theorem half_endpoint_trig :
    (199/500:ℝ)<Real.cos (1/2:ℝ)-Real.sin (1/2:ℝ) ∧
    R*Real.cos (1/2:ℝ)<(869/500:ℝ) ∧
    (479/500:ℝ)<2*Real.sin (1/2:ℝ) := by
  obtain ⟨hsl,hsh,hcl,hch⟩ := rational_taylor (t:=1/2)
    (show ((1/2:ℚ):ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  rw [show ((1/2:ℚ):ℝ)=1/2 by norm_num] at hsl hsh hcl hch
  have hc0 : 0≤Real.cos (1/2:ℝ) := by
    linarith [(transport_trig (show (1/2:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1]
  norm_num [sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,
    PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at hsl hsh hcl hch
  have hprod := mul_le_mul radius_tight.2.le hch hc0 (by norm_num : (0:ℝ)≤494697/250000)
  exact ⟨by linarith,by linarith,by linarith⟩

theorem half_normalized_endpoint {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    -(31/50:ℝ)<r*(Real.cos (1/2:ℝ)-Real.sin (1/2:ℝ))-
      R*r*Real.cos (1/2:ℝ)/pairNorm r 1 (1/2:ℝ) := by
  have hr0 : 0<r := by linarith [hr.1]
  have hn := halfRoot_data hr
  have hN0 := pairNorm_pos hr0 (by norm_num : (0:ℝ)<1)
    (show |(1/2:ℝ)|≤frameCap by norm_num [frameCap])
  have hN2 := pairNorm_sq hr0 (by norm_num : (0:ℝ)<1)
    (show |(1/2:ℝ)|≤frameCap by norm_num [frameCap])
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one] at hN2
  obtain ⟨hphi,hcos,hsin⟩ := half_endpoint_trig
  have hNlower : halfRoot r≤pairNorm r 1 (1/2:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hsin.le hr0.le,hn.2.1]
  have hnum : R*r*Real.cos (1/2:ℝ)≤(869/500)*r := by
    nlinarith only [mul_le_mul_of_nonneg_right hcos.le hr0.le]
  have hquot := div_le_div₀ (by positivity : (0:ℝ)≤(869/500)*r)
    hnum hn.1 hNlower
  have hphi' := mul_le_mul_of_nonneg_left hphi.le hr0.le
  have hmono := halfLower_antitone hr (show (1:ℝ)∈Icc (1/2:ℝ) 1 by norm_num) hr.2
  have hlower : halfLower r≤r*(Real.cos (1/2:ℝ)-Real.sin (1/2:ℝ))-
      R*r*Real.cos (1/2:ℝ)/pairNorm r 1 (1/2:ℝ) := by
    dsimp [halfLower]
    linarith
  exact halfLower_endpoint.trans_le (hmono.trans hlower)

theorem half_bound {p q t : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (ht : t∈Icc 0 (1/2:ℝ)) : -(31/50)*q<Ud p q t := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (1/2:ℝ) 1 :=
    ⟨(le_div_iff₀ hq).2 (by linarith),(div_le_one hq).2 hpq⟩
  have he : -(31/50)*q<Ud p q (1/2:ℝ) := by
    rw [Ud_normalized hq]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (half_normalized_endpoint hr) hq
  exact he.trans_le (Ud_antitone hp hpq hqp
    ⟨ht.1,by norm_num [frameCap] at ⊢; linarith [ht.2]⟩
    (show (1/2:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht.2)

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.PositiveSlope
end
end
end

section
/-!
## The original H block with the far EH multiplier

The multiplier is varied only inside a proved scalar comparison. The
original HG argument and its original H witness are kept throughout.
The mixed radial/angular derivative is bounded on the complete rectangle;
its two integrations give precisely the `.005 t` allowance.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEH.HComparison
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open OrdinaryAngleConcavity NegativeAPositiveTD.PositiveSlope

abbrev A : ℝ := p*(129/200)
def baseRoot (k : ℝ) : ℝ := Real.sqrt (1+k^2)
def ratio (k : ℝ) : ℝ := k^2*(k+A)/(baseRoot k)^3
def mixed (k r t : ℝ) : ℝ :=
  R*k^2*Real.cos t*(k+r*Real.sin t)/(pairNorm k r t)^3

theorem radial_norm_derivative {k r t : ℝ} (hk : 0<k) (hr : 0<r)
    (ht : |t|≤frameCap) :
    HasDerivAt (fun r => pairNorm k r t)
      ((r+k*Real.sin t)/pairNorm k r t) r := by
  have hpos := pair_radicand_pos hk hr ht
  have hs : 0<Real.sqrt (k^2+r^2+2*k*r*Real.sin t) := Real.sqrt_pos.mpr hpos
  have h2 : HasDerivAt (fun r : ℝ => r^2) (2*r) r := by simpa using hasDerivAt_pow 2 r
  have h3 : HasDerivAt (fun r : ℝ => 2*k*r*Real.sin t) (2*k*Real.sin t) r := by
    simpa using ((hasDerivAt_id r).const_mul (2*k)).mul_const (Real.sin t)
  have h1 : HasDerivAt (fun r => k^2+r^2+2*k*r*Real.sin t) (2*r+2*k*Real.sin t) r :=
    (h2.const_add (k^2)).fun_add h3
  have hh : HasDerivAt (fun r => pairNorm k r t)
      ((2*r+2*k*Real.sin t)/(2*Real.sqrt (k^2+r^2+2*k*r*Real.sin t))) r :=
    h1.sqrt hpos.ne'
  refine hh.congr_deriv ?_
  unfold pairNorm
  field_simp

theorem mixed_derivative {k r t : ℝ} (hk : 0<k) (hr : 0<r)
    (ht : |t|≤frameCap) :
    HasDerivAt (fun r => Ud k r t) (-mixed k r t) r := by
  have hn := pairNorm_pos hk hr ht
  have hn2 := pairNorm_sq hk hr ht
  have hh := (hasDerivAt_const r (k*(Real.cos t-Real.sin t))).sub
    ((((hasDerivAt_id r).const_mul (R*k*Real.cos t)).div
      (radial_norm_derivative hk hr ht) hn.ne'))
  convert hh using 1
  · funext x
    dsimp [Ud,mixedPDerivative,normD1,pairProduct]
    simp only [sub_zero]
    ring
  · dsimp [mixed,pairEnergy,pairProduct] at hn2 ⊢
    field_simp [hn.ne']
    nlinarith [congrArg (fun z : ℝ => R*k*Real.cos t*z) hn2]

theorem baseRoot_data (k : ℝ) :
    0<baseRoot k ∧ (baseRoot k)^2=1+k^2 := by
  have hh : 0<1+k^2 := by positivity
  exact ⟨Real.sqrt_pos.mpr hh,Real.sq_sqrt hh.le⟩

theorem baseRoot_derivative (k : ℝ) :
    HasDerivAt baseRoot (k/baseRoot k) k := by
  have hh := ((hasDerivAt_const k (1:ℝ)).add ((hasDerivAt_id k).pow 2)).sqrt
    (by positivity : 1+k^2≠0)
  convert hh using 1
  · rfl
  · dsimp [baseRoot]
    ring

theorem ratio_derivative (k : ℝ) :
    HasDerivAt ratio (k*(3*k+2*A-A*k^2)/(baseRoot k)^5) k := by
  have hn := baseRoot_data k
  have hB : baseRoot k≠0 := hn.1.ne'
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*k) k := by simpa using hasDerivAt_pow 2 k
  have h1 : HasDerivAt (fun x : ℝ => x^2*(x+A)) (2*k*(k+A)+k^2*1) k :=
    h2.fun_mul ((hasDerivAt_id' k).add_const A)
  have h3 : HasDerivAt (fun x => baseRoot x^3) (3*baseRoot k*k) k := by
    refine ((baseRoot_derivative k).fun_pow 3).congr_deriv ?_
    norm_num
    field_simp
  have hh : HasDerivAt ratio (((2*k*(k+A)+k^2*1)*baseRoot k^3-k^2*(k+A)*(3*baseRoot k*k))/
      (baseRoot k^3)^2) k :=
    h1.fun_div h3 (pow_ne_zero 3 hB)
  refine hh.congr_deriv ?_
  rw [div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hB)) (pow_ne_zero _ hB)]
  linear_combination (baseRoot k)^6*(3*k^2+2*A*k)*hn.2

theorem ratio_monotone : MonotoneOn ratio (Icc (3/5:ℝ) (4/5)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun k _ => (ratio_derivative k).continuousAt.continuousWithinAt)
    (fun k _ => ratio_derivative k)
  intro k hk
  have hk0 : 0≤k := by linarith [hk.1]
  have hk2 : k^2≤(4/5:ℝ)^2 := by nlinarith [hk.2]
  have hnum : 0≤3*k+2*A-A*k^2 := by dsimp [A,p]; nlinarith
  exact div_nonneg (mul_nonneg hk0 hnum) (pow_nonneg (baseRoot_data k).1.le 5)

theorem ratio_endpoint : R*ratio (4/5)<1 := by
  have hn := baseRoot_data (4/5)
  have hR : 0<R := by linarith [radius_bounds.1]
  have hp : ((baseRoot (4/5))^3)^2=(1+(4/5:ℝ)^2)^3 := by
    rw [← pow_mul,show (3:ℕ)*2=2*3 by norm_num,pow_mul,hn.2]
  have hnum : (R*(4/5:ℝ)^2*((4/5:ℝ)+A))^2<((baseRoot (4/5))^3)^2 := by
    rw [mul_pow,mul_pow,radius_sq,hp]
    norm_num [A,p,qCap]
  have hh : R*(4/5:ℝ)^2*((4/5:ℝ)+A)<(baseRoot (4/5))^3 := by
    have hright := pow_pos hn.1 3
    nlinarith
  unfold ratio
  rw [← mul_div_assoc]
  exact (div_lt_one (pow_pos hn.1 3)).2 (by nlinarith only [hh])

theorem mixed_bound {k r t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (hr : r∈Icc 1 p) (ht : t∈Icc 0 frameCap) : mixed k r t<1 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hr0 : 0<r := by linarith [hr.1]
  have htf : |t|≤frameCap := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hn := pairNorm_pos hk0 hr0 htf
  have hn2 := pairNorm_sq hk0 hr0 htf
  have hb := baseRoot_data k
  have htrig := transport_trig ht
  have hroot : baseRoot k≤pairNorm k r t := by
    have hprod : 0≤2*k*r*Real.sin t := by
      have := mul_nonneg (mul_nonneg hk0.le hr0.le) htrig.2.2.1
      linarith
    dsimp [pairEnergy,pairProduct] at hn2
    nlinarith [hr.1]
  have hs : r*Real.sin t≤A := by
    have hh := mul_le_mul hr.2
      (show Real.sin t≤(129/200:ℝ) by linarith [htrig.2.2.2.1])
      htrig.2.2.1 (by norm_num [p] : (0:ℝ)≤p)
    exact hh
  have hR : 0≤R := Real.sqrt_nonneg _
  have hnum : R*k^2*Real.cos t*(k+r*Real.sin t)≤R*k^2*(k+A) := by
    have hfactor : 0≤k+r*Real.sin t := by
      have := mul_nonneg hr0.le htrig.2.2.1
      linarith
    have hcos := mul_le_mul_of_nonneg_right htrig.2.1 hfactor
    have hh := mul_le_mul_of_nonneg_left hcos (show 0≤R*k^2 by positivity)
    have hh' := mul_le_mul_of_nonneg_left hs (show 0≤R*k^2 by positivity)
    nlinarith only [hh,hh']
  have hquot := div_le_div₀
    (mul_nonneg (mul_nonneg hR (sq_nonneg k)) (by dsimp [A,p]; linarith : 0≤k+A))
    hnum (pow_pos hb.1 3) (pow_le_pow_left₀ hb.1.le hroot 3)
  have hm := mul_le_mul_of_nonneg_left
    (ratio_monotone hk (by norm_num) hk.2) hR
  have hh : mixed k r t≤R*ratio k := by
    have he : R*ratio k=R*k^2*(k+A)/(baseRoot k)^3 := by unfold ratio; ring
    rw [he]
    exact hquot
  exact (hh.trans hm).trans_lt ratio_endpoint

/-- Integration in the EH multiplier, at a fixed original HG angle. -/
theorem positive_slope_comparison {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) : Ud k 1 t-epsilon≤Ud k p t := by
  have hk0 : 0<k := by linarith [hk.1]
  have htf : |t|≤frameCap := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hd (r : ℝ) (hr : r∈Icc 1 p) :=
    mixed_derivative hk0 (show 0<r by linarith [hr.1]) htf
  have hh := derivative_reserve
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => hd r (Ioo_subset_Icc_self hr))
    (fun r hr => by linarith [mixed_bound hk (Ioo_subset_Icc_self hr) ht])
    (show (1:ℝ)∈Icc 1 p by norm_num [p])
    (show p∈Icc 1 p by norm_num [p]) (show (1:ℝ)≤p by norm_num [p])
    (k:=(-1:ℝ))
  dsimp [p,epsilon] at hh ⊢
  linarith

/-- Integration in the original HG angle: the exact allowance is `.005 t`. -/
theorem positive {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) :
    U R k 1 t-epsilon*t≤U R k p t := by
  have hk0 : 0<k := by linarith [hk.1]
  have hd (x : ℝ) (hx : x∈Icc 0 frameCap) :
      HasDerivAt (fun x => U R k p x-U R k 1 x+epsilon*x)
        (Ud k p x-Ud k 1 x+epsilon) x := by
    have h1 := U_hasDerivAt (q:=p) hk0 (by norm_num [p]) hx
    have h2 := U_hasDerivAt (q:=1) hk0 (by norm_num) hx
    have h3 : HasDerivAt (fun x : ℝ => epsilon*x) epsilon x := by
      simpa using (hasDerivAt_id x).const_mul epsilon
    exact (h1.fun_sub h2).fun_add h3
  have hm : MonotoneOn (fun x => U R k p x-U R k 1 x+epsilon*x)
      (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    intro x hx
    linarith [positive_slope_comparison hk (Ioo_subset_Icc_self hx)]
  have hh := hm (by norm_num [frameCap]) ht ht.1
  simp only [U_zero,mul_zero,sub_self,zero_add] at hh
  linarith

theorem negative_norm_derivative_nonneg {k r t : ℝ}
    (hk : k∈Icc (3/5:ℝ) (4/5)) (hr : r∈Icc 1 p)
    (ht : t∈Icc 0 frameCap) :
    0≤r/pairNorm k r 0-(r-k*Real.sin t)/pairNorm k r (-t) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hr0 : 0<r := by linarith [hr.1]
  have ht0 : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have htn : |-t|≤frameCap := by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2
  have hn0 := pairNorm_pos hk0 hr0 ht0
  have hnn := pairNorm_pos hk0 hr0 htn
  have hn02 := pairNorm_sq hk0 hr0 ht0
  have hnn2 := pairNorm_sq hk0 hr0 htn
  simp only [Real.sin_zero,Real.sin_neg,mul_zero,add_zero] at hn02 hnn2
  dsimp [pairEnergy,pairProduct] at hn02 hnn2
  have htrig := transport_trig ht
  have hS : Real.sin t≤(129/200:ℝ) := by linarith [htrig.2.2.2.1]
  have hk2 : k^2≤(4/5:ℝ)^2 := by nlinarith [hk.2]
  have hr2 : r^2≤p^2 := by nlinarith [hr.2]
  have hkr : (3/5:ℝ)≤k*r := by nlinarith [hr.1,hk.1]
  norm_num only [p] at hr2
  have hm := mul_le_mul (show k^2+r^2≤(4/5:ℝ)^2+(201/200)^2 by linarith)
    hS htrig.2.2.1 (by norm_num : (0:ℝ)≤(4/5)^2+(201/200)^2)
  have hf : 0≤2*k*r-(k^2+r^2)*Real.sin t := by
    nlinarith
  have hdiff : 0≤(r*pairNorm k r (-t))^2-
      ((r-k*Real.sin t)*pairNorm k r 0)^2 := by
    have hh := mul_nonneg (mul_nonneg (sq_nonneg k) htrig.2.2.1) hf
    rw [mul_pow,mul_pow,hnn2,hn02]
    nlinarith only [hh]
  have hright : 0≤r*pairNorm k r (-t) := by positivity
  have hcross : (r-k*Real.sin t)*pairNorm k r 0≤r*pairNorm k r (-t) := by
    nlinarith
  have hh := (div_le_div_iff₀ hnn hn0).2 hcross
  linarith

theorem negative_norm_gain {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) :
    pairNorm k 1 0-pairNorm k 1 (-t)≤pairNorm k p 0-pairNorm k p (-t) := by
  have hk0 : 0<k := by linarith [hk.1]
  have ht0 : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have htn : |-t|≤frameCap := by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2
  have hd (r : ℝ) (hr : r∈Icc 1 p) :
      HasDerivAt (fun r => pairNorm k r 0-pairNorm k r (-t))
        (r/pairNorm k r 0-(r-k*Real.sin t)/pairNorm k r (-t)) r := by
    have hr0 : 0<r := by linarith [hr.1]
    simpa only [Real.sin_zero,Real.sin_neg,mul_zero,add_zero,mul_neg,← sub_eq_add_neg]
      using (radial_norm_derivative hk0 hr0 ht0).fun_sub
        (radial_norm_derivative hk0 hr0 htn)
  have hm : MonotoneOn (fun r => pairNorm k r 0-pairNorm k r (-t)) (Icc 1 p) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
      (fun r hr => hd r (Ioo_subset_Icc_self hr))
    intro r hr
    exact negative_norm_derivative_nonneg hk (Ioo_subset_Icc_self hr) ht
  exact hm (by norm_num [p]) (by norm_num [p]) (by norm_num [p])

/-- The negative HG force has its actual coefficient `k` in the cosine term. -/
theorem negative {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) :
    V R k 1 t≤k*(Real.cos t-1)-R*(pairNorm k p (-t)-pairNorm k p 0) := by
  have hg := mul_le_mul_of_nonneg_left (negative_norm_gain hk ht) (Real.sqrt_nonneg qCap)
  have hc := mul_le_mul_of_nonpos_right (show k≤(1:ℝ) by linarith [hk.2])
    (sub_nonpos.mpr (Real.cos_le_one t))
  dsimp [V]
  nlinarith only [hg,hc]

end SquaresInCircles.Eight.GlobalGA.NegativeEH.HComparison
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowPositive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.PositiveSlope

abbrev pMax : ℝ := 169/125
abbrev qMax : ℝ := 233/125

def ratioModel (r t : ℝ) : ℝ :=
  (Real.cos t-Real.sin t)*(pairNorm r 1 t)^3/
    (Real.cos t*(1+r*Real.sin t))
def ratioFirst (r t : ℝ) : ℝ :=
  pairNorm r 1 t*(r*Real.cos t^2*(Real.cos t-Real.sin t)*(2-r^2+r*Real.sin t)-
    (pairNorm r 1 t)^2*(1+r*Real.sin t))/
      (Real.cos t^2*(1+r*Real.sin t)^2)

theorem ratio_derivative {r t : ℝ} (hr : 0<r) (ht : t∈Icc 0 frameCap) :
    HasDerivAt (ratioModel r) (ratioFirst r t) t := by
  have hn := pairNorm_pos hr (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hn2 := pairNorm_sq hr (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hc := NegativeESecant.cos_pos ht
  have hv : 0<1+r*Real.sin t := by
    have hs := (transport_trig ht).2.2.1
    positivity
  have hnorm := pairNorm_hasDerivAt hr (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hd := (((Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t)).mul
    (hnorm.pow 3)).div ((Real.hasDerivAt_cos t).mul
      (((Real.hasDerivAt_sin t).const_mul r).const_add 1)) (mul_ne_zero hc.ne' hv.ne')
  convert hd using 1
  · rfl
  · dsimp [ratioFirst,normD1,pairEnergy,pairProduct] at hn2 ⊢
    field_simp [hn.ne',hc.ne',hv.ne']
    linear_combination
      (r*Real.cos t^3-r*Real.sin t+r*Real.sin t^3+Real.cos t^2+Real.sin t^2-1)*hn2+
      (r^2+1+2*r*Real.sin t)*(1+r*Real.sin t)*(Real.sin_sq_add_cos_sq t)

theorem ratio_antitone {r : ℝ} (hr : r∈Ioc (0:ℝ) (73/100)) :
    AntitoneOn (ratioModel r) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun t ht => (ratio_derivative hr.1 ht).continuousAt.continuousWithinAt)
    (fun t ht => ratio_derivative hr.1 (Ioo_subset_Icc_self ht))
  intro t ht
  have ht' := Ioo_subset_Icc_self ht
  have hs := transport_trig ht'
  have hn := pairNorm_pos hr.1 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht'.1]; exact ht'.2)
  have hn2 := pairNorm_sq hr.1 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht'.1]; exact ht'.2)
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one] at hn2
  have hr2 := pow_le_pow_left₀ hr.1.le hr.2 2
  have hcos2 : Real.cos t^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq t]
  have hphi : 0≤Real.cos t-Real.sin t := by linarith [hs.1,hs.2.2.2.1]
  have hphi1 : Real.cos t-Real.sin t≤1 := by linarith [Real.cos_le_one t,hs.2.2.1]
  have hfactor : Real.cos t^2*(Real.cos t-Real.sin t)≤1 := by
    have hh := mul_le_mul hcos2 hphi1 hphi (by norm_num : (0:ℝ)≤1)
    simpa using hh
  have hcoef : 0≤r*(2-r^2+r*Real.sin t) := by
    have hh := mul_nonneg hr.1.le hs.2.2.1
    exact mul_nonneg hr.1.le (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hfactor hcoef
  have hrest : 0≤r*Real.sin t*(3+r^2-r) := by
    apply mul_nonneg (mul_nonneg hr.1.le hs.2.2.1)
    nlinarith
  have hpoly : r*(2-r^2+r*Real.sin t)≤(pairNorm r 1 t)^2*(1+r*Real.sin t) := by
    rw [hn2]
    nlinarith [sq_nonneg (1-r),pow_nonneg hr.1.le 3,
      mul_nonneg (sq_nonneg r) (sq_nonneg (Real.sin t))]
  have hnum : r*Real.cos t^2*(Real.cos t-Real.sin t)*(2-r^2+r*Real.sin t)-
      (pairNorm r 1 t)^2*(1+r*Real.sin t)≤0 := by nlinarith only [hscaled,hpoly]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hn.le hnum)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem ratio_below_radius {r t : ℝ} (hr : r∈Ioc (0:ℝ) (73/100))
    (ht : t∈Icc 0 frameCap) : ratioModel r t<R := by
  have hm := ratio_antitone hr (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht ht.1
  have hzero : ratioModel r 0=(Real.sqrt (1+r^2))^3 := by
    simp [ratioModel,pairNorm,add_comm]
  rw [hzero] at hm
  have hn : 0<Real.sqrt (1+r^2) := Real.sqrt_pos.mpr (by positivity)
  have hn2 := Real.sq_sqrt (show 0≤1+r^2 by positivity)
  have hr2 := pow_le_pow_left₀ hr.1.le hr.2 2
  have hcube := pow_le_pow_left₀ (by positivity : 0≤1+r^2)
    (show 1+r^2≤1+(73/100:ℝ)^2 by linarith) 3
  have hpow : ((Real.sqrt (1+r^2))^3)^2=(1+r^2)^3 := by
    rw [←pow_mul,show (3:ℕ)*2=2*3 by norm_num,pow_mul,hn2]
  have htest : (1+(73/100:ℝ)^2)^3<qCap := by norm_num [qCap]
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hh : (Real.sqrt (1+r^2))^3<R :=
    lt_of_pow_lt_pow_left₀ 2 hR.le (by rw [hpow,radius_sq]; exact hcube.trans_lt htest)
  exact hm.trans_lt hh

theorem larger_comparison {p q Q t : ℝ} (hp : 0<p) (hq : 0<q)
    (hqQ : q≤Q) (ht : t∈Icc 0 frameCap) : Ud p Q t≤Ud p q t := by
  have hm : AntitoneOn (fun q => Ud p q t) (Icc q Q) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro v hv
      exact (NegativeEH.HComparison.mixed_derivative hp (hq.trans_le hv.1)
        (by rw [abs_of_nonneg ht.1]; exact ht.2)).continuousAt.continuousWithinAt
    · intro v hv
      exact NegativeEH.HComparison.mixed_derivative hp (hq.trans hv.1)
        (by rw [abs_of_nonneg ht.1]; exact ht.2)
    · intro v hv
      have hcos := (NegativeESecant.cos_pos ht).le
      have hsin := (transport_trig ht).2.2.1
      have hv0 : 0≤v := (hq.trans hv.1).le
      change -NegativeEH.HComparison.mixed p v t≤0
      apply neg_nonpos.mpr
      dsimp [NegativeEH.HComparison.mixed]
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (sq_nonneg p)) hcos) (add_nonneg hp.le (mul_nonneg hv0 hsin)))
        (pow_nonneg (Real.sqrt_nonneg _) 3)
  exact hm ⟨le_rfl,hqQ⟩ ⟨hqQ,le_rfl⟩ hqQ

def smallerFirst (p q t : ℝ) : ℝ :=
  Real.cos t-Real.sin t-R*q^2*Real.cos t*(q+p*Real.sin t)/(pairNorm p q t)^3

theorem smaller_derivative {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (fun p => Ud p q t) (smallerFirst p q t) p := by
  have hn := pairNorm_pos hp hq (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hn2 := pairNorm_sq hp hq (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hnorm : HasDerivAt (fun p => pairNorm p q t)
      ((p+q*Real.sin t)/pairNorm p q t) p := by
    simpa only [pairNorm_symm] using NegativeEH.HComparison.radial_norm_derivative hq hp
      (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hd := ((hasDerivAt_id p).const_mul (Real.cos t-Real.sin t)).sub
    (((hasDerivAt_id p).const_mul (R*q*Real.cos t)).div hnorm hn.ne')
  convert hd using 1
  · funext x
    dsimp [Ud,mixedPDerivative,normD1,pairProduct]
    simp only [sub_zero]
    ring
  · dsimp [smallerFirst,pairEnergy,pairProduct] at hn2 ⊢
    field_simp [hn.ne']
    nlinarith [congrArg (fun v : ℝ => R*q*Real.cos t*v) hn2]

theorem smallerFirst_negative {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (hr : p/q≤73/100) (ht : t∈Icc 0 frameCap) : smallerFirst p q t<0 := by
  have hratio : p/q∈Ioc (0:ℝ) (73/100) := ⟨div_pos hp hq,hr⟩
  have hh := ratio_below_radius hratio ht
  have hn := pairNorm_pos hratio.1 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hc := NegativeESecant.cos_pos ht
  have hv : 0<1+(p/q)*Real.sin t := by
    have hsin := (transport_trig ht).2.2.1
    positivity
  have hclear := (div_lt_iff₀ (mul_pos hc hv)).1 hh
  have hhom : pairNorm p q t=q*pairNorm (p/q) 1 t := by
    have hh := OrdinaryNegativeEnvelope.pairNorm_homogeneous hq.le (p/q) 1 t
    rwa [mul_div_cancel₀ p hq.ne',mul_one] at hh
  have hid : smallerFirst p q t=Real.cos t-Real.sin t-
      R*Real.cos t*(1+(p/q)*Real.sin t)/(pairNorm (p/q) 1 t)^3 := by
    rw [smallerFirst,hhom]
    field_simp [hq.ne',hn.ne']
  rw [hid]
  have hdiv := (lt_div_iff₀ (pow_pos hn 3)).2 hclear
  have e : R*Real.cos t*(1+p/q*Real.sin t)/(pairNorm (p/q) 1 t)^3=
      R*(Real.cos t*(1+p/q*Real.sin t))/(pairNorm (p/q) 1 t)^3 := by ring
  rw [e]
  linarith

theorem smaller_comparison {p t : ℝ} (hp : 0<p) (hpP : p≤pMax)
    (ht : t∈Icc 0 frameCap) : Ud pMax qMax t≤Ud p qMax t := by
  have hq : 0<qMax := by norm_num [qMax]
  have hm : AntitoneOn (fun p => Ud p qMax t) (Icc p pMax) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x hx => (smaller_derivative (hp.trans_le hx.1) hq ht).continuousAt.continuousWithinAt)
      (fun x hx => smaller_derivative (hp.trans hx.1) hq ht)
    intro x hx
    have hr : x/qMax≤73/100 := (div_le_iff₀ hq).2 (by dsimp [qMax,pMax] at *; linarith [hx.2])
    exact (smallerFirst_negative (hp.trans hx.1) hq hr ht).le
  exact hm ⟨le_rfl,hpP⟩ ⟨hpP,le_rfl⟩ hpP

/-- The slope `Ud` at the largest coefficients `pMax`, `qMax` is at most its value at the two
coefficients `p`, `q` of the stress, kept on the right. -/
theorem coefficient_comparison {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (hpP : p≤pMax) (hqQ : q≤qMax) (ht : t∈Icc 0 frameCap) :
    Ud pMax qMax t≤Ud p q t :=
  (smaller_comparison hp hpP ht).trans (larger_comparison hp hq hqQ ht)

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowPositive
end
end
end
