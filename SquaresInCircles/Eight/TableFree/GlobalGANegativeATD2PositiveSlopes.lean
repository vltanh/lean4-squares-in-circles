module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2PositivePolynomial

/-!
# Positive-angle derivative bounds at .38 and .5

Uncompiled transcription of (27)--(29) and the positive-surplus derivative
bound in Section 9 of the negative-A angle companion. Concavity moves the
angle to its actual endpoint. The .38 coefficient interval uses the
displayed quartic; the .5 interval uses the displayed decreasing function.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.PositiveSlope
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryCurvatureBounds
open NegativeSlope

def Ud (p q t : ℝ) : ℝ := mixedPDerivative R p q t 0

theorem U_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) : HasDerivAt (U R p q) (Ud p q t) t := by
  simpa only [mixedBlock_zero_right] using mixedP_hasDerivAt (R:=R) hp hq ht
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])

theorem Ud_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (Ud p q) (curvature R p q t-p*phi t) t := by
  simpa only [sub_zero] using mixedPDerivative_hasDerivAt (R:=R) hp hq ht
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])

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
    simpa [hq.ne'] using hh
  dsimp [Ud,mixedPDerivative,normD1,pairProduct]
  rw [sub_zero,he]
  field_simp [hq.ne']
  ring

theorem short_endpoint_trig :
    (557/1000:ℝ)<Real.cos (19/50:ℝ)-Real.sin (19/50:ℝ) ∧
    R*Real.cos (19/50:ℝ)<(1839/1000:ℝ) ∧
    (741/1000:ℝ)<2*Real.sin (19/50:ℝ) := by
  obtain ⟨hsl,hsh,hcl,hch⟩ := rational_taylor
    (show (19/50:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hc0 : 0≤Real.cos (19/50:ℝ) := by
    linarith [(transport_trig (show (19/50:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1]
  have hprod := mul_le_mul radius_tight.2.le hch hc0 (by norm_num : (0:ℝ)≤494697/250000)
  norm_num [sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,
    PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at hsl hsh hcl hch hprod
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
  have hh := ((hasDerivAt_id r).const_mul (199/500)).sub
    (((hasDerivAt_id r).const_mul (869/500)).div (halfRoot_hasDerivAt hr) hn.1.ne')
  have hpow (n : ℕ) : (halfRoot r)^(n+2)=
      (halfRoot r)^n*(1+r^2+(479/500)*r) := by
    rw [pow_add,hn.2.1]
  convert hh using 1
  · rfl
  · field_simp [hn.1.ne']
    ring_nf
    simp only [hpow 0,hpow 1,hpow 2,hpow 3,hpow 4,hpow 5,hpow 6,
      hpow 7,hpow 8,pow_zero,pow_one]
    ring

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
  obtain ⟨hsl,hsh,hcl,hch⟩ := rational_taylor
    (show (1/2:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hc0 : 0≤Real.cos (1/2:ℝ) := by
    linarith [(transport_trig (show (1/2:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1]
  have hprod := mul_le_mul radius_tight.2.le hch hc0 (by norm_num : (0:ℝ)≤494697/250000)
  norm_num [sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,
    PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at hsl hsh hcl hch hprod
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.PositiveSlope
