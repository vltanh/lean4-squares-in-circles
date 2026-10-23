module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2PositiveSlopes

/-!
# The ordinary slope reserves used by the negative-E concentrations

Uncompiled transcription of (22)--(23) of the E-angle companion.  A
single decreasing normalized lower function proves each positive slope
bound.  The negative slope uses the intrinsic ratio endpoint 2/3 and
the original angle endpoint 8/15.  All bounds apply on whole intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.OrdinarySlope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.PositiveSlope OrdinaryNegativeSlope

def endpoint : Bool → ℝ | false => frameCap | true => 8/15
def linearCoefficient : Bool → ℝ | false => 3/25 | true => 7/20
def numeratorBound : Bool → ℝ | false => 757/500 | true => 853/500
def sineCoefficient : Bool → ℝ | false => 161/125 | true => 127/125
def rootUpper : Bool → ℝ | false => 907/500 | true => 869/500
def rootLower : Bool → ℝ | false => 1813/1000 | true => 217/125
def allowance : Bool → ℝ | false => 18/25 | true => 16/25
def modelRoot (short : Bool) (r : ℝ) : ℝ := Real.sqrt (1+r^2+sineCoefficient short*r)
def model (short : Bool) (r : ℝ) : ℝ :=
  linearCoefficient short*r-numeratorBound short*r/modelRoot short r

theorem coefficient_signs (short : Bool) :
    0<linearCoefficient short ∧ 0<numeratorBound short ∧
      0<sineCoefficient short ∧ 0<rootUpper short ∧ 0<rootLower short := by
  cases short <;> norm_num [linearCoefficient,numeratorBound,sineCoefficient,rootUpper,rootLower]

theorem endpoint_domain (short : Bool) : endpoint short∈Icc 0 frameCap := by
  cases short <;> norm_num [endpoint,frameCap]

theorem endpoint_trig (short : Bool) :
    linearCoefficient short<Real.cos (endpoint short)-Real.sin (endpoint short) ∧
      R*Real.cos (endpoint short)<numeratorBound short ∧
      sineCoefficient short<2*Real.sin (endpoint short) := by
  have hcl := Arithmetic.cos10_le_cos (show 0≤endpoint short from (endpoint_domain short).1)
  have hch := HighOrderTaylor.cos_le_C12 (show 0≤endpoint short from (endpoint_domain short).1)
  have hsl := HighOrderTaylor.S11_le_sin (show 0≤endpoint short from (endpoint_domain short).1)
  have hsh := Arithmetic.sin_le_sin9 (show 0≤endpoint short from (endpoint_domain short).1)
  have hc0 : 0≤Real.cos (endpoint short) := by linarith [(transport_trig (endpoint_domain short)).1]
  have hprod := mul_le_mul PositiveTD.Certificate.radius_le_Rbar hch hc0
    (by norm_num [PositiveTD.Certificate.Rbar] : (0:ℝ)≤(PositiveTD.Certificate.Rbar:ℝ))
  cases short <;>
    norm_num [endpoint,linearCoefficient,numeratorBound,sineCoefficient,frameCap,
      HighOrderTaylor.S11,HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,
      Arithmetic.cos10,Arithmetic.cos8,PositiveTD.Certificate.Rbar]
      at hcl hch hsl hsh hprod ⊢ <;>
    exact ⟨by linarith,by linarith,by linarith⟩

theorem model_root_data (short : Bool) {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    0<modelRoot short r ∧ (modelRoot short r)^2=1+r^2+sineCoefficient short*r ∧
      modelRoot short r<rootUpper short := by
  have hc := coefficient_signs short
  have hr0 : 0≤r := by linarith [hr.1]
  have hs : 0<1+r^2+sineCoefficient short*r := by positivity
  have hn : 0<modelRoot short r := Real.sqrt_pos.mpr hs
  have he : (modelRoot short r)^2=1+r^2+sineCoefficient short*r := Real.sq_sqrt hs.le
  have hr2 : r^2≤1 := by simpa using pow_le_pow_left₀ hr0 hr.2 2
  refine ⟨hn,he,?_⟩
  cases short <;> norm_num [sineCoefficient,rootUpper] at he ⊢ <;> nlinarith [hr.2]

theorem model_root_derivative (short : Bool) {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    HasDerivAt (modelRoot short) ((2*r+sineCoefficient short)/(2*modelRoot short r)) r := by
  have hn := model_root_data short hr
  have hh := (((hasDerivAt_const r (1:ℝ)).add ((hasDerivAt_id r).pow 2)).add
    ((hasDerivAt_id r).const_mul (sineCoefficient short))).sqrt
    (by nlinarith [hn.1,hn.2.1] : 1+r^2+sineCoefficient short*r≠0)
  convert hh using 1
  · rfl
  · dsimp [modelRoot]
    ring

theorem model_derivative (short : Bool) {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    HasDerivAt (model short)
      (linearCoefficient short-numeratorBound short*(1+sineCoefficient short*r/2)/
        (modelRoot short r)^3) r := by
  have hn := model_root_data short hr
  have hh := ((hasDerivAt_id r).const_mul (linearCoefficient short)).sub
    (((hasDerivAt_id r).const_mul (numeratorBound short)).div
      (model_root_derivative short hr) hn.1.ne')
  convert hh using 1
  · rfl
  · field_simp [hn.1.ne']
    nlinarith [congrArg (fun u : ℝ => numeratorBound short*u) hn.2.1]

theorem model_antitone (short : Bool) : AntitoneOn (model short) (Icc (1/2:ℝ) 1) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun r hr => (model_derivative short hr).continuousAt.continuousWithinAt)
    (fun r hr => model_derivative short (Ioo_subset_Icc_self hr))
  intro r hr
  have hn := model_root_data short (Ioo_subset_Icc_self hr)
  have hc := coefficient_signs short
  have hp := pow_le_pow_left₀ hn.1.le hn.2.2.le 3
  have hscaled := mul_le_mul_of_nonneg_left hp hc.1.le
  have hright : linearCoefficient short*(modelRoot short r)^3≤
      numeratorBound short*(1+sineCoefficient short*r/2) := by
    cases short <;> norm_num [linearCoefficient,rootUpper,numeratorBound,sineCoefficient] at hscaled ⊢ <;>
      nlinarith [hr.1]
  have hh := (le_div_iff₀ (pow_pos hn.1 3)).2 hright
  linarith

theorem model_endpoint (short : Bool) : -allowance short<model short 1 := by
  have hn := model_root_data short (r:=1) (by norm_num)
  have hc := coefficient_signs short
  have hl : rootLower short<modelRoot short 1 := by
    cases short <;> norm_num [rootLower,sineCoefficient] at hn ⊢ <;> nlinarith
  have hcross : numeratorBound short<
      (linearCoefficient short+allowance short)*modelRoot short 1 := by
    cases short <;> norm_num [rootLower,numeratorBound,linearCoefficient,allowance] at hl ⊢ <;>
      linarith
  have hh := (div_lt_iff₀ hn.1).2 hcross
  dsimp [model]
  simp only [mul_one]
  linarith

theorem normalized_endpoint (short : Bool) {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    -allowance short<r*(Real.cos (endpoint short)-Real.sin (endpoint short))-
      R*r*Real.cos (endpoint short)/pairNorm r 1 (endpoint short) := by
  have hr0 : 0<r := by linarith [hr.1]
  have hn := model_root_data short hr
  have hN := pairNorm_pos hr0 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg (endpoint_domain short).1]; exact (endpoint_domain short).2)
  have hN2 := pairNorm_sq hr0 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg (endpoint_domain short).1]; exact (endpoint_domain short).2)
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one] at hN2
  obtain ⟨hphi,hcos,hsin⟩ := endpoint_trig short
  have hroot : modelRoot short r≤pairNorm r 1 (endpoint short) := by
    have hh := mul_le_mul_of_nonneg_right hsin.le hr0.le
    nlinarith [hn.2.1]
  have hnum : R*r*Real.cos (endpoint short)≤numeratorBound short*r := by
    nlinarith only [mul_le_mul_of_nonneg_right hcos.le hr0.le]
  have hquot := div_le_div₀ (by have hc := (coefficient_signs short).2.1; positivity)
    hnum hn.1 hroot
  have hlin := mul_le_mul_of_nonneg_right hphi.le hr0.le
  have hlower : model short r≤r*(Real.cos (endpoint short)-Real.sin (endpoint short))-
      R*r*Real.cos (endpoint short)/pairNorm r 1 (endpoint short) := by
    dsimp [model]
    nlinarith only [hquot,hlin]
  exact (model_endpoint short).trans_le
    ((model_antitone short hr (by norm_num) hr.2).trans hlower)

theorem positive_derivative (short : Bool) {p q x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hx : x∈Icc 0 (endpoint short)) :
    -allowance short*q<Ud p q x := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (1/2:ℝ) 1 :=
    ⟨(le_div_iff₀ hq).2 (by linarith),(div_le_one hq).2 hpq⟩
  have he : -allowance short*q<Ud p q (endpoint short) := by
    rw [Ud_normalized hq]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (normalized_endpoint short hr) hq
  exact he.trans_le (Ud_antitone hp hpq hqp ⟨hx.1,hx.2.trans (endpoint_domain short).2⟩
    (endpoint_domain short) hx.2)

theorem positive_derivative_whole {p q x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hx : x∈Icc 0 frameCap) :
    -(18/25)*q<Ud p q x := positive_derivative false hp hpq hqp hx

theorem positive_derivative_short {p q x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hx : x∈Icc 0 (8/15:ℝ)) :
    -(16/25)*q<Ud p q x := positive_derivative true hp hpq hqp hx

theorem negative_short_endpoint :
    (39/50:ℝ)<-Real.sin (8/15:ℝ)+
      R*(2/3)*Real.cos (8/15:ℝ)/VaryingBFunctions.root (2/3) (Real.sin (8/15:ℝ)) := by
  have hx : (8/15:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := VaryingBFunctions.root_pos (2/3) (VaryingBFunctions.sin_mem hx)
  have hN2 := VaryingBFunctions.root_sq (2/3) (VaryingBFunctions.sin_mem hx)
  have hsl := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤8/15 by norm_num)
  have hsh := Arithmetic.sin_le_sin9 (show (0:ℝ)≤8/15 by norm_num)
  have hcl := Arithmetic.cos10_le_cos (show (0:ℝ)≤8/15 by norm_num)
  have ht : (5084/10000:ℝ)<Real.sin (8/15:ℝ) ∧
      Real.sin (8/15:ℝ)<5085/10000 ∧ (8611/10000:ℝ)<Real.cos (8/15:ℝ) := by
    norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      Arithmetic.cos10,Arithmetic.cos8] at hsl hsh hcl
    exact ⟨by linarith,by linarith,by linarith⟩
  have hNu : VaryingBFunctions.root (2/3) (Real.sin (8/15:ℝ))<(219/250:ℝ) := by
    nlinarith [ht.1]
  have hR : (19787/10000:ℝ)<R := by linarith [radius_bounds.1]
  have hprod := mul_lt_mul hR ht.2.2 (by norm_num : (0:ℝ)≤8611/10000)
    (by linarith [radius_bounds.1] : 0<R)
  have hupper := mul_lt_mul_of_pos_left hNu
    (show 0<(39/50:ℝ)+Real.sin (8/15:ℝ) by linarith [ht.1])
  have hupper2 := mul_lt_mul_of_pos_right ht.2.1 (by norm_num : (0:ℝ)<219/250)
  have hcross : ((39/50:ℝ)+Real.sin (8/15:ℝ))*
      VaryingBFunctions.root (2/3) (Real.sin (8/15:ℝ))<R*(2/3)*Real.cos (8/15:ℝ) := by
    nlinarith
  have hdiv := (lt_div_iff₀ hN).2 hcross
  linarith

theorem negative_derivative_short {p q x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : (2/3)*q≤p) (hx : x∈Icc 0 (8/15:ℝ)) :
    (39/50)*q<Vd R p q x := by
  have hq := hp.trans_le hpq
  have harg : (8/15:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfrac := normalized_fraction_mono (by norm_num : (0:ℝ)≤2/3)
    ((le_div_iff₀ hq).2 hqp) ((div_le_one hq).2 hpq) (VaryingBFunctions.sin_mem harg)
  have hm := mul_le_mul_of_nonneg_left hfrac
    (show 0≤R*Real.cos (8/15:ℝ) by
      exact mul_nonneg (Real.sqrt_nonneg _) (by linarith [(transport_trig harg).1]))
  have hs : (39/50:ℝ)<-Real.sin (8/15:ℝ)+
      R*(p/q)*Real.cos (8/15:ℝ)/VaryingBFunctions.root (p/q) (Real.sin (8/15:ℝ)) := by
    have hbase := negative_short_endpoint
    nlinarith only [hm,hbase]
  have he : (39/50)*q<Vd R p q (8/15:ℝ) := by
    rw [Vd_normalized hq]
    nlinarith only [mul_lt_mul_of_pos_left hs hq]
  exact he.trans_le (Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hp hpq
    (by linarith) ⟨hx.1,by norm_num [frameCap]; linarith [hx.2]⟩ harg hx.2)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.OrdinarySlope
