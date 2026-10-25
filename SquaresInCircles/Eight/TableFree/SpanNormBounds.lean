module

public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope
public import SquaresInCircles.Eight.TableFree.OrdinaryPositiveEnvelope

/-!
# Whole-interval norm bounds for the original middle stress

Uncompiled source. The weight varies continuously between .65 and .92.
Angle concavity reduces the derivative bounds to one endpoint; monotonicity
in the weight then gives uniform estimates. All endpoint reserves are
positive-square and Taylor inequalities, not sampled angle rows.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SpanNormBounds
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope

def R : ℝ := Real.sqrt qCap
def c : ℝ := diagonalCoordinate qCap
def N (lambda t : ℝ) : ℝ := pairNorm lambda 1 t
def U (lambda t : ℝ) : ℝ := OrdinaryAngleConcavity.U R lambda 1 t
def V (lambda t : ℝ) : ℝ := OrdinaryAngleConcavity.V R lambda 1 t
def Ud (lambda t : ℝ) : ℝ :=
  lambda*(Real.cos t-Real.sin t)-R*lambda*Real.cos t/N lambda t
def Vd (lambda t : ℝ) : ℝ := OrdinaryNegativeSlope.Vd R lambda 1 t

theorem radius_bounds : (1978787/1000000 : ℝ)<R ∧ R<494697/250000 := by
  have hh := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hn := Real.sqrt_nonneg qCap
  dsimp [R,qCap] at *
  constructor <;> nlinarith

theorem diagonal_bounds : (449607/500000 : ℝ)<c ∧ c<179843/200000 := by
  have hh := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap/2)
  dsimp [c,diagonalCoordinate,qCap] at *
  constructor <;> nlinarith

theorem N_pos {lambda t : ℝ} (hl : 0<lambda) (ht : |t|≤frameCap) : 0<N lambda t :=
  pairNorm_pos hl (by norm_num) ht

theorem N_sq {lambda t : ℝ} (hl : 0<lambda) (ht : |t|≤frameCap) :
    (N lambda t)^2=1+lambda^2+2*lambda*Real.sin t := by
  have hh := pairNorm_sq hl (show (0:ℝ)<1 by norm_num) ht
  simpa [N,pairEnergy,pairProduct,add_comm,add_left_comm,add_assoc] using hh

theorem fixed_norm_bounds :
    (596343/500000 : ℝ)<N (13/20) 0 ∧ N (13/20) 0<1192687/1000000 ∧
      N (13/20) (-frameCap)<7649/10000 ∧
      (5599/5000 : ℝ)<N (13/20) (-(13/100)) ∧
      N (13/20) (-(11/50))<1067147/1000000 ∧
      (1813/1000 : ℝ)<N 1 frameCap := by
  have h0 := N_sq (show (0:ℝ)<13/20 by norm_num) (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hz0 := N_pos (show (0:ℝ)<13/20 by norm_num) (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hh := N_sq (show (0:ℝ)<13/20 by norm_num) (show |-frameCap|≤frameCap by norm_num [frameCap])
  have hh0 := N_pos (show (0:ℝ)<13/20 by norm_num) (show |-frameCap|≤frameCap by norm_num [frameCap])
  have h13 := N_sq (show (0:ℝ)<13/20 by norm_num) (show |-(13/100 : ℝ)|≤frameCap by norm_num [frameCap])
  have h130 := N_pos (show (0:ℝ)<13/20 by norm_num) (show |-(13/100 : ℝ)|≤frameCap by norm_num [frameCap])
  have h22 := N_sq (show (0:ℝ)<13/20 by norm_num) (show |-(11/50 : ℝ)|≤frameCap by norm_num [frameCap])
  have h220 := N_pos (show (0:ℝ)<13/20 by norm_num) (show |-(11/50 : ℝ)|≤frameCap by norm_num [frameCap])
  have h1 := N_sq (show (0:ℝ)<1 by norm_num) (show |frameCap|≤frameCap by norm_num [frameCap])
  have h10 := N_pos (show (0:ℝ)<1 by norm_num) (show |frameCap|≤frameCap by norm_num [frameCap])
  have hsH := cap_sin_lower
  have hs13 := sin_upper_five (show (0:ℝ)≤13/100 by norm_num)
  have hs22 := sin_lower_seven (show (0:ℝ)≤11/50 by norm_num)
  simp only [Real.sin_zero,Real.sin_neg] at h0 hh h13 h22
  norm_num at hs13 hs22 h0
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

theorem Ud_eq_mixed (lambda t : ℝ) : Ud lambda t=mixedPDerivative R lambda 1 t 0 := by
  simp [Ud,N,mixedPDerivative,normD1,pairProduct]
  ring

theorem U_deriv {lambda t : ℝ} (hl : 0<lambda) (ht : t∈Icc 0 frameCap) :
    HasDerivAt (U lambda) (Ud lambda t) t := by
  rw [Ud_eq_mixed]
  have h := mixedP_hasDerivAt (R := R) hl (show (0:ℝ)<1 by norm_num)
    ht (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  convert h using 1
  funext x
  simp [SpanNormBounds.U]

theorem Ud_deriv {lambda t : ℝ} (hl : 0<lambda) (ht : t∈Icc 0 frameCap) :
    HasDerivAt (Ud lambda) (curvature R lambda 1 t-lambda*PositiveAngularEnvelope.phi t) t := by
  have h := mixedPDerivative_hasDerivAt (R := R) hl
    (show (0:ℝ)<1 by norm_num) ht (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  rw [sub_zero] at h
  convert h using 1
  funext x
  exact Ud_eq_mixed lambda x

theorem Ud_antitone {lambda : ℝ} (hl : lambda∈Icc (13/20 : ℝ) 1) :
    AntitoneOn (Ud lambda) (Icc 0 frameCap) := by
  have hl0 : 0<lambda := by linarith [hl.1]
  apply antiOn_of_hasDeriv_nonpos
  · exact fun t ht => (Ud_deriv hl0 ht).continuousAt.continuousWithinAt
  · exact fun t ht => Ud_deriv hl0 (Ioo_subset_Icc_self ht)
  · intro t ht
    have hh := mixedP_second_lt (R := R) (Real.sqrt_nonneg _)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hl0 hl.2
      (by linarith [hl.1]) (Ioo_subset_Icc_self ht)
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    simp only [sub_zero] at hh
    linarith

theorem U_endpoint_weight_deriv {lambda : ℝ} (hl : lambda∈Icc (13/20 : ℝ) 1) :
    HasDerivAt (fun a => Ud a frameCap)
      (Real.cos frameCap-Real.sin frameCap-
        R*Real.cos frameCap*(1+lambda*Real.sin frameCap)/(N lambda frameCap)^3) lambda := by
  have hl0 : 0<lambda := by linarith [hl.1]
  have hh : |frameCap|≤frameCap := by norm_num [frameCap]
  have hN0 := N_pos hl0 hh
  have hNsq := N_sq hl0 hh
  have hrad : 0<1+lambda^2+2*lambda*Real.sin frameCap := by rw [← hNsq]; positivity
  have hraw : HasDerivAt (fun a : ℝ => 1+a^2+2*a*Real.sin frameCap)
      (2*lambda+2*Real.sin frameCap) lambda := by
    have h := ((hasDerivAt_pow 2 lambda).const_add 1).add
      ((hasDerivAt_id lambda).mul_const (2*Real.sin frameCap))
    convert h using 1
    · funext a
      simp only [id,Pi.add_apply]
      ring
    · simp
  have hfun : (fun a => N a frameCap)=fun a : ℝ => Real.sqrt (1+a^2+2*a*Real.sin frameCap) := by
    funext a
    simp only [N,pairNorm]
    congr 1
    ring
  have hNdef : N lambda frameCap=Real.sqrt (1+lambda^2+2*lambda*Real.sin frameCap) :=
    congrFun hfun lambda
  have hN : HasDerivAt (fun a => N a frameCap)
      ((lambda+Real.sin frameCap)/N lambda frameCap) lambda := by
    rw [hfun]
    convert hraw.sqrt hrad.ne' using 1
    rw [← hNdef]
    field_simp
  have hder := ((hasDerivAt_id lambda).mul_const (Real.cos frameCap-Real.sin frameCap)).sub
    (((hasDerivAt_id lambda).mul_const (R*Real.cos frameCap)).div hN hN0.ne')
  convert hder using 1
  · funext a
    simp only [Ud,Pi.sub_apply,Pi.div_apply,id]
    ring
  · simp only [id]
    field_simp
    linear_combination (R*Real.cos frameCap)*hNsq

theorem U_endpoint_weight_antitone :
    AntitoneOn (fun a => Ud a frameCap) (Icc (13/20 : ℝ) 1) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun a ha => (U_endpoint_weight_deriv ha).continuousAt.continuousWithinAt
  · exact fun a ha => U_endpoint_weight_deriv (Ioo_subset_Icc_self ha)
  · intro a ha
    have ha0 : 0<a := by linarith [ha.1]
    have hNa := N_pos ha0 (show |frameCap|≤frameCap by norm_num [frameCap])
    have hNsq := N_sq ha0 (show |frameCap|≤frameCap by norm_num [frameCap])
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
    have hslo := cap_sin_lower
    have hchi := cos_upper_four (show 0≤frameCap by norm_num [frameCap])
    have ha2 := pow_le_pow_left₀ ha0.le ha.2.le 2
    have hprod := mul_le_mul_of_nonneg_left ha.2.le hs0
    have hNtwo : (N a frameCap)^2<329/100 := by nlinarith
    have hNupper : N a frameCap<363/200 := by nlinarith
    have hNcube : (N a frameCap)^3<6 := by
      have hm := mul_lt_mul_of_pos_right hNtwo hNa
      have hn := mul_lt_mul_of_pos_left hNupper (show (0:ℝ)<329/100 by norm_num)
      nlinarith
    have hdiff : Real.cos frameCap-Real.sin frameCap<121/1000 := by
      norm_num [frameCap] at hchi
      linarith
    have hR0 : 0<R := by linarith [radius_bounds.1]
    have hc0 : 0<Real.cos frameCap := by linarith
    have hnum : (151/100 : ℝ)<R*Real.cos frameCap*(1+a*Real.sin frameCap) := by
      have h1 := mul_lt_mul_of_pos_right radius_bounds.1 hc0
      have h2 := mul_lt_mul_of_pos_left hc (show (0:ℝ)<1978787/1000000 by norm_num)
      have h3 := mul_nonneg (mul_nonneg hR0.le hc0.le) (mul_nonneg ha0.le hs0)
      nlinarith
    have hratio : (1/4 : ℝ)<R*Real.cos frameCap*(1+a*Real.sin frameCap)/(N a frameCap)^3 := by
      apply (lt_div_iff₀ (pow_pos hNa 3)).2
      linarith
    linarith

theorem U_unit_endpoint : -(18/25 : ℝ)<Ud 1 frameCap := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hchi := Arithmetic.cos_le_cos8 (show 0≤frameCap by norm_num [frameCap])
  have hcupper : Real.cos frameCap<153/200 := by
    norm_num [Arithmetic.cos8,frameCap] at hchi ⊢; linarith
  have hN := fixed_norm_bounds.2.2.2.2.2
  have hN0 := N_pos (show (0:ℝ)<1 by norm_num) (show |frameCap|≤frameCap by norm_num [frameCap])
  have hR0 : 0≤R := Real.sqrt_nonneg _
  have hnum := mul_le_mul radius_bounds.2.le hcupper.le (by linarith : 0≤Real.cos frameCap)
    (show (0:ℝ)≤494697/250000 by norm_num)
  have hquot : R*Real.cos frameCap/N 1 frameCap<21/25 := by
    apply (div_lt_iff₀ hN0).2
    nlinarith
  have hU : Ud 1 frameCap=(Real.cos frameCap-Real.sin frameCap)-R*Real.cos frameCap/N 1 frameCap := by
    simp only [Ud]
    ring
  rw [hU]
  linarith

theorem U_derivative_lower {lambda t : ℝ}
    (hl : lambda∈Icc (13/20 : ℝ) (23/25)) (ht : t∈Icc 0 frameCap) :
    -(18/25 : ℝ)<Ud lambda t := by
  have hl1 : lambda∈Icc (13/20 : ℝ) 1 := ⟨hl.1,by linarith [hl.2]⟩
  have hparam := U_endpoint_weight_antitone hl1 (by constructor <;> norm_num) hl1.2
  have hangle := Ud_antitone hl1 ht (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht.2
  exact U_unit_endpoint.trans_le (hparam.trans hangle)

theorem V_base_endpoint : (16/25 : ℝ)<Vd (13/20) frameCap := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hNhi := fixed_norm_bounds.2.2.1
  have hN0 := N_pos (show (0:ℝ)<13/20 by norm_num) (show |-frameCap|≤frameCap by norm_num [frameCap])
  have hR0 : 0<R := by linarith [radius_bounds.1]
  have hc0 : 0<Real.cos frameCap := by linarith
  have hnum1 := mul_lt_mul_of_pos_right radius_bounds.1 hc0
  have hnum2 := mul_lt_mul_of_pos_left hc (show (0:ℝ)<1978787/1000000 by norm_num)
  have hupper := mul_lt_mul_of_pos_left hNhi (show 0<(16/25 : ℝ)+Real.sin frameCap by linarith)
  have hupper2 := mul_lt_mul_of_pos_right hs (show (0:ℝ)<7649/10000 by norm_num)
  have hquot : (16/25 : ℝ)+Real.sin frameCap<R*(13/20)*Real.cos frameCap/N (13/20) (-frameCap) := by
    apply (lt_div_iff₀ hN0).2
    nlinarith
  have hV : SpanNormBounds.Vd (13/20) frameCap=
      -Real.sin frameCap+R*(13/20)*Real.cos frameCap/N (13/20) (-frameCap) := by
    simp only [SpanNormBounds.Vd,OrdinaryNegativeSlope.Vd,mixedNDerivative,normD1,pairProduct,N,
      zero_sub,Real.cos_neg]
    ring
  rw [hV]
  linarith

theorem V_derivative_lower {lambda t : ℝ}
    (hl : lambda∈Icc (13/20 : ℝ) (23/25)) (ht : t∈Icc 0 frameCap) :
    (16/25 : ℝ)<Vd lambda t := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hfrac := normalized_fraction_mono (show (0:ℝ)≤13/20 by norm_num) hl.1
    (by linarith [hl.2] : lambda≤1) (VaryingBFunctions.sin_mem hh)
  have hc0 : 0≤Real.cos frameCap := by linarith [(transport_trig hh).1]
  have hmul := mul_le_mul_of_nonneg_left hfrac (mul_nonneg (Real.sqrt_nonneg qCap) hc0)
  have hparam : SpanNormBounds.Vd (13/20) frameCap≤SpanNormBounds.Vd lambda frameCap := by
    simp only [SpanNormBounds.Vd]
    rw [Vd_normalized (show (0:ℝ)<1 by norm_num),Vd_normalized (show (0:ℝ)<1 by norm_num)]
    simp only [div_one,one_mul]
    have e1 : R*(13/20)*Real.cos frameCap/VaryingBFunctions.root (13/20) (Real.sin frameCap)=
        Real.sqrt qCap*Real.cos frameCap*
          (13/20/VaryingBFunctions.root (13/20) (Real.sin frameCap)) := by
      simp only [R]; ring
    have e2 : R*lambda*Real.cos frameCap/VaryingBFunctions.root lambda (Real.sin frameCap)=
        Real.sqrt qCap*Real.cos frameCap*
          (lambda/VaryingBFunctions.root lambda (Real.sin frameCap)) := by
      simp only [R]; ring
    rw [e1,e2]
    linarith
  have hanti := Vd_antitone (R := R) (q := 1) (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (show 0<lambda by linarith [hl.1]) (by linarith [hl.2]) (by linarith [hl.1])
  exact V_base_endpoint.trans_le (hparam.trans (hanti ht hh ht.2))

theorem V_base_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    Vd (13/20) t<1079/1000 := by
  have hN0 := fixed_norm_bounds.1
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone (R := R) (q := 1) (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (show (0:ℝ)<13/20 by norm_num) (by norm_num) (by norm_num)
  have hstart : SpanNormBounds.Vd (13/20) 0<1079/1000 := by
    have hNpos : 0<N (13/20) 0 := by linarith
    have hratio : R*(13/20)/N (13/20) 0<1079/1000 := by
      apply (div_lt_iff₀ hNpos).2
      nlinarith [radius_bounds.2]
    have hV : SpanNormBounds.Vd (13/20) 0=R*(13/20)/N (13/20) 0 := by
      simp only [SpanNormBounds.Vd,OrdinaryNegativeSlope.Vd,mixedNDerivative,normD1,pairProduct,N,
        sub_zero,Real.cos_zero,Real.sin_zero]
      ring
    rw [hV]
    exact hratio
  exact (hanti hz ht ht.1).trans_lt hstart

theorem V_at_013_upper : Vd (13/20) (13/100)<101/100 := by
  have hN := fixed_norm_bounds.2.2.2.1
  have hN0 : 0<N (13/20) (-(13/100)) := by linarith
  have hs := sin_lower_seven (show (0:ℝ)≤13/100 by norm_num)
  have hc := cos_upper_four (show (0:ℝ)≤13/100 by norm_num)
  have hc0 : 0≤Real.cos (13/100 : ℝ) := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := (13/100 : ℝ))
    norm_num at hh
    linarith
  have hnum := mul_le_mul radius_bounds.2.le hc hc0 (show (0:ℝ)≤494697/250000 by norm_num)
  have hprod := mul_lt_mul_of_pos_left hN (show 0<(101/100 : ℝ)+Real.sin (13/100 : ℝ) by linarith [hs])
  have hsinprod := mul_le_mul_of_nonneg_right hs (show (0:ℝ)≤5599/5000 by norm_num)
  have hquot : R*(13/20)*Real.cos (13/100 : ℝ)/N (13/20) (-(13/100))<
      101/100+Real.sin (13/100 : ℝ) := by
    apply (div_lt_iff₀ hN0).2
    norm_num at hnum hsinprod
    nlinarith
  have hV : SpanNormBounds.Vd (13/20) (13/100)=
      -Real.sin (13/100)+R*(13/20)*Real.cos (13/100 : ℝ)/N (13/20) (-(13/100)) := by
    simp only [SpanNormBounds.Vd,OrdinaryNegativeSlope.Vd,mixedNDerivative,normD1,pairProduct,N,
      zero_sub,Real.cos_neg]
    ring
  rw [hV]
  linarith

theorem U_growth {lambda x y : ℝ}
    (hl : lambda∈Icc (13/20 : ℝ) (23/25))
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    -(18/25)*(y-x)≤U lambda y-U lambda x := by
  have hl0 : 0<lambda := by linarith [hl.1]
  exact derivative_reserve (fun t ht => (U_deriv hl0 ht).continuousAt.continuousWithinAt)
    (fun t ht => U_deriv hl0 (Ioo_subset_Icc_self ht))
    (fun t ht => (U_derivative_lower hl (Ioo_subset_Icc_self ht)).le) hx hy hxy

theorem V_growth {lambda x y : ℝ}
    (hl : lambda∈Icc (13/20 : ℝ) (23/25))
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    (16/25)*(y-x)≤V lambda y-V lambda x := by
  have hl0 : 0<lambda := by linarith [hl.1]
  exact derivative_reserve
    (fun t ht => (V_hasDerivAt (R := R) hl0 (show (0:ℝ)<1 by norm_num) ht).continuousAt.continuousWithinAt)
    (fun t ht => V_hasDerivAt (R := R) hl0 (show (0:ℝ)<1 by norm_num) (Ioo_subset_Icc_self ht))
    (fun t ht => (V_derivative_lower hl (Ioo_subset_Icc_self ht)).le) hx hy hxy

end SquaresInCircles.Eight.TableFree.SpanNormBounds
