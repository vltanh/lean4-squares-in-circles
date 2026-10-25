module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3PositivePure
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD0SourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAStress
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3LowScalar
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3Polynomial
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2High
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSecant
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Polynomial
public import SquaresInCircles.Eight.Owners.GA.Secant.DSingleAngle
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveHighTransfer
public import SquaresInCircles.Eight.Owners.Negative.CoreEEntry

/-!
# Eight squares: negative core DE3, nonnegative high A, BT2 and TD0 of either sign

The high negative-DE / BT3 scalar certificate (`NegativeDEPositiveBT.Scalar.scalar_positive`) is
applied at a zero BT tilt, as an algebraic statement; no BT3 witness is assumed or selected. The
BT2 angle stays in B and TD0 stays in the secant D block; the radius `q` and the EH0 witness are
those of the cycle (`original_high_false`).
-/

section
/-!
## The high-BT3 T endpoint lies in the shape domain

The polynomial majorant is evaluated in `x = θ - 1/6`, and its derivative controls the whole high
interval (`coefficient_upper`). The late affine correlation follows from the concavity of the
polynomial difference and its values at the two endpoints (`late_coefficient_upper`). This gives
the hypotheses of the shared third-derivative theorem `NegativeDEHighShape` with its BT3 flag
(`shape_domain`), with no sampled coefficient bound.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighShape
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open WholeIntervalPolynomial

lemma polynomial_hasDerivAt (p : ℚ[X]) (x : ℝ) :
    HasDerivAt (fun x : ℝ => aeval x p) (aeval x p.derivative) x := by
  convert (p.map (algebraMap ℚ ℝ)).hasDerivAt x using 1 <;>
    simp [Polynomial.aeval_def,Polynomial.derivative_map]

lemma native_domain {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    θ-(Certificate.L:ℝ)∈Icc (0:ℝ) (8/15) := by
  norm_num [Certificate.L]
  exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

lemma native_total (θ : ℝ) : θ-(Certificate.L:ℝ)+(Certificate.L:ℝ)=θ := by ring

lemma coefficient_majorant {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.c .high θ θ≤aeval (θ-(Certificate.L:ℝ)) Certificate.highC := by
  have ht := PositiveTD.Certificate.taylor_bounds (Explicit.frame_domain .high hθ)
  have he := Explicit.high_eta hθ
  have hm := (Explicit.high_bounds hθ).m_lower
  have hs := mul_le_mul_of_nonneg_left ht.2.2.1
    (show 0≤Explicit.eta .high θ by linarith [he.1])
  have hh := mul_le_mul_of_nonneg_left (add_le_add ht.2.2.2.2.2 hs)
    (show 0≤Explicit.m .high θ by linarith)
  simpa only [Certificate.highC,map_mul,map_add,aeval_comp,
    Certificate.theta_eval,Certificate.highM_eval,Certificate.highEta_eval,native_total,
    Explicit.c] using hh

lemma majorant_derivative_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (8/15)) :
    aeval x Certificate.highC.derivative<0 := by
  have hc := Certificate.high_auxiliary_certificate.2.2.1
  have hspan : ((Certificate.span:ℚ):ℝ)=8/15 := by
    norm_num [Certificate.span,Certificate.h,Certificate.L]
  have hx' : x∈Icc ((0:ℚ):ℝ) ((Certificate.span:ℚ):ℝ) := by
    rw [hspan,Rat.cast_zero]; exact hx
  have hh := positive_on_interval
    (by norm_num [Certificate.span,Certificate.h,Certificate.L] : (0:ℚ)<Certificate.span)
    hc.1 hc.2 hx'
  rw [map_neg] at hh
  have he : ((22/125:ℚ):ℝ)=22/125 := by norm_num
  linarith

lemma majorant_antitone :
    AntitoneOn (fun x : ℝ => aeval x Certificate.highC) (Icc (0:ℝ) (8/15)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (polynomial_hasDerivAt Certificate.highC x).continuousAt.continuousWithinAt)
    (fun x _ => polynomial_hasDerivAt Certificate.highC x)
  intro x hx
  exact (majorant_derivative_negative (Ioo_subset_Icc_self hx)).le

theorem coefficient_upper {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.c .high θ θ<(1057/1000:ℝ) := by
  have hx := native_domain hθ
  have hm := majorant_antitone (by norm_num : (0:ℝ)∈Icc 0 (8/15)) hx hx.1
  have h0 : aeval (0:ℝ) Certificate.highC<(1057/1000:ℝ) := by
    have he := NegativeDEPositiveTD.Certificate.eval_rat Certificate.highC 0
    rw [Rat.cast_zero] at he
    rw [he]
    have hh : ((Certificate.highC.eval 0:ℚ):ℝ)<((1057/1000:ℚ):ℝ) :=
      Rat.cast_lt.mpr Certificate.high_auxiliary_certificate.2.2.2
    rw [show ((1057/1000:ℚ):ℝ)=1057/1000 by norm_num] at hh
    exact hh
  exact (coefficient_majorant hθ).trans_lt (hm.trans_lt h0)

lemma late_difference_concave :
    ConcaveOn ℝ (Icc (Certificate.lateLeft:ℝ) (Certificate.span:ℝ))
      (fun x : ℝ => aeval x Certificate.lateDifference) := by
  apply concave_of_deriv2
    (fun x _ => polynomial_hasDerivAt Certificate.lateDifference x)
    (fun x _ => polynomial_hasDerivAt Certificate.lateDifference.derivative x)
  intro x hx
  have hc := Certificate.late_coefficient_certificate.1
  have hh := positive_on_interval
    (by norm_num [Certificate.lateLeft,Certificate.span,Certificate.h,Certificate.L] :
      Certificate.lateLeft<Certificate.span) hc.1 hc.2 hx
  simp only [map_neg] at hh
  norm_num at hh
  linarith

theorem late_coefficient_upper {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hlate : (11/20:ℝ)≤θ) : Explicit.c .high θ θ≤2153/2000-(61/200)*θ := by
  have hx : θ-(Certificate.L:ℝ)∈Icc (Certificate.lateLeft:ℝ) (Certificate.span:ℝ) := by
    norm_num [Certificate.lateLeft,Certificate.span,Certificate.h,Certificate.L]
    exact ⟨by linarith,by linarith [hθ.2]⟩
  have hcert := Certificate.late_coefficient_certificate
  have h0 : 0<aeval (Certificate.lateLeft:ℝ) Certificate.lateDifference := by
    rw [NegativeDEPositiveTD.Certificate.eval_rat]
    have hh : ((9/50000:ℚ):ℝ)<((Certificate.lateDifference.eval Certificate.lateLeft:ℚ):ℝ) :=
      Rat.cast_lt.mpr hcert.2.1
    rw [show ((9/50000:ℚ):ℝ)=9/50000 by norm_num] at hh
    exact (by norm_num : (0:ℝ)<9/50000).trans hh
  have h1 : 0<aeval (Certificate.span:ℝ) Certificate.lateDifference := by
    rw [NegativeDEPositiveTD.Certificate.eval_rat]
    have hh : ((3/62500:ℚ):ℝ)<((Certificate.lateDifference.eval Certificate.span:ℚ):ℝ) :=
      Rat.cast_lt.mpr hcert.2.2
    rw [show ((3/62500:ℚ):ℝ)=3/62500 by norm_num] at hh
    exact (by norm_num : (0:ℝ)<3/62500).trans hh
  have hd := concave_gt_of_endpoints late_difference_concave hx h0 h1
  have hc := coefficient_majorant hθ
  simp only [Certificate.lateDifference,Certificate.lateLine,map_sub,map_mul,
    aeval_C,Certificate.theta_eval,native_total,eq_ratCast] at hd
  push_cast at hd hc
  linarith

lemma late_larger {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hlate : (11/20:ℝ)≤θ) (i : Fin 3) : Explicit.q .high θ i≤1 := by
  have hh := NegativeDEPositiveTD.Explicit.high_late_q_le_one hθ
    (show (0:ℝ)∈Icc 0 θ from ⟨le_rfl,by linarith [hθ.1]⟩) hlate i
  simpa [Explicit.q,Explicit.l,Explicit.m,NegativeDEPositiveTD.Explicit.q,
    NegativeDEPositiveTD.Explicit.m] using hh

/-- The shared shape theorem uses the BT3 correlation, not the TD2 one. -/
theorem shape_domain {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    NegativeDEHighShape.Domain true (Explicit.c .high θ θ)
      (Explicit.p .high θ i) (Explicit.q .high θ i) θ := by
  have hp := Explicit.high_pairs hθ i
  have hq := Explicit.high_q_bounds hθ i
  have hm := (Explicit.high_bounds hθ).m_lower
  have hc := (Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1
  refine ⟨Explicit.frame_domain .high hθ,?_,hp.1,hp.2.1,hp.2.2.le,hq.1,?_,?_⟩
  · exact ⟨by linarith,by simpa [NegativeDEHighShape.Early.C] using (coefficient_upper hθ).le⟩
  · intro hlate
    have hh := late_coefficient_upper hθ hlate
    dsimp [NegativeDEHighShape.Late.rate,frameCap]
    linarith
  · exact fun hlate => late_larger hθ hlate i

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighShape
end
end
end

section
/-!
## The high-T support inputs of the DE3 / BT3 endpoint transfer

The total-dependent tilt stays in its circle support. The upper bound of the cubic square root
(`sqrt_cubic_upper`) is proved by a positive-square identity, not read off the cubic norm masses.
The lower polynomial of the baseline (`base_lower`) and the four norm bounds (`norm_bounds`) then
hold at the same total angle.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighTransfer
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds)

abbrev native (θ : ℝ) : ℝ := θ-(Certificate.L:ℝ)
abbrev k (θ : ℝ) := Explicit.k .high θ
abbrev l (θ : ℝ) := Explicit.l .high θ
abbrev m (θ : ℝ) := Explicit.m .high θ
abbrev c (θ : ℝ) := Explicit.c .high θ θ
abbrev eta (θ : ℝ) := Explicit.eta .high θ

def cubic (w : ℝ) : ℝ := 1+w/2-w^2/8+w^3/16

lemma cubic_nonnegative {w : ℝ} (hw : 0≤w) : 0≤cubic w := by
  have he : cubic w=1+w*((w-1)^2+7)/16 := by dsimp [cubic]; ring
  rw [he]
  positivity

theorem sqrt_cubic_upper {w : ℝ} (hw : 0≤w) : Real.sqrt (1+w)≤cubic w := by
  have hs := Real.sq_sqrt (show 0≤1+w by linarith)
  have hp := cubic_nonnegative hw
  have hid : (cubic w)^2-(1+w)=w^4*((w-2)^2+16)/256 := by
    dsimp [cubic]
    ring
  have hnon : 0≤w^4*((w-2)^2+16)/256 := by positivity
  nlinarith [Real.sqrt_nonneg (1+w)]

private lemma r72_td_nt (θ : ℝ) : native θ+(Certificate.L:ℝ)=θ := by simp [native]

private lemma r72_td_K (θ : ℝ) : aeval (native θ) Certificate.highK=k θ := by
  rw [Certificate.highK_eval,r72_td_nt]

private lemma r72_td_L (θ : ℝ) : aeval (native θ) Certificate.highL=l θ := by
  rw [Certificate.highL_eval,r72_td_nt]

private lemma r72_td_M (θ : ℝ) : aeval (native θ) Certificate.highM=m θ := by
  rw [Certificate.highM_eval,r72_td_nt]

private lemma r72_td_eta (θ : ℝ) : aeval (native θ) Certificate.highEta=eta θ := by
  rw [Certificate.highEta_eval,r72_td_nt]

private lemma r72_td_comp (θ : ℝ) (P : ℚ[X]) :
    aeval (native θ) (P.comp Certificate.theta)=aeval θ P := by
  rw [aeval_comp,Certificate.theta_eval,r72_td_nt]

private lemma r72_td_dom {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    native θ∈Icc ((0:ℚ):ℝ) ((Certificate.span:ℚ):ℝ) := by
  have hx := HighShape.native_domain hθ
  have hspan : ((Certificate.span:ℚ):ℝ)=8/15 := by
    norm_num [Certificate.span,Certificate.h,Certificate.L]
  rw [hspan,Rat.cast_zero]
  exact hx

lemma sigma_lower_data {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0≤aeval (native θ) Certificate.etaIncrement ∧
      Explicit.sigma .high θ≤aeval (native θ) Certificate.sigmaUpper := by
  have he := Explicit.high_eta hθ
  obtain ⟨e,hedef⟩ : ∃e:ℝ,e=eta θ := ⟨_,rfl⟩
  obtain ⟨w,hwdef⟩ : ∃w:ℝ,w=(e^2-(293/1000)^2)/(1+(293/1000)^2) := ⟨_,rfl⟩
  have he1 : (293/1000:ℝ)≤e := by rw [hedef]; exact he.1
  have hw : 0≤w := by
    rw [hwdef]; apply div_nonneg _ (by positivity); nlinarith
  have hwpoly : aeval (native θ) Certificate.etaIncrement=w := by
    simp only [Certificate.etaIncrement,map_mul,map_sub,map_pow,aeval_C,r72_td_eta,
      eq_ratCast,← hedef]
    rw [hwdef]
    push_cast [Certificate.eta0]
    ring
  have h1 : 0<Real.sqrt (1+w) := Real.sqrt_pos.mpr (by positivity)
  have hprod : (1+(293/1000:ℝ)^2)*(1+w)=1+e^2 := by
    rw [hwdef]; field_simp; ring
  have hroot : Real.sqrt (1+e^2)=Real.sqrt (1+(293/1000:ℝ)^2)*Real.sqrt (1+w) := by
    rw [← Real.sqrt_mul (by positivity),hprod]
  have hbase : R*Real.sqrt (1+(293/1000:ℝ)^2)≤
      (1415477291/1000000000:ℝ)+(1+293/1000)/2 := by
    have hh := NonnegativeTotals.Charges.sigma_upper
    simp only [PositiveTD.sigma,PositiveTD.eta,fullSupport,
      NonnegativeTotals.Certificate.sigmabar,one_pow] at hh
    push_cast at hh
    linarith
  have hupper := mul_le_mul hbase (sqrt_cubic_upper hw) h1.le (by norm_num)
  refine ⟨by rw [hwpoly]; exact hw,?_⟩
  have hsig : Explicit.sigma .high θ=
      R*(Real.sqrt (1+(293/1000:ℝ)^2)*Real.sqrt (1+w))-(1+e)/2 := by
    rw [← hroot,hedef]
    simp only [Explicit.sigma,fullSupport,one_pow]
  have hpoly : aeval (native θ) Certificate.sigmaUpper=
      ((1415477291/1000000000:ℝ)+(1+293/1000)/2)*(1+w/2-w^2/8+w^3/16)-(1+e)/2 := by
    simp only [Certificate.sigmaUpper,map_sub,map_mul,map_add,map_pow,map_one,aeval_C,
      r72_td_eta,hwpoly,eq_ratCast,← hedef]
    push_cast [Certificate.sigmabar,Certificate.eta0]
    ring
  rw [hsig,hpoly]
  simp only [cubic] at hupper
  linarith

def base (θ : ℝ) : ℝ := 2*k θ+3*l θ+3+
  m θ*(1+2*Real.cos θ+(1/2+(3/2)*eta θ-Explicit.sigma .high θ)*Real.sin θ)

def norms (θ : ℝ) : Fin 4→ℝ :=
  ![pairNorm (k θ) 1 0,pairNorm (k θ) (l θ) 0,
    pairNorm (l θ) (m θ) 0,pairNorm 1 (c θ) 0]

lemma polynomial_sine_negative {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) Certificate.highSineCoefficient≤0 := by
  have hc := Certificate.high_auxiliary_certificate.2.1
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num [Certificate.span,Certificate.h,Certificate.L] : (0:ℚ)<Certificate.span)
    hc.1 hc.2 (r72_td_dom hθ)
  rw [map_neg,Rat.cast_zero] at hh
  linarith

theorem base_lower {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) Certificate.highBase≤base θ := by
  have ht := taylor_bounds (Explicit.frame_domain .high hθ)
  have hsig := (sigma_lower_data hθ).2
  have hs := (transport_trig (Explicit.frame_domain .high hθ)).2.2.1
  have hcoef : aeval (native θ) Certificate.highSineCoefficient≤
      1/2+(3/2)*eta θ-Explicit.sigma .high θ := by
    simp only [Certificate.highSineCoefficient,map_add,map_mul,map_sub,aeval_C,
      r72_td_eta,eq_ratCast]
    push_cast
    linarith
  have hsin := mul_le_mul_of_nonpos_left ht.2.2.1 (polynomial_sine_negative hθ)
  have hsin' := mul_le_mul_of_nonneg_right hcoef hs
  have hinner : 1+2*aeval θ C10+
      aeval (native θ) Certificate.highSineCoefficient*aeval θ S9≤
      1+2*Real.cos θ+(1/2+(3/2)*eta θ-Explicit.sigma .high θ)*Real.sin θ := by
    linarith [ht.2.2.2.2.1]
  have hprod := mul_le_mul_of_nonneg_left hinner
    (show 0 ≤ m θ by linarith [(Explicit.high_bounds hθ).m_lower])
  simp only [Certificate.highBase,map_add,map_mul,map_one,aeval_C,r72_td_comp,
    r72_td_K,r72_td_L,r72_td_M,eq_ratCast,Rat.cast_ofNat]
  simp only [base]
  linarith

lemma base_polynomial_positive {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<aeval (native θ) (Certificate.highBase-1) := by
  have hc := Certificate.high_auxiliary_certificate.1
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num [Certificate.span,Certificate.h,Certificate.L] : (0:ℚ)<Certificate.span)
    hc.1 hc.2 (r72_td_dom hθ)
  have h0 : (0:ℝ)<((399/50:ℚ):ℝ) := by norm_num
  exact h0.trans hh

theorem baseline_identity {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.fullBaseline .high 0 θ 0=base θ-R*(norms θ 0+norms θ 1+norms θ 2+norms θ 3) := by
  rw [Explicit.fullBaseline]
  simp only [zero_add,Explicit.sec,NegativeELargeA.secant,Real.cos_zero,Real.tan_zero,
    div_one,sub_self,mul_zero,add_zero,TwoPositive.ASupport.charge_zero]
  rw [edgeWidth_positive_formula (Explicit.frame_domain .high hθ)]
  rw [fullSupport_pair (k θ) 1,fullSupport_pair (l θ) (k θ),
    fullSupport_pair (m θ) (l θ),fullSupport_pair (c θ) 1,pairNorm_symm (l θ) (k θ),
    pairNorm_symm (m θ) (l θ),pairNorm_symm (c θ) 1]
  simp only [base,norms,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Explicit.c]
  ring

theorem norm_bounds {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 4) :
    (norms θ i)^2≤aeval (native θ) (Certificate.highNormZero i) := by
  have hc := HighShape.coefficient_majorant hθ
  have hc0 : 0≤c θ := by
    linarith [(Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1,
      (Explicit.high_bounds hθ).m_lower]
  have hc2 := pow_le_pow_left₀ hc0 hc 2
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
  all_goals simp only [norms,Certificate.highNormZero,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    map_add,map_pow,map_one,r72_td_K,r72_td_L,r72_td_M,
    NonnegativeTotals.Analytic.norm_zero_square,one_pow]
  · linarith
  · exact le_rfl
  · exact le_rfl
  · linarith [hc2]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighTransfer
end
end
end

section
/-!
## The four high-T endpoints for negative DE3 / positive BT3

The three zero-DE endpoints keep the negative norms of H, G and B (`zero_positive`). At equal
angles the rotated secant-D norm is scaled by the positive cosine (`equal_positive`). Every norm
mass and numerator comes from its whole native interval.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighTransfer
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds num4_transfer)
open Certificate (HighCase)

private lemma r72_nt (θ : ℝ) : native θ+(Certificate.L:ℝ)=θ := by simp [native]

private lemma r72_K (θ : ℝ) : aeval (native θ) Certificate.highK=k θ := by
  rw [Certificate.highK_eval,r72_nt]

private lemma r72_L (θ : ℝ) : aeval (native θ) Certificate.highL=l θ := by
  rw [Certificate.highL_eval,r72_nt]

private lemma r72_M (θ : ℝ) : aeval (native θ) Certificate.highM=m θ := by
  rw [Certificate.highM_eval,r72_nt]

private lemma r72_comp (θ : ℝ) (P : ℚ[X]) :
    aeval (native θ) (P.comp Certificate.theta)=aeval θ P := by
  rw [aeval_comp,Certificate.theta_eval,r72_nt]

lemma qStar_upper {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    max (l θ) (m θ)≤aeval (native θ) Certificate.highQStar := by
  have hh := NegativeDEPositiveTD.Certificate.qStar_lower .atA hθ
  have h1 : aeval θ NegativeDEPositiveTD.Certificate.qStar=l θ+3/20*(7/10-θ) := by
    simp only [NegativeDEPositiveTD.Certificate.qStar,map_add,map_mul,map_sub,aeval_C,aeval_X,
      NegativeDEPositiveTD.Certificate.l_eval]
    norm_num [PositiveTD.Certificate.h]
    rfl
  have h2 : aeval (native θ) Certificate.highQStar=l θ+3/20*(7/10-θ) := by
    simp only [Certificate.highQStar,map_add,map_mul,map_sub,aeval_C,r72_L,
      Certificate.theta_eval,r72_nt]
    norm_num [Certificate.h]
  have h3 : NegativeDEPositiveTD.Explicit.splitM .high .atA θ=m θ := by
    simp [NegativeDEPositiveTD.Explicit.splitM,NegativeDEPositiveTD.Explicit.splitT,
      NegativeDEPositiveTD.Explicit.m,m,Explicit.m]
  rw [h1,h3] at hh
  rw [h2]
  exact hh

def negativeNorm (r : HighCase) (θ : ℝ) : Fin 4→ℝ :=
  ![pairNorm (k θ) 1 (if r=.H then -θ else 0),
    pairNorm (k θ) (l θ) (if r=.G then -θ else 0),
    pairNorm (l θ) (m θ) (if r=.B then -θ else 0),pairNorm 1 (c θ) 0]
def negativeA (r : HighCase) (θ : ℝ) : ℝ := base θ+
  (if r=.H then 1 else if r=.G then l θ else max (l θ) (m θ))*(Real.cos θ-1)

theorem negative_norm_bound (r : HighCase) (hr : r≠.equal) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 4) :
    (negativeNorm r θ i)^2≤aeval (native θ) (Certificate.highP r i) := by
  have hb := Explicit.high_bounds hθ
  have hk : 0<k θ := by linarith [hb.k_lower]
  have hl : 0<l θ := by linarith [hb.l_lower]
  have hm : 0 < m θ := by linarith [hb.m_lower]
  have hf := Explicit.frame_domain .high hθ
  have ht := taylor_bounds hf
  have hzero := norm_bounds hθ
  have hnegative {p q : ℝ} (hp : 0<p) (hq : 0<q) :
      (pairNorm p q (-θ))^2≤p^2+q^2-2*p*q*aeval θ S11 := by
    have hh := NonnegativeTotals.Analytic.norm_negative_square hp hq hf
    have hsin := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤2*p*q by positivity)
    linarith
  have hH := hnegative hk (by norm_num : (0:ℝ)<1)
  have hG := hnegative hk hl
  have hB := hnegative hl hm
  have hS := r72_comp θ S11
  have h0 := hzero 0
  have h1 := hzero 1
  have h2 := hzero 2
  have h3 := hzero 3
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
  all_goals
    cases r <;> (try exact absurd rfl hr) <;>
    simp (config := {decide := true}) only [negativeNorm,norms,Certificate.highP,
      Certificate.highNormZero,Certificate.highIndex,Certificate.highProduct,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons,Fin.isValue,
      ↓reduceIte,sub_zero,map_sub,map_add,map_mul,map_pow,map_one,aeval_C,eq_ratCast,
      Rat.cast_ofNat,hS,r72_K,r72_L,r72_M] at h0 h1 h2 h3 ⊢
  all_goals first
    | assumption
    | linarith only [hH]
    | linarith only [hG]
    | linarith only [hB]

theorem negative_nonradical_lower (r : HighCase) (hr : r≠.equal) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) (Certificate.highA r)≤negativeA r θ := by
  have hb := base_lower hθ
  have ht := taylor_bounds (Explicit.frame_domain .high hθ)
  have hl : 0≤l θ := by linarith [(Explicit.high_bounds hθ).l_lower]
  have hG := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hl
  have hq := qStar_upper hθ
  have hq0 : 0≤aeval (native θ) Certificate.highQStar := (hl.trans (le_max_left _ _)).trans hq
  have hB0 := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hq0
  have hB1 := mul_le_mul_of_nonpos_right hq (sub_nonpos.mpr (Real.cos_le_one θ))
  have hC := r72_comp θ C10
  cases r <;> (try exact absurd rfl hr) <;>
    simp (config := {decide := true}) only [Certificate.highA,Certificate.highIndex,
      Certificate.highCosineCoefficient,↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      map_add,map_mul,map_sub,map_one,hC,r72_L,negativeA,one_mul] <;>
    linarith [ht.2.2.2.2.1]

theorem negative_identity (r : HighCase) (hr : r≠.equal) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ (Certificate.highIndex r) θ=
      negativeA r θ-R*(negativeNorm r θ 0+negativeNorm r θ 1+
        negativeNorm r θ 2+negativeNorm r θ 3) := by
  rw [baseline_identity hθ]
  cases r <;> (try exact absurd rfl hr) <;>
    simp (config := {decide := true}) only [negativeA,negativeNorm,norms,Certificate.highIndex,
      Explicit.V,Explicit.p,Explicit.q,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,↓reduceIte,
      one_mul,OrdinaryAngleConcavity.V,TwoPositive.Certificate.sorted_pair_norm] <;> ring

theorem zero_positive (i : Fin 3) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ i θ := by
  have hrow (r : HighCase) (hr : r≠.equal) :
      0<Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ (Certificate.highIndex r) θ := by
    have hx := HighShape.native_domain hθ
    have hn (j : Fin 4) : 0≤negativeNorm r θ j := by fin_cases j <;> exact Real.sqrt_nonneg _
    have hh := num4_transfer
      (Certificate.high_mass_positive r 0 hx) (Certificate.high_mass_positive r 1 hx)
      (Certificate.high_mass_positive r 2 hx) (Certificate.high_mass_positive r 3 hx)
      (hn 0) (hn 1) (hn 2) (hn 3)
      (negative_norm_bound r hr hθ 0) (negative_norm_bound r hr hθ 1)
      (negative_norm_bound r hr hθ 2) (negative_norm_bound r hr hθ 3)
      (negative_nonradical_lower r hr hθ) (Certificate.high_numerator_positive r hx)
    rwa [negative_identity r hr hθ]
  fin_cases i
  · exact hrow .H (by decide)
  · exact hrow .G (by decide)
  · exact hrow .B (by decide)

def equalNorm (θ : ℝ) : Fin 4→ℝ :=
  ![Real.cos θ*norms θ 0,Real.cos θ*norms θ 1,Real.cos θ*norms θ 2,
    Real.cos θ*pairNorm (Explicit.sec θ) (c θ) 0]
def equalA (θ : ℝ) : ℝ := Real.cos θ*(base θ-1)+1+Explicit.K*Real.sin θ

lemma scaled_D_square {θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    (equalNorm θ 3)^2=1+(c θ)^2*(Real.cos θ)^2 := by
  have hc := NegativeESecant.cos_pos hθ
  simp only [equalNorm,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,mul_pow,
    NonnegativeTotals.Analytic.norm_zero_square,Explicit.sec,NegativeELargeA.secant]
  field_simp

theorem equal_norm_bound {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 4) :
    (equalNorm θ i)^2≤aeval (native θ) (Certificate.highP .equal i) := by
  have hf := Explicit.frame_domain .high hθ
  have hcos := NegativeDEPositiveTD.Certificate.cosine_square_upper hf
  have hzero := norm_bounds hθ
  have hC := HighShape.coefficient_majorant hθ
  have hc0 : 0≤c θ := by
    linarith [(Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1,
      (Explicit.high_bounds hθ).m_lower]
  have hC2 := pow_le_pow_left₀ hc0 hC 2
  have hprod := mul_le_mul hC2 hcos (sq_nonneg (Real.cos θ))
    (sq_nonneg (aeval (native θ) Certificate.highC))
  have hC12 := r72_comp θ C12
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
  all_goals simp (config := {decide := true}) only [Certificate.highP,↓reduceIte]
  all_goals try simp only [equalNorm,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,map_mul,map_pow,hC12,mul_pow]
  · exact mul_le_mul hcos (hzero 0) (sq_nonneg _) (sq_nonneg _)
  · exact mul_le_mul hcos (hzero 1) (sq_nonneg _) (sq_nonneg _)
  · exact mul_le_mul hcos (hzero 2) (sq_nonneg _) (sq_nonneg _)
  · change (equalNorm θ 3)^2≤_
    rw [scaled_D_square hf]
    simp only [map_add,map_one,map_mul,map_pow,hC12]
    linarith

theorem equal_nonradical_lower {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) (Certificate.highA .equal)≤equalA θ := by
  have ht := taylor_bounds (Explicit.frame_domain .high hθ)
  have hc := NegativeESecant.cos_pos (Explicit.frame_domain .high hθ)
  have hpoly := base_polynomial_positive hθ
  have hbase := sub_le_sub_right (base_lower hθ) 1
  have hpoly' : 0≤aeval (native θ) Certificate.highBase-1 := by
    simpa only [map_sub,map_one] using hpoly.le
  have hprod := mul_le_mul ht.2.2.2.2.1 hbase hpoly' hc.le
  have hs := mul_le_mul_of_nonneg_left ht.2.1 (show (0:ℝ)≤13/12 by norm_num)
  have hK : algebraMap ℚ ℝ Certificate.K=13/12 := by norm_num [Certificate.K]
  simp only [Certificate.highA,↓reduceIte,map_add,map_mul,map_sub,map_one,aeval_C,
    r72_comp,hK]
  simp only [equalA,Explicit.K]
  linarith

theorem equal_identity {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Real.cos θ*Explicit.fullBaseline .high 0 θ θ=
      equalA θ-R*(equalNorm θ 0+equalNorm θ 1+equalNorm θ 2+equalNorm θ 3) := by
  have hc := NegativeESecant.cos_pos (Explicit.frame_domain .high hθ)
  have hid : Explicit.fullBaseline .high 0 θ θ=Explicit.fullBaseline .high 0 θ 0+
      (Explicit.sec θ-1)/2+Explicit.K*Real.tan θ-
        (fullSupport (Explicit.sec θ) (c θ)-fullSupport 1 (c θ)) := by
    simp only [Explicit.fullBaseline,Explicit.sec,NegativeELargeA.secant,Real.cos_zero,
      Real.tan_zero,div_one,zero_add,mul_zero]
    ring
  rw [hid,baseline_identity hθ,fullSupport_pair (c θ) (Explicit.sec θ),
    fullSupport_pair (c θ) 1,pairNorm_symm (c θ) (Explicit.sec θ),pairNorm_symm (c θ) 1]
  simp only [equalA,equalNorm,norms,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [Real.tan_eq_sin_div_cos]
  simp only [Explicit.sec,NegativeELargeA.secant]
  field_simp
  ring

theorem equal_positive {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<Explicit.fullBaseline .high 0 θ θ := by
  have hx := HighShape.native_domain hθ
  have hc := NegativeESecant.cos_pos (Explicit.frame_domain .high hθ)
  have hn (i : Fin 4) : 0≤equalNorm θ i := by
    fin_cases i <;> exact mul_nonneg hc.le (Real.sqrt_nonneg _)
  have hh := num4_transfer
    (Certificate.high_mass_positive .equal 0 hx) (Certificate.high_mass_positive .equal 1 hx)
    (Certificate.high_mass_positive .equal 2 hx) (Certificate.high_mass_positive .equal 3 hx)
    (hn 0) (hn 1) (hn 2) (hn 3)
    (equal_norm_bound hθ 0) (equal_norm_bound hθ 1)
    (equal_norm_bound hθ 2) (equal_norm_bound hθ 3)
    (equal_nonradical_lower hθ) (Certificate.high_numerator_positive .equal hx)
  rw [←equal_identity hθ] at hh
  exact (mul_pos_iff_of_pos_left hc).mp hh

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighTransfer
end
end
end

section
/-!
## The high-BT3 right derivative at the original total angle

The two reciprocal-norm
numerators are transferred using the actual total-dependent D support.
The B derivative is compared with G only after the two positive
coefficients and the sorted-pair identity have been established.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighDerivative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope PairNormCalculus

open PositiveTD.Certificate (C10 C12 S9 S11 taylor_bounds)

lemma H_G_endpoint (atH : Bool) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    secantGainDeriv qCap (Explicit.c .high θ θ) θ<
      Vd R (Explicit.k .high θ) (if atH then 1 else Explicit.l .high θ) 0 := by
  have hx := HighShape.native_domain hθ
  have hf := Explicit.frame_domain .high hθ
  have hb := Explicit.high_bounds hθ
  obtain ⟨x,hxdef⟩ : ∃x:ℝ,x=θ-(Certificate.L:ℝ) := ⟨_,rfl⟩
  obtain ⟨p,hpdef⟩ : ∃p:ℝ,p=Explicit.k .high θ := ⟨_,rfl⟩
  obtain ⟨q,hqdef⟩ : ∃q:ℝ,q=(if atH then 1 else Explicit.l .high θ) := ⟨_,rfl⟩
  obtain ⟨c,hcdef⟩ : ∃c:ℝ,c=Explicit.c .high θ θ := ⟨_,rfl⟩
  rw [← hpdef,← hqdef,← hcdef]
  rw [← hxdef] at hx
  have hxL : x+(Certificate.L:ℝ)=θ := by rw [hxdef]; ring
  have hp : 0<p := by rw [hpdef]; linarith [hb.k_lower]
  have hq : 0<q := by
    cases atH
    · simp only [Bool.false_eq_true,↓reduceIte] at hqdef
      rw [hqdef]; linarith [hb.l_lower]
    · simp only [↓reduceIte] at hqdef
      rw [hqdef]; norm_num
  have hn := pairNorm_pos hp hq (t:=0) (by norm_num [frameCap])
  have hnorm : (pairNorm p q 0)^2≤aeval x (Certificate.derivativeP atH) := by
    rw [NonnegativeTotals.Analytic.norm_zero_square]
    cases atH
    · simp only [Bool.false_eq_true,↓reduceIte] at hqdef
      simp only [Certificate.derivativeP,Bool.false_eq_true,↓reduceIte,map_add,map_pow,
        Certificate.highK_eval,Certificate.highL_eval,hxL,hpdef,hqdef,le_refl]
    · simp only [↓reduceIte] at hqdef
      simp only [Certificate.derivativeP,↓reduceIte,map_add,map_one,map_pow,
        Certificate.highK_eval,hxL,hpdef,hqdef]
      linarith
  have hmass := Certificate.derivative_masses_positive atH hx
  have hden := NegativeAPositiveTD.SecantBaseline.denominator_pos c θ
  have hden2 := NegativeAPositiveTD.SecantBaseline.denominator_sq c θ
  have ht := taylor_bounds hf
  have hcos := NegativeESecant.cos_pos hf
  have hC10 : 0≤aeval θ C10 := by linarith [ht.2.2.2.1]
  have hC10sq := pow_le_pow_left₀ hC10 ht.2.2.2.2.1 2
  have hC12sq := NegativeDEPositiveTD.Certificate.cosine_square_upper hf
  have hc0 : 0≤c := by
    rw [hcdef]
    linarith [(Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1,hb.m_lower]
  have hC : c≤aeval x Certificate.highC := by
    rw [hcdef,hxdef]; exact HighShape.coefficient_majorant hθ
  have hC2 := pow_le_pow_left₀ hc0 hC 2
  have hprod := mul_le_mul hC2 hC12sq (sq_nonneg (Real.cos θ))
    (sq_nonneg (aeval x Certificate.highC))
  have hD : (NegativeAPositiveTD.SecantBaseline.denominator c θ)^2≤
      aeval x Certificate.derivativeD := by
    rw [hden2]
    simp only [Certificate.derivativeD,map_add,map_one,map_mul,map_pow,aeval_comp,
      Certificate.theta_eval,hxL]
    linarith
  have hR : (Certificate.Rlo:ℝ)≤R := by
    rw [show R=Real.sqrt qCap from rfl]
    apply Real.le_sqrt_of_sq_le
    norm_num [Certificate.Rlo,qCap]
  have hpoly : 0<
      2*(Certificate.Rlo:ℝ)*aeval x (Certificate.derivativeMass atH)*(p*q)*(aeval θ C10)^2*
        (aeval x Certificate.derivativeD+(aeval x Certificate.derivativeDMass)^2)+
      2*(Certificate.Rlo:ℝ)*aeval x Certificate.derivativeDMass*aeval θ S11*
        (aeval x (Certificate.derivativeP atH)+(aeval x (Certificate.derivativeMass atH))^2)-
      (13/12+aeval θ S9)*
        (aeval x (Certificate.derivativeP atH)+(aeval x (Certificate.derivativeMass atH))^2)*
        (aeval x Certificate.derivativeD+(aeval x Certificate.derivativeDMass)^2) := by
    have hh := Certificate.derivative_numerator_positive atH hx
    have hf' : aeval x (Certificate.derivativeProduct atH)=p*q := by
      cases atH
      · simp only [Bool.false_eq_true,↓reduceIte] at hqdef
        simp only [Certificate.derivativeProduct,Bool.false_eq_true,↓reduceIte,map_mul,
          Certificate.highK_eval,Certificate.highL_eval,hxL,hpdef,hqdef]
      · simp only [↓reduceIte] at hqdef
        simp only [Certificate.derivativeProduct,↓reduceIte,Certificate.highK_eval,hxL,
          hpdef,hqdef,mul_one]
    simp only [Certificate.derivativeNumerator,map_add,map_sub,map_mul,map_pow,aeval_C,
      aeval_comp,Certificate.theta_eval,hxL,hf'] at hh
    norm_num [Certificate.K,Certificate.Rlo] at hh ⊢
    linarith
  have htransfer := NegativeDEPositiveTD.HighDerivative.derivative_transfer hn hden
    hmass.1 hmass.2 hnorm hD (mul_nonneg hp.le hq.le)
    (sq_nonneg _) hC10sq ht.1 ht.2.1 ht.2.2.1
    (by norm_num [Certificate.Rlo] : (0:ℝ)≤(Certificate.Rlo:ℝ)) hR hpoly
  rw [NegativeDEPositiveTD.HighDerivative.zero_slope]
  change (13/12+Real.sin θ-R*Real.sin θ/NegativeAPositiveTD.SecantBaseline.denominator c θ)/
    Real.cos θ^2<R*(p*q)/pairNorm p q 0
  apply (div_lt_iff₀ (pow_pos hcos 2)).2
  have he : R*(p*q)*Real.cos θ^2/pairNorm p q 0=R*(p*q)/pairNorm p q 0*Real.cos θ^2 := by
    ring
  linarith

theorem all_endpoint {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    secantGainDeriv qCap (Explicit.c .high θ θ) θ<
      Vd R (Explicit.p .high θ i) (Explicit.q .high θ i) 0 := by
  have hb := Explicit.high_bounds hθ
  fin_cases i
  · show secantGainDeriv qCap (Explicit.c .high θ θ) θ<Vd R (Explicit.k .high θ) 1 0
    simpa using H_G_endpoint true hθ
  · show secantGainDeriv qCap (Explicit.c .high θ θ) θ<
      Vd R (Explicit.k .high θ) (Explicit.l .high θ) 0
    simpa using H_G_endpoint false hθ
  · show secantGainDeriv qCap (Explicit.c .high θ θ) θ<
      Vd R (min (Explicit.l .high θ) (Explicit.m .high θ))
        (max (Explicit.l .high θ) (Explicit.m .high θ)) 0
    have hm := NegativeDEPositiveTD.HighDerivative.zero_slope_first_mono
      (show 0<Explicit.k .high θ by linarith [hb.k_lower])
      (show Explicit.k .high θ≤Explicit.m .high θ by linarith [hb.k_upper,hb.m_lower])
      (show 0<Explicit.l .high θ by linarith [hb.l_lower])
    have hh := H_G_endpoint false hθ
    simp only [Bool.false_eq_true,↓reduceIte] at hh
    have he : Vd R (min (Explicit.l .high θ) (Explicit.m .high θ))
        (max (Explicit.l .high θ) (Explicit.m .high θ)) 0=
        Vd R (Explicit.m .high θ) (Explicit.l .high θ) 0 := by
      rcases le_total (Explicit.l .high θ) (Explicit.m .high θ) with h|h
      · rw [min_eq_left h,max_eq_right h,NegativeDEPositiveTD.HighDerivative.zero_slope,
          NegativeDEPositiveTD.HighDerivative.zero_slope,pairNorm_symm]
        ring
      · rw [min_eq_right h,max_eq_left h]
    rw [he]
    exact hh.trans_le hm

theorem first_right_negative {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    NegativeAPositiveTD.SecantCoordinate.pureFirst 1 (Explicit.c .high θ θ)
      (Explicit.p .high θ i) (Explicit.q .high θ i) θ (Real.tan θ)<0 := by
  have hh := all_endpoint hθ i
  have hden : 0<1+Real.tan θ^2 := by positivity
  simp only [NegativeAPositiveTD.SecantCoordinate.pureFirst,one_mul,
    NegativeAPositiveTD.SecantCoordinate.arctan_tan (Explicit.frame_domain .high hθ),sub_self,
    NegativeDEPositiveTD.HighDerivative.baseFirst_tan (Explicit.frame_domain .high hθ)]
  exact sub_neg.mpr (div_lt_div_of_pos_right hh hden)

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighDerivative
end
end
end

section
/-!
## The complete high-T negative-DE interval

The original total and coefficients
are fixed while the DE magnitude varies through its whole closed
interval. The shared third-derivative theorem, now supplied with the
actual BT3 domain and right derivative, reduces the stress to the two
proved intrinsic endpoints. No shape or derivative premise remains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighT
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.SecantCoordinate

lemma pure_at_original {θ s : ℝ} (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    pure (Explicit.fullBaseline .high 0 θ 0) 1 (Explicit.c .high θ θ)
      (Explicit.p .high θ i) (Explicit.q .high θ i) θ (Real.tan s)=
      Explicit.fullBaseline .high 0 θ s+Explicit.V .high θ i (θ-s) := by
  have hc := NegativeESecant.cos_pos hs
  have hn := normalized_arctan (Explicit.c .high θ θ) (Real.tan s)
  rw [arctan_tan hs] at hn
  have hg : SecantNormCurvature.normalized R (Explicit.c .high θ θ) s=
      secantGain qCap (Explicit.c .high θ θ) s := by
    rw [secantGain_eq_secant_expression qCap (Explicit.c .high θ θ) hc]
    simp only [SecantNormCurvature.normalized,SecantNormCurvature.secant,
      SecantNormCurvature.supportNorm]
    rw [add_comm ((Explicit.c .high θ θ)^2) ((1/Real.cos s)^2),
      add_comm ((Explicit.c .high θ θ)^2) 1]
    ring
  simp only [NegativeAPositiveTD.SecantCoordinate.pure,Explicit.V,arctan_tan hs,one_mul]
  rw [←hn,hg,Explicit.full_correction .high 0 θ hs,zero_add]

theorem endpoint_minimum {θ s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hs : s∈Icc 0 θ) (i : Fin 3) :
    min (Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ i θ)
        (Explicit.fullBaseline .high 0 θ θ)≤
      Explicit.fullBaseline .high 0 θ s+Explicit.V .high θ i (θ-s) := by
  have hf := Explicit.frame_domain .high hθ
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hf.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan θ) :=
    ⟨tan_nonnegative hsf,tan_monotone hsf hf hs.2⟩
  have hh := NegativeDEHighShape.pure_endpoint_minimum
    (B:=Explicit.fullBaseline .high 0 θ 0) true (HighShape.shape_domain hθ i) hx
    (HighDerivative.first_right_negative hθ i).le
  have h0 : NegativeAPositiveTD.SecantCoordinate.pure (Explicit.fullBaseline .high 0 θ 0) 1
      (Explicit.c .high θ θ) (Explicit.p .high θ i) (Explicit.q .high θ i) θ 0=
      Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ i θ := by
    simp only [NegativeAPositiveTD.SecantCoordinate.pure,Explicit.V,Real.arctan_zero,sub_self,
      mul_zero,add_zero,sub_zero]
  have h1 := pure_at_original (θ:=θ) hf i
  simp only [sub_self,Explicit.V,V_zero,add_zero] at h1
  rw [h0,h1,pure_at_original hsf i] at hh
  exact hh

/-- Complete continuous T-endpoint positivity, with all three original pairs. -/
theorem negative_positive {θ s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hs : s∈Icc 0 θ) (i : Fin 3) :
    0<Explicit.fullBaseline .high 0 θ s+Explicit.V .high θ i (θ-s) :=
  (lt_min (HighTransfer.zero_positive i hθ) (HighTransfer.equal_positive hθ)).trans_le
    (endpoint_minimum hθ hs i)

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighT
end
end
end

section
/-!
## Every original high-total A/BT split

Full-circle support is used only as a lower
stress bound; its compensation term has already been paid in the split
curvature. The A endpoint is the previously proved full-D DE/TD endpoint
with zero T angle. The T endpoint is the new complete high-BT3 theorem.
No restriction on the actual original split remains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open SplitConcavityTools

abbrev shiftedD (q c : ℝ) : ℝ := TwoPositive.Coefficient.affineBranch q 0 shift 0 c

lemma D_slope {q c : ℝ} (hq : 1≤q) (hc : c∈Icc (0:ℝ) (6/5)) :
    R*TwoPositive.Coefficient.normD q 0 c<(1521/1000:ℝ) := by
  have hq0 : 0<q := by linarith
  have hn1 : 0<pairNorm 1 c 0 := by
    rw [pairNorm_zero]; exact Real.sqrt_pos.mpr (by positivity)
  have hnorm : pairNorm 1 c 0≤pairNorm q c 0 := by
    rw [pairNorm_zero,pairNorm_zero]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hquot := div_le_div_of_nonneg_left
    (mul_nonneg (Real.sqrt_nonneg qCap) hc.1) hn1 hnorm
  have hh := PositiveBT3.Analytic.D_slope hc
  simp only [TwoPositive.Coefficient.normD,Real.sin_zero,mul_zero,add_zero] at hh ⊢
  calc R*(c/pairNorm q c 0)=R*c/pairNorm q c 0 := by ring
    _≤R*c/pairNorm 1 c 0 := hquot
    _=R*(c/pairNorm 1 c 0) := by ring
    _<1521/1000 := hh

lemma shiftedD_concave {q : ℝ} (hq : 1≤q) :
    ConcaveOn ℝ (Icc (4/5:ℝ) (6/5)) (shiftedD q) :=
  TwoPositive.Coefficient.affine_concave (by linarith) (by norm_num) (by norm_num [frameCap])

lemma shiftedD_monotone {q : ℝ} (hq : 1≤q) :
    MonotoneOn (shiftedD q) (Icc (4/5:ℝ) (6/5)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun c hc => (TwoPositive.Coefficient.affine_derivative
      (w:=shift) (b:=0) (by linarith : 0<q) (by linarith [hc.1] : 0<c)
      (by norm_num [frameCap])).continuousAt.continuousWithinAt)
    (fun c hc => TwoPositive.Coefficient.affine_derivative
      (w:=shift) (b:=0) (by linarith : 0<q) (by linarith [hc.1] : 0<c)
      (by norm_num [frameCap]))
  intro c hc
  have hh := D_slope hq (show c∈Icc (0:ℝ) (6/5) from ⟨by linarith [hc.1],hc.2.le⟩)
  dsimp [TwoPositive.Coefficient.affineD,shift]
  linarith

def fixedPart (θ s : ℝ) (i : Fin 3) : ℝ :=
  k θ+2*l θ+Explicit.sec s+3/2-fullSupport 1 (k θ)-fullSupport (k θ) (l θ)-
    fullSupport (l θ) (m θ)+Explicit.K*Real.tan s+Explicit.V .high θ i (θ-s)

theorem split_identity {θ s a : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (ha : a∈Icc 0 θ) (i : Fin 3) :
    Explicit.fullBaseline .high a (θ-a) s+Explicit.V .high θ i (θ-s)=
      fixedPart θ s i+(shiftedD (Explicit.sec s) (tilt θ a)+rest θ a) := by
  have hz := (TwoPositive.Split.split_domain (Explicit.frame_domain .high hθ) ha).2
  simp only [Explicit.fullBaseline,show a+(θ-a)=θ by ring]
  rw [edgeWidth_positive_formula hz,
    fullSupport_pair (Explicit.c .high θ (θ-a)) (Explicit.sec s),
    pairNorm_symm (Explicit.c .high θ (θ-a)) (Explicit.sec s)]
  simp only [fixedPart,shiftedD,TwoPositive.Coefficient.affineBranch,rest,smooth,tilt,k,l,m,
    sigma]
  ring

theorem scalar_concave {θ s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    ConcaveOn ℝ (Icc 0 θ)
      (fun a => Explicit.fullBaseline .high a (θ-a) s+Explicit.V .high θ i (θ-s)) := by
  have hq := (NegativeELargeA.secant_range hs).1
  have hc := (compose (shiftedD_concave hq) (shiftedD_monotone hq)
    (tilt_concave hθ) (fun x hx => tilt_range hθ hx)).add (rest_concave hθ)
  apply TwoPositive.Split.congr_on ((concaveOn_const (fixedPart θ s i) (convex_Icc 0 θ)).add hc)
  intro a ha
  rw [split_identity hθ ha i]
  rfl

lemma A_identity (θ s : ℝ) (i : Fin 3) :
    Explicit.fullBaseline .high θ 0 s+Explicit.V .high θ i (θ-s)=
      NegativeDEPositiveTD.Explicit.fullBaseline .high θ 0 s+
        NegativeDEPositiveTD.Explicit.V .high θ 0 i (θ-s) := by
  have hm0 : NegativeDEPositiveTD.Explicit.m .high θ 0=NegativeDEPositiveTD.Explicit.c .high θ := by
    simp [NegativeDEPositiveTD.Explicit.m]
  have hV : Explicit.V .high θ i (θ-s)=NegativeDEPositiveTD.Explicit.V .high θ 0 i (θ-s) := by
    simp only [Explicit.V,NegativeDEPositiveTD.Explicit.V,Explicit.p,Explicit.q,
      NegativeDEPositiveTD.Explicit.p,NegativeDEPositiveTD.Explicit.q,hm0]
    rfl
  have hfs (x y : ℝ) : fullSupport x y=fullSupport y x := by
    unfold fullSupport; rw [add_comm (x^2) (y^2),add_comm x y]
  rw [hV]
  congr 1
  simp only [Explicit.fullBaseline,Explicit.k,Explicit.l,Explicit.m,Explicit.c,Explicit.sigma,
    NegativeDEPositiveTD.Explicit.fullBaseline,NegativeDEPositiveTD.Explicit.baseline,hm0,
    add_zero,Real.cos_zero,Real.sin_zero,mul_zero,mul_one,edgeWidth_zero,Explicit.sec,
    NegativeELargeA.secant,NegativeDEPositiveTD.Explicit.secant,Explicit.K,
    NegativeDEPositiveTD.Explicit.K]
  rw [hfs (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.k .high θ),
    hfs (NegativeDEPositiveTD.Explicit.c .high θ) (NegativeDEPositiveTD.Explicit.l .high θ)]
  ring

theorem negative_positive {a z s : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 (a+z)) (i : Fin 3) :
    0<Explicit.fullBaseline .high a z s+Explicit.V .high (a+z) i (a+z-s) := by
  have hf := Explicit.frame_domain .high hθ
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hf.2⟩
  have hT := HighT.negative_positive hθ hs i
  have hA : 0<Explicit.fullBaseline .high (a+z) 0 s+
      Explicit.V .high (a+z) i (a+z-s) := by
    rw [A_identity]
    have hh := NegativeDEPositiveTD.High.negative_positive (a:=a+z) (z:=0)
      (by simpa only [add_zero] using hθ) (by linarith) le_rfl
      (by simpa only [add_zero] using hs) i
    simpa only [add_zero] using hh
  have hh := concave_gt_of_endpoints (scalar_concave hθ hsf i)
    (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa only [sub_zero] using hT) (by simpa only [sub_self] using hA)
  simpa only [show a+z-a=z by ring] using hh

theorem equal_positive {a z : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) : 0<Explicit.baseline .high a z (a+z) := by
  have hh := negative_positive hθ ha hz
    (show a+z∈Icc 0 (a+z) from ⟨by linarith,le_rfl⟩) (0:Fin 3)
  simp only [sub_self,Explicit.V,V_zero,add_zero] at hh
  exact hh.trans_le (Explicit.full_lower .high a z (a+z))

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighSplit
end
end
end

section
/-!
## The high-total negative-DE3 / positive-BT3 scalar exclusion

Every split, every DE magnitude, both surplus signs and all four signed-mass blocks are joined
(`scalar_positive`). The full-circle scalar is used only below the sorted-D stress. No endpoint,
right-derivative, concentration or support-switch hypothesis remains.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.High
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem pure_positive {a z s : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 frameCap) (i j : Fin 4) :
    0<Explicit.baseline .high a z s+Blocks.pure .high (a+z) z s i j := by
  by_cases hst : s≤a+z
  · have hp := HighSplit.negative_positive hθ ha hz ⟨hs.1,hst⟩ (Blocks.ordinaryIndex j)
    have hl := Explicit.full_lower .high a z s
    have he : Blocks.pure .high (a+z) z s i j=
        Explicit.V .high (a+z) (Blocks.ordinaryIndex j) (a+z-s) := by
      change (if s≤a+z then Blocks.negative .high (a+z) (a+z-s) j else _) = _
      rw [ite_eq_left hst,Blocks.negative_to_ordinary]
    rw [he]
    linarith
  · have hp := HighSplit.equal_positive hθ ha hz
    have hc := PositivePure.pure_intrinsic_lower .high hθ ha hz
      (show s∈Icc (a+z) frameCap from ⟨(lt_of_not_ge hst).le,hs.2⟩) i j
    exact hp.trans_le hc

/-- Positivity on the whole closed domain, for the four-block mass budgets. -/
theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.baseline .high a z s+
      ∑i,Blocks.block .high (a+z) z s (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := HighConcentration.sum_to_pure P N hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) hs hP hN hPb hNb hbalance
  have hh := pure_positive hθ ha hz hs i j
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.High
end
end
end

section
/-!
## The original BT3 stress implies the exact scalar necessary inequality

The D singleton is bounded at its actual
secant, actual force, and actual signed TD0 argument. The T support uses
the total-dependent eta only as a weight direction at the unchanged
original T square. No selected-angle sign, support maximizer, or scalar
positivity premise is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks PairedE

lemma family_eta_nonnegative (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) : 0≤Explicit.eta f θ := by
  cases f
  · norm_num [Explicit.eta]
  · linarith [(Explicit.high_eta hθ).1]

lemma actual_T_support {Q eta : ℝ} {P : SignedPoint}
    (hc : P.Contained Q) (hQ : Q≤qCap) (he : 0≤eta) :
    P.a+eta*P.y≤fullSupport 1 eta := by
  have hh := raw_full_support (f:=1) (g:=eta) (hc.trans hQ)
  have hp := mul_le_mul_of_nonneg_left (le_abs_self P.y) he
  linarith

lemma tReserve_nonnegative {Q m eta : ℝ} {C : SignedCycle}
    (hc : (C.point T).Contained Q) (hQ : Q≤qCap) (hm : 0≤ m) (he : 0≤eta)
    (hz : delta C.theta B∈Icc 0 frameCap) : 0≤tReserve C m eta :=
  mul_nonneg (mul_nonneg hm (transport_trig hz).2.2.1)
    (sub_nonneg.mpr (actual_T_support hc hQ he))

lemma baseline_identity {C : SignedCycle} (ga ab : Bool) (f : Family)
    (hs : magnitude C∈Icc 0 frameCap) :
    base C (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
        (Explicit.m f (total C ga ab)) (Explicit.eta f (total C ga ab))+
      Explicit.l f (total C ga ab)*TwoPositive.ASupport.charge (aTotal C ga ab)=
      Explicit.baseline f (aTotal C ga ab) (delta C.theta B) (magnitude C) := by
  have hd : Real.cos (delta C.theta D)=Real.cos (NegativeDEPositiveTD.Source.magnitude C) := by
    simp only [NegativeDEPositiveTD.Source.magnitude,Real.cos_neg]
  simp only [base,deCorrection,magnitude]
  rw [NegativeDEPositiveTD.Source.deCorrection_identity hs,hd]
  simp only [Explicit.baseline,total,Explicit.sigma,Explicit.c,Explicit.sec,
    NegativeELargeA.secant,tilted,Explicit.K,NegativeDEPositiveTD.Explicit.K,
    NegativeDEPositiveTD.Explicit.secant]
  ring

lemma family_block_coefficients {C : SignedCycle} (hg ga ab : Bool) (f : Family)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f))
    (hz : delta C.theta B∈Icc 0 (total C ga ab)) (i : Fin 4) :
    (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.m f (total C ga ab)) i).p=Blocks.p f (total C ga ab) i ∧
    (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.m f (total C ga ab)) i).q=Blocks.q f (total C ga ab) i := by
  have hc := Explicit.source_coefficients f hθ hz
  exact block_coefficients (C:=C) hg ga ab
    (m:=Explicit.m f (total C ga ab)) (by linarith [hc.1.2]) hc.2.1 i

lemma actual_D_minorant {Q k c s t : ℝ} {P : SignedPoint}
    (hsorted : P.Sorted) (hy : P.y≤0) (hcontained : P.Contained Q) (hQ : Q≤qCap)
    (hk : k∈Icc (1/2:ℝ) (17/20))
    (hc : c∈Icc SecantD.PositiveEndpoint.d SecantD.cUpper) (hkc : k≤c)
    (hs : s∈Icc 0 frameCap) (ht : |t|≤frameCap) :
    -SecantD.slope*max (Explicit.sec s) c*positivePart t+V R k 1 (negativePart t)≤
      SecantD.actualIncrement (Explicit.sec s) c t P := by
  have hq := NegativeELargeA.secant_range hs
  have hcf : c∈Icc SecantD.cLower SecantD.cUpper := by
    refine ⟨?_,hc.2⟩
    have h1 := hc.1
    simp only [SecantD.PositiveEndpoint.d] at h1
    simp only [SecantD.cLower]
    linarith
  exact SecantD.actual_minorant hsorted hy hcontained hQ hq hk hcf hkc ht

lemma actual_blocks_lower {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 4) :
    Blocks.block f (total C ga ab) (delta C.theta B) (magnitude C)
      (blocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).P
      (blocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).N i≤
    actualBlocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.m f (total C ga ab)) (Explicit.eta f (total C ga ab)) i := by
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let m := Explicit.m f (total C ga ab)
  have hb := budgets hg ga ab k l m hvar ha hz hs
  have hc := Explicit.source_coefficients f hθ hb.bt_domain
  have hp := Blocks.family_pairs f hθ
  have hcoef := family_block_coefficients hg ga ab f hθ hb.bt_domain
  have hbudget := block_budgets hg ga ab k l m hvar ha hz hs
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      mixedBlock R (Blocks.p f (total C ga ab) j) (Blocks.q f (total C ga ab) j)
        (blocks C hg ga ab k l m j).P (blocks C hg ga ab k l m j).N≤
      PositiveTD.actualPairIncrement (blocks C hg ga ab k l m j) P := by
    have hpos : 0≤(blocks C hg ga ab k l m j).p := by rw [(hcoef j).1]; exact (hp j).1.le
    have hh := PositiveTD.actual_block_minorant hy hP hQ hpos (hbudget j).1 (hbudget j).2
    rwa [(hcoef j).1,(hcoef j).2] at hh
  fin_cases i
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,m] using hordinary 0 hHy (hcontained H)
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,m] using hordinary 1 (P:=(C.point G).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hcontained G)
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,m] using hordinary 2 (P:=(C.point B).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hcontained B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    have hh := actual_D_minorant (hsorted D) hDy (hcontained D) hQ
      hc.1 hc.2.2.2.2.1 hc.2.2.2.2.2 hb.de_domain (original_error_bound hvar hn T)
    simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,blocks,Blocks.p,Blocks.q,Explicit.gamma,Explicit.c,Explicit.sec,
      NegativeELargeA.secant,magnitude,NegativeDEPositiveTD.Source.magnitude,
      Block.P,Block.N,tilted,k,l,m] using hh

lemma stress_nonpositive {C : SignedCycle} (hg ga ab : Bool) {k l m eta : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0≤ m)
    (hc : 0≤tilted m eta (delta C.theta B))
    (hs : magnitude C∈Icc 0 frameCap)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : stress C hg ga ab k l m eta≤0 := by
  have hsec : 0≤1/Real.cos (delta C.theta D) := by
    have hcos := NegativeESecant.cos_pos hs
    have hd : Real.cos (delta C.theta D)=Real.cos (magnitude C) := by
      simp only [magnitude,NegativeDEPositiveTD.Source.magnitude,Real.cos_neg]
    rw [hd]
    exact div_nonneg zero_le_one hcos.le
  have hw (i : Vertex) : 0≤weights C k l m eta i := by
    obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl :
        i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by revert i; decide
    · exact hk
    · exact hl
    · exact hl
    · exact hm
    · exact hc
    · exact hsec
    · exact zero_le_one
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    have h := hfeasible i
    simp only [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] at h
    exact h
  exact mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr hi)

theorem scalar_nonpositive {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f))
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    Explicit.baseline f (aTotal C ga ab) (delta C.theta B) (magnitude C)+
      ∑i,Blocks.block f (total C ga ab) (delta C.theta B) (magnitude C)
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).P
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab)) i).N i≤0 := by
  have hb := budgets hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
    (Explicit.m f (total C ga ab)) hvar ha hz hs
  have hc := Explicit.source_coefficients f hθ hb.bt_domain
  have hl : 0≤Explicit.l f (total C ga ab) := hc.2.2.1.le
  have hm : 0≤Explicit.m f (total C ga ab) := hc.2.2.2.1.le
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    (show aTotal C ga ab∈Icc 0 frameCap from ⟨ha,hb.a_domain.2.trans hb.total_domain.2⟩)
  have hAg := mul_le_mul_of_nonneg_left hA hl
  have hzframe : delta C.theta B∈Icc 0 frameCap := ⟨hz,hb.bt_domain.2.trans hb.total_domain.2⟩
  have hT := tReserve_nonnegative (hcontained T) hQ hm (family_eta_nonnegative f hθ) hzframe
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower hg ga ab f hsorted hcontained hQ hHy hGy hBy hDy hvar ha hz hs hθ i)
  have hcos : Real.cos (delta C.theta D)≠0 := by
    have hd : Real.cos (delta C.theta D)=Real.cos (magnitude C) := by
      simp only [magnitude,NegativeDEPositiveTD.Source.magnitude,Real.cos_neg]
    rw [hd]
    exact (NegativeESecant.cos_pos hb.de_domain).ne'
  have hidentity := decomposition C hg ga ab (Explicit.k f (total C ga ab))
    (Explicit.l f (total C ga ab)) (Explicit.m f (total C ga ab))
    (Explicit.eta f (total C ga ab)) hflat hcos
  have hbase := baseline_identity ga ab f hb.de_domain
  have haT : aTotal C ga ab=PairedE.total ga ab (delta C.theta G) (delta C.theta A) := rfl
  rw [←haT] at hAg
  have hrot : 0≤tilted (Explicit.m f (total C ga ab)) (Explicit.eta f (total C ga ab))
      (delta C.theta B) := by
    change 0≤Explicit.c f (total C ga ab) (delta C.theta B)
    have h1 := hc.2.2.2.2.1.1
    have h0 : (0:ℝ)≤SecantD.PositiveEndpoint.d := by norm_num [SecantD.PositiveEndpoint.d]
    exact h0.trans h1
  have hk0 : 0≤Explicit.k f (total C ga ab) := by linarith [hc.1.1]
  have hupper := stress_nonpositive hg ga ab hk0 hl hm hrot hb.de_domain hfeasible
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
end
end
end

section
/-!
## The negative-DE3 / nonnegative-BT3 scalar exclusion

The two closed total-angle families cover the whole variation interval (`family_cover`). Every
A/BT split and DE magnitude is covered, and the fourth block is the signed TD0 singleton
(`scalar_positive`). No scalar endpoint or support branch is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Scalar
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem family_cover {θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    ∃f : Family,θ∈Icc (Explicit.left f) (Explicit.right f) := by
  by_cases h : θ≤1/6
  · exact ⟨.low,⟨hθ.1,h⟩⟩
  · exact ⟨.high,⟨(lt_of_not_ge h).le,hθ.2⟩⟩

theorem scalar_positive (f : Family) {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.baseline f a z s+
      ∑i,Blocks.block f (a+z) z s (P i) (N i) i := by
  cases f
  · exact Low.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact High.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Scalar
end
end
end

section
/-!
## The negative-DE3 / nonnegative-BT3 exclusion

The scalar family is selected by the A/BT total. Both HG owners, all four A selections and every
sign of the single selected A errors are covered. The TD0 and EH0 angles have no sign
restriction. The flatness of a core E follows from the EH0 separator itself (`original_flat`),
without moving E or changing a witness. The radius stays the same throughout.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

theorem original_flat_false {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hb0 := budgets hg ga ab 1 1 1 hvar ha hz hs
  obtain ⟨f,hθ⟩ := Scalar.family_cover hb0.total_domain
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let m := Explicit.m f (total C ga ab)
  have hb := budgets hg ga ab k l m hvar ha hz hs
  have hn := scalar_nonpositive hg ga ab f hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hz hs hflat hθ hfeasible
  have hp := Scalar.scalar_positive f
    (a:=aTotal C ga ab) (z:=delta C.theta B) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l m i).P)
    (fun i => (blocks C hg ga ab k l m i).N) hθ ha hz hb.de_domain
    (fun i => (blocks C hg ga ab k l m i).P_nonneg)
    (fun i => (blocks C hg ga ab k l m i).N_nonneg)
    hb.positive_bound hb.negative_bound hb.balance
  exact (not_le_of_gt hp) hn

/-- A feasible EH0 puts a core E on the flat part `a = 7/12`. -/
lemma original_flat {Q : ℝ} {C : SignedCycle}
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hEH : C.Feasible E 0) : (C.point E).a=7/12 := by
  have hh : quarterFeasible (C.point E) (C.point H) (delta C.theta E) 0 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  exact (NegativeCoreE.secondary_flat (hsorted E) hEy hEc
    (hsorted H) (hcontained H) hQ hh).1

theorem original {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have hEH : C.Feasible E 0 := by simpa [owners,E] using hfeasible E
  exact original_flat_false hg ga ab hsorted hcontained hQ hHy hGy hBy hDy
    hvar ha hz hs (original_flat hsorted hcontained hQ hEy hEc hEH) hfeasible

/-- For either HG owner, with no sign restriction on TD0 or EH0. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 3) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  apply original hg ga ab hsorted hcontained hQ hHy hGy hBy hDy hEy hEc
    hvar ha hz hs
  intro i
  fin_cases i
  · simpa [owners,H] using hhg
  · simpa [owners,G] using hGA
  · simpa [owners,A] using hAB
  · simpa [owners,B] using hBT
  · simpa [owners,T] using hTD
  · simpa [owners,D] using hDE
  · simpa [owners,E] using hEH

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
end
end
end

section
/-!
## Actual four-block stress for core DE3, BT2 and arbitrary TD0

The secant-D minorant is taken at the actual negative DE3 angle.
B still owns BT2, including its independent signed error. The two
positive A arguments are only removed through their exact signed
primary total. No T support bound or nonexistent TD2 owner is used.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDETD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev Family := NegativeDEPositiveBT.Family

lemma source_pair_coefficients {C : SignedCycle} {hg : Fin 4}
    (ga ab : Bool) {k l m : ℝ} (hk : k≤1) (hl : k≤l)
    (i : Fin 3) :
    (blocks C hg ga ab k l m i.castSucc).p=
      (![k,k,min l m] : Fin 3→ℝ) i ∧
    (blocks C hg ga ab k l m i.castSucc).q=
      (![1,l,max l m] : Fin 3→ℝ) i :=
  block_coefficients ga ab hk hl i

/-- The same scalar baseline at BT3 zero tilt, without selecting BT3. -/
theorem baseline_identity {C : SignedCycle} {a s : ℝ}
    (hs : s=magnitude C) (hsm : s∈Icc 0 frameCap)
    (k l m : ℝ) :
    base C k l m+l*TwoPositive.ASupport.charge a =
      k+2*l+2*m+(1/Real.cos s)+1-fullSupport 1 k-
        fullSupport k l-fullSupport l m-
        PositiveBT3.sortedSupport (1/Real.cos s) m+
        (13/12)*Real.tan s-((1/Real.cos s)-1)/2+
        l*TwoPositive.ASupport.charge a := by
  subst hs
  have hid := NegativeDEPositiveTD.Source.deCorrection_identity hsm
  have he : Real.cos (delta C.theta D)=Real.cos (magnitude C) := by
    simp [magnitude,NegativeDEPositiveBT.Source.magnitude,NegativeDEPositiveTD.Source.magnitude]
  simp only [base,deCorrection,NegativeDEPositiveBT.Source.deCorrection]
  rw [hid,he]
  simp only [NegativeDEPositiveTD.Explicit.K,NegativeDEPositiveTD.Explicit.secant,
    magnitude,NegativeDEPositiveBT.Source.magnitude]
  ring

lemma high_scalar_baseline {C : SignedCycle} (ga ab : Bool)
    (hs : magnitude C∈Icc 0 frameCap) :
    base C (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab))+
      NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab)*
        TwoPositive.ASupport.charge (aTotal C ga ab)=
    NegativeDEPositiveBT.Explicit.baseline .high (aTotal C ga ab) 0 (magnitude C) := by
  rw [baseline_identity (a:=aTotal C ga ab) (s:=magnitude C) rfl hs]
  simp only [NegativeDEPositiveBT.Explicit.baseline,NegativeDEPositiveBT.Explicit.c,
    NegativeDEPositiveBT.Explicit.sec,NegativeELargeA.secant,NegativeDEPositiveBT.Explicit.K,
    Real.cos_zero,Real.sin_zero,mul_zero,add_zero,mul_one,sub_zero,edgeWidth_zero]
  ring

/-- Three ordinary blocks are protected by circle support; the fourth
retains the actual secant-D inequality across its sorted support switch. -/
theorem high_blocks_lower {Q : ℝ} {C : SignedCycle}
    (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta D≤0)
    (hθ : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (i : Fin 4) :
    NegativeDEPositiveBT.Blocks.block .high (aTotal C ga ab) 0 (magnitude C)
      (blocks C hg ga ab
        (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
        (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
        (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).P
      (blocks C hg ga ab
        (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
        (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
        (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).N i≤
    actualBlocks C hg ga ab
      (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i := by
  have hz : (0:ℝ)∈Icc 0 (aTotal C ga ab) := ⟨le_rfl,ha⟩
  obtain ⟨hk,hkl,hl,hm,hc,hkc⟩ :=
    NegativeDEPositiveBT.Explicit.source_coefficients .high hθ hz
  have hb := budgets hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) hvar ha hs
  have hordinary (j : Fin 3) {P : SignedPoint}
      (hy : 0≤P.y) (hP : P.Contained Q) :
      NegativeDEPositiveBT.Blocks.block .high (aTotal C ga ab) 0 (magnitude C)
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc).P
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc).N j.castSucc≤
      PositiveTD.actualPairIncrement (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc) P := by
    have hpair := source_pair_coefficients (C:=C) (hg:=hg) ga ab
      (m:=NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) (by linarith [hk.2]) hkl j
    have hp' : NegativeDEPositiveBT.Explicit.p .high (aTotal C ga ab) j=
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc).p :=
      hpair.1.symm
    have hq' : NegativeDEPositiveBT.Explicit.q .high (aTotal C ga ab) j=
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) j.castSucc).q :=
      hpair.2.symm
    have hpn := (NegativeDEPositiveBT.Explicit.family_pairs .high hθ j).1.le
    rw [hp'] at hpn
    rw [NegativeDEPositiveBT.Blocks.block_ordinary,hp',hq']
    exact PositiveTD.actual_block_minorant hy hP hQ hpn
      (block_budgets hg ga ab _ _ _ hvar ha hs j.castSucc).1
      (block_budgets hg ga ab _ _ _ hvar ha hs j.castSucc).2
  fin_cases i
  · exact hordinary 0 hHy (hcontained H)
  · exact hordinary 1
      (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hcontained G)
  · exact hordinary 2
      (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hcontained B)
  · have hn : negativeVariation C.theta≤frameCap := by
      rw [←variations_equal]; exact hvar
    have ht : |delta C.theta T|≤frameCap := original_error_bound hvar hn T
    have hD := NegativeDEPositiveBT.Source.actual_D_minorant
      (hsorted D) hDy (hcontained D) hQ hk hc hkc hb.de_domain ht
    have hc0 : NegativeDEPositiveBT.Explicit.c .high (aTotal C ga ab) 0=
        NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab) := by
      simp [NegativeDEPositiveBT.Explicit.c]
    have hsec : NegativeDEPositiveBT.Explicit.sec (magnitude C)=
        1/Real.cos (delta C.theta D) := by
      simp [NegativeELargeA.secant,magnitude,NegativeDEPositiveBT.Source.magnitude,
        NegativeDEPositiveTD.Source.magnitude]
    have hV : NegativeDEPositiveBT.Explicit.V .high (aTotal C ga ab) 0
        (negativePart (delta C.theta T))=
        V R (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab)) 1
          (negativePart (delta C.theta T)) := rfl
    change NegativeDEPositiveBT.Blocks.block .high (aTotal C ga ab) 0 (magnitude C)
        (positivePart (delta C.theta T)+positivePart 0)
        (negativePart (delta C.theta T)+negativePart 0) 3≤
      SecantD.actualIncrement (1/Real.cos (delta C.theta D))
        (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) (delta C.theta T) (C.point D)
    rw [NegativeDEPositiveBT.Blocks.block_D,NegativeDEPositiveBT.Blocks.positive_D,
      NegativeDEPositiveBT.Blocks.negative_D,positivePart_zero,negativePart_zero,add_zero,
      add_zero,hV,NegativeDEPositiveBT.Explicit.gamma,hc0,hsec]
    rw [hc0,hsec] at hD
    linarith

theorem stress_nonpositive {C : SignedCycle} (hg : Fin 4)
    (ga ab : Bool) {k l m : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0≤ m)
    (hs : magnitude C∈Icc 0 frameCap)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) :
    stress C hg ga ab k l m≤0 := by
  have hcos : 0<Real.cos (delta C.theta D) := by
    simpa [magnitude,NegativeDEPositiveTD.Source.magnitude] using
      (show 0<Real.cos (magnitude C) by linarith [(transport_trig hs).1])
  have hw (i : Vertex) : 0≤weights C k l m i := by
    fin_cases i <;> simp [weights] <;> positivity
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hf i
  exact mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr hi)

/-- Original signed BT2/TD0 force yields the scalar nonpositive bound. -/
theorem high_scalar_nonpositive {Q : ℝ} {C : SignedCycle}
    (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (hs : delta C.theta D≤0) (hflat : (C.point E).a=7/12)
    (hhg : hg=0∨hg=2)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) :
    NegativeDEPositiveBT.Explicit.baseline .high (aTotal C ga ab) 0 (magnitude C)+
      ∑i,NegativeDEPositiveBT.Blocks.block .high (aTotal C ga ab) 0 (magnitude C)
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).P
        (blocks C hg ga ab
          (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
          (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).N i≤0 := by
  have ha0 : 0≤aTotal C ga ab := by linarith [ha.1]
  have hbud := budgets hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) hvar ha0 hs
  have hcos : Real.cos (delta C.theta D)≠0 := by
    have he := (transport_trig hbud.de_domain).1
    have hpos : 0<Real.cos (magnitude C) := by linarith [he]
    simpa [magnitude,NegativeDEPositiveBT.Source.magnitude,
      NegativeDEPositiveTD.Source.magnitude] using hpos.ne'
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    high_blocks_lower hg ga ab hsorted hcontained hQ
      hHy hGy hBy hDy hvar ha0 hs ha i)
  have hn : negativeVariation C.theta≤frameCap := by
    rw [←variations_equal]; exact hvar
  have hA : TwoPositive.ASupport.charge (aTotal C ga ab)≤
      PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A) :=
    PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
      (original_error_bound hvar hn G) (original_error_bound hvar hn A) hbud.a_domain
  have hcoef := NegativeDEPositiveBT.Explicit.source_coefficients .high ha
    (show (0:ℝ)∈Icc 0 (aTotal C ga ab) from ⟨le_rfl,ha0⟩)
  have hAl := mul_le_mul_of_nonneg_left hA hcoef.2.2.1.le
  have hi := high_scalar_baseline ga ab hbud.de_domain
  have hd := decomposition C ga ab hhg
    (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) hflat hcos
  have hst := stress_nonpositive hg ga ab
    (k:=NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (l:=NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (m:=NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab))
    (by linarith [hcoef.1.1]) hcoef.2.2.1.le hcoef.2.2.2.1.le hbud.de_domain hf
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDETD0
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDETD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

/-- The owner of BT is B2 here, not the B3 of the scalar certificate; the B2 angle stays in the
masses of B. -/
theorem original_flat_high_false {Q : ℝ} {C : SignedCycle}
    (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (hs : delta C.theta D≤0) (hflat : (C.point E).a=7/12)
    (hhg : hg=0∨hg=2)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  have ha0 : 0≤aTotal C ga ab := by linarith [ha.1]
  have hb := budgets hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) hvar ha0 hs
  have hn := high_scalar_nonpositive hg ga ab
    hsorted hcontained hQ hHy hGy hBy hDy hvar ha hs hflat hhg hf
  have hp := NegativeDEPositiveBT.Scalar.scalar_positive .high
    (a:=aTotal C ga ab) (z:=0) (s:=magnitude C)
    (fun i => (blocks C hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).P)
    (fun i => (blocks C hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).N)
    (by rw [add_zero]; exact ha) ha0 le_rfl hb.de_domain
    (fun i => (blocks C hg ga ab _ _ _ i).P_nonneg)
    (fun i => (blocks C hg ga ab _ _ _ i).N_nonneg)
    (by simpa only [add_zero] using hb.positive_bound)
    hb.negative_bound (by simpa only [add_zero] using hb.balance)
  simp only [add_zero] at hp
  exact (not_le_of_gt hp) hn

theorem original_high_false {Q : ℝ} {C : SignedCycle}
    (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (hs : delta C.theta D≤0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 3) (hEH : C.Feasible E 0) : False := by
  have hflat := NegativeDEPositiveBT.Source.original_flat hsorted hcontained
    hQ hEy hEc hEH
  obtain ⟨hg,hhg,hHG'⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  apply original_flat_high_false hg ga ab hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hs hflat hhg
  intro i
  fin_cases i
  · simpa [owners,H] using hHG'
  · simpa [owners,G] using hGA
  · simpa [owners,A] using hAB
  · simpa [owners,B] using hBT
  · simpa [owners,T] using hTD
  · simpa [owners,D] using hDE
  · simpa [owners,E] using hEH

end SquaresInCircles.Eight.GlobalGA.NegativeDETD0
end
end
end
