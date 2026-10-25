module

public import SquaresInCircles.Eight.Owners.GA.DMinorant
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CurvatureConstants
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowNegativeComparison
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowRanges
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowSeparatedPolynomial
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSecant
public import SquaresInCircles.Eight.Owners.GA.Negative.EHSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData
public import SquaresInCircles.Eight.Owners.PowerTailBounds

/-!
# Eight squares: both original D branches and the low separated alternatives

The short polynomial is transferred to the actual cosine
square before division. The interior comparison uses only coefficient
bounds derived from the original support branch. The resulting scalar
monotonicity retains the original A/TD split and every ordinary angle.
-/

section
/-!
## The low G-pair constants before E-angle reduction

The lower curvature bound is the single degree-sixteen polynomial `reserve` in
`x = 1/6 - θ` (`polynomial_positive`). Its positive higher coefficients and its completed
quadratic are kept as they are.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowG
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryCurvatureBounds OrdinaryNegativeSlope

namespace Certificate
open Polynomial

def k : ℚ[X] := C (1677/2500)-C (3/20)*X+C 4*X^2
def l : ℚ[X] := C (10073/10000)+C (17/10)*X+C (11/5)*X^2
def reserve : ℚ[X] := C (4*(9789/2500))*k^4*l^4-(k^2+l^2)^3

/-- `reserve` is `c₂ (x - 271/5330)² + c₁' x + c₀'` plus `∑ cⱼ xʲ` (`j ≥ 3`) with positive `c₀'`,
`c₁'`, `c₂` and `cⱼ`; `linarith` finds this decomposition. -/
theorem polynomial_positive {x : ℝ} (hx : 0≤x) : 0<aeval x reserve := by
  simp only [reserve,k,l,map_sub,map_mul,map_pow,map_add,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [sq_nonneg (x-271/5330),pow_nonneg hx 3,pow_nonneg hx 4,pow_nonneg hx 5,
    pow_nonneg hx 6,pow_nonneg hx 7,pow_nonneg hx 8,pow_nonneg hx 9,pow_nonneg hx 10,
    pow_nonneg hx 11,pow_nonneg hx 12,pow_nonneg hx 13,pow_nonneg hx 14,pow_nonneg hx 15,
    pow_nonneg hx 16]

theorem original_positive {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<4*qCap*(Explicit.k .low θ)^4*(Explicit.l .low θ)^4-
      ((Explicit.k .low θ)^2+(Explicit.l .low θ)^2)^3 := by
  have hh := polynomial_positive (x:=1/6-θ) (by linarith [hθ.2])
  have hk : aeval (1/6-θ) k=Explicit.k .low θ := by
    simp [k,Explicit.k,Explicit.L]
    ring
  have hl : aeval (1/6-θ) l=Explicit.l .low θ := by
    simp [l,Explicit.l,Explicit.L]
    ring
  simp only [reserve,map_sub,map_mul,map_pow,map_add,aeval_C,eq_ratCast,hk,hl] at hh
  have hq : ((4:ℚ):ℝ)*((9789/2500:ℚ):ℝ)=4*qCap := by norm_num [qCap]
  rw [hq] at hh
  exact hh

end Certificate

/-- Increasing either positive coefficient increases the zero-angle norm slope. This is a scalar
comparison; no witness changes. -/
theorem zero_slope_rectangle {p q P Q : ℝ}
    (hp : 0<p) (hq : 0<q) (hpP : p≤P) (hqQ : q≤Q) :
    NegativeAPositiveTD.Curvature.slopeZero p q≤NegativeAPositiveTD.Curvature.slopeZero P Q := by
  have hP := hp.trans_le hpP
  have hQ := hq.trans_le hqQ
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos hp hq ht
  have hN := pairNorm_pos hP hQ ht
  have hn2 := pairNorm_sq hp hq ht
  have hN2 := pairNorm_sq hP hQ ht
  simp only [pairEnergy,Real.sin_zero,mul_zero,add_zero] at hn2 hN2
  have hp2 := pow_le_pow_left₀ hp.le hpP 2
  have hq2 := pow_le_pow_left₀ hq.le hqQ 2
  have h₁ := mul_le_mul_of_nonneg_left hq2 (mul_nonneg (sq_nonneg p) (sq_nonneg P))
  have h₂ := mul_le_mul_of_nonneg_left hp2 (mul_nonneg (sq_nonneg q) (sq_nonneg Q))
  have hsq : (p*q*pairNorm P Q 0)^2≤(P*Q*pairNorm p q 0)^2 := by
    simp only [mul_pow]
    rw [hn2,hN2]
    nlinarith only [h₁,h₂]
  have hcross : p*q*pairNorm P Q 0≤P*Q*pairNorm p q 0 := by
    nlinarith [mul_pos (mul_pos hp hq) hN,mul_pos (mul_pos hP hQ) hn]
  have hdiv := (div_le_div_iff₀ hn hN).2 hcross
  have hh := mul_le_mul_of_nonneg_left hdiv (Real.sqrt_nonneg qCap)
  simp only [NegativeAPositiveTD.Curvature.slopeZero,pairProduct]
  rw [mul_div_assoc R (p*q),mul_div_assoc R (P*Q)]
  exact hh

theorem zero_slope_upper {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    NegativeAPositiveTD.Curvature.slopeZero (Explicit.k .low θ) (Explicit.l .low θ)<131/100 := by
  have hr := Explicit.low_ranges hθ
  have hh := zero_slope_rectangle (by linarith [hr.1] : 0<Explicit.k .low θ)
    (by linarith [hr.2.2.1] : 0<Explicit.l .low θ) hr.2.1.le hr.2.2.2.1.le
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos (p:=(757/1000:ℝ)) (q:=(1352/1000:ℝ)) (by norm_num) (by norm_num) ht
  have hn2 := pairNorm_sq (p:=(757/1000:ℝ)) (q:=(1352/1000:ℝ)) (by norm_num) (by norm_num) ht
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have he : NegativeAPositiveTD.Curvature.slopeZero (757/1000) (1352/1000)<131/100 := by
    unfold NegativeAPositiveTD.Curvature.slopeZero
    apply quotient_lt_of_square hn (by norm_num)
    rw [mul_pow,hR2,hn2]
    norm_num [pairProduct,pairEnergy,qCap]
  exact hh.trans_lt he

theorem curvature_lower {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (1/2:ℝ)<curvatureZero R (Explicit.k .low θ) (Explicit.l .low θ) := by
  have hr := Explicit.low_ranges hθ
  have hk : 0<Explicit.k .low θ := by linarith [hr.1]
  have hl : 0<Explicit.l .low θ := by linarith [hr.2.2.1]
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos hk hl ht
  have hn2 := pairNorm_sq hk hl ht
  simp only [pairEnergy,Real.sin_zero,mul_zero,add_zero] at hn2
  have hpoly := Certificate.original_positive hθ
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hnum : 0<2*R*(Explicit.k .low θ*Explicit.l .low θ)^2 := by
    have hR : 0<R := by linarith [NegativeAPositiveTD.Curvature.radius_bounds.1]
    positivity
  have hsquare : ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3)^2<
      (2*R*(Explicit.k .low θ*Explicit.l .low θ)^2)^2 := by
    rw [show ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3)^2=
      ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^2)^3 by ring,hn2,
      show (2*R*(Explicit.k .low θ*Explicit.l .low θ)^2)^2=
        4*R^2*(Explicit.k .low θ)^4*(Explicit.l .low θ)^4 by ring,hR2]
    generalize qCap = Q at hpoly ⊢
    linarith only [hpoly]
  have hcross : (pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3<
      2*R*(Explicit.k .low θ*Explicit.l .low θ)^2 :=
    lt_of_pow_lt_pow_left₀ 2 hnum.le hsquare
  unfold curvatureZero
  apply (lt_div_iff₀ (pow_pos hn 3)).2
  dsimp [pairProduct]
  generalize R = R0 at hcross ⊢
  linarith only [hcross]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowG
end
end
end

section
/-!
## The positive-surplus endpoint in the low negative-DE family

The two fixed-pair slope bounds are proved by positive
squaring at their stated endpoints. The larger-s D estimate applies
only on the diagonal branch; the interior branch retains its actual
smaller coefficient bound. The support transition is the original one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowPositive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.PositiveSlope
open Polynomial PositiveTD.Certificate

def slopeAngle : Bool → ℚ | false => 7/10 | true => 1/2
def slopeAllowance : Bool → ℚ | false => 571/500 | true => 519/500

def slopeLeft (short : Bool) : ℚ :=
  (169/125)*(C10.eval (slopeAngle short)-S9.eval (slopeAngle short))+slopeAllowance short
def slopeRight (short : Bool) : ℚ :=
  Rbar*(169/125)*(233/125)*C12.eval (slopeAngle short)
def slopeRadicand (short : Bool) : ℚ :=
  (169/125)^2+(233/125)^2+2*(169/125)*(233/125)*S11.eval (slopeAngle short)

theorem slope_square_certificate (short : Bool) :
    0<slopeLeft short ∧ 0≤ slopeRight short ∧
      (slopeRight short)^2<(slopeLeft short)^2*slopeRadicand short := by
  cases short <;>
    norm_num [slopeLeft,slopeRight,slopeRadicand,slopeAngle,slopeAllowance,
      Rbar,C10,C12,C4,S9,S11,S5]

theorem fixed_endpoint (short : Bool) :
    -(slopeAllowance short:ℝ)<Ud pMax qMax (slopeAngle short:ℝ) := by
  let t : ℝ := slopeAngle short
  have ht : t∈Icc 0 frameCap := by cases short <;> norm_num [t,slopeAngle,frameCap]
  have hp : 0<pMax := by norm_num [pMax]
  have hq : 0<qMax := by norm_num [qMax]
  have hn := pairNorm_pos hp hq (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hn2 := pairNorm_sq hp hq (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have htay := taylor_bounds ht
  have heval (P : ℚ[X]) : aeval t P=((P.eval (slopeAngle short):ℚ):ℝ) :=
    Certificate.eval_rat P (slopeAngle short)
  have hA : (slopeRadicand short:ℝ)≤(pairNorm pMax qMax t)^2 := by
    have hs := htay.2.1
    rw [heval] at hs
    rw [hn2]
    simp only [slopeRadicand,pairEnergy,pairProduct,pMax,qMax]
    push_cast
    linarith only [hs]
  have hL : 0<(slopeLeft short:ℝ) := by exact_mod_cast (slope_square_certificate short).1
  have hM : 0≤(slopeRight short:ℝ) := by exact_mod_cast (slope_square_certificate short).2.1
  have hsq : (slopeRight short:ℝ)^2<
      (slopeLeft short:ℝ)^2*(slopeRadicand short:ℝ) := by
    exact_mod_cast (slope_square_certificate short).2.2
  have hscaled := mul_le_mul_of_nonneg_left hA (sq_nonneg (slopeLeft short:ℝ))
  have hcross : (slopeRight short:ℝ)<(slopeLeft short:ℝ)*pairNorm pMax qMax t := by
    nlinarith [mul_pos hL hn]
  have hnum : R*pMax*qMax*Real.cos t≤(slopeRight short:ℝ) := by
    have hcos : 0≤Real.cos t := by linarith [(transport_trig ht).1]
    have hh := mul_le_mul radius_le_Rbar htay.2.2.2.2.2 hcos
      (by norm_num [Rbar] : (0:ℝ)≤(Rbar:ℝ))
    rw [heval] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤169/125*(233/125) by norm_num)
    simp only [slopeRight,pMax,qMax,Rbar] at hh' ⊢
    push_cast at hh' ⊢
    generalize R = R0 at hh' ⊢
    linarith only [hh']
  have hlinear : (slopeLeft short:ℝ)≤
      pMax*(Real.cos t-Real.sin t)+(slopeAllowance short:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left
      (sub_le_sub htay.2.2.2.2.1 htay.2.2.1) hp.le
    rw [heval,heval] at hh
    simp only [slopeLeft,pMax] at hh ⊢
    push_cast
    linarith only [hh]
  have hdiv : R*pMax*qMax*Real.cos t/pairNorm pMax qMax t<(slopeLeft short:ℝ) :=
    (div_lt_iff₀ hn).2 (hnum.trans_lt hcross)
  have hdiv' : R*(pMax*qMax*Real.cos t/pairNorm pMax qMax t)<(slopeLeft short:ℝ) := by
    have e : R*(pMax*qMax*Real.cos t/pairNorm pMax qMax t)=
        R*pMax*qMax*Real.cos t/pairNorm pMax qMax t := by ring
    rw [e]
    exact hdiv
  change -(slopeAllowance short:ℝ)<Ud pMax qMax t
  simp only [Ud,mixedPDerivative,normD1,pairProduct,sub_zero]
  generalize R = R0 at hdiv' ⊢
  generalize pMax = P0 at hlinear hdiv' ⊢
  generalize qMax = Q0 at hdiv' ⊢
  linarith only [hlinear,hdiv']

theorem derivative_lower (short : Bool) {p q t : ℝ}
    (hp : 0<p) (hq : 0<q) (hpP : p≤pMax) (hqQ : q≤qMax)
    (ht : t∈Icc 0 (slopeAngle short:ℝ)) :
    -(slopeAllowance short:ℝ)<Ud p q t := by
  have hend : (slopeAngle short:ℝ)∈Icc 0 frameCap := by
    cases short <;> norm_num [slopeAngle,frameCap]
  have htf : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hend.2⟩
  have hfixed := Ud_antitone (p:=pMax) (q:=qMax)
    (by norm_num [pMax]) (by norm_num [pMax,qMax])
    (by norm_num [pMax,qMax]) htf hend ht.2
  exact (fixed_endpoint short).trans_le
    (hfixed.trans (coefficient_comparison hp hq hpP hqQ htf))

theorem diagonal_late {s : ℝ} (hs : s∈Icc (1/2:ℝ) frameCap) :
    (1157/1000:ℝ)<LowD.diagonalFirst s := by
  have hsf : s∈Icc 0 frameCap := ⟨by linarith [hs.1],hs.2⟩
  have ht := trig_bracket (l:=(1/2:ℝ)) (u:=frameCap)
    (by norm_num) (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hs
  have hy : (479/1000:ℝ)≤Real.sin s := by norm_num at ht; linarith [ht.1]
  have hsin := (transport_trig hsf).2.2.1
  have hbound := mul_le_mul_of_nonneg_right
    (show GlobalGA.Secondary.diagonal-1/2≤2/5 by linarith [diagonal_bounds.2]) hsin
  have hinc := mul_nonneg (sub_nonneg.mpr hy)
    (show 0≤(1157/1000)*(Real.sin s+479/1000)-2/5 by linarith)
  change (1157/1000:ℝ)<
    (13/12-(GlobalGA.Secondary.diagonal-1/2)*Real.sin s)/Real.cos s^2
  apply (lt_div_iff₀ (sq_pos_of_pos (NegativeESecant.cos_pos hsf))).2
  nlinarith [Real.sin_sq_add_cos_sq s]

theorem diagonal_pure_derivative {θ z s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ)
    (hs : s∈Icc θ frameCap) (i : Fin 3) :
    0<LowD.diagonalFirst s+
      Ud (Explicit.p .low θ z i) (Explicit.q .low θ z i) (s-θ) := by
  have hp := LowRanges.pairs hθ hz i
  have hq := hp.1.trans_le hp.2.1
  have hsf : s∈Icc 0 frameCap := ⟨hθ.1.trans hs.1,hs.2⟩
  by_cases hsmall : s≤1/2
  · have hu := derivative_lower true hp.1 hq hp.2.2.2.1 hp.2.2.2.2
      (show s-θ∈Icc 0 (slopeAngle true:ℝ) by
        norm_num [slopeAngle]; exact ⟨by linarith [hs.1],by linarith [hθ.1]⟩)
    have hd := LowD.diagonal_derivative_lower hsf
    norm_num [slopeAllowance,LowD.M] at hu hd
    linarith
  · have hu := derivative_lower false hp.1 hq hp.2.2.2.1 hp.2.2.2.2
      (show s-θ∈Icc 0 (slopeAngle false:ℝ) by
        norm_num [slopeAngle,frameCap] at hs ⊢
        exact ⟨by linarith [hs.1],by linarith [hθ.1,hs.2]⟩)
    have hd := diagonal_late ⟨(lt_of_not_ge hsmall).le,hs.2⟩
    norm_num [slopeAllowance] at hu
    linarith

theorem full_pure_derivative {θ z s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ)
    (hs : s∈Icc θ frameCap) (hint : Explicit.c .low θ≤LowD.sec s) (i : Fin 3) :
    0<secantGainDeriv qCap (Explicit.c .low θ) s+
      Ud (Explicit.p .low θ z i) (Explicit.q .low θ z i) (s-θ) := by
  have hp := LowRanges.pairs hθ hz i
  have hsf : s∈Icc 0 frameCap := ⟨hθ.1.trans hs.1,hs.2⟩
  have hu := OrdinarySlope.positive_derivative_whole hp.1 hp.2.1 hp.2.2.1
    (show s-θ∈Icc 0 frameCap from ⟨by linarith [hs.1],by linarith [hs.2,hθ.1]⟩)
  have hq := LowRanges.interior_q_upper hθ hz hsf hint i
  have hd := LowD.full_derivative_lower
    (show (519/500:ℝ)≤Explicit.c .low θ by linarith [(Explicit.low_ranges hθ).2.2.2.2.1]) hsf
  norm_num [LowD.M] at hd
  linarith

theorem positive_surplus_monotone {θ z : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    MonotoneOn (fun s => LowD.correction (Explicit.c .low θ) s+
      Explicit.U .low θ z i (s-θ)) (Icc θ frameCap) := by
  have hp := LowRanges.pairs hθ hz i
  apply LowD.add_monotone
    (show 1≤Explicit.c .low θ by linarith [(Explicit.low_ranges hθ).2.2.2.2.1]) hθ.1 le_rfl
  · intro s hs
    have hd := (U_hasDerivAt hp.1 (hp.1.trans_le hp.2.1)
      (show s-θ∈Icc 0 frameCap from ⟨by linarith [hs.1],by linarith [hs.2,hθ.1]⟩)).comp s
      ((hasDerivAt_id s).sub_const θ)
    simpa only [Explicit.U,mul_one,Function.comp_def,id] using hd
  · intro s hs _
    exact (diagonal_pure_derivative hθ hz hs i).le
  · intro s hs hint
    exact (full_pure_derivative hθ hz hs hint i).le

/-- The original split and coefficients are unchanged; only the scalar
E-magnitude is compared with its intrinsic equal-angle endpoint. -/
theorem equal_le_positive_surplus {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 (a+z))
    (hs : s∈Icc (a+z) frameCap) (i : Fin 3) :
    Explicit.baseline .low a z (a+z)≤Explicit.baseline .low a z s+
      Explicit.U .low (a+z) z i (s-(a+z)) := by
  have hf : a+z∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hsf : s∈Icc 0 frameCap := ⟨hf.1.trans hs.1,hs.2⟩
  have hh := positive_surplus_monotone hθ hz i ⟨le_rfl,hf.2⟩ hs hs.1
  simp only [sub_self,Explicit.U,U_zero,add_zero] at hh
  rw [LowD.baseline_correction .low a z hf,LowD.baseline_correction .low a z hsf]
  dsimp only [Explicit.U]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowPositive

namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowD
open Candidate Secondary PositiveAngularEnvelope

abbrev diagonalCorrection := diagonalGain

/-- On the intrinsic interval 0 <= s <= a+z <= 1/6 the original D
support is diagonal. This identity also covers both closed endpoints. -/
theorem diagonal_baseline {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 (a+z)) :
    Explicit.baseline .low a z s=Explicit.baseline .low a z 0+diagonalCorrection s := by
  have hsf : s∈Icc 0 frameCap :=
    ⟨hs.1,by norm_num [frameCap]; linarith [hs.2,hθ.2]⟩
  have hc : 1≤Explicit.c .low (a+z) := by
    linarith [(Explicit.low_ranges hθ).2.2.2.2.1]
  have hdiag : sec s≤Explicit.c .low (a+z) := Certificate.low_D_diagonal hθ hs
  rw [baseline_correction .low a z hsf,correction_diagonal hc hsf hdiag]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowD
end
end
end

section
/-!
## The low negative-DE pure-negative alternative

The short-angle G comparison and the
whole-angle B chord reduce the pure-negative alternative to H. The
remaining scalar is concave in the prescribed coordinate x = tan s;
the original A/TD split and every coefficient remain fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowNegative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryNegativeEnvelope PairNormCalculus OrdinaryCurvatureBounds

theorem H_endpoint_constants :
    shapeC0q R (757/1000)<72/125 ∧ NegativeAPositiveTD.Curvature.shapeD0q (757/1000)<239/200 := by
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  constructor
  · unfold shapeC0q
    apply quotient_lt_of_square (pow_pos (shape_pos _) 3) (by norm_num)
    rw [show ((shape (757/1000:ℝ))^3)^2=((shape (757/1000:ℝ))^2)^3 by ring,shape_sq,
      mul_pow,hR2]
    norm_num [qCap]
  · unfold NegativeAPositiveTD.Curvature.shapeD0q
    apply quotient_lt_of_square (shape_pos _) (by norm_num)
    rw [mul_pow,shape_sq,hR2]
    norm_num [qCap]

theorem H_constants {k : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000)) :
    curvatureZero R k 1<72/125 ∧ NegativeAPositiveTD.Curvature.slopeZero k 1<239/200 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hk1 : k≤1 := by linarith [hk.2]
  obtain ⟨_,_,hC,_⟩ := curvature_constants_normalize (R:=R) hk0 (by norm_num : (0:ℝ)<1)
  obtain ⟨_,hD⟩ := NegativeAPositiveTD.Curvature.constants_normalize hk0 (by norm_num : (0:ℝ)<1)
  have hCbound := (NegativeAPositiveTD.Curvature.shapeC0q_monotone ⟨hk0.le,hk1⟩
    (by norm_num : (757/1000:ℝ)∈Icc 0 1) hk.2).trans_lt H_endpoint_constants.1
  have hDbound := (NegativeAPositiveTD.Curvature.shapeD0q_monotone ⟨hk0.le,hk1⟩
    (by norm_num : (757/1000:ℝ)∈Icc 0 1) hk.2).trans_lt H_endpoint_constants.2
  simp only [div_one,one_mul] at hC hD
  exact ⟨by rw [hC]; exact hCbound,by rw [hD]; exact hDbound⟩

theorem H_slope {k t : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000))
    (ht : t∈Icc 0 frameCap) : Vd R k 1 t<239/200 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hh := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hk0
    (by linarith [hk.2] : k≤1) (by linarith [hk.1] : 1≤2*k)
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) ht ht.1
  have he : Vd R k 1 0=NegativeAPositiveTD.Curvature.slopeZero k 1 := by
    simp only [Vd,mixedNDerivative,NegativeAPositiveTD.Curvature.slopeZero,normD1,
      Real.sin_zero,Real.cos_zero,mul_zero,zero_add,sub_self,mul_one]
    ring
  rw [he] at hh
  exact hh.trans_lt (H_constants hk).2

theorem H_tangent {k t : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000))
    (ht : t∈Icc 0 frameCap) : V R k 1 t≤(239/200)*t := by
  have hh := V_tangent_zero (by linarith [hk.1] : 0<k)
    (by linarith [hk.2] : k≤1) (by linarith [hk.1] : 1≤2*k) ht
  have hd := H_slope hk (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  exact hh.trans (mul_le_mul_of_nonneg_right hd.le ht.1)

theorem B_dominates_H {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .low θ) 1 t≤Explicit.V .low θ z 2 t := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hlm := hr.2.2.2.2.2.2.1.trans hm.1
  have hp := LowRanges.pairs hθ hz 2
  have hh := H_tangent ⟨hr.1.le,hr.2.1.le⟩ ht
  have hb := V_chord_lower hp.1 hp.2.1 hp.2.2.1 ht
  have hlower : 1≤Explicit.p .low θ z 2 := by
    simpa [Explicit.p,min_eq_left hlm] using hr.2.2.1.le
  have hmul := mul_le_mul_of_nonneg_right hlower ht.1
  change _≤Explicit.V .low θ z 2 t at hb
  linarith only [hh,hb,hmul,ht.1]

theorem pure_comparison {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 θ) (i : Fin 3) :
    V R (Explicit.k .low θ) 1 t≤Explicit.V .low θ z i t := by
  have hr := Explicit.low_ranges hθ
  have htf : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2,hθ.2]⟩
  fin_cases i
  · simp [Explicit.V,Explicit.p,Explicit.q]
  · have hh := NegativeAPositiveTD.LowNegativeComparison.larger_coefficient
      (by linarith [hr.1] : 0<Explicit.k .low θ)
      (by linarith [hr.2.1] : Explicit.k .low θ≤1)
      hr.2.2.1.le hr.2.2.2.2.2.2.2.le
      (show t∈Icc 0 (1/5:ℝ) from ⟨ht.1,by linarith [ht.2,hθ.2]⟩)
    simpa [Explicit.V,Explicit.p,Explicit.q] using hh
  · exact B_dominates_H hθ hz htf

theorem tangent_cut {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Real.tan θ<169/1000 := by
  have hframe : θ∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hL : (1/6:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hm := NegativeAPositiveTD.SecantCoordinate.tan_monotone hframe hL hθ.2
  have hc := Real.one_sub_sq_div_two_le_cos (x:=(1/6:ℝ))
  have hs := sin_upper_five (show (0:ℝ)≤1/6 by norm_num)
  have he : Real.tan (1/6:ℝ)<169/1000 := by
    rw [Real.tan_eq_sin_div_cos]
    exact (div_lt_iff₀ (NegativeESecant.cos_pos hL)).2 (by norm_num at hc hs; linarith)
  exact hm.trans_lt he

def scalar (B k θ x : ℝ) : ℝ :=
  B+(13/12)*x-(GlobalGA.Secondary.diagonal-1/2)*(NegativeAPositiveTD.SecantCoordinate.radical 1 x-1)+
    V R k 1 (θ-Real.arctan x)
def first (k θ x : ℝ) : ℝ :=
  13/12-(GlobalGA.Secondary.diagonal-1/2)*x/NegativeAPositiveTD.SecantCoordinate.radical 1 x-
    Vd R k 1 (θ-Real.arctan x)/(1+x^2)
def second (k θ x : ℝ) : ℝ :=
  -(GlobalGA.Secondary.diagonal-1/2)/(NegativeAPositiveTD.SecantCoordinate.radical 1 x)^3+
    NegativeAPositiveTD.SecantCoordinate.negativeSecond k 1 θ x

theorem scalar_hasDerivAt {B k θ x : ℝ} (hk : 0<k)
    (hd : θ-Real.arctan x∈Icc 0 frameCap) :
    HasDerivAt (scalar B k θ) (first k θ x) x := by
  have hb := ((hasDerivAt_id x).const_mul (13/12:ℝ)).const_add B
  have hw := ((NegativeAPositiveTD.SecantCoordinate.radical_hasDerivAt (A:=1) (x:=x) (by norm_num)).sub_const 1)
    |>.const_mul (GlobalGA.Secondary.diagonal-1/2)
  have hv := (V_hasDerivAt (R:=R) hk (by norm_num : (0:ℝ)<1) hd).comp x
    ((Real.hasDerivAt_arctan x).const_sub θ)
  convert (hb.sub hw).add hv using 1
  · funext y
    simp only [scalar,Pi.add_apply,Pi.sub_apply,Function.comp_apply,id]
  · simp only [first]
    ring

theorem first_hasDerivAt {k θ x : ℝ} (hk : 0<k)
    (hd : θ-Real.arctan x∈Icc 0 frameCap) :
    HasDerivAt (first k θ) (second k θ x) x := by
  have hbase := (NegativeAPositiveTD.SecantCoordinate.radicalFirst_hasDerivAt (A:=1) (x:=x) (by norm_num))
    |>.const_mul (GlobalGA.Secondary.diagonal-1/2)
  have hv := NegativeAPositiveTD.SecantCoordinate.pureFirst_hasDerivAt (l:=0) (r:=0) hk (by norm_num : (0:ℝ)<1) hd
  simp only [NegativeAPositiveTD.SecantCoordinate.pureSecond,zero_mul,zero_add] at hv
  convert (hbase.const_sub (13/12:ℝ)).add hv using 1
  · funext y
    simp only [first,Pi.add_apply,NegativeAPositiveTD.SecantCoordinate.pureFirst]
    ring
  · simp only [second]
    ring

theorem second_negative {k θ x : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000))
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hx : x∈Icc 0 (Real.tan θ)) : second k θ x<0 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hframe : θ∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hs := NegativeAPositiveTD.SecantCoordinate.arctan_interval hframe hx
  have hd : θ-Real.arctan x∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1,hframe.2]⟩
  have hdL : θ-Real.arctan x≤1/6 := by linarith [hθ.2,hs.1]
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=θ-Real.arctan x)
  have hd2 := pow_le_pow_left₀ hd.1 hdL 2
  have hcurv := curvature_negative_upper (Real.sqrt_nonneg qCap) hk0
    (by norm_num : (0:ℝ)<1)
    (show -(θ-Real.arctan x)∈Icc (-frameCap) 0 from ⟨by linarith [hd.2],by linarith [hd.1]⟩)
  have hC := (H_constants hk).1
  have hV := H_slope hk hd
  have hproduct := mul_le_mul_of_nonneg_left hV.le hx.1
  have hxU : x<169/1000 := hx.2.trans_lt (tangent_cut hθ)
  have hnum : curvature R k 1 (-(θ-Real.arctan x))-Real.cos (θ-Real.arctan x)+
      2*x*Vd R k 1 (θ-Real.arctan x)<0 := by nlinarith
  have hnegative : NegativeAPositiveTD.SecantCoordinate.negativeSecond k 1 θ x<0 := by
    unfold NegativeAPositiveTD.SecantCoordinate.negativeSecond
    simp only [one_mul]
    exact div_neg_of_neg_of_pos hnum (by positivity)
  have hdiag : 0≤(GlobalGA.Secondary.diagonal-1/2)/(NegativeAPositiveTD.SecantCoordinate.radical 1 x)^3 := by
    exact div_nonneg (by linarith [diagonal_bounds.1])
      (pow_nonneg (Real.sqrt_nonneg _) 3)
  dsimp [second]
  rw [neg_div]
  linarith

theorem scalar_concave {B k θ : ℝ} (hk : k∈Icc (2/3:ℝ) (757/1000))
    (hθ : θ∈Icc (0:ℝ) (1/6)) : ConcaveOn ℝ (Icc 0 (Real.tan θ)) (scalar B k θ) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hframe : θ∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hd (x : ℝ) (hx : x∈Icc 0 (Real.tan θ)) : θ-Real.arctan x∈Icc 0 frameCap := by
    have hs := NegativeAPositiveTD.SecantCoordinate.arctan_interval hframe hx
    exact ⟨by linarith [hs.2],by linarith [hs.1,hframe.2]⟩
  exact concave_of_deriv2 (fun x hx => scalar_hasDerivAt hk0 (hd x hx))
    (fun x hx => first_hasDerivAt hk0 (hd x hx))
    (fun x hx => (second_negative hk hθ hx).le)

/-- The endpoint principle is exported before the A/TD split is changed. -/
theorem original_endpoint_lower {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 (a+z)) :
    min (Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) 1 (a+z))
      (Explicit.baseline .low a z (a+z))≤
    Explicit.baseline .low a z s+V R (Explicit.k .low (a+z)) 1 (a+z-s) := by
  have hframe : a+z∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hframe.2⟩
  have hr := Explicit.low_ranges hθ
  have hx : Real.tan s∈Icc 0 (Real.tan (a+z)) :=
    ⟨NegativeAPositiveTD.SecantCoordinate.tan_nonnegative hsf,NegativeAPositiveTD.SecantCoordinate.tan_monotone hsf hframe hs.2⟩
  have hid {t : ℝ} (ht : t∈Icc 0 (a+z)) :
      scalar (Explicit.baseline .low a z 0) (Explicit.k .low (a+z)) (a+z) (Real.tan t)=
        Explicit.baseline .low a z t+V R (Explicit.k .low (a+z)) 1 (a+z-t) := by
    have htf : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hframe.2⟩
    have hc := NegativeESecant.cos_pos htf
    have hrad : NegativeAPositiveTD.SecantCoordinate.radical 1 (Real.tan t)=LowD.sec t := by
      rw [Real.tan_eq_sin_div_cos]
      have hroot := NegativeAPositiveTD.SecantCoordinate.radical_square (A:=1) (x:=Real.sin t/Real.cos t) (by norm_num)
      have hpos := NegativeAPositiveTD.SecantCoordinate.radical_positive (A:=1) (x:=Real.sin t/Real.cos t) (by norm_num)
      have hsquare : (LowD.sec t)^2=1+(Real.sin t/Real.cos t)^2 := by
        dsimp [LowD.sec,NegativeELargeA.secant]
        field_simp [hc.ne']
        nlinarith [Real.sin_sq_add_cos_sq t]
      have hsec : 0<LowD.sec t := div_pos (by norm_num) hc
      nlinarith
    rw [scalar,NegativeAPositiveTD.SecantCoordinate.arctan_tan htf,hrad,LowD.diagonal_baseline hθ ht]
    rw [LowD.diagonalCorrection,
      show LowD.diagonalGain t=NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) t from rfl,
      NegativeESecant.gain_secant _ htf]
    dsimp [LowD.sec,NegativeELargeA.secant,NegativeESecant.K]
    ring
  have hz : (0:ℝ)∈Icc 0 (Real.tan (a+z)) := ⟨le_rfl,NegativeAPositiveTD.SecantCoordinate.tan_nonnegative hframe⟩
  have he : Real.tan (a+z)∈Icc 0 (Real.tan (a+z)) := ⟨hz.2,le_rfl⟩
  have hh := (scalar_concave (B:=Explicit.baseline .low a z 0) ⟨hr.1.le,hr.2.1.le⟩ hθ)
    |>.min_le_of_mem_Icc hz he hx
  have hzero := hid (t:=0) ⟨le_rfl,hθ.1⟩
  have hlast := hid (t:=a+z) ⟨hθ.1,le_rfl⟩
  simp only [Real.tan_zero,sub_zero] at hzero
  simp only [sub_self,V_zero,add_zero] at hlast
  rw [hzero,hlast,hid hs] at hh
  exact hh

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowNegative
end
end
end

section
/-!
## The low negative-DE same-block alternatives

The G same-block term is differentiated at the E magnitude of the cycle, with both signed budgets
kept (`correction_same_monotone`). The H and B terms use the same-block surplus inequalities, zero
mass included (`HB_negative`, `HB_positive`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSame
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds

theorem sine_linear {t : ℝ} (ht : t∈Icc 0 frameCap) : (23/25)*t≤Real.sin t := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) frameCap) (fun x => Real.sin x-(23/25)*x) := by
    have h1 : ∀ x∈Icc (0:ℝ) frameCap,
        HasDerivAt (fun x => Real.sin x-(23/25)*x) (Real.cos x-23/25) x := fun x _ =>
      ((Real.hasDerivAt_sin x).fun_sub ((hasDerivAt_id' x).const_mul (23/25:ℝ))).congr_deriv
        (by ring)
    have h2 : ∀ x∈Icc (0:ℝ) frameCap,
        HasDerivAt (fun x => Real.cos x-23/25) (-Real.sin x) x := fun x _ =>
      (Real.hasDerivAt_cos x).sub_const _
    apply concave_of_deriv2 h1 h2
    intro x hx
    exact neg_nonpos.mpr (transport_trig hx).2.2.1
  have hh := hc.min_le_of_mem_Icc (by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht
  have hcap : 0≤Real.sin frameCap-(23/25)*frameCap := by
    have hs := OrdinaryNegativeEnvelope.cap_sin_lower
    norm_num [frameCap]
    linarith
  simp only [Real.sin_zero,mul_zero,sub_zero,min_eq_left hcap] at hh
  linarith

def ordinary (θ s : ℝ) : ℝ := mixedBlock R (Explicit.k .low θ) (Explicit.l .low θ)
  (frameCap-θ) (frameCap-s)
def ordinaryFirst (θ s : ℝ) : ℝ :=
  Explicit.l .low θ*Real.sin (frameCap-s)-
    R*normD1 (Explicit.k .low θ) (Explicit.l .low θ) (s-θ)

theorem ordinary_hasDerivAt {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 frameCap) : HasDerivAt (ordinary θ) (ordinaryFirst θ s) s := by
  have hr := Explicit.low_ranges hθ
  have hP : frameCap-θ∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hh := (mixedN_hasDerivAt (R:=R) (by linarith [hr.1] : 0<Explicit.k .low θ)
    (by linarith [hr.2.2.1] : 0<Explicit.l .low θ) hP hN).comp s
    ((hasDerivAt_id s).const_sub frameCap)
  convert hh using 1
  · rfl
  · dsimp [ordinaryFirst,mixedNDerivative]
    rw [show frameCap-θ-(frameCap-s)=s-θ by ring]
    ring

theorem combined_derivative_positive {θ s D : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 frameCap)
    (hD : (209/200:ℝ)<D) : 0<D+ordinaryFirst θ s := by
  have hr := Explicit.low_ranges hθ
  have hk : 0<Explicit.k .low θ := by linarith [hr.1]
  have hl : 0<Explicit.l .low θ := by linarith [hr.2.2.1]
  have hkl : Explicit.k .low θ≤Explicit.l .low θ := by linarith [hr.2.1,hr.2.2.1]
  have hqp : Explicit.l .low θ≤2*Explicit.k .low θ := hr.2.2.2.2.2.2.2.le
  have ht : |s-θ|≤frameCap := by
    rw [abs_le]
    constructor <;> norm_num [frameCap] at * <;> linarith [hs.1,hs.2,hθ.1,hθ.2]
  have hn := NegativeAPositiveTD.Curvature.norm_slope_signed_tangent hk hl ht
  have hzero := LowG.zero_slope_upper hθ
  have hC := LowG.curvature_lower hθ
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  by_cases horder : θ≤ s
  · have hcurv := mul_le_mul_of_nonneg_right hC.le (sub_nonneg.mpr horder)
    have hsin := sine_linear hN
    have hlower := mul_le_mul_of_nonneg_right hr.2.2.1.le (transport_trig hN).2.2.1
    have hslope : R*normD1 (Explicit.k .low θ) (Explicit.l .low θ) (s-θ)<
        131/100-(s-θ)/2 := by nlinarith only [hn,hzero,hcurv]
    dsimp [ordinaryFirst]
    norm_num [frameCap] at hsin hN hs
    nlinarith [hθ.2]
  · have hCupper := (NegativeAPositiveTD.Curvature.universal_constants hk hkl hqp).1
    have hCmax : curvatureZero R (Explicit.k .low θ) (Explicit.l .low θ)<1183/1250 := by
      linarith [hr.2.2.2.1]
    have hprod := mul_le_mul hCmax.le
      (show θ-s≤1/6 by linarith [hθ.2,hs.1])
      (show 0≤θ-s by linarith) (by norm_num : (0:ℝ)≤1183/1250)
    have hsin : (127/250:ℝ)<Real.sin (frameCap-s) := by
      have hinterval : frameCap-s∈Icc (8/15:ℝ) frameCap := by
        dsimp [frameCap] at *
        exact ⟨by linarith [hθ.2],hN.2⟩
      have hh := trig_bracket (l:=(8/15:ℝ)) (u:=frameCap)
        (by norm_num) (by norm_num [frameCap]; linarith [Real.pi_gt_three]) hinterval
      norm_num [frameCap] at hh
      linarith [hh.1]
    have hlower := mul_le_mul_of_nonneg_right hr.2.2.1.le (transport_trig hN).2.2.1
    dsimp [ordinaryFirst]
    nlinarith

theorem correction_same_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => LowD.correction (Explicit.c .low θ) s+ordinary θ s)
      (Icc (0:ℝ) frameCap) := by
  have hr := Explicit.low_ranges hθ
  apply LowD.add_monotone
    (show 1≤Explicit.c .low θ by linarith [hr.2.2.2.2.1]) le_rfl le_rfl
    (fun s hs => ordinary_hasDerivAt hθ hs)
  · intro s hs _
    exact (combined_derivative_positive hθ hs (LowD.diagonal_derivative_lower hs)).le
  · intro s hs _
    exact (combined_derivative_positive hθ hs
      (LowD.full_derivative_lower
        (show (519/500:ℝ)≤Explicit.c .low θ by linarith [hr.2.2.2.2.1]) hs)).le

def zeroEnvelope (a z : ℝ) : ℝ :=
  Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) 1 (a+z)+
    Explicit.k .low (a+z)*(PositiveAngularEnvelope.phi (frameCap-(a+z))-1)+
    Explicit.l .low (a+z)*(Real.cos frameCap-Real.cos (a+z))

theorem original_zero_lower {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 (a+z))
    (hs : s∈Icc 0 frameCap) :
    zeroEnvelope a z≤Explicit.baseline .low a z s+ordinary (a+z) s := by
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hm := correction_same_monotone hθ hzero hs hs.1
  have hG := LowNegative.pure_comparison hθ hz ⟨hθ.1,le_rfl⟩ (1:Fin 3)
  have hid : ordinary (a+z) 0=V R (Explicit.k .low (a+z)) (Explicit.l .low (a+z)) (a+z)+
      Explicit.k .low (a+z)*(PositiveAngularEnvelope.phi (frameCap-(a+z))-1)+
      Explicit.l .low (a+z)*(Real.cos frameCap-Real.cos (a+z)) := by
    simp only [ordinary,sub_zero,mixedBlock,V]
    rw [show frameCap-(a+z)-frameCap= -(a+z) by ring]
    ring
  rw [LowD.baseline_correction .low a z hs]
  have hc0 : LowD.correction (Explicit.c .low (a+z)) 0=0 := by
    simp [LowD.correction,LowD.sec,NegativeELargeA.secant]
  dsimp only at hm
  rw [hc0,zero_add,hid] at hm
  simp only [Explicit.V,Explicit.p,Explicit.q,Matrix.cons_val] at hG
  dsimp [zeroEnvelope]
  linarith

theorem HB_negative {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) (i : Fin 3) (hi : i=0∨i=2) :
    Explicit.V .low θ z i (θ-s)≤ mixedBlock R
      (Explicit.p .low θ z i) (Explicit.q .low θ z i) (frameCap-θ) (frameCap-s) := by
  have hp := LowRanges.pairs hθ hz i
  have hr := LowRanges.HB_ratio hθ hz i hi
  have hP : frameCap-θ∈Icc 0 (frameCap-s) :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hs.2]⟩
  have hN : frameCap-s∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2,hs.2],by linarith [hs.1]⟩
  have hpay : Explicit.q .low θ z i*Real.sin (frameCap-s)≤Explicit.p .low θ z i := by
    have htrig := transport_trig hN
    have hh := mul_le_mul hr htrig.2.2.2.1.le htrig.2.2.1
      (show 0≤(3/2)*Explicit.p .low θ z i by linarith [hp.1])
    nlinarith [hp.1]
  have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le hP hN hpay
  simpa only [Explicit.V,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh

theorem HB_positive {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc θ frameCap) (i : Fin 3) (hi : i=0∨i=2) :
    Explicit.U .low θ z i (s-θ)≤ mixedBlock R
      (Explicit.p .low θ z i) (Explicit.q .low θ z i) (frameCap-θ) (frameCap-s) := by
  have hp := LowRanges.pairs hθ hz i
  have hr := LowRanges.HB_ratio hθ hz i hi
  have hP : frameCap-θ∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  have hN : frameCap-s∈Icc 0 (frameCap-θ) := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hh := NegativeAPositiveTD.SameBlock.positive_surplus hp.1.le
    (show Explicit.q .low θ z i≤(17/10)*Explicit.p .low θ z i by nlinarith [hp.1]) hP hN
  simpa only [Explicit.U,show frameCap-θ-(frameCap-s)=s-θ by ring] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSame
end
end
end

section
/-!
## The actual interior-D slope comparison

The stricter coefficient rectangle is
used only after c <= sec s has been obtained at the original E angle.
The quartic gives the quadratic D-slope reserve, and the final cubic is
bounded by the displayed completed square on the whole interval.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds OrdinaryNegativeSlope

def smallRoot (q : ℝ) : ℝ := Real.sqrt ((17/25:ℝ)^2+q^2)
def smallCurvature (q : ℝ) : ℝ := R*(17/25:ℝ)^2*q^2/(smallRoot q)^3

theorem smallRoot_pos (q : ℝ) : 0<smallRoot q := Real.sqrt_pos.mpr (by positivity)
theorem smallRoot_sq (q : ℝ) : (smallRoot q)^2=(17/25:ℝ)^2+q^2 := Real.sq_sqrt (by positivity)
theorem smallRoot_derivative (q : ℝ) : HasDerivAt smallRoot (q/smallRoot q) q := by
  convert (((hasDerivAt_id q).pow 2).const_add ((17/25:ℝ)^2)).sqrt
    (by positivity : (17/25:ℝ)^2+q^2≠0) using 1
  · rfl
  · dsimp [smallRoot]
    ring

theorem smallCurvature_derivative (q : ℝ) :
    HasDerivAt smallCurvature
      (R*(17/25:ℝ)^2*q*(2*(17/25:ℝ)^2-q^2)/(smallRoot q)^5) q := by
  have hr := smallRoot_pos q
  have hs := smallRoot_sq q
  have hh := (((hasDerivAt_id q).pow 2).const_mul (R*(17/25:ℝ)^2)).div
    ((smallRoot_derivative q).pow 3) (pow_ne_zero 3 hr.ne')
  convert hh using 1
  · rfl
  · simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,
      show (3:ℕ)-1=2 from rfl,pow_one]
    field_simp
    linear_combination (-1250*q)*hs

theorem smallCurvature_antitone : AntitoneOn smallCurvature (Icc (1:ℝ) (283/250)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun q _ => (smallCurvature_derivative q).continuousAt.continuousWithinAt)
    (fun q _ => smallCurvature_derivative q)
  intro q hq
  have hsign : 2*(17/25:ℝ)^2-q^2≤0 := by nlinarith [hq.1]
  have hfactor : 0≤R*(17/25:ℝ)^2*q :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by norm_num)) (by linarith [hq.1])
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hfactor hsign)
    (pow_nonneg (smallRoot_pos q).le 5)

theorem curvature_smaller_monotone {p P q : ℝ}
    (hp : 0<p) (hpP : p≤P) (hPq : P≤q) (hq : 0<q) :
    curvatureZero R p q≤curvatureZero R P q := by
  have hP := hp.trans_le hpP
  obtain ⟨_,_,hC,_⟩ := curvature_constants_normalize (R:=R) hp hq
  obtain ⟨_,_,hC',_⟩ := curvature_constants_normalize (R:=R) hP hq
  rw [hC,hC']
  apply mul_le_mul_of_nonneg_left _ hq.le
  exact NegativeAPositiveTD.Curvature.shapeC0q_monotone
    ⟨div_nonneg hp.le hq.le,(div_le_one hq).2 (hpP.trans hPq)⟩
    ⟨div_nonneg hP.le hq.le,(div_le_one hq).2 hPq⟩
    ((div_le_div_iff_of_pos_right hq).2 hpP)

theorem interior_constants {p q : ℝ} (hp : 0<p) (hpU : p≤17/25)
    (hq : q∈Icc (1:ℝ) (283/250)) :
    NegativeAPositiveTD.Curvature.slopeZero p q<577/500 ∧ curvatureZero R p q<259/500 := by
  have hq0 : 0<q := by linarith [hq.1]
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hD := LowG.zero_slope_rectangle hp hq0 hpU hq.2
  have hDend : NegativeAPositiveTD.Curvature.slopeZero (17/25) (283/250)<577/500 := by
    have hn := pairNorm_pos (p:=(17/25:ℝ)) (q:=(283/250:ℝ)) (by norm_num) (by norm_num) ht
    have hn2 : (pairNorm (17/25:ℝ) (283/250) 0)^2=(17/25:ℝ)^2+(283/250)^2 := by
      rw [pairNorm,Real.sin_zero,mul_zero,add_zero,Real.sq_sqrt (by positivity)]
    unfold NegativeAPositiveTD.Curvature.slopeZero
    apply quotient_lt_of_square hn (by norm_num)
    rw [hn2,mul_pow,hR2,pairProduct]
    norm_num [qCap]
  have hC := curvature_smaller_monotone hp hpU (by linarith [hq.1] : (17/25:ℝ)≤q) hq0
  have hCeq (q : ℝ) : curvatureZero R (17/25) q=smallCurvature q := by
    simp only [curvatureZero,pairProduct,pairNorm,smallCurvature,smallRoot,Real.sin_zero,
      mul_zero,add_zero,mul_pow]
    ring
  rw [hCeq] at hC
  have hCm := smallCurvature_antitone (by norm_num : (1:ℝ)∈Icc 1 (283/250)) hq hq.1
  have hCend : smallCurvature 1<259/500 := by
    unfold smallCurvature
    apply quotient_lt_of_square (pow_pos (smallRoot_pos _) 3) (by norm_num)
    rw [show ((smallRoot 1)^3)^2=((smallRoot 1)^2)^3 by ring,smallRoot_sq,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  exact ⟨hD.trans_lt hDend,(hC.trans hCm).trans_lt hCend⟩

theorem interior_negative_slope {p q d : ℝ} (hp : 0<p) (hpU : p≤17/25)
    (hq : q∈Icc (1:ℝ) (283/250)) (hd : d∈Icc 0 frameCap) :
    Vd R p q d<577/500-(241/500)*d+(189/1000)*d^3 := by
  have hq0 : 0<q := by linarith [hq.1]
  have hn := negative_slope_linear_model hp hq0 hd
  obtain ⟨hD,hC⟩ := interior_constants hp hpU hq
  have hCd := mul_le_mul_of_nonneg_right hC.le hd.1
  have hqd := mul_le_mul_of_nonneg_right hq.1 hd.1
  have hqcube := mul_le_mul_of_nonneg_right hq.2 (pow_nonneg hd.1 3)
  nlinarith [pow_nonneg hd.1 3]

theorem interior_D_quadratic {c s : ℝ} (hc : (519/500:ℝ)≤c)
    (hs : s∈Icc 0 frameCap) (hy : (27/100:ℝ)≤Real.sin s) :
    209/200+(3/5)*(s-1/4)^2<secantGainDeriv qCap c s := by
  have ht := transport_trig hs
  have hcos := NegativeESecant.cos_pos hs
  have hroot := LowD.full_root_upper hc hs
  have hmul := mul_le_mul_of_nonneg_right hroot.le ht.2.2.1
  have hslope := LowSame.sine_linear hs
  have hsinle := Real.sin_le hs.1
  have hsq : (s-1/4)^2≤((25/23)*Real.sin s-1/4)^2 := by
    have hleft : 0≤ s-1/4 := by linarith
    have hright : s-1/4≤(25/23)*Real.sin s-1/4 := by linarith
    exact pow_le_pow_left₀ hleft hright 2
  have hscaled := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.cos s))
  have hpoly := Certificate.interior_positive
    (show Real.sin s∈Icc (27/100:ℝ) (129/200) from ⟨hy,by linarith [ht.2.2.2.1]⟩)
  have hid : aeval (Real.sin s) Certificate.interiorPolynomial=
      13/12-(3/8)*Real.sin s-(11/25)*(Real.sin s)^3-
        (1-(Real.sin s)^2)*(209/200+(3/5)*((25/23)*Real.sin s-1/4)^2) := by
    simp [Certificate.interiorPolynomial]
    ring
  rw [hid] at hpoly
  have htrig : 1-(Real.sin s)^2=(Real.cos s)^2 := by nlinarith [Real.sin_sq_add_cos_sq s]
  rw [htrig] at hpoly
  change 209/200+(3/5)*(s-1/4)^2<
    (13/12+Real.sin s-R*Real.sin s/Real.sqrt (gainRadicand c s))/Real.cos s^2
  apply (lt_div_iff₀ (sq_pos_of_pos hcos)).2
  have he : R*Real.sin s/Real.sqrt (gainRadicand c s)=
      (R/Real.sqrt (gainRadicand c s))*Real.sin s := by ring
  rw [he]
  nlinarith only [hpoly,hmul,hscaled]

theorem interior_slope_comparison {p q c s : ℝ}
    (hp : 0<p) (hpU : p≤17/25) (hq : q∈Icc (1:ℝ) (283/250))
    (hc : (519/500:ℝ)≤c) (hs : s∈Icc 0 frameCap)
    (hy : (27/100:ℝ)≤Real.sin s) :
    Vd R p q (frameCap-s)<secantGainDeriv qCap c s := by
  have hn : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hV := interior_negative_slope hp hpU hq hn
  have hD := interior_D_quadratic hc hs hy
  have hcube := mul_nonneg (sq_nonneg (frameCap-s)) (sub_nonneg.mpr hn.2)
  have hreserve : (1/100:ℝ)<1/80-(29/500)*(frameCap-s)+
      (3/5)*(frameCap-s)^2-(189/1000)*(frameCap-s)^3 := by
    norm_num [frameCap] at hcube
    nlinarith [sq_nonneg ((frameCap-s)-290/4677)]
  dsimp [frameCap] at hV hD hreserve
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
end
end
end

section
@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryNegativeSlope

theorem diagonal_slope_comparison {p q s : ℝ}
    (hp : 0<p) (hp0 : p≤p0) (hq : q∈Icc 1 qMax)
    (hs : s∈Icc 0 frameCap) :
    Vd R p q (frameCap-s)<LowD.diagonalFirst s := by
  let d : ℝ := frameCap-s
  have hd : d∈Icc 0 frameCap := ⟨by dsimp [d]; linarith [hs.2],by dsimp [d]; linarith [hs.1]⟩
  by_cases hshort : d≤9/25
  · have hpoly := Certificate.short_model_reserve ⟨hd.1,hshort⟩
    have hid : frameCap-d=s := by dsimp [d]; ring
    rw [hid] at hpoly
    have hV := completed_model hp hp0 hq hd
    have hM := model_nonnegative hd
    have hsin := sin_upper_five hs.1
    have hcos := cos_upper_four hs.1
    have hsinP : Real.sin s≤aeval s PositiveTD.Certificate.S5 := by
      have e : aeval s PositiveTD.Certificate.S5=s-s^3/6+s^5/120 := by
        simp [PositiveTD.Certificate.S5]; ring
      rw [e]
      exact hsin
    have hcosP : Real.cos s≤aeval s PositiveTD.Certificate.C4 := by
      have e : aeval s PositiveTD.Certificate.C4=1-s^2/2+s^4/24 := by
        simp [PositiveTD.Certificate.C4]; ring
      rw [e]
      exact hcos
    have hcos0 := NegativeESecant.cos_pos hs
    have hcos2 := pow_le_pow_left₀ hcos0.le hcosP 2
    have hscale := mul_le_mul_of_nonneg_right hcos2 hM
    have hVscale := mul_le_mul_of_nonneg_right hV.le (sq_nonneg (Real.cos s))
    have hd0 : GlobalGA.Secondary.diagonal-1/2≤2/5 := by linarith [diagonal_bounds.2]
    have h₁ := mul_le_mul_of_nonneg_right hd0 (transport_trig hs).2.2.1
    have h₂ := mul_le_mul_of_nonneg_left hsinP (show (0:ℝ)≤2/5 by norm_num)
    change Vd R p q d<(13/12-(GlobalGA.Secondary.diagonal-1/2)*Real.sin s)/Real.cos s^2
    apply (lt_div_iff₀ (sq_pos_of_pos hcos0)).2
    nlinarith only [hpoly,hscale,hVscale,h₁,h₂]
  · have hV := late_slope_upper hp hp0 hq ⟨(lt_of_not_ge hshort).le,hd.2⟩
    have hD := LowD.diagonal_derivative_lower hs
    norm_num [LowD.M] at hD
    change Vd R p q d<LowD.diagonalFirst s
    linarith

def larger (atH : Bool) (θ : ℝ) : ℝ := if atH then 1 else Explicit.l .low θ

theorem actual_pair_domain (atH : Bool) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<Explicit.k .low θ ∧ Explicit.k .low θ≤p0 ∧
      larger atH θ∈Icc 1 qMax := by
  have hr := Explicit.low_ranges hθ
  refine ⟨by linarith [hr.1],hr.2.1.le,?_⟩
  cases atH
  · refine ⟨hr.2.2.1.le,?_⟩
    show Explicit.l .low θ≤qMax
    norm_num [qMax]
    linarith [hr.2.2.2.1]
  · norm_num [larger,qMax]

theorem actual_diagonal_comparison (atH : Bool) {θ s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 frameCap) :
    Vd R (Explicit.k .low θ) (larger atH θ) (frameCap-s)<LowD.diagonalFirst s := by
  have hp := actual_pair_domain atH hθ
  exact diagonal_slope_comparison hp.1 hp.2.1 hp.2.2 hs

theorem actual_interior_comparison (atH : Bool) {θ s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 frameCap)
    (hint : Explicit.c .low θ≤LowD.sec s) :
    Vd R (Explicit.k .low θ) (larger atH θ) (frameCap-s)<
      secantGainDeriv qCap (Explicit.c .low θ) s := by
  have hr := Explicit.low_ranges hθ
  have hi := LowRanges.interior_ranges hθ hs hint
  have hq : larger atH θ∈Icc (1:ℝ) (283/250) := by
    cases atH
    · exact ⟨hr.2.2.1.le,hi.2.1.le⟩
    · norm_num [larger]
  exact interior_slope_comparison (by linarith [hr.1]) hi.1.le hq
    (by linarith [hr.2.2.2.2.1]) hs hi.2.2.le

theorem correction_negative_monotone (atH : Bool) {θ : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => LowD.correction (Explicit.c .low θ) s+
      V R (Explicit.k .low θ) (larger atH θ) (frameCap-s)) (Icc 0 frameCap) := by
  have hp := actual_pair_domain atH hθ
  have hq : 0<larger atH θ := by linarith [hp.2.2.1]
  apply LowD.add_monotone
    (by linarith [(Explicit.low_ranges hθ).2.2.2.2.1] : 1≤Explicit.c .low θ) le_rfl le_rfl
    (df:=fun s => -Vd R (Explicit.k .low θ) (larger atH θ) (frameCap-s))
  · intro s hs
    have hh := (V_hasDerivAt (R:=R) hp.1 hq
      (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hs.2],by linarith [hs.1]⟩)).comp s
        ((hasDerivAt_id s).const_sub frameCap)
    simpa only [mul_neg_one,Function.comp_def] using hh
  · intro s hs _
    linarith [actual_diagonal_comparison atH hθ hs]
  · intro s hs hint
    linarith [actual_interior_comparison atH hθ hs hint]

theorem original_negative_zero_le (atH : Bool) {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 frameCap) :
    Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) (larger atH (a+z)) frameCap≤
      Explicit.baseline .low a z s+
        V R (Explicit.k .low (a+z)) (larger atH (a+z)) (frameCap-s) := by
  have hh := correction_negative_monotone atH hθ
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hs hs.1
  simp only [LowD.correction_zero,sub_zero,zero_add] at hh
  rw [LowD.baseline_correction .low a z hs]
  linarith

theorem q_le_m {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    Explicit.q .low θ z i≤Explicit.m .low θ z := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hlm := hr.2.2.2.2.2.2.1.trans hm.1
  fin_cases i
  · change 1≤Explicit.m .low θ z
    linarith [hr.2.2.1]
  · exact hlm
  · change max (Explicit.l .low θ) (Explicit.m .low θ z)≤Explicit.m .low θ z
    exact max_le hlm le_rfl

theorem positive_allowance {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    -(109/200)*Explicit.m .low θ z*(frameCap-θ)≤Explicit.U .low θ z i (frameCap-θ) := by
  have hp := LowRanges.pairs hθ hz i
  have hP : frameCap-θ∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1 hp.2.2.1 hP
  have hscale := mul_le_mul_of_nonneg_right (q_le_m hθ hz i) hP.1
  change _≤Explicit.U .low θ z i (frameCap-θ) at hh
  generalize frameCap = F at hh hscale ⊢
  linarith only [hh,hscale]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
end
end
end
