module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowRanges

/-!
# The positive-surplus endpoint in the low negative-DE family

Uncompiled transcription of Section 5 of the negative-DE TD2 angle
companion. The two fixed-pair slope bounds are proved by positive
squaring at their stated endpoints. The larger-s D estimate applies
only on the diagonal branch; the interior branch retains its actual
smaller coefficient bound. The support transition is the original one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowPositive
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowPositive

namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowD
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowD
