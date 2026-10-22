module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2Polynomial
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveWeights

/-!
# Whole-domain ranges of the negative-DE weight families

Uncompiled transcription of Section 4.  The high l/c lower bounds keep
the single completed cubic at t=24/25.  The low tilted ratio and the two
high ratios are the displayed whole-interval coefficient sums.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD
open Candidate Secondary PositiveAngularEnvelope

namespace Certificate
open Polynomial WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (L h etaQ)

def lowTiltGap : ℚ[X] := C (69/50)*l .low-c .low*(1+C etaQ*X)
def highRatioGap (upper : Bool) : ℚ[X] :=
  if upper then C (1017/1000)*l .high-c .high else c .high-C (9/10)*l .high

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_tilt_certificate :
    centered 0 L lowTiltGap=expansion 3 (centered 0 L lowTiltGap) ∧
    lowerOn 3 0 L lowTiltGap=(11909/16000000:ℚ) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_ratio_certificate (upper : Bool) :
    centered L h (highRatioGap upper)=expansion 3 (centered L h (highRatioGap upper)) ∧
    (if upper then 2596/10000000 else 0)<lowerOn 3 L h (highRatioGap upper) := by
  cases upper <;> decide

def highLC (atC : Bool) : ℚ[X] :=
  if atC then C (1021248/1000000)-C (168873/1000000)*X-
    C (165381/1000000)*X^2+C (175944/1000000)*X^3
  else C (1005069/1000000)-C (146411/1000000)*X-
    C (157739/1000000)*X^2+C (162815/1000000)*X^3
def highLCReverse (atC : Bool) : ℚ[X] := (highLC atC).comp (C (24/25)-X)
def highLCCoeff (atC : Bool) (j : ℕ) : ℚ := (highLCReverse atC).coeff j
def highLCQuadratic (atC : Bool) : ℚ := highLCCoeff atC 2+(24/25)*highLCCoeff atC 3
def highLCLower : Bool → ℚ | false => 863/1000 | true => 862/1000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_lc_identity (atC : Bool) : highLCReverse atC=
    C (highLCCoeff atC 0)+C (highLCCoeff atC 1)*X+
      C (highLCCoeff atC 2)*X^2+C (highLCCoeff atC 3)*X^3 := by
  cases atC <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_lc_certificate (atC : Bool) :
    highLCCoeff atC 3<0 ∧ 0<highLCQuadratic atC ∧
    highLCLower atC<highLCCoeff atC 0-
      (highLCCoeff atC 1)^2/(4*highLCQuadratic atC) := by
  cases atC <;> decide

theorem high_lc_lower (atC : Bool) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (highLCLower atC:ℝ)<aeval u (highLC atC) := by
  let w : ℝ := 24/25-u
  have hw : w≤24/25 := by dsimp [w]; linarith [hu.1]
  have hcube : w^3≤(24/25)*w^2 := by nlinarith [mul_nonneg (sq_nonneg w) (sub_nonneg.mpr hw)]
  have hc : (highLCCoeff atC 3:ℝ)<0 := by exact_mod_cast (high_lc_certificate atC).1
  have hq : (0:ℝ)<(highLCQuadratic atC:ℝ) := by exact_mod_cast (high_lc_certificate atC).2.1
  have hcub := mul_le_mul_of_nonpos_left hcube hc.le
  have hmin := quadratic_min (a:=(highLCCoeff atC 0:ℝ))
    (b:=(highLCCoeff atC 1:ℝ)) (x:=w) hq
  have hr : (highLCLower atC:ℝ)<(highLCCoeff atC 0:ℝ)-
      (highLCCoeff atC 1:ℝ)^2/(4*(highLCQuadratic atC:ℝ)) := by
    exact_mod_cast (high_lc_certificate atC).2.2
  have he := congrArg (fun p : ℚ[X] => aeval w p) (high_lc_identity atC)
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at he
  have hv : aeval w (highLCReverse atC)=aeval u (highLC atC) := by
    simp [highLCReverse,aeval_comp,w]
  rw [hv] at he
  dsimp [highLCQuadratic] at hmin
  push_cast at hmin
  nlinarith

end Certificate

namespace Explicit

theorem low_ranges {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (2/3:ℝ)<k .low θ ∧ k .low θ<757/1000 ∧
      1<l .low θ ∧ l .low θ<1352/1000 ∧
      (10389/10000:ℝ)≤c .low θ ∧ c .low θ<1864/1000 ∧
      l .low θ≤c .low θ ∧ l .low θ<2*k .low θ := by
  let x : ℝ := 1/6-θ
  have hx : x∈Icc (0:ℝ) (1/6) := ⟨by dsimp [x]; linarith [hθ.2],by dsimp [x]; linarith [hθ.1]⟩
  have hx2 : x^2≤x/6 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hk : k .low θ=6708/10000-(3/20)*x+4*x^2 := by dsimp [k,L,x]; ring
  have hl : l .low θ=10073/10000+(17/10)*x+(11/5)*x^2 := by dsimp [l,L,x]; ring
  have hc : c .low θ=10389/10000+(69/20)*x+9*x^2 := by dsimp [c,L,x]; ring
  have hratio : 2*k .low θ-l .low θ=72935/450000+θ/15+(29/5)*θ^2 := by
    dsimp [k,l,L]
    ring
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith [sq_nonneg (x-3/160)]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hθ.1,sq_nonneg θ]

theorem high_parameter {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) : t θ∈Icc (0:ℝ) 1 := by
  dsimp [t,L]
  exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem high_ranges {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (670158/1000000:ℝ)≤k .high θ ∧ k .high θ≤800408/1000000 ∧
      (863/1000:ℝ)<l .high θ ∧ l .high θ≤1005069/1000000 ∧
      (862/1000:ℝ)<c .high θ ∧ c .high θ≤1021248/1000000 ∧
      l .high θ<(3/2)*k .high θ ∧ c .high θ≤1073/1000-(3/10)*θ := by
  have ht := high_parameter hθ
  have hpow (n : ℕ) : 0≤(t θ)^n ∧ (t θ)^n≤1 :=
    ⟨pow_nonneg ht.1 n,by simpa using pow_le_pow_left₀ ht.1 ht.2 n⟩
  have h2 : (t θ)^2≤t θ := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have h3 : (t θ)^3≤(t θ)^2 := by nlinarith [mul_nonneg (sq_nonneg (t θ)) (sub_nonneg.mpr ht.2)]
  have hl := Certificate.high_lc_lower false ht
  have hc := Certificate.high_lc_lower true ht
  norm_num [Certificate.highLCLower,Certificate.highLC] at hl hc
  have hratio : (3/2)*k .high θ-l .high θ=
      168/1000000+(316988/1000000)*t θ+(167498/1000000)*(t θ)^2-
        (149276/1000000)*(t θ)^3+(15/10000)*(t θ)^4 := by dsimp [k,l]; ring
  have hcorrelation : 1073/1000-(3/10)*θ-c .high θ=
      (1752/1000000)*(1-t θ)+(62/1000000)*t θ+
        t θ*(1-t θ)*(10563/1000000+(175944/1000000)*t θ) := by
    dsimp [c,t,L]
    ring
  have hlast := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    (show 0≤10563/1000000+(175944/1000000)*t θ by linarith [ht.1])
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [k]; nlinarith [(hpow 1).1,(hpow 2).1,(hpow 3).1,(hpow 4).1]
  · dsimp [k]; nlinarith [(hpow 1).2,(hpow 2).2,(hpow 3).2,(hpow 4).2]
  · simpa [l] using hl
  · dsimp [l]; nlinarith [ht.1]
  · simpa [c] using hc
  · dsimp [c]; nlinarith [ht.1]
  · nlinarith [ht.1,(hpow 2).1,(hpow 4).1]
  · nlinarith [ht.1,ht.2]

theorem low_tilted {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) :
    c .low θ≤m .low θ z ∧ m .low θ z<(69/50)*l .low θ := by
  have hr := low_ranges hθ
  have hc : 0<c .low θ := by linarith [hr.2.2.2.2.1]
  have hz' : z∈Icc 0 PositiveTD.Explicit.split := ⟨hz.1,hz.2.trans hθ.2⟩
  have hf := PositiveTD.Explicit.low_factor hz'
  have hlow := mul_le_mul_of_nonneg_left hf.1 hc.le
  have hupper := mul_le_mul_of_nonneg_left
    (show Real.cos z+eta*Real.sin z≤1+eta*θ by
      have he : PositiveTD.eta=eta := rfl
      rw [he] at hf
      dsimp [eta] at *
      linarith [hz.2,hf.2]) hc.le
  have hcert := (WholeIntervalPolynomial.interval_bounds
    (by norm_num [PositiveTD.Certificate.L] : (0:ℚ)<PositiveTD.Certificate.L)
    Certificate.low_tilt_certificate.1 hθ).1
  rw [Certificate.low_tilt_certificate.2] at hcert
  norm_num [Certificate.lowTiltGap,PositiveTD.Certificate.etaQ] at hcert
  exact ⟨by simpa [m,eta,PositiveTD.eta] using hlow,by dsimp [m]; linarith⟩

theorem high_ratios {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (9/10)*l .high θ<c .high θ ∧ c .high θ<(1017/1000)*l .high θ := by
  have hfalse := Certificate.high_ratio_certificate false
  have htrue := Certificate.high_ratio_certificate true
  have hL := WholeIntervalPolynomial.positive_on_interval
    (by norm_num [PositiveTD.Certificate.L,PositiveTD.Certificate.h] :
      PositiveTD.Certificate.L<PositiveTD.Certificate.h) hfalse.1 hfalse.2 hθ
  have hU := WholeIntervalPolynomial.positive_on_interval
    (by norm_num [PositiveTD.Certificate.L,PositiveTD.Certificate.h] :
      PositiveTD.Certificate.L<PositiveTD.Certificate.h) htrue.1 htrue.2 hθ
  norm_num [Certificate.highRatioGap] at hL hU
  exact ⟨by linarith,by linarith⟩

theorem high_tilted {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) :
    k .high θ<m .high θ z ∧ m .high θ z<(1061/1000)*l .high θ ∧
      m .high θ z<(1066/1000:ℝ) ∧ (2/3)*l .high θ<m .high θ z := by
  have hr := high_ranges hθ
  have hrat := high_ratios hθ
  have hc : 0<c .high θ := by linarith [hr.2.2.2.2.1]
  have hl : 0<l .high θ := by linarith [hr.2.2.1]
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2,hθ.2]⟩
  have hlow₀ := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_lower hz') hc
  have hupper := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_upper z) hc
  have hlow : (19/20)*c .high θ<m .high θ z := by
    simpa [m,eta,PositiveTD.eta,mul_comm] using hlow₀
  change m .high θ z<c .high θ*(1043/1000) at hupper
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,
      hr.2.2.2.2.2.1,hrat.1,hrat.2]

theorem family_positive (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left f) (right f)) (hz : z∈Icc 0 θ) :
    0<k f θ ∧ 0<l f θ ∧ 0<c f θ ∧ 0<m f θ z := by
  cases f
  · have hr := low_ranges hθ
    have hm := low_tilted hθ hz
    exact ⟨by linarith [hr.1],by linarith [hr.2.2.1],
      by linarith [hr.2.2.2.2.1],by linarith [hr.2.2.2.2.1,hm.1]⟩
  · have hr := high_ranges hθ
    have hm := high_tilted hθ hz
    exact ⟨by linarith [hr.1],by linarith [hr.2.2.1],
      by linarith [hr.2.2.2.2.1],by linarith [hr.1,hm.1]⟩

theorem high_pairs {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (i : Fin 3) : 0<p .high θ z i ∧ p .high θ z i≤q .high θ z i ∧
      (2/3)*q .high θ z i<p .high θ z i ∧
      (863/1000:ℝ)<q .high θ z i ∧ q .high θ z i<(1066/1000:ℝ) := by
  have hr := high_ranges hθ
  have hm := high_tilted hθ hz
  have hk : 0<k .high θ := by linarith [hr.1]
  have hl : 0<l .high θ := by linarith [hr.2.2.1]
  have hm0 : 0<m .high θ z := hk.trans hm.1
  have hkl : k .high θ<l .high θ := by linarith [hr.2.1,hr.2.2.1]
  fin_cases i
  · simp only [p,q,Matrix.cons_val_zero]
    exact ⟨hk,by linarith [hr.2.1],by linarith [hr.1],by norm_num,by norm_num⟩
  · simp only [p,q,Matrix.cons_val_succ,Matrix.cons_val_zero]
    exact ⟨hk,hkl.le,by linarith [hr.2.2.2.2.2.2.1],hr.2.2.1,
      by linarith [hr.2.2.2.1]⟩
  · simp only [p,q,Matrix.cons_val_succ,Matrix.cons_val_zero]
    refine ⟨lt_min hl hm0,min_le_max,?_,?_,?_⟩
    · rcases le_total (l .high θ) (m .high θ z) with hh | hh
      · rw [min_eq_left hh,max_eq_right hh]
        nlinarith [hm.2.1]
      · rw [min_eq_right hh,max_eq_left hh]
        exact hm.2.2.2
    · exact hr.2.2.1.trans_le (le_max_left _ _)
    · exact max_lt (by linarith [hr.2.2.2.1]) hm.2.2.1

theorem high_q_ratio {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (i j : Fin 3) : q .high θ z i<(29/25)*q .high θ z j := by
  have hi := high_pairs hθ hz i
  have hj := high_pairs hθ hz j
  have hr := high_ranges hθ
  have hm := high_tilted hθ hz
  by_cases hl : 1≤l .high θ
  · have hj1 : 1≤q .high θ z j := by
      fin_cases j <;> simp only [q,Matrix.cons_val_succ,Matrix.cons_val_zero]
      · exact le_rfl
      · exact hl
      · exact hl.trans (le_max_left _ _)
    nlinarith [hi.2.2.2.2]
  · by_cases hm1 : m .high θ z≤1
    · have hi1 : q .high θ z i≤1 := by
        fin_cases i <;> simp only [q,Matrix.cons_val_succ,Matrix.cons_val_zero]
        · exact le_rfl
        · exact (lt_of_not_ge hl).le
        · exact max_le (lt_of_not_ge hl).le hm1
      nlinarith [hj.2.2.2.1]
    · have hiM : q .high θ z i≤m .high θ z := by
        fin_cases i <;> simp only [q,Matrix.cons_val_succ,Matrix.cons_val_zero]
        · exact (lt_of_not_ge hm1).le
        · linarith [lt_of_not_ge hl,lt_of_not_ge hm1]
        · exact max_le (by linarith [lt_of_not_ge hl,lt_of_not_ge hm1]) le_rfl
      have hjL : l .high θ≤q .high θ z j := by
        fin_cases j <;> simp only [q,Matrix.cons_val_succ,Matrix.cons_val_zero]
        · exact (lt_of_not_ge hl).le
        · exact le_rfl
        · exact le_max_left _ _
      nlinarith [hm.2.1,hr.2.2.1]

end Explicit
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD
