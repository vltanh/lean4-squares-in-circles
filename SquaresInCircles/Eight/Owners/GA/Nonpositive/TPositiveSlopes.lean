module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PositiveSlopes
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TPairedBounds
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveCoefficientCalculus

/-!
# Eight squares: the positive derivative at the short paired-T endpoint

Concavity first moves the angle to 8/15. The coefficient comparisons
then move q to 27/20 and p to 2269/2000. The last comparison uses exactly
the displayed C10/C12/S11/S9 positive-square reserve, on the whole range.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.PositiveSlope NegativeAPositiveTD.NegativeSlope

namespace PositiveSlope

abbrev star : ℝ := 8/15
abbrev pMax : ℝ := 2269/2000
def norm (r : ℝ) : ℝ := pairNorm 1 r star
def fraction (r : ℝ) : ℝ := (1+r*Real.sin star)/(norm r)^3
def normalized (r : ℝ) : ℝ :=
  r*(Real.cos star-Real.sin star)-R*Real.cos star*r/norm r

theorem star_domain : star∈Icc 0 frameCap := by norm_num [star,frameCap]
theorem star_abs : |star|≤frameCap := by norm_num [star,frameCap]

theorem star_trig : (1/2:ℝ)<Real.sin star ∧ Real.sin star<(51/100:ℝ) ∧
    (43/50:ℝ)<Real.cos star ∧ Real.cos star-Real.sin star<(1/2:ℝ) := by
  obtain ⟨hs,hS,hc,hC⟩ := rational_taylor (t:=8/15) (by norm_num [frameCap])
  have hst : ((8/15:ℚ):ℝ)=star := by norm_num [star]
  rw [hst] at hs hS hc hC
  norm_num [sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,
    PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at hs hS hc hC
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem norm_positive {r : ℝ} (hr : 0<r) : 0<norm r :=
  pairNorm_pos (by norm_num) hr star_abs

theorem norm_square {r : ℝ} (hr : 0<r) :
    (norm r)^2=1+r^2+2*r*Real.sin star := by
  simpa [norm,pairEnergy,pairProduct] using pairNorm_sq (by norm_num : (0:ℝ)<1) hr star_abs

theorem norm_derivative {r : ℝ} (hr : 0<r) :
    HasDerivAt norm ((r+Real.sin star)/norm r) r := by
  have h := TwoPositive.Coefficient.norm_derivative (l:=1) (m:=r) (by norm_num) hr star_abs
  simp only [TwoPositive.Coefficient.normD,one_mul] at h
  exact h

theorem fraction_derivative {r : ℝ} (hr : 0<r) :
    HasDerivAt fraction
      ((-2*Real.sin star-3*r-2*r^2*Real.sin star-r*(Real.sin star)^2)/(norm r)^5) r := by
  have hn := norm_positive hr
  have hp (n : ℕ) : (norm r)^(n+2)=(norm r)^n*(1+r^2+2*r*Real.sin star) := by
    rw [pow_add,norm_square hr]
  have hd := (((hasDerivAt_id r).mul_const (Real.sin star)).const_add 1).div
    ((norm_derivative hr).pow 3) (pow_ne_zero 3 hn.ne')
  convert hd using 1
  · rfl
  · have key : Real.sin star*(norm r)^2-3*(1+r*Real.sin star)*(r+Real.sin star)=
        -2*Real.sin star-3*r-2*r^2*Real.sin star-r*(Real.sin star)^2 := by
      rw [norm_square hr]
      ring
    rw [← key]
    simp only [id,Pi.pow_apply]
    field_simp
    ring

theorem fraction_antitone : AntitoneOn fraction (Icc (1/2:ℝ) (17/20:ℝ)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun r hr => (fraction_derivative (by linarith [hr.1])).continuousAt.continuousWithinAt)
    (fun r hr => fraction_derivative (by linarith [hr.1]))
  intro r hr
  have hr0 : 0≤r := by linarith [hr.1]
  have hs0 : 0≤Real.sin star := by linarith [star_trig.1]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [mul_nonneg (sq_nonneg r) hs0,mul_nonneg hr0 (sq_nonneg (Real.sin star))]
  · exact pow_nonneg (norm_positive (by linarith [hr.1])).le 5

theorem fraction_reserve {r : ℝ} (hr : r∈Icc (1/2:ℝ) (17/20:ℝ)) :
    (1/2:ℝ)<R*Real.cos star*fraction r := by
  have hn := norm_positive (r:=17/20) (by norm_num)
  have hn2 := norm_square (r:=17/20) (by norm_num)
  have hnU : norm (17/20)<(161/100:ℝ) := by nlinarith [star_trig.2.1]
  have hn3 := pow_le_pow_left₀ hn.le hnU.le 3
  have hR : (197/100:ℝ)<R := by linarith [radius_tight.1]
  have hc : 0<Real.cos star := by linarith [star_trig.2.2.1]
  have hmul : (197/100:ℝ)*(43/50)≤R*Real.cos star :=
    mul_le_mul hR.le star_trig.2.2.1.le (by norm_num) (by linarith [hR])
  have hs : (1+(17/20)*(1/2):ℝ)≤1+(17/20)*Real.sin star := by
    linarith [star_trig.1]
  have hnum := mul_le_mul hmul hs (by norm_num : (0:ℝ)≤1+(17/20)*(1/2))
    (mul_nonneg (Real.sqrt_nonneg qCap) hc.le)
  have hcross : (1/2)*(norm (17/20))^3<R*Real.cos star*(1+(17/20)*Real.sin star) := by
    nlinarith only [hn3,hnum]
  have hend : (1/2:ℝ)<R*Real.cos star*fraction (17/20) := by
    dsimp [fraction]
    rw [←mul_div_assoc]
    exact (lt_div_iff₀ (pow_pos hn 3)).2 hcross
  have hm := fraction_antitone hr (show (17/20:ℝ)∈Icc (1/2:ℝ) (17/20:ℝ) by norm_num) hr.2
  exact hend.trans_le (mul_le_mul_of_nonneg_left hm
    (mul_nonneg (Real.sqrt_nonneg qCap) hc.le))

theorem normalized_derivative {r : ℝ} (hr : 0<r) :
    HasDerivAt normalized
      (Real.cos star-Real.sin star-R*Real.cos star*fraction r) r := by
  have hn := norm_positive hr
  have hp (n : ℕ) : (norm r)^(n+2)=(norm r)^n*(1+r^2+2*r*Real.sin star) := by
    rw [pow_add,norm_square hr]
  have hd := ((hasDerivAt_id r).mul_const (Real.cos star-Real.sin star)).sub
    (((hasDerivAt_id r).const_mul (R*Real.cos star)).div (norm_derivative hr) hn.ne')
  convert hd using 1
  · rfl
  · have key : 1+r*Real.sin star=(norm r)^2-r*(r+Real.sin star) := by
      rw [norm_square hr]
      ring
    dsimp only [fraction]
    rw [key]
    simp only [id]
    field_simp

theorem normalized_antitone : AntitoneOn normalized (Icc (1/2:ℝ) (17/20:ℝ)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun r hr => (normalized_derivative (by linarith [hr.1])).continuousAt.continuousWithinAt)
    (fun r hr => normalized_derivative (by linarith [hr.1]))
  intro r hr
  linarith [star_trig.2.2.2,fraction_reserve (Ioo_subset_Icc_self hr)]

theorem Ud_formula (p q t : ℝ) :
    Ud p q t=p*(Real.cos t-Real.sin t)-R*p*q*Real.cos t/pairNorm p q t := by
  simp only [Ud,mixedPDerivative,normD1,pairProduct,sub_zero]
  ring

theorem q_monotone {p q : ℝ} (hp : 0<p) (hq : 0<q) (hqc : q≤c) :
    Ud p c star≤Ud p q star := by
  have hc : 0<c := by norm_num [c,NonnegativeTotals.NegativeTD.c]
  have hn := pairNorm_pos hp hq star_abs
  have hN := pairNorm_pos hp hc star_abs
  have hn2 := pairNorm_sq hp hq star_abs
  have hN2 := pairNorm_sq hp hc star_abs
  dsimp [pairEnergy,pairProduct] at hn2 hN2
  have hsin : 0≤Real.sin star := by linarith [star_trig.1]
  have hpoly : 0≤p^2*(c-q)*(c+q)+2*p*q*c*(c-q)*Real.sin star := by positivity
  have hsq : (q*pairNorm p c star)^2≤(c*pairNorm p q star)^2 := by
    rw [mul_pow,mul_pow,hN2,hn2]
    nlinarith only [hpoly]
  have hcross : q*pairNorm p c star≤c*pairNorm p q star := by
    nlinarith [mul_pos hq hN,mul_pos hc hn]
  have hquot := (div_le_div_iff₀ hn hN).2 hcross
  have hcoef : 0≤R*p*Real.cos star := by
    have hh : 0≤Real.cos star := by linarith [star_trig.2.2.1]
    positivity
  have hm := mul_le_mul_of_nonneg_left hquot hcoef
  rw [Ud_formula,Ud_formula]
  have he (q' : ℝ) : R*p*q'*Real.cos star/pairNorm p q' star=
      (R*p*Real.cos star)*(q'/pairNorm p q' star) := by ring
  rw [he,he]
  linarith

theorem p_monotone {p : ℝ} (hp : p∈Icc (3/4:ℝ) pMax) :
    Ud pMax c star≤Ud p c star := by
  have hc : 0<c := by norm_num [c,NonnegativeTotals.NegativeTD.c]
  have hr : p/c∈Icc (1/2:ℝ) (17/20:ℝ) := by
    dsimp [c,NonnegativeTotals.NegativeTD.c,pMax] at *
    constructor <;> linarith [hp.1,hp.2]
  have hR : pMax/c∈Icc (1/2:ℝ) (17/20:ℝ) := by
    norm_num [pMax,c,NonnegativeTotals.NegativeTD.c]
  have hh := mul_le_mul_of_nonneg_left
    (normalized_antitone hr hR (div_le_div_of_nonneg_right hp.2 hc.le)) hc.le
  rw [Ud_normalized hc,Ud_normalized hc]
  simpa only [normalized,norm,pairNorm_symm,mul_div_assoc,mul_assoc,mul_left_comm,mul_comm] using hh

theorem corner_reserve : -(81/100:ℝ)<Ud pMax c star := by
  obtain ⟨hs,hS,hc,hC⟩ := rational_taylor (t:=8/15) (by norm_num [frameCap])
  have hst : ((8/15:ℚ):ℝ)=star := by norm_num [star]
  rw [hst] at hs hS hc hC
  let CL : ℝ := (cosLo (8/15):ℚ)
  let CU : ℝ := (cosHi (8/15):ℚ)
  let SL : ℝ := (sinLo (8/15):ℚ)
  let SU : ℝ := (sinHi (8/15):ℚ)
  let H : ℝ := pMax*(CL-SU)+81/100
  have hH : 0<H := by
    norm_num [H,CL,SU,pMax,sinHi,cosLo,PositiveTD.Certificate.S9,
      PositiveTD.Certificate.S5,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4]
  have hCU : 0≤CU := by
    norm_num [CU,cosHi,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4]
  have hcert : (237/10000:ℝ)<H^2*(pMax^2+c^2+2*pMax*c*SL)-qCap*pMax^2*c^2*CU^2 := by
    norm_num [H,CL,CU,SL,SU,pMax,c,NonnegativeTotals.NegativeTD.c,qCap,
      sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,
      PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,
      PositiveTD.Certificate.C4]
  have hp : 0<pMax := by norm_num [pMax]
  have hq : 0<c := by norm_num [c,NonnegativeTotals.NegativeTD.c]
  have hn := pairNorm_pos hp hq star_abs
  have hn2 := pairNorm_sq hp hq star_abs
  have hnl : pMax^2+c^2+2*pMax*c*SL≤(pairNorm pMax c star)^2 := by
    have hm := mul_le_mul_of_nonneg_left (show SL≤Real.sin star from hs)
      (show 0≤2*pMax*c by positivity)
    dsimp only [pairEnergy,pairProduct] at hn2
    rw [hn2]
    linarith [hm]
  have hscaled := mul_le_mul_of_nonneg_left hnl (sq_nonneg H)
  have hR2 := radius_sq
  have hcross : R*pMax*c*CU<H*pairNorm pMax c star := by
    have hsq : (R*pMax*c*CU)^2<(H*pairNorm pMax c star)^2 := by
      rw [mul_pow,mul_pow,mul_pow,mul_pow,hR2]
      exact (lt_of_sub_pos (lt_trans (by norm_num) hcert)).trans_le hscaled
    nlinarith [mul_pos hH hn]
  have hnum := mul_le_mul_of_nonneg_left hC (show 0≤R*pMax*c by positivity)
  have hdiv : R*pMax*c*Real.cos star/pairNorm pMax c star<H := by
    exact (div_lt_iff₀ hn).2 (hnum.trans_lt hcross)
  have hlow := mul_le_mul_of_nonneg_left (sub_le_sub hc hS) hp.le
  rw [Ud_formula]
  dsimp [H,CL,SU] at hdiv
  linarith

theorem endpoint {p q : ℝ} (hp : p∈Icc (3/4:ℝ) pMax) (hq : 0<q) (hqc : q≤c) :
    -(81/100:ℝ)<Ud p q star :=
  corner_reserve.trans_le ((p_monotone hp).trans (q_monotone (by linarith [hp.1]) hq hqc))

end PositiveSlope

theorem positive_slope {E t : ℝ} (hE : E∈Icc 0 M) (i : Fin 4)
    (ht : t∈Icc 0 (8/15:ℝ)) : -(81/100:ℝ)<Ud (p E i) (q E i) t := by
  have hEf : E∈Icc 0 frameCap := ⟨hE.1,by norm_num [M,frameCap] at *; linarith [hE.2]⟩
  have hc := coefficients hEf i
  have hp : p E i∈Icc (3/4:ℝ) PositiveSlope.pMax := by
    fin_cases i <;> dsimp [p,NonnegativeTotals.NegativeTD.p,k,l,
      NonnegativeTotals.NegativeTD.k,NonnegativeTotals.NegativeTD.l,PositiveSlope.pMax,M] at * <;>
      constructor <;> linarith [hE.1,hE.2]
  have he := PositiveSlope.endpoint hp (hc.1.trans_le hc.2.1) hc.2.2.2.2
  exact he.trans_le (Ud_antitone hc.1 hc.2.1 (by linarith [hc.2.2.1])
    ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩ PositiveSlope.star_domain ht.2)

theorem positive_growth {E x y : ℝ} (hE : E∈Icc 0 M) (i : Fin 4)
    (hx : x∈Icc 0 (8/15:ℝ)) (hy : y∈Icc 0 (8/15:ℝ)) (hxy : x≤y) :
    -(81/100)*(y-x)≤U R (p E i) (q E i) y-U R (p E i) (q E i) x := by
  have hEf : E∈Icc 0 frameCap := ⟨hE.1,by norm_num [M,frameCap] at *; linarith [hE.2]⟩
  have hc := coefficients hEf i
  have hd (t : ℝ) (ht : t∈Icc 0 (8/15:ℝ)) := U_hasDerivAt hc.1 (hc.1.trans_le hc.2.1)
    (show t∈Icc 0 frameCap from ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩)
  exact derivative_reserve
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => (positive_slope hE i (Ioo_subset_Icc_self ht)).le) hx hy hxy

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired
