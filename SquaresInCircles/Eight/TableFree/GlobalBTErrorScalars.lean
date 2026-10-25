module

public import SquaresInCircles.Eight.TableFree.GlobalBTTailPolynomials
public import SquaresInCircles.Eight.TableFree.GlobalEHSupport

/-!
# Complete positive-zero and negative-AB error gains

The positive-zero gain is concave on the whole frame interval.  The
negative-AB gain uses one degree-six polynomial with a retained
positive quadratic, giving the stronger 9z/2000 reserve directly.
No angle partition or altered feasible frame is introduced.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Polynomial FrameCircleArc

def positiveZeroGain (lambda z : ℝ) : ℝ := z+lambda*Real.sin z-2*lambda*R*Real.sin (z/2)
def positiveZeroGainD (lambda z : ℝ) : ℝ := 1+lambda*Real.cos z-lambda*R*Real.cos (z/2)
def positiveZeroGainDD (lambda z : ℝ) : ℝ := -lambda*Real.sin z+(lambda*R/2)*Real.sin (z/2)

theorem positiveZeroGain_deriv (lambda z : ℝ) :
    HasDerivAt (positiveZeroGain lambda) (positiveZeroGainD lambda z) z := by
  have hh : HasDerivAt (fun y => Real.sin (y/2)) (Real.cos (z/2)*(1/2)) z := by
    have h := (Real.hasDerivAt_sin (z/2)).comp z ((hasDerivAt_id' z).div_const 2)
    exact h
  have h : HasDerivAt (fun y => y+lambda*Real.sin y-2*lambda*R*Real.sin (y/2))
      (1+lambda*Real.cos z-2*lambda*R*(Real.cos (z/2)*(1/2))) z :=
    ((hasDerivAt_id' z).fun_add ((Real.hasDerivAt_sin z).const_mul lambda)).fun_sub
      (hh.const_mul (2*lambda*R))
  unfold positiveZeroGain positiveZeroGainD
  exact h.congr_deriv (by ring)

theorem positiveZeroGainD_deriv (lambda z : ℝ) :
    HasDerivAt (positiveZeroGainD lambda) (positiveZeroGainDD lambda z) z := by
  have hh : HasDerivAt (fun y => Real.cos (y/2)) (-Real.sin (z/2)*(1/2)) z := by
    have h := (Real.hasDerivAt_cos (z/2)).comp z ((hasDerivAt_id' z).div_const 2)
    exact h
  have h : HasDerivAt (fun y => 1+lambda*Real.cos y-lambda*R*Real.cos (y/2))
      (lambda*(-Real.sin z)-lambda*R*(-Real.sin (z/2)*(1/2))) z :=
    (((Real.hasDerivAt_cos z).const_mul lambda).const_add 1).fun_sub (hh.const_mul (lambda*R))
  unfold positiveZeroGainD positiveZeroGainDD
  exact h.congr_deriv (by ring)

theorem sine_half_identity (z : ℝ) : Real.sin z=2*Real.sin (z/2)*Real.cos (z/2) := by
  have h := Real.sin_two_mul (z/2)
  rwa [show 2*(z/2)=z by ring] at h

theorem positiveZeroGain_concave :
    ConcaveOn ℝ (Icc 0 frameCap) (positiveZeroGain kappa) := by
  apply concave_of_deriv2 (fun z _ => positiveZeroGain_deriv kappa z)
    (fun z _ => positiveZeroGainD_deriv kappa z)
  intro z hz
  have hhalf : z/2∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc] at hz ⊢
    constructor <;> linarith [hz.1,hz.2]
  have tr := transport_trig hhalf
  have hr : R<2 := by
    have hh := FrameHighArc.radius_bound
    dsimp [FrameHighArc.radiusUpper] at hh
    linarith
  have hcoeff : R/2-2*Real.cos (z/2)≤0 := by linarith [tr.1]
  have hp := mul_nonpos_of_nonneg_of_nonpos tr.2.2.1 hcoeff
  rw [positiveZeroGainDD,sine_half_identity z]
  dsimp [kappa]
  nlinarith only [hp]

theorem positiveZeroGain_last : 0<positiveZeroGain kappa frameCap := by
  have hs := sin_lower_seven (by norm_num : (0:ℝ)≤7/10)
  have hu := sin_upper_five (by norm_num : (0:ℝ)≤7/20)
  have hhalf : 0≤Real.sin (7/20:ℝ) :=
    (transport_trig (by norm_num [frameCap] : (7/20:ℝ)∈Icc 0 frameCap)).2.2.1
  have hR : R<1979/1000 := by
    have hh := FrameHighArc.radius_bound
    dsimp [FrameHighArc.radiusUpper] at hh
    linarith
  have hp := mul_le_mul hR.le hu hhalf (by norm_num : (0:ℝ)≤1979/1000)
  dsimp [positiveZeroGain,kappa,frameCap]
  norm_num at hs hu hp ⊢
  linarith

theorem positive_zero_gain {lambda z : ℝ} (hl : 0≤lambda) (hlu : lambda≤kappa)
    (hz : z∈Icc 0 frameCap) : 0≤positiveZeroGain lambda z := by
  have hbase := positiveZeroGain_concave.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hz
  have hzero : positiveZeroGain kappa 0=0 := by simp [positiveZeroGain]
  rw [hzero,min_eq_left positiveZeroGain_last.le] at hbase
  have hhalf : z/2∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc] at hz ⊢
    constructor <;> linarith [hz.1,hz.2]
  have hsn := (transport_trig hhalf).2.2.1
  have hR : 1<R := by
    have hh := R_sq
    have hp := R_pos
    norm_num [Q0] at hh
    nlinarith
  have hchange : Real.sin z-2*R*Real.sin (z/2)≤0 := by
    rw [sine_half_identity z]
    nlinarith [mul_nonneg hsn (show 0≤R-Real.cos (z/2) by linarith [Real.cos_le_one (z/2)])]
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlu) hchange
  dsimp [positiveZeroGain] at hbase ⊢
  nlinarith only [hbase,hm]

namespace NegativeABPolynomial

def P : ℚ[X] :=
  C ((49/50)*(847/800)-2009/2000)-C ((49/50)/5)*X+
    C ((2009/2000)/2-(49/50)*(847/800)/6)*X^2+C ((49/50)/60)*X^3+
    C ((49/50)*(847/800)/120-(2009/2000)/24)*X^4-
    C ((49/50)/1800)*X^5-C ((49/50)*(847/800)/5040)*X^6

private theorem coeffs : P.coeff 0=(49/50)*(847/800)-2009/2000 ∧ P.coeff 1=-((49/50)/5) ∧
    P.coeff 2=(2009/2000)/2-(49/50)*(847/800)/6 ∧ P.coeff 3=(49/50)/60 ∧
    P.coeff 4=(49/50)*(847/800)/120-(2009/2000)/24 ∧ P.coeff 5=-((49/50)/1800) ∧
    P.coeff 6=-((49/50)*(847/800)/5040) ∧ ∀ n, 7≤n → P.coeff n=0 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,fun n hn => ?_⟩ <;>
    simp only [P,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C] <;>
    norm_num
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),
    ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),
    ite_eq_right (by omega)]
  norm_num

theorem identity : P=C (P.coeff 0)+C (P.coeff 1)*X+C (P.coeff 2)*X^2+
    PowerTailBounds.tail P 3 4 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := coeffs
  ext n
  simp only [PowerTailBounds.tail,Fin.sum_univ_four,coeff_add,coeff_C_mul,
    coeff_X_pow,coeff_X,coeff_C]
  rcases n with _|_|_|_|_|_|_|n <;> simp [h0,h1,h2,h3,h4,h5,h6]
  exact h7 _ (by omega)

theorem reserves : 0<P.coeff 2-DirectedPowerBounds.negativeNorm P 3 4 (7/10) ∧
    (P.coeff 1)^2<4*(P.coeff 0)*(P.coeff 2-DirectedPowerBounds.negativeNorm P 3 4 (7/10)) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,-⟩ := coeffs
  have hn : DirectedPowerBounds.negativeNorm P 3 4 (7/10)=
      max (-P.coeff 3) 0*(7/10)+max (-P.coeff 4) 0*(7/10)^2+max (-P.coeff 5) 0*(7/10)^3+
        max (-P.coeff 6) 0*(7/10)^4 := by
    simp [DirectedPowerBounds.negativeNorm,Fin.sum_univ_four]
  rw [hn,h0,h1,h2,h3,h4,h5,h6]
  norm_num

theorem positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z P := by
  have hz' : z∈Icc 0 ((7/10:ℚ):ℝ) := by
    simp only [frameCap] at hz
    push_cast
    exact hz
  have hh := DirectedPowerBounds.quadratic_lower identity hz'
  have ha : 0<(P.coeff 2:ℝ)-(DirectedPowerBounds.negativeNorm P 3 4 (7/10):ℝ) := by
    exact_mod_cast reserves.1
  have hd : (P.coeff 1:ℝ)^2<4*
      ((P.coeff 2:ℝ)-(DirectedPowerBounds.negativeNorm P 3 4 (7/10):ℝ))*(P.coeff 0:ℝ) := by
    have h := reserves.2
    exact_mod_cast (by linarith [h] : (P.coeff 1)^2<4*
      (P.coeff 2-DirectedPowerBounds.negativeNorm P 3 4 (7/10))*(P.coeff 0))
  have hp := TailPolynomial.strict_quadratic (x := z) ha hd
  linarith

theorem identity_eval (z : ℝ) : z*aeval z P=
    kappa*((847/800)*(z-z^3/6+z^5/120-z^7/5040)+
      (2/5)*(1-z^2/2+z^4/24-z^6/720)-2/5)-
        (2009/2000)*z*(1-z^2/2+z^4/24) := by
  simp [P,kappa] <;> ring

end NegativeABPolynomial

/-- The sharper negative-AB comparison multiplied by its positive
cosine.  Its 9/2000 reserve survives either original zero owner. -/
theorem negative_AB_gain_scaled {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (2009/2000)*z*Real.cos z≤
      kappa*((847/800)*Real.sin z-(2/5)*(1-Real.cos z)) := by
  have hp := mul_nonneg hz.1 (NegativeABPolynomial.positive hz).le
  rw [NegativeABPolynomial.identity_eval] at hp
  have hs := mul_le_mul_of_nonneg_left (sin_lower_seven hz.1)
    (show 0≤kappa*(847/800) by norm_num [kappa])
  have hc := mul_le_mul_of_nonneg_left (cos_lower_six hz.1)
    (show 0≤kappa*(2/5) by norm_num [kappa])
  have hu := mul_le_mul_of_nonneg_left (cos_upper_four hz.1)
    (mul_nonneg (by norm_num : (0:ℝ)≤2009/2000) hz.1)
  linarith only [hp,hs,hc,hu]

end SquaresInCircles.Eight.TableFree.GlobalBT
