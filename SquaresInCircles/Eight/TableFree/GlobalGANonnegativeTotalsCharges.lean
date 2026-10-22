module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsBalanced
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveAEnvelope

/-!
# The A/E charge polynomials across the actual support transition

Uncompiled transcription of equations (32)--(37). The E envelope uses
its own complete interval: 8/15 on the triangle and 7/10 on the rectangle.
The ratio comparison pays the circle loss only above the genuine support
transition. The angle theta on the rectangle remains on the axis branch.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Charges
open Secondary TensorWholeIntervalPolynomial TwoVariablePolynomial
open TwoPositive.ASupport

theorem radius_upper : R≤(Certificate.Rbar:ℝ) := by
  simpa [Certificate.Rbar,PositiveTD.Certificate.Rbar] using PositiveTD.Certificate.radius_le_Rbar

theorem axial_upper : axial≤(Certificate.abar:ℝ) := by
  simpa [Certificate.abar,TwoPositive.Certificate.abar] using axial_le_abar

theorem sigma_upper : PositiveTD.sigma≤(Certificate.sigmabar:ℝ) := by
  simpa [Certificate.sigmabar,PositiveTD.Certificate.sigmabar] using PositiveTD.Certificate.sigma_le_sigmabar

def polynomialJ (u : ℝ) : ℝ :=
  (aeval u PositiveTD.Certificate.C10-1)/2+
    (1/2-(Certificate.abar:ℝ))*aeval u PositiveTD.Certificate.S9

theorem J_lower_axial {u : ℝ} (hu : u∈Icc 0 frameCap) : polynomialJ u≤axialCharge u := by
  have ht := PositiveTD.Certificate.taylor_bounds hu
  have hs := (transport_trig hu).2.2.1
  have hneg : (1/2:ℝ)-(Certificate.abar:ℝ)≤0 := by norm_num [Certificate.abar]
  have h1 := mul_le_mul_of_nonpos_left ht.2.2.1 hneg
  have h2 := mul_le_mul_of_nonneg_right axial_upper hs
  dsimp [polynomialJ,axialCharge]
  nlinarith only [ht.2.2.2.2.1,h1,h2]

theorem evaluate_J (u : Bivar) (x y : ℝ) :
    evaluate x y (Certificate.J u)=polynomialJ (evaluate x y u) := by
  simp [Certificate.J,polynomialJ]
  ring

def lossRatio (u : ℝ) : ℝ := (u-1/2)^2/u^3

theorem lossRatio_hasDerivAt {u : ℝ} (hu : (1/2:ℝ)≤u) :
    HasDerivAt lossRatio ((u-1/2)*(3/2-u)/u^4) u := by
  have hu0 : u≠0 := by linarith
  have hh := (((hasDerivAt_id u).sub_const (1/2)).pow 2).div
    ((hasDerivAt_id u).pow 3) (pow_ne_zero 3 hu0)
  convert hh using 1
  · rfl
  · field_simp [hu0]
    ring

theorem lossRatio_monotone : MonotoneOn lossRatio (Icc (1/2:ℝ) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun u hu => (lossRatio_hasDerivAt hu.1).continuousAt.continuousWithinAt)
    (fun u hu => lossRatio_hasDerivAt hu.1.le)
  intro u hu
  exact div_nonneg
    (mul_nonneg (by linarith [hu.1]) (by dsimp [frameCap] at hu; linarith [hu.2]))
    (pow_nonneg (by linarith [hu.1] : (0:ℝ)≤u) 4)

theorem loss_quartic {u cap κ : ℝ}
    (hcap : cap∈Icc (1/2:ℝ) frameCap) (hu : u∈Icc (1/2:ℝ) cap)
    (hκ : (Certificate.Rbar:ℝ)/8*lossRatio cap≤κ) :
    (R/8)*u*(u-1/2)^2≤κ*u^4 := by
  have hu0 : 0<u := by linarith [hu.1]
  have hratio := lossRatio_monotone ⟨hu.1,hu.2.trans hcap.2⟩ hcap hu.2
  have hr0 : 0≤lossRatio u := div_nonneg (sq_nonneg _) (pow_nonneg hu0.le 3)
  have hrad := mul_le_mul_of_nonneg_right radius_upper hr0
  have hbound := mul_le_mul_of_nonneg_left hratio
    (show (0:ℝ)≤(Certificate.Rbar:ℝ)/8 by norm_num [Certificate.Rbar])
  have hwhole : (R/8)*lossRatio u≤κ := by nlinarith only [hrad,hbound,hκ]
  have hprod := mul_le_mul_of_nonneg_right hwhole (pow_nonneg hu0.le 4)
  have hid : (R/8)*lossRatio u*u^4=(R/8)*u*(u-1/2)^2 := by
    dsimp [lossRatio]
    field_simp [hu0.ne']
    ring
  rwa [hid] at hprod

theorem charge_quartic {u cap κ : ℝ}
    (hcap : cap∈Icc (1/2:ℝ) frameCap) (hu : u∈Icc 0 cap) (hκ0 : 0≤κ)
    (hκ : (Certificate.Rbar:ℝ)/8*lossRatio cap≤κ) :
    axialCharge u-κ*u^4≤charge u := by
  by_cases haxis : u≤alpha
  · rw [charge,if_pos haxis]
    linarith [mul_nonneg hκ0 (pow_nonneg hu.1 4)]
  · have htransition : u∈Icc alpha frameCap := ⟨(lt_of_not_ge haxis).le,hu.2.trans hcap.2⟩
    have hhalf : u∈Icc (1/2:ℝ) cap := ⟨by linarith [alpha_bounds.1,lt_of_not_ge haxis],hu.2⟩
    have hloss := circle_loss_bound htransition
    have hpay := loss_quartic hcap hhalf hκ
    rw [charge,if_neg haxis]
    linarith

theorem triangle_E_charge {u : ℝ} (hu : u∈Icc 0 (8/15:ℝ)) :
    polynomialJ u-(1/500)*u^4≤charge u := by
  have hframe : u∈Icc 0 frameCap := ⟨hu.1,by dsimp [frameCap]; linarith [hu.2]⟩
  have hh := charge_quartic (κ:=1/500) (by norm_num [frameCap]) hu
    (by norm_num) (by norm_num [Certificate.Rbar,lossRatio])
  linarith [J_lower_axial hframe]

theorem rectangle_E_charge {u : ℝ} (hu : u∈Icc 0 frameCap) :
    polynomialJ u-(29/1000)*u^4≤charge u := by
  have hh := charge_quartic (κ:=29/1000) (by norm_num [frameCap]) hu
    (by norm_num) (by norm_num [Certificate.Rbar,lossRatio,frameCap])
  linarith [J_lower_axial hu]

theorem theta_charge (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.jTheta r)≤charge (Explicit.theta r x y) := by
  cases r
  · have hθ := (Explicit.domains hd).1
    have ht : Explicit.theta .triangle x y∈Icc (1/6:ℝ) frameCap :=
      ⟨by dsimp [Explicit.theta]; linarith [hd.1],hθ.2⟩
    have hcharge := high_charge_lower ht
    have hJ := J_lower_axial hθ
    simp only [Certificate.jTheta,map_sub,map_mul,map_pow,evaluate_scalar,
      evaluate_X,evaluate_J,Certificate.evaluate_theta]
    have he : Explicit.theta .triangle x y-1/6=x := by dsimp [Explicit.theta]; ring
    rw [he] at hcharge
    linarith
  · have hθ := Explicit.rectangle_theta hd
    have hJ := J_lower_axial (Explicit.domains hd).1
    rw [charge_low hθ.2]
    simpa only [Certificate.jTheta,evaluate_J,Certificate.evaluate_theta] using hJ

theorem E_charge (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.jE r)≤charge (Explicit.e r x y) := by
  cases r
  · have he : Explicit.e .triangle x y∈Icc 0 (8/15:ℝ) :=
      ⟨hd.2.1,by dsimp [Explicit.e]; linarith [hd.1,hd.2.2]⟩
    simpa only [Certificate.jE,map_sub,map_mul,map_pow,evaluate_scalar,
      evaluate_J,Certificate.evaluate_e] using triangle_E_charge he
  · simpa only [Certificate.jE,map_sub,map_mul,map_pow,evaluate_scalar,
      evaluate_J,Certificate.evaluate_e] using rectangle_E_charge (Explicit.domains hd).2.1

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Charges
