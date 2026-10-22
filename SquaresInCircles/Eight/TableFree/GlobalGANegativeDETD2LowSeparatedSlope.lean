module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowSeparatedData

/-!
# The low separated negative-slope model

Uncompiled transcription of equations (20)--(21) and (37)--(38) of the
negative-DE TD2 angle companion. The signed curvature tangent is
integrated toward the original negative argument. Only afterward is
the smaller coefficient compared with the prescribed endpoint .757.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds OrdinaryNegativeSlope
open NegativeAPositiveTD (Curvature)

theorem negative_norm_tangent {p q d : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    R*normD1 p q (-d)≤Curvature.slopeZero p q+
      curvatureZero R p q*d-curvatureSlope R p q*d^2/2 := by
  have hq := hp.trans_le hpq
  let f : ℝ→ℝ := fun x => curvatureZero R p q*x-
    curvatureSlope R p q*x^2/2-R*normD1 p q (-x)
  have hf (x : ℝ) (hx : x∈Icc 0 frameCap) : HasDerivAt f
      (curvatureZero R p q-curvatureSlope R p q*x-curvature R p q (-x)) x := by
    have hn := ((normD1_hasDerivAt hp hq
      (show |-x|≤frameCap by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)).comp x
        (hasDerivAt_neg x)).const_mul R
    have hlin := (hasDerivAt_id x).const_mul (curvatureZero R p q)
    have hquad := (((hasDerivAt_id x).pow 2).const_mul (curvatureSlope R p q)).div_const 2
    convert (hlin.sub hquad).sub hn using 1 <;> dsimp [f,curvature] <;> ring
  have hm : MonotoneOn f (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => hf x (Ioo_subset_Icc_self hx))
    intro x hx
    have ht := Curvature.curvature_signed_tangent hp hpq hqp
      (show |-x|≤frameCap by rw [abs_neg,abs_of_pos hx.1]; exact hx.2.le)
    nlinarith only [ht]
  have hh := hm (by norm_num [frameCap]) hd hd.1
  dsimp [f] at hh
  simp only [mul_zero,zero_pow,zero_div,sub_zero,neg_zero] at hh
  have he : R*normD1 p q 0=Curvature.slopeZero p q := by
    simp [normD1,Curvature.slopeZero]
  rw [he] at hh
  linarith

theorem negative_slope_model {p q d : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    Vd R p q d≤Curvature.slopeZero p q+(curvatureZero R p q-q)*d-
      q*d^2/6+q*d^3/6 := by
  have hq := hp.trans_le hpq
  have hn := negative_norm_tangent hp hpq hqp hd
  have hC := (Curvature.universal_constants hp hpq hqp).2.1
  have hCsq := mul_le_mul_of_nonneg_right hC.le (sq_nonneg d)
  have hs := mul_le_mul_of_nonneg_left (sin_lower_three hd.1) hq.le
  simp only [Vd,mixedNDerivative,zero_sub]
  nlinarith only [hn,hCsq,hs]

theorem negative_slope_linear_model {p q d : ℝ}
    (hp : 0<p) (hq : 0<q) (hd : d∈Icc 0 frameCap) :
    Vd R p q d≤Curvature.slopeZero p q+(curvatureZero R p q-q)*d+q*d^3/6 := by
  have hn := Curvature.norm_slope_signed_tangent hp hq
    (show |-d|≤frameCap by rw [abs_neg,abs_of_nonneg hd.1]; exact hd.2)
  have hs := mul_le_mul_of_nonneg_left (sin_lower_three hd.1) hq.le
  simp only [Vd,mixedNDerivative,zero_sub]
  nlinarith only [hn,hs]

theorem Vd_smaller_monotone {p P q d : ℝ}
    (hp : 0≤p) (hpP : p≤P) (hPq : P≤q) (hq : 0<q) (hd : d∈Icc 0 frameCap) :
    Vd R p q d≤Vd R P q d := by
  have hh := NegativeAPositiveTD.NegativeSlope.normalized_slope_mono
    (div_nonneg hp hq.le) ((div_le_div_iff_of_pos_right hq).2 hpP)
    ((div_le_one hq).2 hPq) hd
  have hscaled := mul_le_mul_of_nonneg_left hh hq.le
  rw [Vd_normalized hq,Vd_normalized hq]
  simpa only [Vd_normalized (by norm_num : (0:ℝ)<1),div_one,one_mul] using hscaled

def A (d : ℝ) : ℝ := 13753/50000-(13607/12500)*d-d^2/6+d^3/6
def B (d : ℝ) : ℝ := 32033/25000-(2729/4000)*d-(5/24)*d^2+(5/24)*d^3
def model (d : ℝ) : ℝ := B d+(500/389)*(A d)^2

theorem quadratic_model {p q d : ℝ}
    (hp : 0<p) (hp0 : p≤p0) (hq : q∈Icc 1 qMax) (hd : d∈Icc 0 frameCap) :
    Vd R p q d<B d+A d*(q-q0)-(389/2000)*(q-q0)^2 := by
  have hq0 : 0<q := by linarith [hq.1]
  have hpq : p0≤q := by norm_num [p0]; linarith [hq.1]
  have hqp : q≤2*p0 := by norm_num [p0,qMax] at *; linarith [hq.2]
  have hm := Vd_smaller_monotone hp.le hp0 hpq hq0 hd
  have hn := negative_slope_model (p:=p0) (by norm_num [p0]) hpq hqp hd
  have ht := rounded_tangents hq
  have hC := mul_le_mul_of_nonneg_right ht.2.le hd.1
  rw [D0_original] at ht
  rw [C0_original] at hC
  have he : (32033/25000+(13753/50000)*(q-q0)-(389/2000)*(q-q0)^2)+
      (2271/4000-(1107/12500)*(q-q0)-q)*d-q*d^2/6+q*d^3/6=
        B d+A d*(q-q0)-(389/2000)*(q-q0)^2 := by dsimp [A,B,q0]; ring
  rw [←he]
  nlinarith only [hm,hn,ht.1,hC]

theorem completed_model {p q d : ℝ}
    (hp : 0<p) (hp0 : p≤p0) (hq : q∈Icc 1 qMax) (hd : d∈Icc 0 frameCap) :
    Vd R p q d<model d := by
  have hh := quadratic_model hp hp0 hq hd
  dsimp [model]
  nlinarith [sq_nonneg ((q-q0)-(1000/389)*A d)]

theorem model_nonnegative {d : ℝ} (hd : d∈Icc 0 frameCap) : 0≤model d := by
  have hd2 := pow_le_pow_left₀ hd.1 hd.2 2
  have hd3 := pow_nonneg hd.1 3
  have hB : 0≤B d := by
    dsimp [B,frameCap] at *
    nlinarith
  exact add_nonneg hB (mul_nonneg (by norm_num) (sq_nonneg _))

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSeparated
