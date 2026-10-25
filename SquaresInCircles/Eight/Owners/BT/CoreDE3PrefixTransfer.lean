module

public import SquaresInCircles.Eight.Owners.BT.CoreDE3PrefixCalculus
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Tangent
public import SquaresInCircles.Eight.Owners.BT.TailTransfer

/-!
# Eight squares: transferring the two saturated derivative certificates

The actual varying-circle numerator lies above its polynomial, its
norm square lies below the explicit energy polynomial, and the exact
other-circle ratio lies below its tangent.  The signed radius choices
then transfer each complete polynomial certificate to the derivative.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open Polynomial FrameCircleArc

theorem radius_lower : (989/500:ℝ)<R := by
  have hs := R_sq
  have hp := R_pos
  norm_num [Q0] at hs
  nlinarith

theorem norm_ratio_lower {N X P b B : ℝ}
    (hN : 0<N) (_hP : 0<P) (hB : 0<B) (hX : N^2≤X) (hb : B≤b) :
    0<X+P^2 ∧ 2*B*P/(X+P^2)≤b/N := by
  have hD : 0<X+P^2 := by nlinarith [sq_pos_of_pos hN,sq_nonneg P]
  have hs : 2*P*N≤X+P^2 := by nlinarith [sq_nonneg (N-P)]
  have hfirst := mul_le_mul_of_nonneg_left hs hB.le
  have hlast := mul_le_mul_of_nonneg_right hb hD.le
  refine ⟨hD,(div_le_div_iff₀ hD hN).2 ?_⟩
  nlinarith only [hfirst,hlast]

theorem polynomial_ratio_lower (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0<aeval p (SaturatedPolynomial.denominator last) ∧
      2*aeval p (SaturatedPolynomial.numerator last)*aeval p (SaturatedPolynomial.P last)/
        aeval p (SaturatedPolynomial.denominator last)≤
          prefixRatio (SaturatedPolynomial.a last:ℝ) p := by
  let a : ℝ := (SaturatedPolynomial.a last:ℝ)
  have ha : 0<a := (SaturatedPolynomial.a_bounds last).2
  have hc := weight_pos hp
  have hN := tailNorm_pos ha hc hp
  have hP : 0<aeval p (SaturatedPolynomial.P last) := by
    linarith [SaturatedPolynomial.envelope_positive last hp]
  have hB := SaturatedPolynomial.numerator_positive last hp
  have hsin := sin7_lower hp.1
  have hcos := cos_lower_six hp.1
  have hsinProduct := mul_le_mul_of_nonneg_left hsin (show 0 ≤ slope*a by
    dsimp [slope]; positivity)
  have hcosProduct := mul_le_mul_of_nonneg_left hcos (mul_nonneg ha.le hc.le)
  have hb : aeval p (SaturatedPolynomial.numerator last)≤
      a*weight p*Real.cos p+slope*a*Real.sin p-slope*weight p := by
    simp only [SaturatedPolynomial.numerator,map_sub,map_add,map_mul,aeval_C,eq_ratCast,
      PrefixPolynomial.c_eval,TailPolynomial.C6_eval,TailPolynomial.S7_eval]
    push_cast
    dsimp [a,slope] at hsinProduct hcosProduct ⊢
    nlinarith only [hsinProduct,hcosProduct]
  have hsq := tailNorm_sq ha hc hp
  have hsinEnergy := mul_le_mul_of_nonneg_left hsin (show 0≤2*a*weight p by positivity)
  have hX : (tailNorm a (weight p) p)^2≤aeval p (SaturatedPolynomial.energy last) := by
    rw [hsq]
    simp only [SaturatedPolynomial.energy,map_sub,map_add,map_mul,map_pow,aeval_C,eq_ratCast,
      PrefixPolynomial.c_eval,TailPolynomial.S7_eval]
    push_cast
    dsimp [a] at hsinEnergy ⊢
    nlinarith only [hsinEnergy]
  have hh := norm_ratio_lower hN hP hB hX hb
  simpa [SaturatedPolynomial.denominator,prefixRatio,a] using hh

def rawDerivative (last : Bool) (p : ℝ) : ℝ :=
  (if last then -3/5+slope*Real.cos p-weight p*Real.sin p else -1/5-kappa*Real.sin p)+
    R*(prefixRatio (SaturatedPolynomial.a last:ℝ) p-
      slope*weight p/tailNorm (SaturatedPolynomial.other last:ℝ) (weight p) 0)

theorem polynomial_affine_lower (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    aeval p (SaturatedPolynomial.affinePart last)+
      (1979/1000)*slope*aeval p (SaturatedPolynomial.tangent last)≤
        (if last then -3/5+slope*Real.cos p-weight p*Real.sin p
          else -1/5-kappa*Real.sin p) := by
  have hsin : Real.sin p≤aeval p SaturatedPolynomial.U := by
    have h := sin_upper_five hp.1
    simp only [SaturatedPolynomial.U,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,
      eq_ratCast]
    push_cast
    linarith
  have hcos := cos_lower_six hp.1
  have hsinW := mul_le_mul_of_nonneg_left hsin (weight_pos hp).le
  have hsinK := mul_le_mul_of_nonneg_left hsin (show 0≤kappa by norm_num [kappa])
  cases last <;>
    simp only [SaturatedPolynomial.affinePart,Bool.false_eq_true,↓reduceIte,
      map_sub,map_add,map_mul,aeval_C,eq_ratCast,
      PrefixPolynomial.c_eval,TailPolynomial.C6_eval] <;>
    norm_num [slope,kappa] at hsinK ⊢ <;> nlinarith only [hcos,hsinW,hsinK]

theorem rawDerivative_positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0<rawDerivative last p := by
  let B : ℝ := aeval p (SaturatedPolynomial.numerator last)
  let P : ℝ := aeval p (SaturatedPolynomial.P last)
  let D : ℝ := aeval p (SaturatedPolynomial.denominator last)
  let L : ℝ := aeval p (SaturatedPolynomial.affinePart last)
  let T : ℝ := aeval p (SaturatedPolynomial.tangent last)
  let q : ℝ := 2*B*P/D
  have hB : 0<B := SaturatedPolynomial.numerator_positive last hp
  have hP : 0<P := by dsimp [P]; linarith [SaturatedPolynomial.envelope_positive last hp]
  have hrat := polynomial_ratio_lower last hp
  have hD : 0<D := hrat.1
  have hq : 0≤q := by dsimp [q]; positivity
  have hratio : q≤prefixRatio (SaturatedPolynomial.a last:ℝ) p := hrat.2
  have hRratio := mul_le_mul radius_lower.le hratio hq R_pos.le
  have hb : 0<(SaturatedPolynomial.other last:ℝ) := by
    cases last <;> norm_num [SaturatedPolynomial.other]
  have hnorm := tailNorm_pos hb (weight_pos hp)
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  have htangent := saturated_tangent_upper last hp
  have hpenalty := mul_le_mul radius_upper.le htangent
    (div_nonneg (weight_pos hp).le hnorm.le) (by norm_num : (0:ℝ)≤1979/1000)
  have hpenalty' := mul_le_mul_of_nonneg_left hpenalty (show 0 ≤ slope by norm_num [slope])
  have hpoly : 0<L*D+2*(989/500)*B*P := by
    simpa [SaturatedPolynomial.H,L,D,B,P] using SaturatedPolynomial.positive last hp
  have hmodel : 0<L+(989/500)*q := by
    have hid : (L+(989/500)*q)*D=L*D+2*(989/500)*B*P := by
      dsimp [q]
      field_simp [hD.ne']
    have hh : 0<(L+(989/500)*q)*D := by rw [hid]; exact hpoly
    exact (mul_pos_iff_of_pos_right hD).1 hh
  have hbase := polynomial_affine_lower last hp
  dsimp [L,T] at hmodel
  dsimp [rawDerivative]
  have e1 : R*(slope*weight p/tailNorm (SaturatedPolynomial.other last:ℝ) (weight p) 0)=
      slope*(R*(weight p/tailNorm (SaturatedPolynomial.other last:ℝ) (weight p) 0)) := by
    ring
  linarith only [hmodel,hbase,hRratio,hpenalty',e1]

theorem firstD_at_m_positive {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<firstD p m := by
  simpa [rawDerivative,firstD,SaturatedPolynomial.a,SaturatedPolynomial.other,kappa,m] using
    rawDerivative_positive false hp

theorem lastD_at_m_positive {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<lastD p m := by
  simpa [rawDerivative,lastD,SaturatedPolynomial.a,SaturatedPolynomial.other,kappa,m] using
    rawDerivative_positive true hp

end SquaresInCircles.Eight.GlobalBT.CoreDE3
