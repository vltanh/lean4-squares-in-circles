module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3DEndpoints

/-!
# Whole signed diagonal charge and wider D endpoint interpolation

Uncompiled Section 3 of the negative-A BT3 note. The exact changes are
alpha=.67, k*=.68 and C*=1.2; the negative initial slope is below 1.113.
The support interpolation is used only in the forward mixed quadrant,
where both actual forces have been proved strictly positive.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3
open PairNormCalculus OrdinaryNegativeSlope

/-- The actual sorted support, including its tangent-zero branch, is
convex along the coefficient interpolation used in the hand proof. -/
theorem D_weight_concave {c x n : ℝ} (hc : c∈Icc 1 Cmax)
    (hx : x∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    ((Cmax-c)/(Cmax-1))*D 1 x (-n)+((c-1)/(Cmax-1))*D Cmax x (-n)≤D c x (-n) := by
  have hp := forward_force_positive hc hx hn
  obtain ⟨a,b,ha,hb,hs,hcircle,he⟩ := sortedSupport_attained hp.1 hp.2
  have hp1 := forward_force_positive (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hx hn
  have hpC := forward_force_positive (show Cmax∈Icc 1 Cmax by norm_num [Cmax]) hx hn
  have h1 := raw_sorted_support ha hb hs hcircle.le hp1.1.le hp1.2.le
  have hC := raw_sorted_support ha hb hs hcircle.le hpC.1.le hpC.2.le
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  have hα : 0≤(Cmax-c)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤(c-1)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hh1 := mul_le_mul_of_nonneg_left h1 hα
  have hhC := mul_le_mul_of_nonneg_left hC hβ
  have hbary : (Cmax-c)/(Cmax-1)+(c-1)/(Cmax-1)=1 := by field_simp [hden.ne']; ring
  have hcoef : (Cmax-c)/(Cmax-1)+((c-1)/(Cmax-1))*Cmax=c := by
    field_simp [hden.ne']; ring
  dsimp [D]
  rw [he]
  dsimp [forceA,forceB] at hh1 hhC
  nlinarith [congrArg (fun z : ℝ => z*(edgeWidth (-n)-1+diagonal)) hbary,
    congrArg (fun z : ℝ => z*(edgeWidth x-1+diagonal)) hcoef,
    congrArg (fun z : ℝ => z*(Real.cos (-n)*a+Real.sin (-n)*b)) hbary,
    congrArg (fun z : ℝ => z*(Real.sin x*a+Real.cos x*b)) hcoef]

theorem mixed_far_endpoint {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) :
    0<D c frameCap (-n)+slope*frameCap-vstar n := by
  have h1 := DEndpoint.endpoint .one hn
  have hC := DEndpoint.endpoint .upper hn
  norm_num [DEndpoint.coefficient] at h1 hC
  have hw := D_weight_concave hc (by norm_num [frameCap]) hn
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  have hα : 0≤(Cmax-c)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤(c-1)/(Cmax-1) := div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hs : (Cmax-c)/(Cmax-1)+(c-1)/(Cmax-1)=1 := by field_simp [hden.ne']; ring
  have hpos : 0<((Cmax-c)/(Cmax-1))*(D 1 frameCap (-n)+slope*frameCap-vstar n)+
      ((c-1)/(Cmax-1))*(D Cmax frameCap (-n)+slope*frameCap-vstar n) := by
    by_cases hα0 : (Cmax-c)/(Cmax-1)=0
    · have hβ1 : (c-1)/(Cmax-1)=1 := by linarith
      simpa [hα0,hβ1] using hC
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne hα (Ne.symm hα0)) h1) (mul_nonneg hβ hC.le)
  nlinarith [congrArg (fun z : ℝ => z*(slope*frameCap-vstar n)) hs]

theorem vstar_slope_zero : Vd R K 1 0<1113/1000 := by
  have hN := pairNorm_pos (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hR2 : (R*K)^2=qCap*K^2 := by rw [mul_pow,radius_sq]
  have hs : (R*K)^2<((1113/1000)*pairNorm K 1 0)^2 := by
    norm_num [pairEnergy,pairProduct,K] at hN2
    norm_num [qCap,K] at hR2 ⊢
    nlinarith
  have hc : R*K<(1113/1000)*pairNorm K 1 0 := by
    nlinarith [Real.sqrt_nonneg qCap]
  have he : Vd R K 1 0=R*K/pairNorm K 1 0 := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [he]
  exact (div_lt_iff₀ hN).2 hc

theorem vstar_linear_upper {n : ℝ} (hn : n∈Icc 0 frameCap) :
    vstar n≤(1113/1000)*n := by
  have hh := V_tangent_zero (p:=K) (q:=1) (by norm_num [K])
    (by norm_num [K]) (by norm_num [K]) hn
  have hm := mul_le_mul_of_nonneg_right vstar_slope_zero.le hn.1
  exact hh.trans hm

theorem diagonal_increment_lower {w x : ℝ} (hw : w∈Icc 1 Cmax)
    (hx : |x|≤frameCap) :
    -slope*positivePart x+(1327/1000)*negativePart x≤diagonalIncrement w x := by
  by_cases hx0 : 0≤x
  · have ht : x∈Icc 0 frameCap := ⟨hx0,by simpa [abs_of_nonneg hx0] using hx⟩
    have hphi : Real.sin x+Real.cos x-1≤x := by
      linarith [Real.sin_le hx0,Real.cos_le_one x]
    have hwd : w*(diagonal-1/2)≤slope := by
      have hm := mul_le_mul_of_nonneg_right hw.2
        (by linarith [diagonal_bounds.1] : 0≤diagonal-1/2)
      have hd := mul_lt_mul_of_pos_left
        (show diagonal-1/2<(2/5:ℝ) by linarith [diagonal_bounds.2])
        (show 0<Cmax by norm_num [Cmax])
      norm_num [slope,Cmax] at *
      linarith
    have hmul := mul_le_mul_of_nonneg_left hphi
      (mul_nonneg (by linarith [hw.1]) (by linarith [diagonal_bounds.1]))
    have hsl := mul_le_mul_of_nonneg_right hwd hx0
    rw [diagonalIncrement,edgeWidth_positive_formula ht]
    simp only [positivePart,negativePart,max_eq_left hx0,
      max_eq_right (neg_nonpos.mpr hx0),mul_zero,add_zero]
    nlinarith
  · have hn : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
    have hh := diagonal_negative_growth hn
    have hg : 0≤(diagonal+1/2)*Real.sin (-x)+(diagonal-1/2)*(1-Real.cos (-x)) := by
      nlinarith [hn.1]
    have hm := mul_le_mul_of_nonneg_right hw.1 hg
    have he : diagonalIncrement w x=
        w*((diagonal+1/2)*Real.sin (-x)+(diagonal-1/2)*(1-Real.cos (-x))) := by
      have hwidth := edgeWidth_negative_formula hn
      simp only [neg_neg] at hwidth
      rw [diagonalIncrement,hwidth,Real.sin_neg,Real.cos_neg]
      ring
    rw [he]
    simp only [positivePart,negativePart,max_eq_right (le_of_not_ge hx0),
      max_eq_left (show 0≤ -x by linarith),mul_zero,zero_add]
    linarith

/-- The explicit diagonal expression is safe throughout each orthant,
so integrating it does not assume that a path stays in that branch. -/
theorem diagonal_residual {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hxy : SignedDomain x y) :
    0≤c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)+
      slope*positiveTotal x y-vstar (negativeTotal x y) := by
  have hangle := signed_domain_angles hxy
  have hx := diagonal_increment_lower hc hangle.1
  have hy := diagonal_increment_lower
    (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hangle.2
  have hN : negativeTotal x y∈Icc 0 frameCap :=
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hxy.2⟩
  have hv := vstar_linear_upper hN
  have he : c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)=
      diagonalIncrement c x+diagonalIncrement 1 y := by
    dsimp [diagonalSupport,forceA,forceB,diagonalIncrement]
    ring
  rw [he]
  have hh : 0≤diagonalIncrement c x+diagonalIncrement 1 y+
      slope*positiveTotal x y-vstar (negativeTotal x y) := by
    dsimp [positiveTotal,negativeTotal] at *
    nlinarith
  exact hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope
