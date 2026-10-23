module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTPairedScalars
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDSlopes

/-!
# The .82 negative derivative required by the short paired-T domain

Uncompiled equation (22). The original H and B endpoint reserves are
unchanged; G uses the exact stronger quartic transcribed in the paired
T certificate. Concavity propagates the endpoint slope to all angles.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope PairNormCalculus
open NonnegativeTotals.NegativeTD

theorem slope_polynomial_identity (E : ℝ) :
    aeval E Certificate.slopePolynomial=qCap*(k E)^2*(l E)^2*capC^2-
      (41/50+l E*capSinHi)^2*((k E)^2+(l E)^2-2*k E*l E*capSinLo) := by
  simp only [Certificate.slopePolynomial,map_sub,map_mul,map_add,map_pow,aeval_C,
    Certificate.slopeK,Certificate.slopeL,aeval_X]
  rw [←NonnegativeTotals.Certificate.eval_rat,←NonnegativeTotals.Certificate.eval_rat,
    ←NonnegativeTotals.Certificate.eval_rat]
  norm_num [k,l,capC,capSinLo,capSinHi,Certificate.h,frameCap,qCap]

theorem G_cap_lower {E : ℝ} (hE : E∈Icc 0 frameCap) :
    (41/50:ℝ)<Vd R (k E) (l E) frameCap := by
  obtain ⟨hk0,hk1,hl0,hl1,hkl,hlc,hbalG,hbalB⟩ := ranges hE
  have hp : 0<k E := by linarith
  have hq : 0<l E := by linarith
  have hn := pairNorm_pos hp hq (t:=-frameCap) (by norm_num [frameCap])
  have hnsq := pairNorm_sq hp hq (t:=-frameCap) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_neg] at hnsq
  have ht := cap_trig_bounds
  have hpoly := Certificate.slope_positive hE
  rw [slope_polynomial_identity] at hpoly
  have hupper := mul_le_mul_of_nonneg_left ht.2.2.2.2.2.1
    (show 0≤2*k E*l E by positivity)
  have hnormsq : (pairNorm (k E) (l E) (-frameCap))^2≤
      (k E)^2+(l E)^2-2*k E*l E*capSinLo := by nlinarith only [hnsq,hupper]
  have hscaled := mul_le_mul_of_nonneg_left hnormsq (sq_nonneg (41/50+l E*capSinHi))
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hR2 := radius_sq
  have hnum : 0≤R*k E*l E*capC := by positivity
  have hcharge : 0<41/50+l E*capSinHi := by
    have hs : 0≤capSinHi := le_trans (by linarith [ht.1] : 0≤Real.sin frameCap) ht.2.2.2.2.2.2
    positivity
  have hcross : (41/50+l E*capSinHi)*pairNorm (k E) (l E) (-frameCap)<R*k E*l E*capC := by
    have hsq : ((41/50+l E*capSinHi)*pairNorm (k E) (l E) (-frameCap))^2<
        (R*k E*l E*capC)^2 := by
      rw [mul_pow,mul_pow,mul_pow,mul_pow,hR2]
      nlinarith only [hpoly,hscaled]
    nlinarith [mul_pos hcharge hn]
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
    (show 0≤R*k E*l E by positivity)
  have hsin := mul_le_mul_of_nonneg_left ht.2.2.2.2.2.2 hq.le
  have hsinN := mul_le_mul_of_nonneg_right hsin hn.le
  have hfinal : (41/50+l E*Real.sin frameCap)*pairNorm (k E) (l E) (-frameCap)<
      R*k E*l E*Real.cos frameCap := by nlinarith only [hcross,hcos,hsinN]
  rw [Vd_formula]
  have hh := (lt_div_iff₀ hn).2 hfinal
  linarith

theorem cap_slope {E : ℝ} (hE : E∈Icc 0 frameCap) (i : Fin 4) :
    (41/50:ℝ)<Vd R (p E i) (q E i) frameCap := by
  have hr := ranges hE
  have hcap : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hH := Vd_first_coefficient (p₀:=3/4) (p₁:=k E) (q:=1)
    (by norm_num) hr.1 (by linarith [hr.2.1]) (by norm_num) hcap
  have hB := Vd_first_coefficient (p₀:=19/20) (p₁:=l E) (q:=c)
    (by norm_num) hr.2.2.1 hr.2.2.2.2.2.1.le (by norm_num [c]) hcap
  fin_cases i
  · change (41/50:ℝ)<Vd R (k E) 1 frameCap
    linarith [H_cap_lower]
  · exact G_cap_lower hE
  · change (41/50:ℝ)<Vd R (l E) c frameCap
    linarith [B_cap_lower]
  · change (41/50:ℝ)<Vd R (k E) 1 frameCap
    linarith [H_cap_lower]

theorem negative_slope {E t : ℝ} (hE : E∈Icc 0 frameCap) (i : Fin 4)
    (ht : t∈Icc 0 frameCap) : (41/50:ℝ)<Vd R (p E i) (q E i) t := by
  have hc := coefficients hE i
  have hm := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le
    hc.1 hc.2.1 (by linarith [hc.2.2.1]) ht
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht.2
  exact (cap_slope hE i).trans_le hm

theorem negative_growth {E x y : ℝ} (hE : E∈Icc 0 frameCap) (i : Fin 4)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    (41/50)*(y-x)≤V R (p E i) (q E i) y-V R (p E i) (q E i) x := by
  have hc := coefficients hE i
  have hd (t : ℝ) (ht : t∈Icc 0 frameCap) := V_hasDerivAt hc.1 (hc.1.trans_le hc.2.1) ht
  exact derivative_reserve
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => (negative_slope hE i (Ioo_subset_Icc_self ht)).le) hx hy hxy

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired
