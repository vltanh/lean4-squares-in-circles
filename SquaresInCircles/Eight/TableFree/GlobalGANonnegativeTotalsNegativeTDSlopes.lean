module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDScalars
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2NegativeSlopes

/-!
# All three original negative curves have derivative greater than 4/5

Uncompiled transcription of equations (17)--(21). The H and B endpoints
use their original fixed larger coefficient and the monotonic smaller
coefficient. The G endpoint uses the one quartic already specified by
the hand proof. Concavity then covers the entire angle interval.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope PairNormCalculus

def capC : ℝ := aeval frameCap Certificate.C6
def capSinLo : ℝ := aeval frameCap PositiveTD.Certificate.S11
def capSinHi : ℝ := aeval frameCap PositiveTD.Certificate.S9

theorem cap_trig_bounds :
    (3221/5000:ℝ)<Real.sin frameCap ∧ Real.sin frameCap<(129/200:ℝ) ∧
      (478/625:ℝ)<Real.cos frameCap ∧ 0<capC ∧ capC≤Real.cos frameCap ∧
      capSinLo≤Real.sin frameCap ∧ Real.sin frameCap≤capSinHi := by
  have ht := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hs := sin_lower_seven (by norm_num [frameCap] : (0:ℝ)≤frameCap)
  have hc := cos_lower_six (by norm_num [frameCap] : (0:ℝ)≤frameCap)
  have hT := PositiveTD.Certificate.taylor_bounds
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hC : capC=1-frameCap^2/2+frameCap^4/24-frameCap^6/720 := by simp [capC,Certificate.C6]; ring
  have hCp : 0<capC := by norm_num [capC,Certificate.C6,frameCap]
  norm_num [frameCap] at hs
  exact ⟨by linarith,by linarith [ht.2.2.2.1],by linarith [ht.1],hCp,by rw [hC]; exact hc,hT.2.1,hT.2.2.1⟩

theorem Vd_formula (p q t : ℝ) :
    Vd R p q t=-q*Real.sin t+R*p*q*Real.cos t/pairNorm p q (-t) := by
  dsimp [Vd,mixedNDerivative,normD1,pairProduct]
  simp only [zero_sub,Real.cos_neg]
  ring

theorem Vd_scale {p q : ℝ} (hq : 0<q) (t : ℝ) :
    Vd R p q t=q*Vd R (p/q) 1 t := by
  rw [Vd_normalized hq,Vd_normalized (by norm_num : (0:ℝ)<1)]
  norm_num

theorem Vd_first_coefficient {p₀ p₁ q t : ℝ}
    (hp₀ : 0≤p₀) (hp : p₀≤p₁) (hpq : p₁≤q) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) : Vd R p₀ q t≤Vd R p₁ q t := by
  have hr0 : 0≤p₀/q := div_nonneg hp₀ hq.le
  have hr : p₀/q≤p₁/q := div_le_div_of_nonneg_right hp hq.le
  have hr1 : p₁/q≤1 := (div_le_one hq).2 hpq
  have hh := NegativeAPositiveTD.NegativeSlope.normalized_slope_mono hr0 hr hr1 ht
  rw [Vd_scale hq,Vd_scale hq]
  exact mul_le_mul_of_nonneg_left hh hq.le

theorem H_cap_norm : pairNorm (3/4:ℝ) 1 (-frameCap)<3861/5000 := by
  have hs := pairNorm_sq (p:=(3/4:ℝ)) (q:=(1:ℝ)) (by norm_num) (by norm_num)
    (t:=-frameCap) (by norm_num [frameCap])
  have hn := pairNorm_pos (p:=(3/4:ℝ)) (q:=(1:ℝ)) (by norm_num) (by norm_num)
    (t:=-frameCap) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_neg] at hs
  nlinarith [cap_trig_bounds.1]

theorem B_cap_norm : pairNorm (19/20:ℝ) c (-frameCap)<10357/10000 := by
  have hs := pairNorm_sq (p:=(19/20:ℝ)) (q:=c) (by norm_num) (by norm_num [c])
    (t:=-frameCap) (by norm_num [frameCap])
  have hn := pairNorm_pos (p:=(19/20:ℝ)) (q:=c) (by norm_num) (by norm_num [c])
    (t:=-frameCap) (by norm_num [frameCap])
  norm_num [pairEnergy,pairProduct,Real.sin_neg,c] at hs
  nlinarith [cap_trig_bounds.1]

theorem fixed_cap_lower {p q n a : ℝ} (hp : 0<p) (hq : 0<q)
    (hn : 0<n) (hN : pairNorm p q (-frameCap)<n)
    (hreserve : (a+q*(129/200))*n<(1978787/1000000)*p*q*(478/625))
    (ha : 0≤a) : a<Vd R p q frameCap := by
  have hnorm := pairNorm_pos hp hq (t:=-frameCap) (by norm_num [frameCap])
  have hR := NegativeAPositiveTD.NegativeSlope.radius_tight.1
  have hcos := cap_trig_bounds.2.2.1
  have hRcos := mul_le_mul hR.le hcos.le (by norm_num : (0:ℝ)≤478/625)
    (Real.sqrt_nonneg qCap)
  have hnum := mul_le_mul_of_nonneg_right hRcos (mul_nonneg hp.le hq.le)
  have hsin := mul_le_mul_of_nonneg_left cap_trig_bounds.2.1.le hq.le
  have hleft := mul_le_mul
    (show a+q*Real.sin frameCap≤a+q*(129/200) by linarith) hN.le hnorm.le
    (show 0≤a+q*(129/200) by positivity)
  have hcross : (a+q*Real.sin frameCap)*pairNorm p q (-frameCap)<R*p*q*Real.cos frameCap := by
    nlinarith only [hleft,hreserve,hnum]
  have hdiv := (lt_div_iff₀ hnorm).2 hcross
  rw [Vd_formula]
  linarith

theorem H_cap_lower : (103/125:ℝ)<Vd R (3/4) 1 frameCap :=
  fixed_cap_lower (by norm_num) (by norm_num) (by norm_num) H_cap_norm
    (by norm_num) (by norm_num)

theorem B_cap_lower : (1:ℝ)<Vd R (19/20) c frameCap :=
  fixed_cap_lower (by norm_num) (by norm_num [c]) (by norm_num) B_cap_norm
    (by norm_num [c]) (by norm_num)

theorem slope_polynomial_identity (E : ℝ) :
    aeval E Certificate.slopePolynomial=qCap*(k E)^2*(l E)^2*capC^2-
      (4/5+l E*capSinHi)^2*((k E)^2+(l E)^2-2*k E*l E*capSinLo) := by
  have hh : (frameCap:ℝ)=((Certificate.h:ℚ):ℝ) := by norm_num [frameCap,Certificate.h]
  have hC : capC=((Certificate.C6.eval Certificate.h:ℚ):ℝ) := by
    rw [capC,hh,NonnegativeTotals.Certificate.eval_rat]
  have hlo : capSinLo=((PositiveTD.Certificate.S11.eval Certificate.h:ℚ):ℝ) := by
    rw [capSinLo,hh,NonnegativeTotals.Certificate.eval_rat]
  have hhi : capSinHi=((PositiveTD.Certificate.S9.eval Certificate.h:ℚ):ℝ) := by
    rw [capSinHi,hh,NonnegativeTotals.Certificate.eval_rat]
  rw [hC,hlo,hhi]
  simp only [Certificate.slopePolynomial,map_sub,map_mul,map_add,map_pow,aeval_C,
    Certificate.slopeK,Certificate.slopeL,aeval_X,eq_ratCast]
  push_cast
  simp only [k,l,qCap]
  ring

theorem G_cap_lower {E : ℝ} (hE : E∈Icc 0 frameCap) :
    (4/5:ℝ)<Vd R (k E) (l E) frameCap := by
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
  have hscaled := mul_le_mul_of_nonneg_left hnormsq (sq_nonneg (4/5+l E*capSinHi))
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hR2 := radius_sq
  have hC0 := ht.2.2.2.1
  have hnum : 0≤R*k E*l E*capC := by positivity
  have hcharge : 0<4/5+l E*capSinHi := by
    have hs : 0≤capSinHi := le_trans (by linarith [ht.1] : 0≤Real.sin frameCap) ht.2.2.2.2.2.2
    positivity
  have hcross : (4/5+l E*capSinHi)*pairNorm (k E) (l E) (-frameCap)<R*k E*l E*capC := by
    have hsq : ((4/5+l E*capSinHi)*pairNorm (k E) (l E) (-frameCap))^2<
        (R*k E*l E*capC)^2 := by
      rw [mul_pow,mul_pow,mul_pow,mul_pow,hR2]
      nlinarith only [hpoly,hscaled]
    nlinarith [mul_pos hcharge hn]
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
    (show 0≤R*k E*l E by positivity)
  have hsin := mul_le_mul_of_nonneg_left ht.2.2.2.2.2.2 hq.le
  have hsinN := mul_le_mul_of_nonneg_right hsin hn.le
  have hfinal : (4/5+l E*Real.sin frameCap)*pairNorm (k E) (l E) (-frameCap)<
      R*k E*l E*Real.cos frameCap := by nlinarith only [hcross,hcos,hsinN]
  rw [Vd_formula]
  have hh := (lt_div_iff₀ hn).2 hfinal
  linarith

theorem cap_slope {E : ℝ} (hE : E∈Icc 0 frameCap) (i : Fin 4) :
    (4/5:ℝ)<Vd R (p E i) (q E i) frameCap := by
  have hr := ranges hE
  have hcap : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hH := Vd_first_coefficient (p₀:=3/4) (p₁:=k E) (q:=1)
    (by norm_num) hr.1 (by linarith [hr.2.1]) (by norm_num) hcap
  have hB := Vd_first_coefficient (p₀:=19/20) (p₁:=l E) (q:=c)
    (by norm_num) hr.2.2.1 hr.2.2.2.2.2.1.le (by norm_num [c]) hcap
  fin_cases i
  · change (4/5:ℝ)<Vd R (k E) 1 frameCap
    linarith [H_cap_lower]
  · exact G_cap_lower hE
  · change (4/5:ℝ)<Vd R (l E) c frameCap
    linarith [B_cap_lower]
  · change (4/5:ℝ)<Vd R (k E) 1 frameCap
    linarith [H_cap_lower]

theorem negative_slope {E t : ℝ} (hE : E∈Icc 0 frameCap) (i : Fin 4)
    (ht : t∈Icc 0 frameCap) : (4/5:ℝ)<Vd R (p E i) (q E i) t := by
  have hc := coefficients hE i
  have hm := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le
    hc.1 hc.2.1 (by linarith [hc.2.2.1]) ht
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht.2
  exact (cap_slope hE i).trans_le hm

theorem negative_growth {E x y : ℝ} (hE : E∈Icc 0 frameCap) (i : Fin 4)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    (4/5)*(y-x)≤V R (p E i) (q E i) y-V R (p E i) (q E i) x := by
  have hc := coefficients hE i
  have hd (t : ℝ) (ht : t∈Icc 0 frameCap) := V_hasDerivAt (R:=R) hc.1 (hc.1.trans_le hc.2.1) ht
  exact derivative_reserve
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => (negative_slope hE i (Ioo_subset_Icc_self ht)).le) hx hy hxy

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD
