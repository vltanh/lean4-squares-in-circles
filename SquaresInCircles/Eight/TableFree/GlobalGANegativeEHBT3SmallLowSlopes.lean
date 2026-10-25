module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3SmallLowInputs
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# Whole-interval slope comparisons for the small EH1/BT3 low family

Uncompiled Section 4. The separated negative slope is bounded on the
entire coefficient interval by one concave quadratic, then on the whole
remaining-angle interval by the ordinary concavity theorem. The H/G
same-block estimate retains both original masses and uses the signed
norm tangent, not an independently weakened positive/negative split.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds OrdinaryNegativeSlope

open NegativeAPositiveTD.PositiveSlope
open Arithmetic SecondWord.ReferenceTrig

lemma low_k_range {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    k θ∈Icc (2933/5000:ℝ) (1673/2500) := PositiveBT3.Analytic.low_ranges hθ |>.1

lemma at_six_trig :
    (56464/100000:ℝ)<Real.sin (3/5) ∧ Real.sin (3/5)<56465/100000 ∧
      Real.cos (3/5)<82534/100000 := by
  have hlo := sin11_le_sin (show (0:ℝ)≤3/5 by norm_num)
  have hhi := sin_le_sin9 (show (0:ℝ)≤3/5 by norm_num)
  have hcos := cos_le_cos12 (show (0:ℝ)≤3/5 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hlo hhi hcos
  exact ⟨by linarith,by linarith,by linarith⟩

lemma negative_slope_at_six {κ : ℝ} (hk : κ∈Icc (2933/5000:ℝ) (1673/2500)) :
    Vd R κ 1 (3/5)<(3/4:ℝ) := by
  have hk0 : 0<κ := by linarith [hk.1]
  have ht : (3/5:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos hk0 (by norm_num : (0:ℝ)<1)
    (show |-(3/5:ℝ)|≤frameCap by norm_num [frameCap])
  have hn2 := pairNorm_sq hk0 (by norm_num : (0:ℝ)<1)
    (show |-(3/5:ℝ)|≤frameCap by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,one_pow,mul_one,Real.sin_neg] at hn2
  let b : ℝ := 1+κ^2-2*κ*(56465/100000)
  have hb : 0<b := by dsimp [b]; nlinarith [sq_nonneg (κ-56465/100000)]
  have hbN : b≤(pairNorm κ 1 (-(3/5)))^2 := by
    have hh := mul_le_mul_of_nonneg_left at_six_trig.2.1.le (show 0≤2*κ by positivity)
    dsimp [b]
    nlinarith only [hn2,hh]
  have hlin : (3/4:ℝ)+56464/100000≤3/4+Real.sin (3/5) := by linarith [at_six_trig.1]
  have hsquare := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/4+56464/100000) hlin 2
  have hden := mul_le_mul hsquare hbN hb.le (sq_nonneg _)
  have hc0 : 0≤Real.cos (3/5) := by linarith [(transport_trig ht).1]
  have hc2 := pow_le_pow_left₀ hc0 at_six_trig.2.2.le 2
  have hnum := mul_le_mul_of_nonneg_left hc2 (show 0≤R^2*κ^2 by positivity)
  have hpoly : 0<(3/4+(56464/100000:ℝ))^2*b-qCap*κ^2*(82534/100000)^2 := by
    have hchord := mul_nonneg (sub_nonneg.mpr hk.1) (sub_nonneg.mpr hk.2)
    dsimp [b,qCap]
    nlinarith [hk.1,hk.2]
  have hsq : (R*κ*Real.cos (3/5))^2<
      (3/4+Real.sin (3/5))^2*(pairNorm κ 1 (-(3/5)))^2 := by
    rw [mul_pow,mul_pow]
    rw [radius_sq] at hnum ⊢
    nlinarith only [hnum,hden,hpoly]
  have hh := quotient_lt_of_square hn
    (show 0<3/4+Real.sin (3/5) by linarith [at_six_trig.1]) hsq
  have he : Vd R κ 1 (3/5)= -Real.sin (3/5)+R*κ*Real.cos (3/5)/pairNorm κ 1 (-(3/5)) := by
    dsimp [Vd,mixedNDerivative,normD1,pairProduct]
    rw [zero_sub,Real.cos_neg]
    ring
  rw [he]
  linarith only [hh]

lemma late_negative_slope {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc (3/5:ℝ) frameCap) : Vd R (k θ) 1 t<(3/4:ℝ) := by
  have hk := low_k_range hθ
  have hm := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le
    (show 0<k θ by linarith [hk.1]) (show k θ≤1 by linarith [hk.2])
    (show (1:ℝ)≤2*k θ by linarith [hk.1])
    (show (3/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show t∈Icc 0 frameCap from ⟨by linarith [ht.1],ht.2⟩) ht.1
  exact hm.trans_lt (negative_slope_at_six hk)

lemma HG_constants {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    curvatureZero R (k θ) 1<259/500 ∧ NegativeAPositiveTD.Curvature.slopeZero (k θ) 1<1113/1000 := by
  have hk := low_k_range hθ
  have hk0 : 0<k θ := by linarith [hk.1]
  have hkI : k θ∈Icc (0:ℝ) 1 := ⟨hk0.le,by linarith [hk.2]⟩
  have hkm : k θ≤17/25 := by linarith [hk.2]
  obtain ⟨_,_,hC,_⟩ := curvature_constants_normalize (R:=R) hk0 (by norm_num : (0:ℝ)<1)
  obtain ⟨_,hD⟩ := NegativeAPositiveTD.Curvature.constants_normalize hk0 (by norm_num : (0:ℝ)<1)
  have hCm := NegativeAPositiveTD.Curvature.shapeC0q_monotone hkI (by norm_num : (17/25:ℝ)∈Icc 0 1) hkm
  have hDm := NegativeAPositiveTD.Curvature.shapeD0q_monotone hkI (by norm_num : (17/25:ℝ)∈Icc 0 1) hkm
  have href := NegativeEHPositiveTD.SmallLow.G_ratio_constants
  simp only [div_one,mul_one,one_mul] at hC hD
  rw [hC,hD]
  exact ⟨hCm.trans_lt href.1,hDm.trans_lt href.2⟩

def HG_same (θ s : ℝ) : ℝ := gain s+mixedBlock R (k θ) 1 (frameCap-θ) (frameCap-s)
def HG_same_slope (θ s : ℝ) : ℝ :=
  NegativeEH.gD s+Real.sin (frameCap-s)-R*normD1 (k θ) 1 (s-θ)

lemma HG_same_derivative {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc (0:ℝ) (1/10)) : HasDerivAt (HG_same θ) (HG_same_slope θ s) s := by
  have hk := low_k_range hθ
  have ht : |s-θ|≤frameCap := by
    rw [abs_le]; norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2,hθ.1,hθ.2]
  have hN := (pairNorm_hasDerivAt (show 0<k θ by linarith [hk.1])
    (by norm_num : (0:ℝ)<1) ht).comp s ((hasDerivAt_id s).sub_const θ)
  have hc := (Real.hasDerivAt_cos (frameCap-s)).comp s ((hasDerivAt_id s).const_sub frameCap)
  have hh := (NegativeEH.g_hasDerivAt s).add
    (((hasDerivAt_const s ((k θ)*(PositiveAngularEnvelope.phi (frameCap-θ)-1))).add (hc.sub_const 1)).sub
      ((hN.sub_const (pairNorm (k θ) 1 0)).const_mul R))
  convert hh using 1
  · funext x
    rw [HG_same,gain_eq]
    dsimp [mixedBlock]
    rw [show frameCap-θ-(frameCap-x)=x-θ by ring]
    ring
  · dsimp [HG_same_slope]
    ring

lemma HG_same_slope_positive {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc (0:ℝ) (1/10)) : 0<HG_same_slope θ s := by
  have hk := low_k_range hθ
  have hk0 : 0<k θ := by linarith [hk.1]
  have ht : |s-θ|≤frameCap := by
    rw [abs_le]; norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2,hθ.1,hθ.2]
  have hn := NegativeAPositiveTD.Curvature.norm_slope_signed_tangent hk0
    (by norm_num : (0:ℝ)<1) ht
  have hc := HG_constants hθ
  have hC0 : 0≤curvatureZero R (k θ) 1 := by dsimp [curvatureZero,pairNorm]; positivity
  have hshift := mul_le_mul_of_nonneg_left
    (show -(s-θ)≤1/6 by linarith [hs.1,hθ.2]) hC0
  have hC := mul_le_mul_of_nonneg_right hc.1.le (by norm_num : (0:ℝ)≤1/6)
  have hsin : (141/250:ℝ)<Real.sin (frameCap-s) := by
    have hh := trig_bracket (l:=(3/5:ℝ)) (u:=frameCap) (x:=frameCap-s) (by norm_num)
      (by norm_num [frameCap]; linarith [Real.pi_gt_three])
      (by norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2])
    norm_num at hh
    linarith [hh.1]
  have hg := NegativeEH.small_slope hs
  dsimp only [HG_same_slope]
  nlinarith only [hn,hc.2,hshift,hC,hsin,hg]

lemma HG_same_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (HG_same θ) (Icc (0:ℝ) (1/10)) := by
  exact monoOn_of_hasDeriv_nonneg
    (fun s hs => (HG_same_derivative hθ hs).continuousAt.continuousWithinAt)
    (fun s hs => HG_same_derivative hθ (Ioo_subset_Icc_self hs))
    (fun s hs => (HG_same_slope_positive hθ (Ioo_subset_Icc_self hs)).le)

lemma separated_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => gain s+V R (k θ) 1 (frameCap-s)) (Icc (0:ℝ) (1/10)) := by
  have hk := low_k_range hθ
  have hd (s : ℝ) (hs : s∈Icc (0:ℝ) (1/10)) :
      HasDerivAt (fun s => NegativeEH.g s+V R (k θ) 1 (frameCap-s))
        (NegativeEH.gD s+Vd R (k θ) 1 (frameCap-s)*(-1)) s :=
    (NegativeEH.g_hasDerivAt s).add
      ((V_hasDerivAt (R:=R) (show 0<k θ by linarith [hk.1]) (by norm_num : (0:ℝ)<1)
        (show frameCap-s∈Icc 0 frameCap by
          simp only [frameCap,mem_Icc]; constructor <;> linarith [hs.1,hs.2])).comp s
            ((hasDerivAt_id s).const_sub frameCap))
  simp only [gain_eq]
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  have hh := Ioo_subset_Icc_self hs
  have hg := NegativeEH.small_slope hh
  have hv := late_negative_slope hθ
    (show frameCap-s∈Icc (3/5:ℝ) frameCap by
      norm_num [frameCap]; constructor <;> linarith [hh.1,hh.2])
  linarith

lemma positive_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (i : Fin 4) :
    MonotoneOn (fun s => gain s+positive θ (s-θ) i) (Icc θ (1/10:ℝ)) := by
  have hp := coefficients hθ i
  by_cases hi : i=3
  · subst i
    have e : (fun s => gain s+positive θ (s-θ) 3)=fun s => NegativeEH.g s-dCost*(s-θ) := by
      funext x
      simp only [gain_eq,positive,PositiveTD.Hybrid.positive,↓reduceIte]
      ring
    have hd (s : ℝ) : HasDerivAt (fun s => NegativeEH.g s-dCost*(s-θ))
        (NegativeEH.gD s-dCost*1) s :=
      (NegativeEH.g_hasDerivAt s).sub (((hasDerivAt_id s).sub_const θ).const_mul dCost)
    rw [e]
    apply monoOn_of_hasDeriv_nonneg
      (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => hd s)
    intro s hs
    have hg := NegativeEH.small_slope
      (show s∈Icc (0:ℝ) (1/10) from ⟨by linarith [hθ.1,hs.1],hs.2.le⟩)
    dsimp [dCost]
    linarith
  · have e : (fun s => gain s+positive θ (s-θ) i)=
        fun s => NegativeEH.g s+U R (p θ i) (q θ i) (s-θ) := by
      funext x
      simp only [gain_eq,positive,PositiveTD.Hybrid.positive,hi,↓reduceIte]
    have hd (s : ℝ) (hs : s∈Icc θ (1/10:ℝ)) :
        HasDerivAt (fun s => NegativeEH.g s+U R (p θ i) (q θ i) (s-θ))
          (NegativeEH.gD s+Ud (p θ i) (q θ i) (s-θ)*1) s := by
      have hU : HasDerivAt (U R (p θ i) (q θ i)) (Ud (p θ i) (q θ i) (s-θ)) (s-θ) :=
        U_hasDerivAt hp.1 (hp.1.trans_le hp.2.1)
          (show s-θ∈Icc 0 frameCap from ⟨by linarith [hs.1],
            by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩)
      have h := (NegativeEH.g_hasDerivAt s).add (hU.comp s ((hasDerivAt_id' s).sub_const θ))
      exact h
    rw [e]
    apply monoOn_of_hasDeriv_nonneg
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => hd s (Ioo_subset_Icc_self hs))
    intro s hs
    have hg := NegativeEH.small_slope
      (show s∈Icc (0:ℝ) (1/10) from ⟨by linarith [hθ.1,hs.1],hs.2.le⟩)
    have hu := NegativeEH.Slopes.small_positive hp.1 hp.2.1 hp.2.2.1
      (show s-θ∈Icc (0:ℝ) (1/10) from ⟨by linarith [hs.1],by linarith [hs.2,hθ.1]⟩)
    linarith [hp.2.2.2]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.SmallLow
