module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveFullEndpoint
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveATD0LowSource

/-!
# The four-circle high-A scalar envelope

Uncompiled transcription of Sections 4--6 of the positive-A/TD0 proof.
The fourth negative curve is removed by the two coefficient
monotonicities already proved on the entire angle interval. The
remaining three expressions are the exact full-D pure-A certificates.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveATD0
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeSlope OrdinaryPositiveEnvelope

/-- All four original circle supports are relaxed to their full circles. -/
def fullBaseline (k l c : ℝ) : ℝ :=
  k+2*l+2*c+2-fullSupport 1 k-fullSupport l k-fullSupport c l-fullSupport 1 c

def pWeights (k l c : ℝ) : Fin 4→ℝ := ![k,k,min l c,min 1 c]
def qWeights (k l c : ℝ) : Fin 4→ℝ := ![l,1,max l c,max 1 c]

def envelope (k l c a : ℝ) : ℝ :=
  min (V R k 1 a) (min (V R k l a) (V R (min l c) (max l c) a))

def endpoint (k l c a : ℝ) (i j : Fin 4) : ℝ :=
  min (V R (pWeights k l c j) (qWeights k l c j) a)
    (if i=j then M R (pWeights k l c i) (qWeights k l c i) a
     else U R (pWeights k l c i) (qWeights k l c i) (frameCap-a)+
       V R (pWeights k l c j) (qWeights k l c j) frameCap)

theorem high_coefficient_ranges {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    (∀i : Fin 4,0<pWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i) ∧
    (∀i : Fin 4,pWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i≤
      qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i) ∧
    (∀i : Fin 4,2*qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i≤
      3*pWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i) ∧
    (∀i j : Fin 4,5*qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i≤
      6*qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) j) := by
  have hr := TwoPositive.high_ranges ha
  have hp (i : Fin 4) :
      0<pWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i := by
    fin_cases i <;> simp [pWeights,lt_min_iff] <;> linarith [hr.1,hr.2.2.1,hr.2.2.2.2.1]
  have hpq (i : Fin 4) :
      pWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i≤
        qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i := by
    fin_cases i
    · simp only [pWeights,qWeights,Matrix.cons_val_zero]
      linarith [hr.2.1,hr.2.2.1]
    · simp [pWeights,qWeights]
      linarith [hr.2.1]
    · exact min_le_max
    · exact min_le_max
  have hbal (i : Fin 4) :
      2*qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i≤
        3*pWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i := by
    fin_cases i
    · simp [pWeights,qWeights]
      linarith [hr.1,hr.2.2.2.1]
    · simp [pWeights,qWeights]
      linarith [hr.1]
    · change 2*max (TwoPositive.highL a) (TwoPositive.highC a)≤
        3*min (TwoPositive.highL a) (TwoPositive.highC a)
      rcases le_total (TwoPositive.highL a) (TwoPositive.highC a) with hh | hh
      · rw [max_eq_right hh,min_eq_left hh]
        linarith [hr.2.2.1,hr.2.2.2.2.2.1]
      · rw [max_eq_left hh,min_eq_right hh]
        linarith [hr.2.2.2.1,hr.2.2.2.2.1]
    · change 2*max 1 (TwoPositive.highC a)≤3*min 1 (TwoPositive.highC a)
      rcases le_total (1:ℝ) (TwoPositive.highC a) with hh | hh
      · rw [max_eq_right hh,min_eq_left hh]
        linarith [hr.2.2.2.2.2.1]
      · rw [max_eq_left hh,min_eq_right hh]
        linarith [hr.2.2.2.2.1]
  have hq (i : Fin 4) :
      (89/100:ℝ)<qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i ∧
        qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i≤10163/10000 := by
    fin_cases i
    · exact ⟨hr.2.2.1,by simpa [qWeights] using
        (show TwoPositive.highL a≤10163/10000 by linarith [hr.2.2.2.1])⟩
    · norm_num [qWeights]
    · change (89/100:ℝ)<max (TwoPositive.highL a) (TwoPositive.highC a) ∧
        max (TwoPositive.highL a) (TwoPositive.highC a)≤10163/10000
      exact ⟨hr.2.2.1.trans_le (le_max_left _ _),max_le
        (by linarith [hr.2.2.2.1]) hr.2.2.2.2.2.1⟩
    · change (89/100:ℝ)<max 1 (TwoPositive.highC a) ∧
        max 1 (TwoPositive.highC a)≤10163/10000
      exact ⟨(by norm_num : (89/100:ℝ)<1).trans_le (le_max_left _ _),
        max_le (by norm_num) hr.2.2.2.2.2.1⟩
  exact ⟨hp,hpq,hbal,fun i j => by linarith [(hq i).2,(hq j).1]⟩

/-- This is the larger-coordinate comparison of (46)--(50), obtained
from the previously transcribed full-interval comparison. Its certified
ratio interval contains the `[5/6,1]` interval used here. -/
theorem balanced_second_coefficient {p q₀ q₁ a : ℝ}
    (hp : 0<p) (hpq : p≤q₀) (hqq : q₀≤q₁) (hratio : (5/6)*q₁≤p)
    (ha : a∈Icc 0 frameCap) : V R p q₀ a≤V R p q₁ a := by
  have hq₁ : 0≤q₁ := (hp.trans_le (hpq.trans hqq)).le
  have hc : PositiveStressCoefficients.ratio frameCap*q₁≤p := by
    have hm := mul_le_mul_of_nonneg_right
      (show PositiveStressCoefficients.ratio frameCap≤(5/6:ℝ) by
        norm_num [PositiveStressCoefficients.ratio,frameCap]) hq₁
    exact hm.trans hratio
  exact VaryingBComparison.V_larger_coefficient hp hpq hqq hc
    (by norm_num [frameCap]) ha

theorem high_D_redundant {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) {b : ℝ}
    (hb : b∈Icc 0 frameCap) :
    V R (TwoPositive.highK a) 1 b≤
      V R (min 1 (TwoPositive.highC a)) (max 1 (TwoPositive.highC a)) b := by
  have hr := TwoPositive.high_ranges ha
  by_cases hc : TwoPositive.highC a≤1
  · rw [min_eq_right hc,max_eq_left hc]
    exact PositiveTD.V_first_coefficient (by norm_num)
      (by linarith [hr.1]) (by linarith [hr.2.1,hr.2.2.2.2.1])
      (by linarith) hb
  · have hc' : 1≤TwoPositive.highC a := (lt_of_not_ge hc).le
    rw [min_eq_left hc',max_eq_right hc']
    have hfirst : V R (TwoPositive.highK a) 1 b≤V R 1 1 b :=
      PositiveTD.V_first_coefficient (by norm_num)
        (by linarith [hr.1]) (by linarith [hr.2.1]) (by norm_num) hb
    exact hfirst.trans (balanced_second_coefficient (by norm_num) le_rfl hc'
      (by linarith [hr.2.2.2.2.2.1]) hb)

theorem high_pure_lower {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) (j : Fin 4) :
    envelope (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) a≤
      V R (pWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) j)
        (qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) j) a := by
  fin_cases j
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact (min_le_left _ _).trans (high_D_redundant ha ⟨by linarith [ha.1],ha.2⟩)

theorem high_endpoint_lower {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) (i j : Fin 4) :
    envelope (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) a≤
      endpoint (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) a i j := by
  have hd := high_coefficient_ranges ha
  have haf : a∈Icc 0 frameCap := ⟨by linarith [ha.1],ha.2⟩
  have hlen : 0≤frameCap-a := by linarith [ha.2]
  unfold endpoint
  apply le_min (high_pure_lower ha j)
  by_cases hij : i=j
  · subst j
    simp only [if_pos rfl]
    exact (high_pure_lower ha i).trans (M_ge_V (hd.1 i).le
      ((hd.1 i).trans_le (hd.2.1 i)).le (by linarith [hd.2.2.1 i]) haf)
  · simp only [if_neg hij]
    have hu := U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      (hd.1 i) (hd.2.1 i) (by linarith [hd.2.2.1 i])
      (show frameCap-a∈Icc 0 frameCap from ⟨hlen,by linarith [haf.1]⟩)
    have hv := V_growth (hd.1 j) (hd.2.1 j) (by linarith [hd.2.2.1 j]) haf
      (by norm_num [frameCap]) ha.2
    have hc : 0≤(2/3)*qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) j-
        (109/200)*qWeights (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) i := by
      linarith [hd.2.2.2 i j,(hd.1 j).trans_le (hd.2.1 j)]
    have hm := mul_nonneg hc hlen
    linarith [high_pure_lower ha j]

theorem full_A_endpoint (a : ℝ) :
    TwoPositive.Certificate.fullEndpointBase .atA a=
      fullBaseline (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a)+
        TwoPositive.highL a*TwoPositive.ASupport.charge a := by
  norm_num [TwoPositive.Certificate.fullEndpointBase,TwoPositive.Certificate.endpointBase,
    TwoPositive.Certificate.aAt,TwoPositive.Certificate.zAt,PositiveTD.baseline,
    PositiveTD.tilted,edgeWidth,pairWidth,TwoPositive.highK,TwoPositive.highL,TwoPositive.highC,
    fullBaseline]
  ring

theorem high_scalar_positive {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    0<fullBaseline (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a)+
      TwoPositive.highL a*TwoPositive.ASupport.charge a+
        envelope (TwoPositive.highK a) (TwoPositive.highL a) (TwoPositive.highC a) a := by
  have hh := TwoPositive.Certificate.high_six_full_scalars_positive .atA ha
  rw [full_A_endpoint] at hh
  simp only [TwoPositive.Certificate.mAt,TwoPositive.Certificate.zAt,PositiveTD.tilted,
    Real.cos_zero,Real.sin_zero,mul_zero,add_zero,mul_one] at hh
  unfold envelope
  rw [add_min,add_min]
  exact lt_min hh.1 (lt_min hh.2.1 hh.2.2)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveATD0
